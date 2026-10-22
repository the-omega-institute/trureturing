# Recursive relational observation: finite encoded checkpoints for a coupled unknown-ray family

> Append-only reference input for `generic-v1`. This volume records an
> ordinary mathematical result about the finite checkpoint interface declared
> below. It carries no Lean certification, physical implementation claim, or
> literature-priority claim.

## 1. Source contract, overlap, and the checkpoint interface

The source is [FIB ATOM recursive holographic boundary geometry, Continuation
VII](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VII.md)
at immutable revision `4442fb66c4d7017bb7b932cc63f058b46c83b71c`, blob
`d3b82c91d43cea5e84d75328161f8a31eefb1e84`, content SHA256
`8bc226e06d503cb5e698c3ea3346dcb57504ef32d89b90fd1dcca0b2057d50ca`.
Sections 201–213 supply the two-copy state, the common twirl, the signed
charge blocks, the fifteen probabilities, and the pointwise PPT/NPT and
inverse-filter results used here. Sections 214–225, published at the same
revision, analyze a fixed known-parameter postfilter problem, its finite
attainer, and a stricter single-product ceiling. Section 225 explicitly
leaves a $q$-independent operation with unknown active/spectator
basis unresolved. The present result addresses a different, finite
source-independent encoded checkpoint and does not duplicate that
known-parameter frontier.

The common preparation is exactly VII Definition 201.1 and Assumption 201.2:
two independent compatible UNTWiRLED preparations of the same one-copy
resource, followed by one common local-number twirl. The creation order is
$(\ell _1,r_1,R_1,\ell _2,r_2,R_2)$, the cut is
$(\ell _1,\ell _2)\mid(r_1,R_1,r_2,R_2)$, and the regrouping sign is

$$
(-1)^{(n_{r_1}+n_{R_1})n_{\ell _2}}.
$$

The transpose below is ordinary Alice partial transpose in this fixed
occupation tensor. The enlarged independent-ray orbit is a declared
mathematical preparation family; it is not passive or native reachability and
does not provide a source label, an external phase reference, preparations
beyond the declared two copies, or a correlated programme.

Fix

$$
t=\frac14,\qquad s=1-t=\frac34,\qquad
Z=2(1+t)^2=\frac{25}{8},\qquad
x_* = \frac{3-\sqrt5}{6}.
$$

For a unit vector $\eta\in\mathbb C^2$ and
$x\in(x_*,1/2]$, set

$$
v_{x,\eta}=(\sqrt{x},\sqrt{1-x}\,\eta),\qquad
w_\eta=(0,\eta),
$$

and let $\Omega_{x,\eta}$ be the normalized $64$-dimensional two-copy
resource of VII §§201–203 for these vectors. No $x$ or $\eta$ label is
delivered to the controller. This is a coupled subfamily of the independently
assignable rays in VII Definition 201.1, not the whole independent-ray family
or a claimed realization by the native principal-root metrics.

**Definition 1.1 (finite encoded checkpoint bank).** A finite bank is a list

$$
\mathcal B=\{(A_j,B_j):1\le j\le N\},\qquad
A_j:\mathbb C^4\to\mathbb C^2,\quad
B_j:\mathbb C^{16}\to\mathbb C^2,
$$

whose matrices are fixed independently of both $x$ and $\eta$. Its refined
unnormalized successor on the two output qubits is

$$
\tau_j(x,\eta)=(A_j\otimes B_j)\Omega_{x,\eta}
(A_j\otimes B_j)^*.
\tag{1.1}
$$

The bank is a mathematical superclass of finite source-independent local
instruments. A complete finite instrument may have a finite actual record set
$\mathcal R$ and a refinement map $j\mapsto r(j)$. Its actual coarse successor,
probability, and flagged successor are

$$
\Phi_r(\Omega)=\sum_{j:r(j)=r}\tau_j(\Omega),\qquad
p_r=\operatorname{Tr}\Phi_r(\Omega),\qquad
\widehat\Omega=\bigoplus_{r\in\mathcal R}\Phi_r(\Omega).
\tag{1.2}
$$

The refinement index $j$ is not an additional controller observation. It is
only a finite Kraus decomposition of an actual CP successor. Records already
written by the instrument are exactly the $r$'s (and any declared finite
subrecords folded into them). A complete instrument includes every success,
failure, and stopped-residue leaf. With the disjoint record partition
$\mathcal R=\mathcal R_{\rm succ}\sqcup\mathcal R_{\rm fail}\sqcup
\mathcal R_{\rm res}$, its actual masses are

$$
p_{\rm succ}=\sum_{r\in\mathcal R_{\rm succ}}p_r,\qquad
p_{\rm fail}=\sum_{r\in\mathcal R_{\rm fail}}p_r,\qquad
p_{\rm res}=\sum_{r\in\mathcal R_{\rm res}}p_r,\qquad
p_{\rm succ}+p_{\rm fail}+p_{\rm res}=1.
\tag{1.3}
$$

A residual quantum system
that remains callable after the checkpoint is part of a larger interface and
is not silently treated as a two-qubit output.

## 2. The moving boundary kernel

The substitutions in VII §202 are, for the family above,

$$
\begin{aligned}
D&=tI_2+s(1-x)\eta\eta^*,&
E&=tI_2-ts\eta\eta^*,\\
f&=s\sqrt{x(1-x)}\,\eta,&g=0,\\
c&=t+sx,&b=t,&d=t^2,\\
q_0&=9x(1-x),&q_3&=0.
\end{aligned}
\tag{2.1}
$$

The exact identity $9x_*(1-x_*)=1$ gives

$$
f=t\eta,\qquad E-ff^*=t(I_2-\eta\eta^*).
\tag{2.2}
$$

All other factors in VII §§203–206 are strictly positive at $x=x_*$. More
explicitly, the one-dimensional-Alice blocks are tensor products of the
positive blocks $A_0$ and $A_1$; the $N_B=0,4$ blocks are $cI_2$ and $bdI_2$;
the $N_B=1$ partial transpose is unitarily equivalent to

$$
cD\oplus cD\oplus(E-ff^*)\oplus(E+ff^*);
$$

and, since $g=0$, the two $N_B=2$ blocks in VII (206.4) are positive
diagonal block matrices with entries $E\otimes D$, $D\otimes E$, and $d$.
The $N_B=3$ blocks are $bE$ and $dD$ (twice). Thus the only zero direction
of $M_\eta:=\Omega_{x_*,\eta}^{T_A}$ is the null direction of $E-ff^*$.

**Lemma 2.1 (rank-one moving kernel).** For every unit $\eta$,
$M_\eta\succeq0$ has rank $63$, and its kernel is spanned by

$$
\chi_\eta
 =p\otimes L(\eta)+q\otimes R(\eta),
\qquad p=|10\rangle,\quad q=|01\rangle,
\tag{2.3}
$$

where, in the two-copy Bob one-particle sector,

$$
L(\eta)=\eta\otimes|0\rangle,\qquad
R(\eta)=|0\rangle\otimes\eta.
\tag{2.4}
$$

The Bob Schmidt support of $\chi_\eta$ is

$$
K_\eta=\operatorname{span}\{L(\eta),R(\eta)\}.
\tag{2.5}
$$

Distinct projective rays give distinct supports: $K_\eta=K_\zeta$ implies
$\mathbb C\eta=\mathbb C\zeta$.

**Proof.** Equation (2.2) and the complete normal forms of VII §206 show
that exactly one eigenvalue vanishes. Ordinary Alice transposition moves the
negative CAR off-diagonal of VII (205.2) to the two rail components in (2.3),
so the null combination has the displayed plus sign. Projecting (2.5) to
the first Bob-copy summand recovers the line $\mathbb C\eta$; hence equal
supports imply equal projective rays. $\square$

The same source gives the full-rank lower bound needed for actual masses.
Since $R\succeq t^2I_8$, the common twirl and the normalization in VII §203
give

$$
\Omega_{x,\eta}\succeq\frac{t^4}{Z^2}I_{64}
=\frac1{2500}I_{64}
\tag{2.6}
$$

for every $x$ in the declared interval and every unit $\eta$.

## 3. Uniform finite compression obstruction

**Theorem 3.1 (no uniform finite two-qubit encoded checkpoint).** For every
finite bank $\mathcal B$ of Definition 1.1, there exist a unit ray $\eta$ and
$\epsilon>0$ with $x_*+\epsilon<1/2$ such that, for every
$x\in(x_*,x_*+\epsilon)$ and every $j\le N$,

$$
\tau_j(x,\eta)^{T_A}\succeq0.
\tag{3.1}
$$

Nevertheless, every source $\Omega_{x,\eta}$ in this same interval has a
lawful source-dependent encoded NPT branch of strictly positive probability
in the sense of VII §208. Consequently no one finite source-independent bank
in this output class supplies an NPT two-qubit checkpoint with positive
probability for every source in the declared unknown-ray family.

**Proof.** First consider a bank element for which either $A_j$ or $B_j$ has
rank at most one. Its positive output has one-dimensional support on one
party and is therefore a separable, hence PPT, operator for every source.

Suppose both ranks are two. Put

$$
C_j=\overline{A_j}\otimes B_j.
$$

Then $C_j$ has full row rank and

$$
\tau_j(x_*,\eta)^{T_A}=C_jM_\eta C_j^*.
\tag{3.2}
$$

Because $C_j^*$ is injective and $M_\eta$ has the one-dimensional kernel
in Lemma 2.1, the compression in (3.2) fails to be positive definite only
if $\chi_\eta\in\operatorname{ran}(C_j^*)$. But

$$
\operatorname{ran}(C_j^*)
 =\operatorname{ran}(A_j^{\mathsf T})\otimes
  \operatorname{ran}(B_j^*).
\tag{3.3}
$$

Membership forces the Bob Schmidt support $K_\eta$ to be contained in
$\operatorname{ran}(B_j^*)$. Both spaces have dimension two, so it forces
$K_\eta=\operatorname{ran}(B_j^*)$. By Lemma 2.1 a fixed rank-two $B_j$
can match at most one projective ray. There are finitely many such $j$;
choose a unit ray $\eta$ outside their finite exceptional set. For this
choice every rank-two/rank-two compression is positive definite at $x_*$.

Each matrix in (3.2) depends continuously on $x$. Positive definiteness is
open, and there are only finitely many bank elements, so one common
$\epsilon>0$ exists for which all of them remain positive definite on
$(x_*,x_*+\epsilon)$. Shrink it so that $x_*+\epsilon<1/2$.
The rank-deficient elements remain PPT by the first paragraph. This proves
(3.1).

For the pointwise comparison, use the source-dependent direction from VII
§208. In this family $E\eta=t^2\eta$, so its inverse direction is
$k_0=\eta$. With

$$
a_0=t^2,\qquad m_0=s^2x(1-x),\qquad B_0=t+m_0,
$$

the legal encoded branch has unnormalized matrix

$$
X_0=\frac1{Z^2}
\begin{pmatrix}
t^2&0&0&0\\
0&B_0&-m_0&0\\
0&-m_0&B_0&0\\
0&0&0&t^2
\end{pmatrix}.
\tag{3.4}
$$

Because $9x(1-x)>1$ on $(x_*,1/2]$, $m_0>t^2$. The partial transpose of
(3.4) has eigenvalue $(t^2-m_0)/Z^2<0$, while

$$
\operatorname{Tr}X_0=\frac{2(t^2+B_0)}{Z^2}>0.
\tag{3.5}
$$

Thus each selected source has a positive-probability pointwise NPT witness,
but its direction is $\eta$ and is not an acquired controller input. This
is a source-specific existence statement, not a uniform selection rule.
$\square$

## 4. Same-run finite-instrument meaning

**Definition 4.1 (declared finite instrument).** A declared finite instrument
is a bounded finite-outcome local adaptive tree with source-independent finite
dimensional product ancillas, finite local Kraus menus, and complete actual
records. Every local Kraus menu, adaptive policy, coin law, ancillary and
controller initialization, and selector is fixed across the whole
$(x,\eta)$ family. Choices use only actually acquired finite record prefixes
and the source-independent initialized control; a coin value is a selector
input only when actually generated and made available in that record.
All randomization is included in the finite tree. Hidden Kraus indices,
unacquired $x,\eta$ labels, source-correlated programmes, and
parameter-dependent reference inputs are unavailable. Outcome probabilities
may depend on the source through the declared quantum instrument.
Every complete leaf includes the records written before stopping,
its unnormalized two-qubit successor, and its success/failure or residue
label. All unused quantum systems are either discarded or declared outside
the checkpoint; no discarded system is callable by a later consumer.

Refining each local node into its finitely many Kraus components gives a
finite list of product maps $A_j\otimes B_j$ from the original
$\mathbb C^4\otimes\mathbb C^{16}$ input to the two output qubits. The
refinement labels are hidden Kraus indices, not controller observations.
Conversely, no assertion is made that every finite programme, finite carrier,
finite controller, or almost-surely stopping adaptive process has such a
globally finite list. An unbounded or continuous effective menu is outside
Definition 4.1 even when every realized run is finite.

**Corollary 4.2 (actual records, failures, and retained use).** For every
declared finite instrument there are $\eta$ and $\epsilon$ supplied by
Theorem 3.1 such that every $x\in(x_*,x_*+\epsilon)$ has the following
properties.

1. Every refined leaf is PPT by (3.1). For each actual record $r$,
   $\Phi_r(\Omega_{x,\eta})$ is PPT because it is a positive sum of refined
   leaves. Retaining the record produces the block-diagonal PPT operator
   $\widehat\Omega$ in (1.2), and forgetting it also preserves PPT.
2. Equation (2.6) gives, for every nonzero refined leaf,

   $$
   p_j=\operatorname{Tr}\tau_j\ge
   \frac1{2500}\operatorname{Tr}(A_j^*A_j)\operatorname{Tr}(B_j^*B_j)>0.
   \tag{4.1}
   $$

   Zero maps have zero mass. The complete instrument retains every actual
   success and failure mass, so $\sum_r p_r=1$; no failure is converted into
   an omitted branch or a selected conditional state at zero probability.
3. Any later finite local or separable continuation acting only on the two
   output qubits and the actually retained classical records keeps every
   successor PPT: each refined continuation is another positive product
   congruence, and positive sums and classical flags preserve positivity of
   the partial transpose. Hence the pointwise NPT branch in (3.4) cannot be
   recovered from this checkpoint interface.
4. If a failure residue, measurement environment, spectator, or source port
   remains quantum-callable, it is a quantum bypass and the interface is not
   the two-qubit-only contract of Definition 4.1. If it is discarded, it is
   unavailable for later feedback. The corollary therefore accounts for
   retained records and all declared residues without assuming a free hidden
   quantum channel.

**Proof.** The finite-tree reduction is the standard composition of local
Kraus operators along each actual transcript; communication changes the next
local choice but does not change the product form of a complete leaf. Apply
Theorem 3.1 to the resulting finite bank. The expressions in (1.2) account
for each coarse record and each refined successor. The mass bound (4.1)
follows from (2.6) and
$\operatorname{Tr}[(A^*A)\otimes(B^*B)]
=\operatorname{Tr}(A^*A)\operatorname{Tr}(B^*B)$. Finally, ordinary partial
transpose sends every later product Kraus congruence of a PPT operator to a
positive congruence. More explicitly, if $D_\gamma$ is the unnormalized
successor on the complete current quantum carriers after the actual prefix
$\gamma$ and $y$ is the next recorded outcome, then

$$
D_{\gamma y}=\sum_k K_{\gamma,y,k}D_\gamma K_{\gamma,y,k}^*,\qquad
\operatorname{Tr}D_{\gamma y}=\Pr(\gamma y),
\tag{4.2}
$$

where the $K_{\gamma,y,k}$ are the product Kraus components of that node,
including declared local discards. The summed index $k$ is not an observed
input; the record stored at that node is the actual prefix $(\gamma,y)$.
Terminal $D_\gamma$'s are exactly the successors summed in (1.2), including
failures and residues. Induction over this same-run recursion proves the
claim. $\square$

## 5. The exact uncovered delta and boundaries

VII §§201–213 already supply the signed resource, all fifteen charge
probabilities, the exact PPT/NPT criterion, and the parameter-dependent
inverse filters. VII §§214–225 supply the fixed known-parameter postfilter
frontier, complete success/failure probabilities for that different task, and
the finite single-product ceiling. QSSR2, in
[Joint Relations and Clocks, Continuation](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS_CONTINUATION.md),
§§2–5, supplies a known-setting installed transfer and branchwise continued
use; it does not infer an unknown setting from the source.

The native comparison uses VII §§226–230 at immutable revision
`4c566797ebaed644c5a319c7daa1ae2ce2647058`, blob
`b00e9fc43f806f9e3caf2102d6e8b0658019e918`, content SHA256
`9c33f109a9b5ed743ba05b12be3bd5e9a7e14bde14582cfc7aa92656f0f51886`.
Definition 226.1 fixes the native principal-root cut without an extra
rotation; Proposition 227.1 reduces its coordinates to scalar equations.
Theorems 228.1 and 229.1 give its unique extrema and exact interior and
closed images. Theorem 230.1 and Corollary 230.2 characterize native
membership in the scalar postfilter image and attainment of the scalar
thermal threshold. These resolve the native scalar-realization boundary of
§225 for that cut. The final paragraph of §230 explicitly retains the
source-informed basis and control assumptions and leaves unknown-$q$
extraction unresolved. Neither the scalar inverse nor native membership
identifies or acquires the coupled pairs $(v_{x,\eta},w_\eta)$ used here.
No identification of this family with the native $q$ family is made.
Consequently §§226–230 neither change the premises of Lemma 2.1 and
Theorem 3.1 nor supply their uniform finite-bank conclusion.

The remaining supplier correspondence uses immutable revision
`57235d816537668f092de005a3f9dd370566798a`; each source retains its own
declared domain and initialization.

| Reused source | Exact correspondence and limit |
| --- | --- |
| [NCR](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), Definitions 5.1–5.2 and Theorems 5.3, 6.3 | Acquired seed, actual receipt clock and deterministic installed continuation give four exact kernels on its fixed-controller tree domain. They supply neither this quantum preparation nor an unknown-$\eta$ selector. |
| [PVC](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), Assumption 1.2, Definition 1.3 and §§6–10 | The fixed-$H$ acquired entrance and additional installed converter support paid view conversion, publication and return. No correspondence installing those services on $\Omega_{x,\eta}$ is assumed or proved here. |
| [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §57.1, Definitions PR57.D1, D5 and Theorem PR57.T2 | Constructed tapes, paid source supply and whole-action guards realize its original ordered-tree menu. Finite control and finite realized runs do not imply Definition 4.1's globally finite Kraus bank. |
| [PG](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), Definitions 19.1, 19.6 and Theorems 19.7–19.8; [Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md), §§1–2 | Complete responses and successors, actual reachable records, selectors, ownership and installed historical calls retain their own contracts. These conditions neither make the present continuous source family a finite carrier nor install an unknown-ray extraction service. |
| [FiniteKrausInstrumentBornMarginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean), `finite_kraus_instrument_born_marginal`, and its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.scribe.cs) | The same-carrier finite normalized Kraus theorem equates branch trace with its Born weight. Its Scribe explains actual-prefix recursion, complete finite leaf masses and the discarded-environment boundary. These support the conventions in (1.2) and §4; the rectangular product-map argument and moving-kernel obstruction are proved here as ordinary mathematics, without transferring Lean certification. |

The standard
ingredients here—positive partial-transpose congruence, finite direct sums,
continuity of finite matrices, and the finite-dimensional kernel argument—are
reused mechanisms.

The `repo-derived` inference beyond these suppliers is the moving-kernel
statement of Theorem 3.1 on the declared coupled subfamily: a finite
source-independent product bank can be defeated by one unknown ray and
a nonempty interval of $x$ arbitrarily close to the VII PPT boundary, even
though the same sources have a positive-probability source-specific NPT
filter. This is a separation between pointwise lawful extraction and a
uniform finite encoded-memory checkpoint. It is not a source-identification
theorem: the proof never asks a controller to identify $\eta$ and never
claims that all useful unknown-source operations fail.

The result is conditional on the declared common two-copy preparation and
finite checkpoint contract. It does not classify larger retained charge
sectors, continuous or unbounded menus, arbitrary stopping trees, extra
copies, source-dependent side information, promised margins away from the
boundary, entangled ancillary resources, or a returning quantum environment.
It proves no physical installation impossibility, no universal finite-observer
impossibility, no rate or optimality statement, no native $\alpha/\beta$
reduction, and no recovery of space, time, boundary, and memory as four
mutual inverses. The original fixed-$G_{gc}$, original-$Q$, parked-consumer,
and unchanged-initialization obligations retain their exact scopes. The
full four-expression programme remains open.

## 追加锚（本行以下为增补区）

## 6. Paid same-setting specimens for a fixed Bell consumer

The task in this section is to acquire, from actual observations, a common
encoded pair for one fixed Bell-measurement teleportation call. The call's
performance is Haar-average pure-input fidelity, conditional on a resource
herald obtained before the input arrives. The task is a bounded subtask of
the four-expression programme; a two-qubit port is not imposed on that
programme or on tasks already served by the larger charge sector.

**Definition 6.1 (the paid-specimen model).** Keep $t=1/4$, $s=3/4$,
$Z=25/8$, $x_*=(3-\sqrt5)/6$, the occupation bases, and the CAR cut of
§1. For every unit $\eta\in\mathbb C^2$, set

$$
\begin{gathered}
P_\eta=\eta\eta^\dagger,\quad
v=(\sqrt x,\sqrt{1-x}\,\eta),\quad w=(0,\eta),\\
R_{x,\eta}=1\oplus(tI_3+s vv^\dagger)
 \oplus(tI_3-ts ww^\dagger)\oplus t^2,\qquad
\rho_{x,\eta}=R_{x,\eta}/Z,\\
m=s^2x(1-x),\qquad \Delta=m-t^2,\qquad c=t+sx.
\end{gathered}
\tag{6.1}
$$

The two three-dimensional sector bases are $(\ell,R,r)$ and
$(r\wedge R,\ell\wedge R,\ell\wedge r)$, as in VII Definition 201.1.
The ordered internal Bob space is $H=\operatorname{span}(R,r)$.
In the notation of VII §202 the scalar named $b$ there is $t$, and its
scalar $d$ is $t^2$; neither is the public margin below.

Supply a public rational margin $d$ with $0<d\le5/64$. The entire promised
domain is

$$
\mathcal P_d=
\left\{(x,\eta):\ \|\eta\|=1,\quad
x_d\le x\le\tfrac12\right\},\qquad
x_d=\frac{3-\sqrt{5-64d}}6.
\tag{6.2}
$$

Equivalently, $x_*<x\le1/2$ and $\Delta\ge d$. The endpoint $d=5/64$
is included and forces $x=1/2$. There is no directional restriction on
$\eta$ and no distribution over the setting.

For a chosen integer $N$, the preparation service supplies $N$ preliminary
full specimens of $\rho_{x,\eta}$ and then a compatible target pair at the
same fixed unknown setting. The preliminary specimens are consumed before
the pair is delivered for the common twirl. Conditional on that setting,
the joint carrier law at these stages is

$$
\rho_{x,\eta}^{\otimes N}\otimes\Omega_{x,\eta},\qquad
\Omega_{x,\eta}=
 \sum_{a=0}^2\sum_{k=0}^4
 \Pi_{a,k}J(\rho_{x,\eta}\otimes\rho_{x,\eta})J^\dagger\Pi_{a,k}.
\tag{6.3}
$$

Here $J$ has precisely the sign in VII (203.1). The target pair is made
from two independent **untwirled** preparations with compatible labelled
modes and coupling phases, followed by one common local-number twirl.
The pair's joint availability at this stage is a preparation premise;
no storage of it throughout calibration is required. The specimen bill is
$N+2$, not $N$ copies of the already twirled two-copy resource.

The raw parameter includes a unit representative of the ray. Replacing
$\eta$ by a common phase multiple can change raw one-copy coherences, but
leaves the calibration laws and $\Omega$ below unchanged. Compatibility of
the target preparations is still required: independent unrecorded coupling
phases or preliminary per-copy twirls are different preparations. A prior
mixture, if used, must mix the whole same-setting law (6.3), rather than
independently mixing its factors.

The supplied margin, repeatability, independence and phase compatibility
are hypotheses. Observations in the construction do not certify them.
The enlarged independent-sector-ray preparation is distinct from the native
principal-root $q$ family and from passive native reachability. It is not a
cloning procedure, an unknown-source fabrication theorem, or the original
two-specimen initialization of §§1–4.

**Definition 6.2 (controls and terminal interface).** The controller has
source-independent initialization, the public $d$, a fixed specimen schedule,
labelled Bob Pauli axes on $H$, coherent local number-preserving projectors
and the finite rotations specified below. It has fresh readout pointers,
classical counters, actual communication and permanent discard. These are
ideal instrument resources. The axes use a fixed relative control phase
between Bob's labelled modes; they require no unknown source label or
reference state breaking local total-number superselection.

Its only source-dependent inputs are actual measured outcomes and reports.
The true $x,\eta$, a calibration-error flag, hidden Kraus labels and a
source-correlated programme are unavailable. There is no entangled ancillary
pair, extra target attempt or returning discarded environment.

Success is the communicated joint acceptance of the target tests in §7.
After alignment, all accessible calibration outcomes, counters, selected-menu
indices, work registers, pointer copies and control residues identifying the
chosen direction are made permanently inaccessible. On success only two
fixed encoded rail qubits and the common success report remain callable.
On failure all source carriers are discarded and a failure symbol remains.
Discard is part of the channel; no thermodynamic reset or reusable apparatus
cycle is asserted. This explicit reduced-interface convention does not assert
NPT for every finer calibration-conditioned history.

## 7. The acquired selector and the complete target instrument

The source coordinates of VII (202.1), specialized to (6.1), are

$$
D=tI_2+s(1-x)P_\eta,\qquad
E=tI_2-tsP_\eta,\qquad
f=s\sqrt{x(1-x)}\,\eta,\qquad g=0.
\tag{7.1}
$$

Consequently Bob's one-particle marginal on a preliminary specimen is

$$
\left.\operatorname{Tr}_A\rho_{x,\eta}\right|_H
 =\frac{D+E}{Z}=\frac{2tI_2+uP_\eta}{Z},\qquad
u=s(1-x-t).
\tag{7.2}
$$

Write $P_\eta=(I+n\cdot\sigma)/2$, $n\in\mathbb R^3$, $\|n\|=1$,
using the fixed ordered basis of $H$. For axis $i=1,2,3$, measure the
projectors $(I_H\pm\sigma_i)/2$ on $H$ and the complementary Bob
projector $I_B-\Pi_H$. Record $Y=+1,-1,0$, respectively. These three
effects sum to $I_B$ and preserve Bob number. Their full law is

$$
\begin{aligned}
\pi_i(\pm1)&=\frac{2t+u(1\pm n_i)/2}{Z},\\
\pi_i(0)&=1-\frac{4t+u}{Z},\qquad
\mathbb E Y= a_{\rm sig}n_i,\qquad
 a_{\rm sig}=u/Z\ge\frac3{50}.
\end{aligned}
\tag{7.3}
$$

The signal floor follows from $x\le1/2$. All three masses are nonnegative.
A preliminary successor for outcome $y$ is
$(I_A\otimes E_{i,y})\rho(I_A\otimes E_{i,y})$, where $E_{i,y}$ is
its projector, with trace $\pi_i(y)$. After updating the actual counter,
that specimen, its Alice part and its readout residue are discarded.
Thus outside-sector zeros consume full specimens, rather than being free
rejections from an accepted-sample budget.

Take exactly $M$ fresh specimens on each axis, in deterministic order;
$N=3M$. Let $h=(y_{i,j})$ denote the sequence of actually acquired
outcomes, whether or not individual outcomes are subsequently retained.
Its probability and signed counters are

$$
p_h=\prod_{i=1}^3\prod_{j=1}^M\pi_i(y_{i,j}),\qquad
T_i=\sum_{j=1}^M y_{i,j},\qquad z=T/M.
\tag{7.4}
$$

This product law uses independence at the same fixed setting. It includes
all histories and satisfies $\sum_h p_h=1$. Only the counters, rather
than an archive of $h$, are needed for selection. Set $\widehat n=T/\|T\|$
when $T\ne0$, and set $\widehat n=(0,0,1)$ when $T=0$. Choose

$$
k(T)=
\begin{cases}
\displaystyle\left(\sqrt{\frac{1+\widehat n_3}{2}},
 \frac{\widehat n_1+i\widehat n_2}{\sqrt{2(1+\widehat n_3)}}\right),
 &\widehat n_3\ne-1,\\[4pt]
(0,1),&\widehat n_3=-1.
\end{cases}
\tag{7.5}
$$

It is a unit vector with Bloch vector $\widehat n$. Both poles and the
zero-counter case are defined. For each $T\in\{-M,\ldots,M\}^3$ a
specified unitary sending this vector to $e=(1,0)$ is

$$
U_T=\begin{pmatrix}\overline{k_1}&\overline{k_2}\\-k_2&k_1\end{pmatrix},
\qquad U_Tk=e.
\tag{7.6}
$$

For fixed $M$ these are at most $(2M+1)^3$ algebraically specified
controls, independent of $x,\eta$. Their exact availability is a declared
finite menu, not an oracle implementing an unknown direction. Their Fock
lifts are even Bob-local number-preserving controls, applied identically in
both copies; they commute with the CAR regrouping sign and the charge tests.

Let $P_A$ be Alice's projection onto $p=|10\rangle,q=|01\rangle$.
For the acquired $k_h=k(T(h))$, let $Q_h$ be Bob's coherent projector
onto $\operatorname{span}\{L(k_h),R(k_h)\}$ inside total Bob number one,
extended by zero on other sectors. Alice first tests $P_A$ and communicates
its bit. On acceptance Bob tests $Q_h$, aligns by (7.6), and communicates
his bit. Neither test resolves which copy contains the particle. Equivalently,
Bob first applies the selected rotation and tests the fixed corresponding
subspace. On joint acceptance the code is always

$$
|0\rangle_A=p,\quad |1\rangle_A=q,\qquad
|0\rangle_B=L(e),\quad |1\rangle_B=R(e).
\tag{7.7}
$$

The original modes can be this owned, addressed port; no transfer to new
quantum memories is needed. Common code and Bell basis do not mean a
source-independent density matrix.

For every $h$, define $r_h=|k_h^\dagger\eta|^2$. Compressing the supplied
VII (205.2) matrix and applying the alignment gives the accepted operator
in the order $(pL(e),pR(e),qL(e),qR(e))$:

$$
\begin{gathered}
X(r)=\frac1{Z^2}
\begin{pmatrix}
a(r)&0&0&0\\
0&B(r)&-mr&0\\
0&-mr&B(r)&0\\
0&0&0&a(r)
\end{pmatrix},\\
a(r)=t-tsr,\qquad B(r)=c\{t+s(1-x)r\},\qquad
P(r)=\operatorname{Tr}X(r)=\frac{2\{a(r)+B(r)\}}{Z^2}.
\end{gathered}
\tag{7.8}
$$

Indeed $k^\dagger Ek=a(r)$, $c k^\dagger Dk=B(r)$ and
$|k^\dagger f|^2=mr$. The off-diagonal minus sign is the actual CAR
sign, and its phase cancels because the same $k$ and compatible $f$ occur
in both rails. This uses the supplied source compression, without assuming
that $k$ is its exact inverse direction. Positivity is also visible from
$a(r)\ge t^2$ and $B(r)-mr=t\{c+s(1-x)r\}>0$.

For completeness put $A=P_A\otimes I_B$, $C_h=P_A\otimes Q_h$.
Before disposal the three target successors are

$$
G_0=(I-A)\Omega(I-A),\qquad
G_{1,h}=(A-C_h)\Omega(A-C_h),\qquad
G_{s,h}=C_h\Omega C_h.
\tag{7.9}
$$

The last successor, after alignment and code identification, is $X(r_h)$.
The first two include every rejected charge, spectator and rail residue.
Writing

$$
\begin{gathered}
\delta_D=\operatorname{Tr}D=\tfrac54-\tfrac34x,\qquad
\varepsilon_E=\operatorname{Tr}E=\tfrac5{16},\\
\alpha=\operatorname{Tr}(A\Omega)
 =\frac{2(1+\delta_D+t)(c+\varepsilon_E+t^2)}{Z^2},
\end{gathered}
\tag{7.10}
$$

their same-run joint masses with history $h$ are, respectively,

$$
p_h(1-\alpha),\qquad p_h\{\alpha-P(r_h)\},\qquad p_hP(r_h).
\tag{7.11}
$$

Equation (7.10) is the Alice-number-one row sum of VII (204.1), or the
product of the two one-copy Alice-number probabilities. The projections in
(7.9) are orthogonal and sum to identity, proving nonnegativity and total
mass $p_h$. In particular no charge-preparation rejection is omitted from
the normalization of $\Omega$. After permanent discard, the first two
successors are failure symbols with these masses and no quantum port.
There is no other stopped or callable residue: terminal residue mass is
zero. The complete preliminary and target procedure has total mass one.

## 8. Acquisition, the observed herald and one consumable call

**Theorem 8.1 (paid acquisition to the common Bell-use port).** For every
public rational $0<d\le5/64$, set

$$
M=\left\lceil\frac{5000(t+d)}{3d}\right\rceil,\qquad N_{\rm cal}=3M.
\tag{8.1}
$$

Under Definitions 6.1–6.2, for every $(x,\eta)\in\mathcal P_d$, the
actual procedure of §7 consumes $N_{\rm cal}+2$ full specimens and has
the following output law. Put

$$
\bar r=\sum_h p_h r_h,\quad
\bar a=t-ts\bar r,\quad
\bar B=c\{t+s(1-x)\bar r\},\quad
P_s=\frac{2(\bar a+\bar B)}{Z^2},\quad
\sigma_s=\frac{X(\bar r)}{P_s}.
\tag{8.2}
$$

After the specified record discard, its success report has probability
$P_s\ge16/625$ and conditional state $\sigma_s$ on exactly (7.7).
The two failure masses are $1-\alpha$ and $\alpha-P_s$, summing to
$1-P_s$. The exact correctness condition for this retained pair is

$$
\begin{aligned}
\sigma_s\text{ is NPT}
&\ \Longleftrightarrow\ (t+\Delta)\bar r>t\\
&\ \Longleftrightarrow\
\mathbb E_h(1-|k_h^\dagger\eta|^2)<\frac{\Delta}{t+\Delta}.
\end{aligned}
\tag{8.3}
$$

The displayed construction satisfies it uniformly, with

$$
\mathcal N(\sigma_s)
 =\frac{[(t+\Delta)\bar r-t]_+}{2(\bar a+\bar B)}
 \ge\frac{\Delta}{2Z^2P_s}\ge\frac{32d}{625}>0.
\tag{8.4}
$$

On the observed success branch this very pair supports the fixed
teleportation call specified below, with average pure-input fidelity at
least $2/3+64d/1875$. The call consumes the shared pair. None of these
conclusions asserts that each finer $h$-conditioned pair is NPT.

Proof. The independent complete calibration laws give

$$
\mathbb E z=a_{\rm sig}n,\qquad
\mathbb E\|z-a_{\rm sig}n\|^2
 =\sum_{i=1}^3\frac{\operatorname{Var}(Y_i)}M\le\frac3M.
\tag{8.5}
$$

Use the normalization inequality of Phase Boundary (278.18), including its
zero-vector convention: $\|\widehat n-n\|\le
2\|z-a_{\rm sig}n\|/a_{\rm sig}$. The qubit projector identity
$1-|k^\dagger\eta|^2=\|\widehat n-n\|^2/4$ therefore yields

$$
\mathbb E_h(1-r_h)\le\frac3{a_{\rm sig}^2M}
 \le\frac{2500}{3M}\le\frac{d}{2(t+d)}.
\tag{8.6}
$$

This is a uniform mean bound at each fixed setting; it uses no prior over
$n$, accepted-sample replacement or hidden good-calibration event.

Conditional independence in (6.3) leaves the target state $\Omega$
unchanged conditional on every preliminary history. Hence the accepted
classical–quantum operator before the final erasure is
$\sum_h p_h|h\rangle\langle h|\otimes X(r_h)$, allowing already
discarded records to be represented by their inaccessible environment.
Tracing all those registers gives

$$
X_s=\sum_h p_hX(r_h)=X(\bar r).
\tag{8.7}
$$

The second equality uses the affine source-specific formula (7.8).
Conditioning follows this sum. Equivalently, the normalized successful
histories have weights $p_hP(r_h)/P_s$, not $p_h$.
Equation (8.7) is precisely the declared erasure channel applied to the
actual controlled process; it is not an alternative averaging convention.
Accessible copies of calibration or setting information would give a finer
interface and would not establish the historywise conclusion excluded above.

The partial-transpose eigenvalues of $X_s$ are

$$
\frac1{Z^2}\{\bar B,\bar B,\bar a+m\bar r,\bar a-m\bar r\}.
\tag{8.8}
$$

Since $ts+m=t+\Delta$, (8.3) and the exact expression in (8.4) follow.
For (8.1), (8.6) gives

$$
(t+\Delta)\bar r-t
 \ge\Delta-\frac{(t+\Delta)d}{2(t+d)}\ge\frac\Delta2,
\tag{8.9}
$$

where the last inequality is equivalent to $\Delta\ge d$.
Also $a(r),B(r)\ge t^2$ give
$P_s\ge4t^2/Z^2=16/625$. Dividing (8.9) by $Z^2P_s$ gives the first
lower bound in (8.4); $P_s\le1$ gives the second. All statements include
the maximum-margin endpoint. Equations (7.4), (7.9)–(7.11) prove the
claimed complete flag law on the same run. The call law below finishes the
consumer assertion. $\square$

For that call fix the four Bell vectors in code (7.7), beginning with
$\psi^-=(|01\rangle-|10\rangle)/\sqrt2$. The state in (8.2) is Bell
diagonal. Its weights, in the order $\psi^-,\psi^+,\phi^-,\phi^+$, are

$$
q_0=\frac{\bar B+m\bar r}{2(\bar a+\bar B)},\quad
q_z=\frac{\bar B-m\bar r}{2(\bar a+\bar B)},\quad
q_x=q_y=\frac{\bar a}{2(\bar a+\bar B)}.
\tag{8.10}
$$

They are nonnegative and sum to one. In the NPT regime,
$q_0=1/2+\mathcal N(\sigma_s)>1/2$.
Only after receiving the resource herald, Alice is supplied an independent
logical input qubit $\tau$ in an additional fixed-number rail code.
The consumer is the standard complete logical Bell measurement on input
and Alice's resource qubit, its actual two-bit transmission, and Bob's
fixed Pauli correction table, chosen so that $\psi^-$ gives identity.
No source-dependent choice is made by this consumer. A complete encoded
Bell instrument, including coherent control inside Alice's total-number-two
input/resource sector, is an additional explicit primitive; local rail
rotations alone are not asserted to synthesize it.

The ordinary Bell-component teleportation identity, applied to (8.10), gives

$$
\mathcal T_{x,\eta}(\tau)=q_0\tau+q_xX\tau X+q_yY\tau Y+q_zZ\tau Z.
\tag{8.11}
$$

For each of the four Bell reports $b$, its corrected subnormalized Bob
output on the full preparation run is

$$
\frac{P_s}{4}\mathcal T_{x,\eta}(\tau),\qquad
\Pr(s,b)=P_s/4.
\tag{8.12}
$$

To check the identity, on resource $\psi^-$ each Bell report has probability
$1/4$ and the fixed correction returns $\tau$. The other resource Bell
vectors are obtained by Bob Paulis; commuting them past a correction changes
only an irrelevant sign, and gives the respective Pauli error in (8.11).
Linearity gives (8.12), with the same channel for every report. This also
holds with an untouched reference entangled with the input, provided the
input–reference system is independent of resource preparation. Failed
resource runs have the two failure-symbol successors of Theorem 8.1; no
input is requested on them. Thus all failure masses and all four call
branches sum to one, with no input-dependent postselection.

For a Haar-distributed pure qubit the mean squared overlap with any
nonidentity Pauli image is $1/3$. The declared metric is therefore

$$
F_{\rm av}(\mathcal T)=q_0+\frac{1-q_0}{3}
 =\frac23+\frac23\mathcal N(\sigma_s)
 \ge\frac23+\frac{64d}{1875}.
\tag{8.13}
$$

This is average fidelity after an input-independent resource herald, not
worst-input fidelity or perfect transmission. Alice's measured systems are
consumed/discarded; Bob's rail is now the noisy transmitted input, not a
second callable copy of the entanglement resource. The Bell readout uses
fresh pointers and actual communication in addition to the earlier herald.

Immediate sequential use supplies no durable-storage guarantee. If a wait
is desired, the separate QSSR2 Definition 5.1 isolation premise must actually
hold on these retained rails: $H_M=\varepsilon_A N_A+\varepsilon_B N_B$,
no residual coupling or rail splitting, stable classical flag, and addressed
controls at the later call. Here $N_A=N_B=1$, so $H_M$ restricts to the
scalar $\varepsilon_A+\varepsilon_B$ and preserves $\sigma_s$ during each
finite wait. This is the existing QSSR2 storage argument instantiated on the
successful code, conditional on that extra premise. It is not inferred from
raw thermal stationarity or from the immediate-call theorem.

## 9. Specimen resources and the restricted small-margin lower order

Theorem 8.1 uses exactly

$$
N_{\rm cal}=3\left\lceil\frac{5000(t+d)}{3d}\right\rceil
 <\frac{5000(t+d)}d+3
\tag{9.1}
$$

preliminary specimens and two target specimens. This is a sufficient
$O(d^{-1})$ specimen bound. For example, at $d=5/64$ the specified
$M$ is $7000$ and the calibration bill is $21000$; the constants make no
claim of practical economy or sharpness.

**Definition 9.1 (the lower-bound interface).** A procedure in this class
has a fixed number $N$ of independent full raw preliminary specimens at the
same setting. It may measure them collectively, even with $x$ disclosed,
using any setting-independent ancillary initialization and randomness.
It always outputs a classical unit direction $k$. It has no calibration
abstention or calibration-dependent target rejection gate. Every preliminary
history is processed through exactly the canonical two-specimen filter and
alignment of §7, followed by the same terminal erasure. No preliminary
quantum system remains available to alter that filter or supply the call.
This is a class of estimators followed by a prescribed extractor, not the
class of all acquisition protocols.

**Proposition 9.2 (sample-order necessity in that interface).** For every
public rational $0<d\le1/1020$, if a Definition 9.1 procedure gives an NPT erased
successful pair for every source in $\mathcal P_d$, then

$$
N>\frac{5(t+d)}{256d}.
\tag{9.2}
$$

Together with (9.1), the least sufficient preliminary specimen count in
this interface is $\Theta(d^{-1})$ as $d\downarrow0$. Only the upper
construction is asserted on the full interval $0<d\le5/64$.

Proof. Restrict to $x=x_d$, so $\Delta=d$, and put
$e=d/(t+d)\le1/256$. The affine compression proof (8.7) is valid for
any classical direction law independent of the reserved target pair.
Equation (8.3) therefore requires

$$
\mathbb E_\eta(1-|k^\dagger\eta|^2)<e
\quad\hbox{for every unit }\eta.
\tag{9.3}
$$

Compare $\eta_0=(1,0)$ and
$\eta_\theta=(\cos\theta,\sin\theta)$ with
$\theta=8\sqrt e\le1/2$. Their projective angle is $\theta$.
Classify the estimate $k$ by the nearer of these two rays, breaking ties
arbitrarily. An error under either source implies projective distance at
least $\theta/2$ from the true ray. Thus (9.3) bounds each error by

$$
\frac{e}{\sin^2(\theta/2)}
 \le\frac{\pi^2e}{\theta^2}=\frac{\pi^2}{64}<\frac14.
\tag{9.4}
$$

The inequalities use the projective-angle triangle inequality and
$\sin(\theta/2)\ge\theta/\pi$. By the ordinary binary trace-distance
bound, the two calibration inputs must have half trace distance greater
than $1/2$. This reasoning allows arbitrary collective measurements and
independent coins; a classical decision cannot increase input trace distance.

It remains to bound that distance for these actual raw sources. Their
positive square roots are supplied directly by the number-block spectra:

$$
\sqrt R=1\oplus\{\sqrt tI_3+(1-\sqrt t)P_v\}
 \oplus\{\sqrt tI_3+(t-\sqrt t)P_w\}\oplus t.
\tag{9.5}
$$

For the two rays, the rank-one projector identity gives

$$
\|P_{v_0}-P_{v_\theta}\|_F^2\le2(1-x)\theta^2,\qquad
\|P_{w_0}-P_{w_\theta}\|_F^2\le2\theta^2.
\tag{9.6}
$$

For the first bound use
$v_0^\dagger v_\theta=x+(1-x)\cos\theta$,
$1-a^2\le2(1-a)$ for $0\le a\le1$, and
$1-\cos\theta\le\theta^2/2$; the second follows from
$w_0^\dagger w_\theta=\cos\theta$. At $t=1/4$, division by $Z$
in (9.5) gives

$$
\|\sqrt{\rho_0}-\sqrt{\rho_\theta}\|_F^2
 \le\frac{5-4x}{25}\theta^2\le\frac{\theta^2}{5}.
\tag{9.7}
$$

The unit canonical purifications obtained by vectorizing the positive
square roots have real overlap
$g_{\rm pur}=\operatorname{Tr}(\sqrt{\rho_0}\sqrt{\rho_\theta})$.
Since both densities have trace one, (9.7) gives
$g_{\rm pur}\ge1-\theta^2/10>0$. Their $N$-fold purifications have
overlap $g_{\rm pur}^N$. The pure-state trace-distance identity and
contraction under partial trace yield

$$
\frac12\|\rho_0^{\otimes N}-\rho_\theta^{\otimes N}\|_1
 \le\sqrt{1-g_{\rm pur}^{2N}}
 \le\sqrt{2N(1-g_{\rm pur})}
 \le\sqrt{N\theta^2/5}.
\tag{9.8}
$$

Combining this with the strict $1/2$ requirement proves
$N>5/(4\theta^2)=5/(256e)$, which is (9.2). Theorem 8.1 belongs to
the restricted interface and supplies its matching upper order. $\square$

No lower bound has been proved here for coherent calibration–target
processing, postselected calibration, a different extractor, unbounded
stopping with only an expected count, retained quantum programmes, larger
ports, or arbitrary distillation protocols. In particular (9.2) neither
makes the extra preparation assumptions necessary for every consumer nor
makes (9.1) a total-cost optimum.

The same-run resource coordinates are distinct:

| Coordinate | Resources and boundary |
| --- | --- |
| Source | $3M+2$ full raw preparations at one unknown setting; no physical production probability or native $P_{\rm full}$ is assigned to this supply. |
| Acquired control | $3M$ complete Bob three-outcome readouts, three signed counters and a schedule; no random choice of axes is needed. |
| Active classical memory | Counters use at most $3\lceil\log_2(2M+1)\rceil$ bits, a schedule uses $\lceil\log_2(3M+1)\rceil$, with bounded outcome/control workspace. This is $O(\log M)$ mutable storage, excluding the installed menu. |
| Installed controls | Three labelled axes, at most $(2M+1)^3$ selected rotations, coherent target tests, and the later Bell instrument and correction table. A finite exact specification is not a gate-synthesis or installation result; setup/menu storage is a separate coordinate. |
| Consumed and discarded systems | $3M$ preliminary full specimens and readout pointer uses; target rejection carriers and all calibration/control residues; further pointers for target and Bell reports. Inaccessible environments can grow with the number of operations despite bounded active counters. |
| Retained quantum interface | On success, the two original fixed-charge rail qubits and common flag until the single call; failure has no quantum port. The input and Bob's subsequent output are additional consumer carriers. |
| Communication | Actual Alice acceptance report and conditional Bob report, distributed as needed to give a common herald; then two Bell bits and fixed corrections. No party reads an unsent remote flag. |
| Other costs | Specimen arrival order, classical processing, control accuracy, time, energy, discard/reset work and physical synthesis are unpriced. Protected waiting additionally requires the stated isolation. No price is inferred from a copy count. |

## 10. Supplier correspondence, sufficient alternatives and four-view limits

The source-specific deduction is the chain

$$
\text{raw Bob marginal}\ \longrightarrow\
\text{acquired finite counters}\ \longrightarrow\
\text{coherently aligned target output}\ \longrightarrow\
\text{erased-interface herald}\ \longrightarrow\
\text{one fixed Bell call}.
\tag{10.1}
$$

Its content is the actual correspondence (7.2)–(8.13) for the same source
and run, with the restricted source-distance calculation in §9. The generic
normalization inequality, positive instrument accounting, source blocks,
storage condition and teleportation identities are suppliers, not new general
theorems of this appendix.

For **mere NPT retention**, the cheaper existing same-source route is to
retain the whole $(N_A,N_B)=(1,1)$ charge sector, with Alice dimension two
and Bob dimension four. VII (204.1), (205.2), (206.3) already give

$$
P_{11}=\frac{2(\varepsilon_E+c\delta_D)}{Z^2}>0,\qquad
E-ff^\dagger=tI_2-(ts+m)P_\eta,
\tag{10.2}
$$

whose $\eta$ eigenvalue is $-\Delta$. The charge report therefore
heralds an NPT larger port on the entire original interval $x>x_*$,
without calibration or a positive lower margin. All other charge outcomes
keep their published masses. Owned, addressable modes can remain in place;
isolation and absent controls are still separate premises. Calibration is
unnecessary for this weaker task.

The fixed spatial-erasure decoder of VII §§235–238 is another existing
supplier, with a different source domain. On the native principal-root
family its actual common output has Werner weight

$$
\zeta=\frac{g_{\rm nat}}{2t+g_{\rm nat}+2th_{\rm nat}},\quad
P_{\rm full}=\frac{2t+g_{\rm nat}+2th_{\rm nat}}{2(1+t)^4},\quad
 g_{\rm nat}>t(1+h_{\rm nat})
\tag{10.3}
$$

as its exact NPT criterion. Here
$g_{\rm nat}=(1-t)^2p(1-p)$ and $h_{\rm nat}=t+(1-t)p$ belong to
that native source, not to $x,\eta$ above. Reuse this decoder on its own
successful domain; no calibration is required there. At the present $t=1/4$,
$g_{\rm nat}\le9/64<t$, whereas the independent-ray source has
$\Delta>0$. Source, threshold, probability and budget do not transfer
through a shared parameter name.

Applying that same copy-rail spatial trace to the present larger port instead
gives the unnormalized two-qubit matrix

$$
\frac1{Z^2}
\begin{pmatrix}
\varepsilon_E&0&0&0\\
0&c\delta_D&-m&0\\
0&-m&c\delta_D&0\\
0&0&0&\varepsilon_E
\end{pmatrix}.
\tag{10.4}
$$

This follows by tracing $E,D,ff^\dagger$ in the actual VII (205.2)
block, not by substituting names into the native theorem. Its trace is
$P_{11}$ and its least partial-transpose corner is positive, since
$\varepsilon_E-m\ge5/16-9/64=11/64$. Thus this inexpensive fixed decoder
does not supply the present Bell-use port.

There is also a same-task two-specimen boundary. At fixed $x$, mix the two
complete $\Omega$ sources with orthogonal rays, keeping the same ray in
both preparations within each summand. The potentially negative block in
VII (206.3) averages to
$tI_2-(ts+m)I_2/2\succ0$, since $ts+m\le21/64<2t$; its rail
permutation is independent of the ray. All other partial-transpose blocks
are positive for each summand because $g=0$, or have one-dimensional Alice
factor. The complete mixture is PPT. Any fixed source-independent
PPT-preserving successful map to the common pair, including local feedback
through a larger interim port with separable ancillary resources, preserves
PPT on this mixture. For any unnormalized two-qubit PPT $Y$,
$\operatorname{Tr}(P_-Y)\le\operatorname{Tr}Y/2$, because
$P_-^{T_A}\preceq I/2$. Positive success and singlet fraction $>1/2$
on both sources would contradict this inequality by linearity. This explains
the difference from mere larger-port NPT; it does not classify all old
extraction tasks. The enlarged same-setting law (6.3) changes that input and
is not a tensor power of the two-source averaged marginal.

If a known direction $e_0$ and a preparation promise
$\inf_\eta|e_0^\dagger\eta|^2>t/(t+d)$ are supplied, (7.8)–(8.3)
already give the same Bell consumer using only two specimens and the fixed
$e_0$ filter. That alternative buys directional information as a hypothesis;
it does not acquire it over the full sphere. A finite recorded-basis bank
with occasional unrecognized NPT leaves or NPT classical–quantum density
also has a different retained interface and success assertion. Neither that
weaker assertion nor the larger port should be renamed the common
Bell-use guarantee. No global comparison of hardware or total resource
vectors follows from the specimen savings of these alternatives.

The precise suppliers and limits are as follows. Repository references use
their immutable statements: VII §§201–234 and Phase Boundary §278 at
3af7031e507c22d39798c7032afc58924a88f904; VII §§235–238 at
09acfc92b732e916b7061b1bd92e55146e568179; QSSR2 and the finite Born
supplier at 57235d816537668f092de005a3f9dd370566798a.

| Supplier | Correspondence and limit |
| --- | --- |
| VII Definition 201.1, Assumption 201.2, (202.1), (203.1)–(206.3), (208.1)–(208.3) | Supplies the full independent-ray source, sign, complete charge probabilities and canonical compression. The new joint specimen supply and measured selector are explicit additions; source-dependent inverse filtering does not acquire them. |
| [Phase Boundary](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md), §278, especially (278.17)–(278.19) | Supplies paid same-setting calibration and normalization/mean-risk reasoning without a good-estimate flag on a different unknown-$U(1)$ reset/discrimination source. Its query lower bound is not the lower bound of §9. |
| [QSSR2](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS_CONTINUATION.md), Definition 5.1, Theorem 5.2 and Proposition 6.2 | Supplies complete continued-use accounting and the conditional scalar-on-charge storage/in-place argument. It neither prepares the present repeated unknown-ray source nor installs the present Pauli/Bell controls. |
| FiniteKrausInstrumentBornMarginal and its owning Scribe, named in §5 | Supplies the existing finite normalized same-carrier branch-trace/Born identity and actual-prefix/discard conventions. The rectangular filters and acquisition theorem here are ordinary mathematics, with no inherited Lean certificate. |
| NCR, PVC, PR57, PG and Callable Storage Atlas, with the exact domains already listed in §5 | Their acquired seeds, fixed-controller trees, paid converter/entrance contracts, tapes, rights, complete successors and installed calls retain those domains. No correspondence installing them on (6.3), no free unknown seed and no new four-view inverse is assumed. |

The estimate-then-act method is literature-attested, including Bagan,
Ballester, Muñoz-Tapia and Romero-Isart, *Purity estimation with separable
measurements*, [quant-ph/0509087v2](https://arxiv.org/abs/quant-ph/0509087v2).
Its three-axis preliminary direction estimate and subsequent adaptive
measurement concern many identical qubits with averaged/asymptotic purity
criteria; those criteria do not replace the uniform finite calculation
(7.3), (8.5)–(8.9). The Bell consumer reuses the ordinary identity underlying
Horodecki, Horodecki and Horodecki, *General teleportation channel, singlet
fraction, and quasidistillation*,
[quant-ph/9807091v2](https://arxiv.org/abs/quant-ph/9807091v2), §III.E.
Its optimized trace-preserving fidelity theorem is not a claim of optimal
heralded preprocessing here. The two-point decision reduction, canonical
purification and trace-distance contraction in §9 are mature statistical
and quantum-information tools.

Tirone, Mele, Giovannetti and Lami, *Universal entanglement distillation*,
[2609.40080v1](https://arxiv.org/abs/2609.40080v1), supplies a general
asymptotic tomography/adaptive-distillation alternative for unknown iid
finite-dimensional mixed states. Its main universal statement does not
supply the finite local-number-preserving menu, actual erased-output formula
or explicit specimen bounds for this source. No rate or control-cost
comparison with that alternative is asserted. The contribution here is a
repository-derived source-specific acquisition/use synthesis. Bounded source
and statement searches do not establish worldwide originality.

The remaining four-view obligations have independent meanings in this model:

| View | Actual structure here and remaining obligation |
| --- | --- |
| Space | Labelled modes, their incidence and the fixed Alice–Bob partition are specified. No physical metric, raw occurrence geometry or producer from candidate $\alpha/\beta$ foundations is recovered from the final port. |
| Time | Specimen acquisition, counter updates, messages, target tests and the later input/call have an actual order. Neither a physical clock nor recovery of chronology/duration from another view is proved. |
| Boundary | CAR coordinates, charges, complete successors, inaccessible discards and the callable port are explicit. Compression does not invert discarded sectors, calibration specimens or the former action boundary. |
| Memory | Actual acquired counters lawfully control this run and the surviving pair supports one stated call. Exact ray certification, an unlimited archive, arbitrary historical access and reusable multi-call memory are not obtained. |

Mutual recovery of all four independently meaningful views, agreement of
recovery routes and dynamics compatibility on a broader common actual
internal-observer process remain unproved. Alpha/beta generation remains a
candidate foundation. Original fixed-$G_{gc}$, original-$Q$, parked-consumer
and unchanged-initialization obligations retain their existing scopes and
settlements. Theorem 8.1 is not completion of those obligations, the original
two-copy problem or the sustained four-expression objective. Physical source
supply, compatible phases, exact controls and any optional isolation remain
unverified installation premises; no physical or Lean certification is claimed.

## 追加锚（本行以下为增补区）
