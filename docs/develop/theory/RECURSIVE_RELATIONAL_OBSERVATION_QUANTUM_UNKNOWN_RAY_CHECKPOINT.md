# Recursive relational observation: finite unknown-ray encoded checkpoints

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
does not provide a source label, an external phase reference, a second
specimen, or a correlated programme.

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
delivered to the controller.

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
p_r=\operatorname{Tr}\Phi_r(\Omega),qquad
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
p_{\rm res}=\sum_{r\in\mathcal R_{\rm res}}p_r,qquad
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
L(\eta)=\eta\otimes|0\rangle,qquad
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
records. Every complete leaf includes the records written before stopping,
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
successor after the actual prefix $\gamma$ and $y$ is the next recorded
outcome, then

$$
D_{\gamma y}=K_{\gamma,y}D_\gamma K_{\gamma,y}^*,qquad
\operatorname{Tr}D_{\gamma y}=\Pr(\gamma y),
\tag{4.2}
$$

and the record stored at that node is the actual prefix $(\gamma,y)$.
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
use; it does not infer an unknown setting from the source. The standard
ingredients here—positive partial-transpose congruence, finite direct sums,
continuity of finite matrices, and the finite-dimensional kernel argument—are
reused mechanisms.

The new inference is the exact moving-kernel statement of Theorem 3.1: a
finite source-independent product bank can be defeated by one unknown ray and
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
