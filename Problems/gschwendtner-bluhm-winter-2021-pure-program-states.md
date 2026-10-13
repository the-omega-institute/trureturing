---
slug: gschwendtner-bluhm-winter-2021-pure-program-states
bibkey: gschwendtnerbluhmwinter2021programmability
doi: 10.22331/q-2021-06-29-488
url: https://arxiv.org/abs/2012.00717v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result
---

# Pure programs need more dimension than mixed covariant programs

## Problem

Gschwendtner, Bluhm and Winter, *Programmability of covariant quantum channels*,
Quantum **5**, 488, DOI 10.22331/q-2021-06-29-488, arXiv:2012.00717v2,
Section 5, ask:

> We leave it as an open question whether the upper bounds can be improved to match the lower ones also for pure program states.

The setting is a compact group, an irreducible unitary input representation
$U$, and an arbitrary unitary output representation $V$. A single exact
processor must implement every $UV$-covariant channel. The mixed optimum is
$d_c=\sum_k n_k$, where the commutant of $\bar U\otimes V$ is
$\bigoplus_k\mathbb1_{b_k}\otimes\mathcal B(\mathbb C^{n_k})$.
The affirmative assertion is that pure programs attain this same dimension.
Issue [#15518](https://github.com/the-omega-institute/trureturing/issues/15518)
fixes the source question and its quantifiers.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Compact group $G$ | `claim` quantifies over a group with `Fintype` | A finite group is compact in its discrete topology; this restriction suffices for a counterexample. |
| Unitary $U,V$ | `MonoidHom` into `Matrix.unitaryGroup` | Every group element acts by its coerced complex matrix. |
| Irreducible input | Frozen `NiceErrorBasisNonNormalStabilizer.IrredProj` | Its Euclidean-space invariant subspaces are transported by `WithLp.linearEquiv` to coordinate functions. |
| Completely positive, trace-preserving channel | Supporting `IsChannel` | A finite complete Kraus family and the frozen `MatrixMap.of_kraus` action. |
| $UV$ covariance | `IsCovariant` | The literal two-sided conjugation equality, for every group element and input matrix. |
| One fixed processor for every channel | `MixedProgrammable`, `PureProgrammable` | The processor is existentially quantified before the channel. |
| Mixed density program | Frozen `GHZMeasureBiseparableBound.IsDensity` | The literal positive-semidefinite, trace-one predicate on `Matrix`; `DensityState` uses a different `CStarMatrix` subtype carrier. |
| Pure density program | Frozen `PureStateHandshake.rankOneDensity` and normalized vector | Its body is `vecMulVec` with the starred vector; normalization is the conjugate dot product equal to one. |
| Tensor input | Mathlib `Matrix.kronecker` | The product-index matrix has the source tensor expression. |
| Match the mixed lower bound | `claim` | Every mixed program dimension also admits pure programs. The source's Theorems 25 and 31 identify the mixed optimum with $d_c$. |
| Negative answer | Settling `result` | A closed negation of `claim`, with $G=\mathrm{DihedralGroup}\ 4$, $d_1=d_2=d_P=2$. |

The arbitrary finite input index types in `IsChannel` include the processor's
product indices. Equality on all matrices expresses exact channel equality.
These conventions add no restriction that could exclude the source's counterexample.

## Motivation

The settling declaration is
`D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result`.
Its supporting theorem is
`D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction.no_four_replacements`.
The source's abelian-commutant construction already attains the mixed lower
bound with pure programs. A multiplicity-two block exhibits the obstruction.

## Gap

For the dihedral group of order eight, the standard two-dimensional irreducible
$U$ and trivial two-dimensional $V$ give one commutant block of multiplicity two,
so $d_c=2$. Mixed qubit programs implement all replacement channels. Pure qubit
programs cannot realize the two basis states, their equal superposition, and
$\mathbb1/2$ through the same processor.

## Route

The complete Kraus family turns the output for a fixed basis input and pure
program into the Gram matrix of a linear program-to-environment matrix map.
The first two pure targets give independent program vectors. The superposition
target makes the environment rows proportional. Every program then has a
rank-at-most-one output, which excludes $\mathbb1/2$.
The settling module constructs the dihedral representation, proves its
irreducibility, averages over its eight elements to characterize covariant
channels as replacements, and implements those channels with mixed qubit programs.

## Falsifier

The universal affirmative `claim` is refuted by `result`, whose type is literally
its negation. A counterexample to the supporting four-output obstruction would
invalidate the proposed mechanism; the Lean theorem excludes one for every
finite input dimension and every finite Kraus family. A publication already
settling the same question would invalidate the unresolved-literature premise,
without invalidating the mathematical theorem.

## Evidence

The two modules are Lean kernel-checked. The axiom closure of every public
declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The source and its citation screen are recorded in #15518. The Library locator is
`Library/QuantumChannels/gschwendtnerbluhmwinter2021programmability.md`.

### Experiment

[Covariant pure-program numerical checks](https://github.com/the-omega-institute/trureturing-experiments/tree/707a77a045f220eca00d6243967482d2db06f3ba/docs/reports/gschwendtner-bluhm-winter-2021-pure-program-covariant)
contains `check.py`. Command: `python3 check.py`; exit 0; final reading `bad= 0`.
Script SHA-256: `ba75df54b52797813a70c303a6a2360aec8c9637698e18b0600ad04f6dc461e1`.
The tested scope is all eight dihedral matrices and their products, the two
common-eigenvector candidates, twenty random qubit states for the group average,
fifty random qubit states for symmetric purification, and two hundred samples
for each environment dimension $r\in\{1,2,3,5\}$ for the rank-one algebraic step.
It also checks that the $A_4$ matrix and product sets each have twelve elements,
computes commutant dimensions
$1$ for $\vartheta$, $7$ for $\bar\vartheta\otimes\vartheta$, and $4$ for the
dihedral instance, and checks the block projector's trace six, its commutation
with all twelve tensor matrices, and the phase relation.
`commutant_dim` uses matrix-rank tolerance $10^{-9}$. The `allclose` and
`isclose` comparisons use NumPy defaults ($\mathrm{rtol}=10^{-5}$,
$\mathrm{atol}=10^{-8}$). The common-eigenvector test uses an explicit
$10^{-6}$ threshold, and the parallel-environment test bounds the second
singular value by $10^{-12}$. The phase test branches on
$|\operatorname{tr}V|>10^{-9}$; matrix and product sets are rounded to eight
decimal places before comparison. There are no $A_4$ averaging or purification
loops. These are finite numerical checks, not a proof of a uniform statement
or of an exact pure optimum.

### Escape audit

The escape audit is unfinished under
[#15645](https://github.com/the-omega-institute/trureturing/issues/15645).
The supporting public `no_four_replacements` has no delivered Reg mirror.
Its dependent-family registration lacks whole-family variation, sensitivity,
observational-dependence, and current source-selection evidence. The DTR reading
for this target is `DTR-Unregistered` (Observe); no completed registration is claimed.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

### What the settlement shows

**Qubit rigidity — literature ingredient.** Braun, Giraud, Nechita, Pellegrini
and Žnidarič, *A universal set of qubit quantum channels*,
[arXiv:1306.0495v2](https://arxiv.org/abs/1306.0495v2), Theorem IV.9,
DOI [10.1088/1751-8113/47/13/135302](https://doi.org/10.1088/1751-8113/47/13/135302),
classify the pure outputs of a qubit channel: three distinct pure outputs
force unitary conjugation. Evidence kind: literature reading; the Library
note is `Library/QuantumChannels/braun2014universalqubitchannels.md`.
Fixing a normalized basis input of a qubit-program processor yields a qubit
channel from programs to outputs. The three distinct pure replacement targets
force it to send every pure program to a pure state, so it cannot also attain
$\mathbb1/2$ with a pure program. GBW-5 applies this known ingredient to
covariant programming. The supporting Lean theorem proves the stronger
selected-target algebraic obstruction without program normalization; the full
classification is not a Lean statement of this delivery.

**Mechanism — kernel-checked obstruction.** `PureProgramQubitObstruction.no_four_replacements`
states that a fixed Kraus channel with a two-dimensional pure program space
cannot attain the four displayed qubit outputs. Its internal
`three_pure_outputs_rigidity` proves row dependence for every program;
`four_target_obstruction` uses that dependence to exclude $\mathbb1/2$.
The isometric interpretation follows in prose from Kraus completeness:
$W\psi=\sum_i K_i(|x\rangle\otimes\psi)\otimes|i\rangle$ satisfies
$\langle W\psi,W\phi\rangle=\langle\psi,\phi\rangle$ because
$\sum_i K_i^*K_i=\mathbb1$. Orthogonal pure targets give orthogonal program
vectors and rank-one images. The superposition target forces parallel environment
vectors. This interpretation is explanation; the addressable kernel theorem is
the four-output impossibility. `CovariantPureProgramDimensionRefutation.result`
uses it to give the negative answer.

**General bound — proved in prose, not in Lean here.** For irreducible input,
the source's Choi correspondence and teleportation construction identify
covariant channels with the states of
$\bigoplus_k\mathcal B(\mathbb C^{n_k})$. Feeding a fixed maximally entangled
input into any exact processor and compressing each commutant block by partial
trace gives a channel from its program space onto these states. Let $W$ be its
Stinespring isometry. Let $S_k$ span all pure program vectors whose output is
entirely in block $k$. Positivity of the reduced output implies
$W(S_k)\subseteq\mathbb C^{n_k}\otimes E$ in that output sector.
Different sectors are orthogonal, hence the $S_k$ are orthogonal.
The $n_k$ pure basis targets have orthonormal program preimages $p_j$, since
$Wp_j=e_j\otimes a_j$ and $W$ is an isometry. Therefore $\dim S_k\ge n_k$.
If equality holds, those $p_j$ form a basis. The pure target
$(e_j+e_\ell)/\sqrt2$ has a program in $S_k$; expanding it in that basis
forces $a_j$ and $a_\ell$ to be parallel. For every pair this gives one common
environment factor, so every vector in $W(S_k)$ has pure reduced output.
For $n_k\ge2$, a pure program realizing $\mathbb1/n_k$ belongs to $S_k$
and contradicts this. Thus $\dim S_k\ge n_k+1$ for non-scalar blocks. Summing,

$$d_P^{\rm pure}\ge\sum_k\bigl(n_k+[n_k\ge2]\bigr).$$

A nonabelian commutant has a strict pure/mixed gap. If every block is scalar,
Corollary 19 supplies pure programs of dimension $d_c$; the optima therefore
agree exactly for abelian commutants, in the source's irreducible-input setting.

**Symmetric upper construction — proved in prose.** For a spectral decomposition
$\sigma=\sum_j\lambda_j|u_j\rangle\langle u_j|$, the unit vector
$\sum_j\sqrt{\lambda_j}\,u_j\otimes u_j$ lies in
$\mathrm{Sym}^2(\mathbb C^n)$ and its first marginal is $\sigma$.
The fixed embedding followed by partial trace is a channel. Its program
dimension is $n(n+1)/2$. For $n=2$ this is three; with the lower obstruction,
the dihedral instance's pure optimum is three. The upper construction and
optimality equality are proved in prose, not stated by the delivered Lean result.

**The source's $A_4$ example — proved in prose; dimensions computed.** The source
decomposes $\vartheta\otimes\vartheta$ as
$\varphi_0+\varphi_1+\varphi_2+2\vartheta$, with multiplicities $(1,1,1,2)$.
Its mixed optimum is $1+1+1+2=5$. The general bound gives pure dimension at
least $1+1+1+3=6$. Direct-summing the three scalar sectors and the symmetric
qubit construction, and dephasing coherences between sectors, implements every
block state with pure dimension six. Thus its pure optimum is six. These lower
and upper arguments are proved in prose. The experiment computes the commutant
dimension seven and checks the block projector's trace six and commutation;
it does not itself
compute or kernel-prove the optimum.

**Readings — computed.** The pinned experiment entry in Evidence returns
`bad= 0` (`python3 check.py`, exit 0, SHA-256
`ba75df54b52797813a70c303a6a2360aec8c9637698e18b0600ad04f6dc461e1`).
It checks the eight $D_4$ matrices and products, two eigenvector candidates,
twenty $D_4$ group averages, fifty qubit symmetric purifications, and two
hundred parallel-environment samples at each $r\in\{1,2,3,5\}$. For $A_4$ it
checks the twelve-element matrix and product sets, the commutant ranks, the phase
relation, and the block projector's trace six and commutation. Its tolerances are stated in that entry;
no $A_4$ averaging or purification loop or uniform extension is computed.

**Larger blocks — open exact optimum.** For one multiplicity block $n\ge3$,
the exact pure optimum remains open between
$\lceil(n^2+1)/2\rceil$ and $n(n+1)/2$. The upper bound is the symmetric
construction. For the lower bound, a channel's map from pure program rays is
smooth from $\mathbb{CP}^{m-1}$, of real dimension $2m-2$, to Hermitian
trace-one matrices. If $2m-2<n^2-1$, all values are critical, and Sard's theorem
makes its image measure zero in the target affine space. It cannot cover the
state body's nonempty interior. Hence $m\ge\lceil(n^2+1)/2\rceil$.
This dimension argument is prose, and no claim of Lean verification is made.

**Consequences for the source — literature reading.** Theorems 25 and 31 for
mixed programs and Corollary 19 for abelian commutants survive. The negative
answer rules out extending the abelian conclusion to all commutants; the
source's mixed-program bounds do not rely on such an extension.

## ASSUMED-UNVERIFIED

The source/citation screen in #15518 found no prior settlement within its listed
scope. Exhaustive prior-art coverage and originality are unverified. Literature coverage does not include unavailable citing full texts,
including arXiv:2312.03188, 2210.08566 and 2207.05713; OpenAlex rate limits
leave the citation enumeration unverified beyond the scope listed in #15518. The general multiplicity
bound, symmetric construction, exact optimum three, $A_4$ optimum six and
higher-dimensional bounds above are prose arguments, not Lean declarations of
this delivery. The numerical checks cover only the stated finite matrices and
sample sizes. The four-slot escape registration remains unfinished under #15645.
