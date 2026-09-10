---
slug: mub-six-fourth-basis
bibkey: mcnultyweigert2024mutually
arxiv_id: 2410.23997
triage: wall
motivation_gids:
  - D5/S3/Quantum/Tomography/MUBHadamardCompatibility
  - D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes
  - D5/S3/Quantum/Tomography/RankOneContextCommutator
  - D5/S3/Quantum/Tomography/CompleteContextTomography
  - D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras
  - D5/S3/QuantumBounds/Designs/CollisionConservation
---

# A fourth mutually unbiased basis in dimension six

## Problem

Does there exist a family indexed by `Fin 4` of orthonormal bases of
six-dimensional complex space such that vectors from distinct bases have
squared inner-product magnitude exactly `1 / 6`?

Problem 10.2 of arXiv:2410.23997v2 asks for nonexistence of such a family.
Zauner's MUB conjecture predicts that dimension six admits at most three MUBs.
The complete-set question concerns seven bases. Excluding seven does not exclude
four, while excluding four automatically excludes every larger family.

Here "Zauner's conjecture" means the MUB upper-bound conjecture. It is separate
from the SIC-POVM conjecture carrying the same name.

## Fixed-coordinate Hadamard normal form

After applying one common unitary, the first basis may be fixed to the
coordinate basis. Multiplying each of the other three normalized basis matrices
by `sqrt 6` produces three order-six complex Hadamard matrices
`H_0,H_1,H_2`. Their exact constraints are

```math
H_r H_r^\dagger = 6I,
\qquad |(H_r)_{ij}|^2=1,
```

and for every distinct pair,

```math
|(H_r^\dagger H_s)_{ij}|^2=6.
```

`D5/S3/Quantum/Tomography/MUBHadamardCompatibility.lean` now records this
algebraic carrier as `FourMUBHadamardWitness`. It avoids square roots by using
unnormalized Hadamard matrices throughout.

The same module defines:

- `EntrywiseUnit` and `IsComplexHadamard` in arbitrary finite order;
- `HadamardEquivalent`, with row and column permutations and unit phases;
- `HadamardUnbiased`, the flat relative-transition constraint;
- `IsExactHadamardAtlas`, the completeness and soundness contract required of
  a classified atlas;
- `HasLiftedFourMUBWitness`, the joint compatibility problem over three atlas
  entries and their explicit equivalence lifts.

The public theorem

```text
nonempty_fourMUBHadamardWitness_iff_lifted_atlas
```

proves that any exact order-six atlas reduces the normalized four-MUB problem
to this lifted triple search.

## The essential quotient obstruction

A single complex Hadamard matrix is classified up to

```math
H \longmapsto D_r P_r H P_c D_c.
```

For three matrices, independently choosing left factors changes a relative
transition by

```math
H_r^\dagger H_s
\longmapsto
D_{c,r}^\dagger P_{c,r}^\dagger
H_r^\dagger
(P_{r,r}^\dagger D_{r,r}^\dagger D_{r,s}P_{r,s})
H_s
P_{c,s}D_{c,s}.
```

The middle factor depends on both independently chosen left gauges. Only a
common ambient left gauge cancels. Independent right gauges merely relabel and
rephase vectors inside each basis and preserve flatness.

Therefore MUB compatibility is not a property of three independently selected
Hadamard equivalence classes. A finite class atlas cannot be queried by taking
one canonical representative from each class and testing those representatives
alone. The relative left gauges must remain variables or be fixed by a proved
simultaneous normal form.

The theorem

```text
independent_hadamard_equivalence_does_not_preserve_unbiasedness
```

makes this failure exact in order two. Two copies of the Fourier matrix are not
mutually unbiased. Multiplying one copy by the row phase `diag(1,i)` gives an
equivalent Hadamard matrix that is mutually unbiased with the unphased copy.
This small counterexample prevents an invalid quotient step from entering the
order-six proof.

## Existing projector geometry

For a family of four rank-one contexts, define pairwise mutual unbiasedness by
uniform overlaps `1/6`. The same new module commits three exact consequences:

```text
fourMUBContexts_have_maximal_incompatibility
fourMUBContexts_have_pairwise_orthogonal_planes
fourMUBContexts_have_commutator_sum_ten
```

For every distinct pair, normalized incompatibility equals one, the centered
trace-zero projector planes are orthogonal under the existing record-measurement
interface, and the aggregate squared Hilbert-Schmidt commutator norm equals
`10`.

These theorems connect the open problem to the repository's existing
`centeredProjector`, `centeredContextPlane`, tomography, purity, and commutator
truth sources. They derive necessary geometry from a hypothetical family. They
do not prove that the family exists or that it is impossible.

`CollisionConservation.lean` remains complete-set background. Its projective
2-design hypothesis follows naturally from a complete `d+1` MUB family. Four
bases in dimension six do not automatically provide that design, and no such
bridge is assumed here.

## The 2026 order-six classification claim

arXiv:2608.18053v2, by Mateo Cárdenes Wuttig and Joseph Tindall, claims a
complete exact finite-incidence classification of order-six complex Hadamard
matrices up to standard equivalence.

Its branch-complete construction starts from a dephased `3 x 3` corner. The
global routing proof examines all 400 positional corners. If no selected corner
has finite normalized horizontal and vertical candidate fibres, the matrix is
forced into the Karlsson sector or the Tao orbit. Exact exceptional certificates
then supply a finite-corner witness there as well. Soundness and completeness
identify the retained output with all order-six Hadamard matrices.

Version 2 further states that every class is algebraically recoverable from a
suitable corner, and that all classes except Tao's isolated matrix and one
explicit Karlsson matrix have a product-regular four-phase representative.
Such a representative is reconstructed by one quadratic and one cubic equation
in each direction.

The authors expose a public Lean 4 audit repository. This dossier inspected
commit

```text
57b03025ecbe259e474281f49e201ea7cb474e34
```

and its paper-facing theorem spine. GitHub Actions run `33350075705` completed
the Lean build and theorem-boundary audit successfully on 2026-08-31. The
upstream toolchain is Lean `v4.33.0-rc2`; trureturing uses `v4.33.0`.

This is materially stronger evidence than an unsupported preprint claim. It is
still an external, recent result. The current trureturing lane neither imports
that project nor postulates its classification. `IsExactHadamardAtlas` remains
an explicit hypothesis until a pinned translation is rebuilt on the local
carrier.

## Degree-four SoS boundary

arXiv:2606.13903 proves a coordinate-sensitive separation.

In raw vector coordinates, a degree-four pseudoexpectation satisfies the MUB
constraints for arbitrary proposed numbers of bases. That relaxation cannot
detect even the universal upper bound.

In centered projector coordinates,

```math
Q_{a,i}=P_{a,i}-I/d,
```

the cross-unbiasedness constraints become quadratic Gram equations. Applying
the trace-rank sum-of-squares identity to

```math
S=\sum_{a,i}q_{a,i}q_{a,i}^{T}
```

reduces to

```math
m(d-1)^2(d+1-m)\ge 0,
```

and recovers `m <= d+1` at degree four.

For `d=6` this is `25m(7-m)`. It is positive at `m=4`, so this certificate has
no exclusion power for the fourth-basis problem. Its useful contribution is the
correct coordinate system. Any new certificate must use extra order-six branch
information beyond the general trace-rank identity.

## Prior analytic exclusions and their present reliability

### Fourier family

arXiv:0902.0882 proves that the standard basis together with any member of the
two-parameter Fourier family cannot be extended to a MUB quartet. This is the
cleanest established branch exclusion and the best first target for an exact
Lean port. It can serve as a positive control for the new compatibility
interface.

### H2-reducible and Karlsson sector

arXiv:2110.13646 derives strong restrictions on H2-reducible matrices in a
hypothetical quartet and excludes several named families. A 2025 comment,
arXiv:2504.13067, identifies an erroneous real-`3 x 2` submatrix lemma and
questions downstream exclusions relying on it. The reply arXiv:2504.15576
reproves some restrictions and proposes replacements, while leaving a disputed
proof history.

Consequently no Karlsson-wide exclusion from that chain is consumed as a black
box. Each needed lemma must be re-established from its exact hypotheses. The
new 2026 Hadamard audit is valuable here because it provides explicit Karlsson,
Fourier-seam, Tao, and regular-corner algebra on which replacement certificates
can be built.

### Numerical searches

arXiv:2203.09429 gives three numerical approaches that all support
nonexistence. These experiments are valuable for finding candidate separating
polynomials and difficult branches. Approximate infeasibility, optimizer
failure, or an unverified floating-point SDP dual does not close the problem.

## Exact next route

The formal lane now has six measured stages.

### Stage A. Basis and projector bridge

Construct an explicit `OrthonormalBasis` or unitary-matrix carrier and prove:

```text
orthonormal basis
  -> complete RankOneContext
coordinate-unbiased basis
  <-> scaled ComplexHadamard
pairwise MUB
  <-> HadamardUnbiased
```

The present `FourMUBHadamardWitness` is the exact algebraic normalized carrier.
The remaining task is a theorem connecting it bidirectionally to the basis and
rank-one-context carriers.

### Stage B. Pinned atlas translation

Translate the upstream definitions and paper-facing theorem at a pinned commit,
or provide a checked adapter proving

```text
IsExactHadamardAtlas atlas.
```

The adapter must preserve the source's standard equivalence witnesses. Copying
only a class-membership proposition is insufficient for the joint problem.

### Stage C. Simultaneous gauge normal form

Reduce the lifted compatibility system by transformations known to preserve the
whole MUB family:

- one common left monomial action;
- independent right monomial actions;
- permutation of the three non-coordinate bases;
- complex conjugation or transposition only after proving their simultaneous
  action preserves every pairwise constraint.

The output should minimize variables without quotienting away relative left
gauges.

### Stage D. Branch compatibility compiler

For each classified branch, emit exact polynomial constraints for three lifted
matrices. Unit phases become real pairs

```math
z=x+iy,
\qquad x^2+y^2=1.
```

Hadamard and MUB equations then become real polynomial equalities. Branch
inequalities and nonvanishing conditions remain explicit side constraints.
Each emitted instance must carry:

```text
branch identifier
source parameter domain
gauge normalization
polynomial equations
inequalities and nonzero guards
reconstruction soundness theorem
```

### Stage E. Exact exclusion certificates

Accepted certificate forms include:

- symbolic elimination or a resultant with a proved nonvanishing conclusion;
- a rational Positivstellensatz or centered-projector SoS identity;
- interval certificates whose rational boxes cover the complete compact
  parameter domain;
- exact SDP duals converted into rational Gram factorizations and checked as
  polynomial identities.

A generic algebraic certificate has the form

```math
-1=\sum_a s_a(x)^2
   +\sum_j q_j(x)f_j(x)
   +\sum_k t_k(x)g_k(x),
```

where the `f_j=0` are branch and MUB equations and the `g_k>=0` encode the
allowed semialgebraic domain. Lean should check the expanded identity and the
sign conditions; numerical solvers may discover the certificate but are not
trusted to validate it.

### Stage F. Global aggregation

Prove every lifted atlas triple enters an excluded branch. This is the final
finite-cover theorem. The global nonexistence result then follows through

```text
no_fourMUBHadamardWitness_of_no_lifted_atlas
```

and, after Stage A, transfers to four orthonormal bases and four rank-one
contexts.

## Branch order

The recommended order is:

1. Fourier family and Fourier seams, because an analytic quartet exclusion is
   already known and gives a calibration target.
2. Tao orbit and the single product-exceptional Karlsson matrix, because both
   are isolated or finitely exceptional.
3. Regular four-phase finite-corner branches, using the quadratic-cubic
   reconstruction to keep elimination degrees controlled.
4. The remaining Karlsson parameter domain, with every disputed historical
   lemma replaced by a checked local certificate.
5. The global atlas-cover aggregation.

A rigorous exclusion of one previously open continuous branch is already a new
mathematical contribution even before the global theorem is closed.

## Current machine status

| Component | Status |
| --- | --- |
| Rank-one context overlap and commutator geometry | proved |
| MUB equals orthogonal centered projector planes | proved |
| Dimension-six maximal incompatibility and commutator value | proved in this lane |
| Generic complex Hadamard and standard equivalence carrier | proved in this lane |
| Gauge-retaining exact-atlas reduction | proved in this lane |
| Independent-class quotient obstruction | proved in this lane |
| Basis-to-Hadamard-to-context equivalence | open |
| Pinned local verification of the full order-six atlas | open |
| Fourier branch exact exclusion port | open |
| New branch compatibility certificate | open |
| All-branch four-MUB exclusion | open |

## Falsifiers

A concrete exact family of four pairwise mutually unbiased bases in dimension
six refutes the nonexistence conjecture.

For the normalized matrix carrier, three explicit order-six matrices satisfying
`FourMUBHadamardWitness` refute every proposed global exclusion certificate.

For an individual branch certificate, one exact parameter point and explicit
gauge lifts satisfying all branch and pairwise transition equations refute that
certificate. Floating-point near-solutions are diagnostic evidence and must be
converted to exact or interval-validated witnesses before they count as
falsifiers.

## Triage

`wall`, with a live formal entry point.

The wall has moved. The repository now knows exactly what must be checked after
a single-matrix Hadamard classification and formally prevents the invalid use
of independent canonical representatives. It does not yet possess the
basis-context bridge, a locally rebuilt order-six atlas, or a branch-complete
compatibility exclusion.

## Verification boundary

- The upstream order-six classification was inspected through its current
  arXiv v2 text, public theorem spine, pinned commit, and successful upstream
  CI. No local rebuild of all upstream modules was performed in this lane.
- No theorem in trureturing assumes the classification claim.
- The centered-projector degree-four SoS identity proves only the general
  `m <= d+1` bound. It is not presented as evidence excluding `m=4`.
- Historical H2-reducible exclusions affected by the 2025 comment are treated
  as research leads until their exact dependencies are re-proved.
- The current Hadamard witness is a normalized algebraic carrier. Its full
  equivalence to the orthonormal-basis and rank-one-context formulations
  remains an explicit next theorem.

## 2026-09-07 audited local result and remaining obligations

This dated addition qualifies earlier uses of the word "proved" in this
cumulative dossier. Source-level proof scripts, successfully replayed external
certificates, and Lean-kernel acceptance are different evidence levels. This
continuation did not run Lean/lake, Scribe emission or CI, and does not report
the entire lane as kernel-accepted.

### The substantive progress on the original existence problem

A full directed-interval computation now excludes an explicit nonempty
neighborhood of an exact order-six seed, with the stronger local conclusion
that a complete third MUB cannot be accompanied by even one further vector
unbiased to the three bases. This is a literal `(6,6,6,1)` exclusion, and hence
a local four-basis exclusion, not just a failure to find numerical roots.

Let `b=(-3+4i)/5`, `e=(-2+i sqrt(21))/5`, and

```math
H_0=\begin{pmatrix}
J_3+(b-1)I_3&J_3+(e-1)I_3\\
J_3+(\bar e-1)I_3&-J_3-(\bar b-1)I_3
\end{pmatrix}.
```

For actual order-six complex Hadamard H, the certified scope is

```math
\max_a\sum_j|H_{ja}-(H_0)_{ja}|\le9/4096.
```

It contains the entire entrywise ball of radius `3/8192`. The proof uses an
exhaustive cover of the ALL-SIX residual sublevel at `1/64`, actual matrix
residual transfer at tolerance `1/256`, and a complete two-relation finite
certificate with no possible extra-vector partner. It permits unknown root
multiplicity and does not need every tube to contain a unique root.

The final local code and mathematical proof are documented in
`docs/develop/certificates/real_x_balanced_sublevel/README.md`. The driver is
`scripts/research/check_real_x_balanced_cover.py`; it recomputes the seed,
local refinement, graph and all charts instead of reading a previous PASS.

The delivery turn actually repeated the full computation: 32 charts,
4,900,318 boxes, zero pending and unresolved boxes, 2,403 candidate first
six-cliques and no common partner after residual-preserving refinement.
These are algorithmic diagnostics, not counts of actual completion bases.
The repeated result object equals the preceding result object. Rational
LP-vertex and malformed-certificate tests were rerun as well.

### The additional formalized analysis

`HadamardResidualConservation.lean` and its canonical Scribe add two public
proof scripts. `hadamard_residual_box_dual` derives the exact residual identity
`sum_j (normSq((H* u)_j)-6)=0` from the actual scaled Gram equation and unit
input moduli, then bounds the real residual readout using arbitrary dual
shifts. `balanced_hadamard_sublevel_row_enclosure` consumes the existing
mean-value owner and retains the complete derivative remainder. These scripts
supply actual matrix-to-analysis connections, not an assumed desired bound.

The finite graph owner `RealXFinitePartnerCertificate.lean` is retained from
another agent. Its literal tables and coloring proof remove an abstract finite
no-partner hypothesis. They do not remove the analytic tube-cover hypotheses.
No duplicate graph, context or Hadamard carrier is introduced here.

### Three distinct gaps remain

1. **Local kernel closure.** Prove the concrete rational interval operations and
   expressions contain the actual residual and derivative, verify the entire
   split/contract/exclude certificate tree, and connect actual rank-one
   projectors to the covered signed-Cayley domain. A generic theorem with
   these facts as premises does not discharge them. Compiling the new two
   proof scripts alone is also insufficient.
2. **Parameter coverage.** The explicit ball is small. No complete X-family
   cover, universal strict-X affinity bound, or all-parameter strong-
   unextendibility theorem has been obtained. Larger incomplete traversals
   are recorded as INCOMPLETE and excluded from the result.
3. **Global MUB reduction.** Even a full X-family exclusion would still need
   a justified reduction from every possible quartet to the covered matrix
   families, or a complete lifted-atlas compatibility argument. A classification
   of individual Hadamard matrices does not by itself solve this joint problem.

The current publication target remains a verified local strong-unextendibility
result and its proof-producing method. Classical residual conservation, support
functions, interval methods and coloring bounds are not claimed as new
principles. First-priority and publication significance require a separate
comparison with prior exclusions and independent expert review.

Matolcsi, Matszangosz, Varga and Weiner, *Triplets of mutually unbiased bases*,
J. Algebraic Combinatorics 63, 26 (published 4 March 2026), Conjecture 3, still
states the whole Szollosi-family quartet exclusion as a conjecture. The
publisher text was checked again in the delivery turn. Jaming et al.,
arXiv:0902.0882, already proves a whole Fourier-family quartet exclusion; the
present local ball is not advertised as superseding that full-family result.

No global upper bound on the number of six-dimensional MUBs is improved by this
local computation. No numerical percentage of the open problem is assigned.
