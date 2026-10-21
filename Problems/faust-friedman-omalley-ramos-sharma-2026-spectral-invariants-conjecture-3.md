---
slug: faust-friedman-omalley-ramos-sharma-2026-spectral-invariants-conjecture-3
bibkey: faust2026spectralinvariants
doi: 10.48550/arXiv.2602.08304
url: https://arxiv.org/abs/2602.08304v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation.result
---

# A singular nonzero point of the odd spectral-invariant variety

## Problem

M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma,
*Algebraic Properties of the Ideal of Spectral Invariants for the Discrete
Laplacian*, arXiv:2602.08304v1, Conjecture 3, p. 11:

> When q is odd, then V(I′) has only regular nonzero points, and when it is an even number greater than 6 there is a single singular point, up to symmetry, of multiplicity 2^{q/2−2}. Moreover, the multiplicity at 𝟎 is 2^{⌊q/2⌋}.

This delivery refutes the odd clause under the Jacobian regularity criterion
specified in [preregistration #19188](https://github.com/the-omega-institute/trureturing/issues/19188).
The [Library note](../Library/GraphInvariants/faust2026spectralinvariants.md)
records the source definitions. Period means a period, without a least-period
requirement. The even and origin-multiplicity clauses are not settled here.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $L_V=L_V(1)$, diagonal $V$, cyclic off-diagonal entries one | `floquetMatrix` | Literal cyclic-adjacency formula; the claim uses sizes at least five |
| $D_V(\lambda)=\det(L_V-\lambda I)$ | `floquetCharPoly` | This sign convention is retained |
| $U=(u_1,\ldots,u_m,0,-u_m,\ldots,-u_1)$ | `specializedPotential` | Zero-based indices; no additional constraint on the coordinates |
| $\zeta_U=D_U-D_{\mathbf0}$ | `zeta` | Full polynomial difference |
| $p'_k=(-1)^{n+k}[\lambda^{n-2k}]\zeta_U$ | `pPrime` | Literal coefficient and sign; only $1\leq k\leq m$ generate the ideal |
| A point of $V(I')$ | `InVariety` | Every generator vanishes |
| Regular nonzero points | `jacobianAt`, `IsRegularPoint`, `u ≠ 0` in `claim` | Regularity is precisely nonvanishing of the generator Jacobian determinant |
| Every odd $q=2m+1>3$ | `claim`, with $2\leq m$ | No least-period hypothesis |
| Refutation | `result` | Negates this full universal claim |

All names in this table belong to
`D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation`.
Section 3, p. 7 refers to multiplicity for the defining ideal rather than its
radical. No separate local-algebra equivalence between multiplicity one and
Jacobian invertibility is formalized in this delivery.

## Motivation

The fifteen-site potential repeats a nonzero five-site solution three times.
The smaller solution is regular at its own period, while the repeated
potential has a cyclic symmetry that identifies two Jacobian columns.

## Gap

The literature screen recorded in #19188 reports arXiv v1 only, zero Semantic
Scholar citations, zero solutions on MathDB pages 373040 and 373041, and no
match in formal-conjectures or the repository problem register. These source
and literature readings are orchestrator-reported. Literature completeness
and absence of a settlement outside that screen are `ASSUMED-UNVERIFIED`.

## Route

Choose $a\in\mathbb C$ with $a^2=1-2i$ and put $b=ia$. The point is
$u=(a,b,0,-b,-a,a,b)$, with $m=7$. Its specialized potential is
$(a,b,0,-b,-a)$ repeated three times.

The shared theorem
`D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace.cycleDiag_det_transfer`
identifies the cyclic determinant with the transfer trace minus two over every
commutative ring. The private `floquet_transfer` applies that theorem to the
source's sign convention. A five-step block has the same trace as the free
block and determinant one. The consumed frozen theorem
`D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two` identifies their cube
traces, proving equality of the fifteen-site characteristic polynomials.

The private `membership` proves that all seven specialized generators vanish.
Cyclic relabelling by five fixes the potential and its characteristic
coefficients. Differentiation through the antisymmetric specialization yields
`jacobian_columns`: columns 0 and 5 agree. The private `singular` applies
`Matrix.det_zero_of_column_eq`. The public `result` combines this singularity,
membership and nonzeroness to refute `claim`.

## Falsifier

The explicit witness would fail if a generator did not vanish, if its Jacobian
were nonsingular, or if the point were zero. The compiled proof excludes
those cases for $m=7$ and $a^2=1-2i$. A conjecture restricted to least period
$q$ would exclude this repeated witness and is a different statement.

## Evidence

The kernel-checked public declaration is
`D5.S3.Combinatorics.SpectralGraph.FaustSpectralInvariantsOddRefutation.result`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The five supporting public theorems have an unfinished escape audit in
[#19504](https://github.com/the-omega-institute/trureturing/issues/19504):
`cycleDiag_apply`, `cycleDiag_det_transfer`, `transfer_det`, `evolution_add`
and `evolution_det`. No `declared_validated` registration is claimed.

### Experiment

[Published symbolic check](https://github.com/the-omega-institute/trureturing-experiments/tree/cbd9018bd08d6f9bbf95783f310c5d6d27d6c088/docs/reports/faust-friedman-omalley-ramos-sharma-2026-spectral-invariants-odd-singular),
script `check.py`, SHA-256
`3104c3f22110fa427ebe87e793f831c5fff8c3c0206f1b4b7bd608762bb62c31`.
Command: `python3 docs/reports/faust-friedman-omalley-ramos-sharma-2026-spectral-invariants-odd-singular/check.py` from the experiments checkout; exit 0, `RESULT PASS`.

Computed scope: at $q=15$, the script checks the transfer determinant against
one direct $15\times15$ determinant at its seeded rational potential and
$\lambda=3/7$; checks the seven odd-offset coefficients symbolically; verifies
$a^2=1-2i$ and vanishing of all seven generators at the explicit radical
witness; verifies equality of Jacobian columns 1 and 6 exactly; and reports
numerical rank 2 using 50-digit evaluation with a $10^{-30}$ zero tolerance.
The rank is a numerical reading, separate from the kernel proof of zero
determinant. This experiment does not test $q=5$ or a uniform family.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| $q=15$ refutation of the unchanged odd-clause claim | Proved in Lean by `result`, with the private `membership`, `jacobian_columns` and `singular` on its proof path |
| $q=5$ generators $a^2+b^2$ and $a^2b^2+2a^2-2ab+b^2$ | Proved in prose by the transfer expansion below; no Lean theorem for these exact formulas |
| $q=5$ membership and Jacobian determinant $16-12i$ at $b=ia$, $a^2=1-2i$ | Proved in prose below; separate from the published $q=15$ computation |
| Repetition of arbitrary nonzero odd-period solutions an odd number of times | Open; only the five-site word repeated three times is formalized |
| Restriction to least period $q$ | Open; the witness has period five |
| Even-period clause | Open |
| Origin-multiplicity clause | Open |
| Local-algebra multiplicity equivalence | Open in Lean; regularity in the compiled claim is exactly the stated Jacobian criterion |
| Effect on the source's finite data and other results | The odd clause is unavailable as a universal premise; the finite data, even clause and origin clause are not refuted by this result |

For the prose $q=5$ calculation, multiplication of the five transfer matrices
gives trace
$\lambda^5-(5+a^2+b^2)\lambda^3+
(5+a^2b^2+2a^2-2ab+b^2)\lambda$.
Subtracting the free trace and applying the source's coefficient signs gives
$p'_1=a^2+b^2$ and $p'_2=a^2b^2+2a^2-2ab+b^2$.
With $b=ia$ these become zero and $a^2(1-2i-a^2)$, hence both vanish.
Their Jacobian determinant is
$4ab(a^2-b^2)-4a^2-4ab+4b^2$; substitution gives
$(8ia^2-8-4i)a^2=(8+4i)(1-2i)=16-12i\ne0$.
This derivation supplies the exact $q=5$ values without claiming that the
published experiment or a Lean theorem checks them.

The failure mechanism is repetition symmetry: two distinct coordinate
directions give the same first-order generator data. For odd $q\leq11$ there
is no proper odd divisor $q_0\geq5$; at $q_0=3$ the sole generator is $a^2$,
so its zero set has no nonzero point. This arithmetic explains why that
repetition mechanism is absent from the source's displayed small-period data;
it does not prove regularity for all primitive odd periods.

## ASSUMED-UNVERIFIED

Literature completeness and absence of an external settlement outside the
screen recorded in #19188 remain `ASSUMED-UNVERIFIED`. The source's geometric
multiplicity terminology has not been independently identified with the Lean
Jacobian predicate by a local-algebra theorem. The least-period, arbitrary
repetition, even-period and origin-multiplicity questions remain open in this
delivery. The supporting escape audit is unfinished under #19504.
