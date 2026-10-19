---
slug: cobucci-tavakoli-2024-odd-ghz-ten-setting-witness
bibkey: cobuccitavakoli2024dimensionality
doi: 10.1126/sciadv.adq4467
url: https://arxiv.org/abs/2402.06234
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.result
---

# The Cobucci–Tavakoli ten-setting GHZ witness in odd dimensions

## Problem

G. Cobucci and A. Tavakoli, “Detecting the dimensionality of genuine
multi-particle entanglement”, Science Advances 10, eadq4467,
DOI 10.1126/sciadv.adq4467, arXiv:2402.06234v4, Supplementary
Material V, printed page 22, states:

> We have shown this explicitly for odd d ≤ 17 and conjecture it to hold for odd d in general.

For the nine labelled triples in (V1), the three-party witness operator
$\mathcal W_d$ in (V2), and every odd natural local dimension $d$, the
conjectured operator comparison is

$$
\mathcal W_d\preceq9|\mathrm{ghz}_{3,d}\rangle
\langle\mathrm{ghz}_{3,d}|+3\mathbf1. \tag{V5}
$$

Consequently, every density state $\rho$ satisfies

$$
F_{\mathrm{ghz}}(\rho)\geq\frac{W_d(\rho)-3}{9},
\qquad
W_d(\rho)\leq3+\frac{9D_{\mathrm{GME}}(\rho)}{d}. \tag{V4,V3}
$$

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| All odd local dimensions | `claim`, binder `d` and hypothesis `Odd d` | All odd natural dimensions, including composite dimensions and 1 |
| Nine triples (V1) | `tuples` | A list retains all nine labelled multiplicities |
| Witness (V2) | `omega`, `basisVec`, `proj`, `witness`, `witnessValue` | The literal preregistered expressions |
| GHZ vector, Eq. (5) and fidelity | `ghz`, `ghzFidelity` | The normalized three-party vector and real expectation |
| Schmidt rank and Schmidt number | `WitnessKernelTraceCriteriaRefutation.schmidtRank`, `cutRank`, `SchmidtNumberLE` | Frozen coefficient-matrix rank owner and finite convex decompositions across each cut |
| Definition 1, Eq. (2) | `GMEDecomposable`, `gmeDim` | Mixtures across all three cuts; the natural infimum is attained |
| (V5) | `witness_quadratic_bound`, `witness_density_bound` | Quadratic-form and density-state comparisons |
| (V4) and (V3) | `result : claim` | Both inequalities for every density state |

Except for the imported Schmidt-rank owner, names in the table belong to
`D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness`.
The state carrier is the canonical `FiniteStateChannel.DensityState`.
The witness expressions follow the formulas fixed by
[preregistration #16991](https://github.com/the-omega-institute/trureturing/issues/16991).

## Motivation

Ten measurement settings certify genuine three-party Schmidt dimension.
The certificate uses the expectation of the witness and does not require
mutual unbiasedness of the quadratic-phase bases. The source's result is
therefore applicable to composite odd dimensions as well as prime ones.

## Gap

The source explicitly verifies the comparison only through odd dimension
17. The missing assertion is uniformity over all odd dimensions, including
composite moduli. Counting arguments over a field do not alone establish
the composite case.

## Route

`character_orthogonality`, `constrained_character_sum`, and `witness_entry`
express the entries through additive characters and the two coordinate
differences. `count_le_three` bounds the multiplicity of a nonzero
frequency fibre among the nine labelled pairs. Oddness makes multiplication
by two cancellable; it does not assume primality.

`dft_energy` uses the frozen `FullBispectrumStability.cyclic_parseval`.
The block estimates give `witness_quadratic_bound`, and a spectral ensemble
extends it to `witness_density_bound`. The GHZ block has its extra coefficient
nine in addition to the scalar contribution three. Their sum is twelve;
this is an explanation of the block formula, not a separately stated Lean
eigenvalue theorem.

`diagonal_trace_rank_bound` applies the public frozen
`TomiyamaDiagonalKPositivity.trace_rank_bound`. The cut-rank overlap bound
extends through convex decompositions to `gmeDim_ghz_fidelity_bound`.
Combining it with the witness estimate proves `result`.

## Falsifier

An odd dimension and density state violating either conjunct of `claim`
would falsify the stated settlement. A nonzero coordinate-difference fibre
with four labels would falsify the counting route. Even dimensions are
outside the statement. Failure of spectral sharpness in an odd dimension
would not falsify the upper bound proved here.

## Evidence

The formal source is
[OddGhzTenSettingWitness.lean](../D5/S3/Quantum/Entanglement/GHZ/OddGhzTenSettingWitness.lean).
Its settling theorem is `result : claim`; the corresponding Scribe carries
one Proved resolution claim. The axiom closure of every public declaration
is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The module uses `utility: none` and
`admission_basis: open-problem-resolution (#16991; Proved)`.
Schmidt rank is imported from the frozen
`D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation` owner,
whose definition is `(Matrix.of fun i j => v (i, j)).rank` on `Fin m × Fin n`.
Each cut flattens the other two indices with `finProdFinEquiv`;
`Matrix.rank_submatrix` preserves the original coefficient-matrix rank.
The module has `generality: I`, following this import.
The proof-shape classification is `bind-only`; the named external settlement
supplies the admission basis. Every supporting helper has a mathematical
consumer.

The four-slot escape audit is unfinished for `result`,
`weight_le_one_of_total`, and `spectral_ensemble_nonempty`; see
[issue #17622](https://github.com/the-omega-institute/trureturing/issues/17622).
Faithful statement bridges are available, but whole-family variation,
sensitivity and actual observational-dependence evidence is not established.
No validated registration is claimed.

### Experiment

The experiment is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/6f98e1f5648a24ecf09a3376ec130d0c37b61237/docs/reports/cobucci-tavakoli-2024-odd-ghz-ten-setting-witness).
Its `check.py` has SHA-256
`acc189480ed8add3e04ed0df7ef43ec65b39a01f5155751d323503d248e02ac7`.
The reproducible command is `python3 check.py` in that directory at the pinned
commit. The implementation-seat reading executes that exact pinned blob
with Python; its exit code is 0 and its result is `ALL_OK`.
Dense spectra and their closed-form comparison are checked only for
$d=3,5,7,9,11,13,15$. The integer fibre-count check covers
$d=3,5,\ldots,201$. These finite readings do not replace the universal proof.

## Triage

### What the settlement shows

- **Proved — mechanism (kernel-checked).** `witness_entry` depends on the
  coordinate differences; `count_le_three` bounds each nonzero fibre by
  three; `grid_dft_bound`, `block_value_bound`, and
  `witness_quadratic_bound` give the block Parseval comparison. Oddness is
  used in the fibre count. Mutual unbiasedness is not an assumption.
  The zero-difference block formula explains the GHZ coefficient twelve
  as three plus nine, as derived in Route.
- **Proved — strength (kernel-checked).** `witness_quadratic_bound` and
  `witness_density_bound` prove the quadratic-form version of (V5);
  `fidelity_lower_bound` proves (V4), and `result` proves (V3) together
  with (V4). All odd dimensions, including composite dimensions, are in
  the quantified statement.
- **Proved — consequence (kernel-checked).** The first conjunct of `result`
  certifies the source's genuine three-party Schmidt dimension from the
  ten-setting expectation in every odd dimension. This removes the
  dimension restriction from this certificate; it does not extend any
  separate source theorem with additional hypotheses.
- **Open — sharpness and parity.** Attainment of the non-GHZ bound three
  in every odd dimension is not established by a Lean theorem here.
  The experiment computes attainment only for its seven dense-spectrum
  dimensions. Even-dimensional analogues remain open here.
- **Computed — finite experiment.** The pinned `check.py` experiment has
  exit 0 and `ALL_OK`. Its dense spectra have largest eigenvalue twelve,
  second eigenvalue three, and agree with the closed form within the
  script's tolerance $10^{-8}$ at exactly the seven listed dimensions.
  The exact integer count is at most three for odd dimensions from 3
  through 201. No uniform sharpness claim follows from these readings.
- **Open — literature completeness.** The literature screen found no
  all-odd-dimensional settlement within the stated sources. Completeness
  and prior occurrence of the nine-tuple eigenbasis in GHZ-stabilizer or
  qudit-graph-state witness literature are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The source quotations, Definition 1 correspondence, and literature screen
are attributed to the orchestrator's preregistration. The reported screen
covers Semantic Scholar, OpenAlex, INSPIRE and Crossref citation records of
the arXiv and Science Advances versions, the authors' arXiv lists and QIQC.
No all-odd settlement was found in that scope. The completeness of those
records, unread citing papers, and earlier nine-tuple eigenbasis constructions
are not verified. Kernel checking proves the formal statement within the
stated conventions and does not certify literature priority.
