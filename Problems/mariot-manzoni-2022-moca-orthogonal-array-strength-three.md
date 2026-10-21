---
slug: mariot-manzoni-2022-moca-orthogonal-array-strength-three
bibkey: mariotmanzoni2022moca
doi: 10.48550/arXiv.2207.08280
url: https://arxiv.org/abs/2207.08280v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.result
---

# Strength three of every Mariot–Manzoni MOCA array

## Problem

L. Mariot and L. Manzoni, *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*, arXiv:2207.08280v1, Section 5, asks to “prove that the binary OA obtained from a set of k-MOCA has always at least strength 3”. The precise target and source quotations are preregistered in [#19624](https://github.com/the-omega-institute/trureturing/issues/19624). The source is described in [the Library note](../Library/StatisticalMechanics/mariotmanzoni2022moca.md).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Definition 1: sliding windows of length $d$ | `ca` | $n=2b$, $d=b+1$, zero-based finite indices |
| Bipermutive: $f(y)=y_0+\phi(y_1,\ldots,y_{b-1})+y_b$ over $\mathbf F_2$ | `IsBipermutive` | existential arbitrary central Boolean function |
| Eq. (6): unequal superposed pairs at distinct cells | `AreOrthogonal` | input halves joined by `Fin.append` |
| A family of $k$ pairwise orthogonal bipermutive CA | `IsMOCA` | every rule bipermutive, distinct rule indices orthogonal |
| Eq. (7): juxtaposition of all $k$ output vectors | `mocaArray` | all $2^{2b}$ input rows, columns in `Fin k × Fin b` |
| Each pattern occurs $N/2^t$ times in any $t$ distinct columns | `IsOrthogonalArray` | injective column selections, subtype cardinality, natural division |
| Always strength at least three | `claim`, `result` | all $b,k$ and all such families; strength $t=3$ |

For $b=0$ the output is empty; this degenerate extension exceeds Definition 1's $d\le n$ parameter range and introduces no three-column selection. The same vacuity applies whenever $kb<3$. The theorem retains the complete source range $b\ge1$ and does not assert that three columns exist.

## Motivation

Lemma 3 of the source gives strength two. Section 5 asks whether strength three always holds; this is the tier-1 external named question settled here. The theorem concerns the array with all input rows, without an assumption on linearity of the local rules.

## Gap

The inspected arXiv:2503.10320v1 survey, Section 5.3.2, describes strength three as experimental. The source and literature screen in #19624 found no settlement in the inspected sources. Completeness is `ASSUMED-UNVERIFIED`: the full Springer chapter 10.1007/978-3-031-42250-8_11, the final journal survey 10.1016/j.dam.2025.10.014, and exhaustive forward citations are outside that screen.

## Route

A coordinate flip reverses a column's endpoint bit. For three columns sorted by starting position, flip the earliest left endpoint if the first two positions differ, the latest right endpoint if only the last position differs, and their common left endpoint if all positions coincide. In each case the triple XOR reverses. Distinct-start pairs use the earlier left endpoint. At a shared start, orthogonality makes the pair of complete output vectors a bijection, permitting reindexing and an output-bit flip. The seven nonconstant integer character sums vanish. Summing the three-bit indicator expansion gives eight times each fiber cardinality equal to the row cardinality.

## Falsifier

The statement would fail if a MOCA family and an injective selection of three columns had unequal binary-pattern counts. Source fidelity would fail if an input row were removed, boundary conditions changed, or linearity imposed; none of those restrictions occurs in `claim`.

## Evidence

**Kernel-checked:** `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.result` proves `claim`. The public declaration axiom closures are contained in `{propext, Classical.choice, Quot.sound}`. No D5 module is imported.

**Escape audit unfinished:** the sole public theorem `D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength.result` is covered by [#19669](https://github.com/the-omega-institute/trureturing/issues/19669). No valid four-slot registration is delivered; no `declared_validated` status is asserted. Admission is `open-problem-resolution (#19624; Proved)`, with conservative `proof_shape: bind-only`, `escape_witness: none`, and `utility: none`.

### Experiment

[Finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/dc61cd52eb2c29a580484a5b13d31c6795749cf2/docs/reports/mariot-manzoni-2022-moca-orthogonal-array-strength-three): run `python3 docs/reports/mariot-manzoni-2022-moca-orthogonal-array-strength-three/check.py` from that experiments revision. Script SHA-256: `741e7ffd7258cf0555ccb265ae097f501b3f09b793a9efb1117aa2133bf404eb`. Measured exit 0 (`RESULT PASS`). For $b=2,3,4$ respectively the checker enumerates $4,16,256$ rules, $4,36,852$ orthogonal pairs and $0,16,264$ unordered 3-MOCA families. Every enumerated 2- and 3-MOCA array passes strength three. It also samples arbitrary bipermutive families at $b=2,\ldots,5$ for single/triple XOR balance; that part is random, not exhaustive.

## Triage

### What the settlement shows

1. **Kernel-checked (`result`):** every set of $k$-MOCA has the requested strength-three array. The private consumed `triple_sum_zero` proves the three-column sign sum vanishes for arbitrary bipermutive families, without orthogonality and even with repeated columns. Orthogonality enters pair balance. No claim of balanced XOR for arbitrary odd-size selections is needed.
2. **Proved in prose:** the arbitrary odd-size assertion fails already for five columns. Set $b=3$, $\phi_0=0$, $\phi_1(t_0,t_1)=t_0t_1$, and choose $(0,0),(1,0),(0,1),(0,2),(1,2)$. Their XOR is $x_1x_2+x_3x_4+x_1+x_4=x_1(x_2+1)+x_4(x_3+1)$. Each summand is one on one of its four assignments. Their XOR is one on $2\cdot1\cdot3=6$ of the sixteen assignments of $x_1,\ldots,x_4$, hence on $24$ of the $64$ full rows, and zero on $40$. The pair of complete output vectors takes exactly $40$ values: write $u_j=x_j+x_{j+3}$ and $v=(x_1x_2,x_2x_3,x_3x_4)$. For each fixed $u$, the possible $v$ form $\{000,100,010,001,111\}$ if $u_1=0$ and $\{000,001,011,100,110\}$ if $u_1=1$. Each case has five values; there are eight choices of $u$. These are exact finite algebraic enumerations, not additional Lean statements. This family is not MOCA: the all-zero input and $(1,0,0,1,0,0)$ both give the zero vector for both CA. This disproves the auxiliary odd-size assertion, not the strength-three theorem.
3. **Computed (finite checker above):** All $16$ 3-MOCA arrays at $d=4$ and $192$ of $264$ at $d=5$ have strength exactly three. Thus a universal strength-four claim cannot replace the proved bound. The untested families and larger diameters are not classified by these computations. Sharpness is not an additional Lean theorem.
4. **Admission:** the pre-nominated three-column balance helper is compiled and consumed by `result`. All sixteen helpers and the settling result have the conservative `bind-only` assessment; the external named problem supplies the admission basis, rather than an independent escape-witness claim.
5. **Proved in prose from the array statement and the source's array-to-function correspondence:** replacing strength two by strength three in that correspondence raises its correlation-immunity bound to three. This is not an additional Lean theorem about Boolean-function constructions. The source's strength-two statement remains valid. The finite counterexamples above rule out uniform strength four. A classification of higher strengths at larger diameters is not addressed by this delivery.

## ASSUMED-UNVERIFIED

Literature completeness and global priority remain `ASSUMED-UNVERIFIED` for the explicit scope in Gap. The public theorem's four-slot escape audit is unfinished at #19669. The array-to-Boolean-function correspondence is used here only as a source-level consequence; its formalization and a uniform classification of higher strengths are outside this theorem.
