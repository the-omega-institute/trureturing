# Common stopped coefficient realizability

## Abstract

A normalized quadratic output kernel has a common stopped catalog law exactly when its vector demand and common mass budget fit.

**Definition 1.1 (Actual schedule alternatives).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Schedule`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Schedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, Schedule L is the original sum of the empty schedule, one address in Fin L, and an increasing pair in Pair L. The actual table constructor uses these alternatives directly; no additional schedule model is introduced.

**Definition 1.2 (Preselected terminal labels).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Labels`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Labels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every output type J, Labels J is J times J times J. The three coordinates store every terminal choice before replies; no new randomness is drawn at a visited cell.

**Definition 1.3 (Stored terminal readout).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.label`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type J, terminal triple t in Labels J and cell k in Fin 3, label t k selects respectively the first, second or third stored output. The cell and table interfaces consume this readout.

**Definition 1.4 (Chronological stopped cell).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.cell`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, schedule s in Schedule L and Boolean word b on Fin L, cell s b is zero for an empty schedule or the first queried false reply, one for singleton success or pair first success followed by second false, and two for pair success. The pair addresses are increasing, and the selected third terminal output need not be queried.

**Definition 1.5 (Original entire catalog table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.table`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, schedule s in Schedule L and terminal triple t in Labels(Fin(L+1)), table s t is the entire word-to-label function b mapped to label t (cell s b), with its original Catalog true L witness. StoppedResidualSynthesis.subsetTable and prefixTable use this constructor and its stored terminal semantics on their live derivation paths.

**Definition 1.6 (Increasing query pairs).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Pair`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, Pair L consists of two indices in Fin L with the first strictly smaller than the second. Index i denotes the original prime address i+1. These query indices are distinct from output labels in Fin(L+1), whose zero is the base mark.

**Definition 1.7 (Output-label mass).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.mass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite output type J and a real vector u on J, mass u is its sum over output labels. Signed coefficient vectors may have zero mass without being zero; the zero-mass argument used for terminal vectors requires coordinatewise nonnegativity.

**Definition 1.8 (All-word quadratic expansion).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.polynomial`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For L, any output type J, a constant vector c, address-indexed vectors ell and increasing-pair vectors Q, polynomial at word b and label r is c(r), plus ell(i,r) for every true bit b(i), plus Q(i,j,r) for every pair of true bits. The theorem requires this expansion at every Boolean word, including every pattern with multiple zeros. Values at zero, unit and two-unit input words identify the coefficients; they do not replace the all-word expansion hypothesis.

**Definition 1.9 (Outgoing negative pair demand).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.outgoing`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.outgoing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For Q, address i and label r, outgoing Q i r is V_i(r): sum the coordinatewise negative parts of Q over increasing pairs whose first address is i. The sum runs over pairs, not labels. It is zero when there are no outgoing pairs.

**Definition 1.10 (First-zero row demand).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.rowDemand`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.rowDemand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell and Q, rowDemand at i,r is h_i(r), the maximum of V_i(r)-ell_i(r) and zero. This demand must be accommodated by the unnormalized vector for schedules whose first query is i.

**Definition 1.11 (Total vector demand).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.totalDemand`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.totalDemand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell and Q, totalDemand at output label r is H(r), the sum of h_i(r) over addresses. Comparing H with c is coordinatewise; it does not authorize an independent probability budget for each label.

**Definition 1.12 (One common scalar budget).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.budget`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For L, a finite output type J, ell and Q, budget is beta: sum over addresses of the maximum of mass V_i and mass h_i. Each mass sums output labels. Under wordwise probability normalization, mass c is one and the signed masses of every ell_i and Q_ij are zero. These identities follow by evaluating the all-word expansion at zero, unit and two-unit inputs. Consequently mass h_i is at least mass V_i, each m_i equals mass h_i, and beta equals mass H. The scalar criterion beta at most one is retained exactly as in the source, although it follows from H at most c under this normalization.

**Definition 1.13 (A law of entire catalog tables).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Realizes`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and real kernel p on all Boolean words with output labels Fin(L+1), Realizes L p means that one PMF w on OriginalScheduledWitnessTables.Catalog true L has evaluated mass p(b,r) at every word and label. The same w is used for every b. Its outcomes are whole word-to-label functions represented by an empty, singleton or increasing pair schedule and a terminal table fixed before replies.

**Theorem 1.14 (Original Theorem 109.1).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.stopped_coefficient_realization_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.stopped_coefficient_realization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L, every family p of PMFs on Fin(L+1) indexed by all Boolean words on Fin L, every constant output vector c, address-indexed output vectors ell and increasing-pair output vectors Q, assume that each real probability p(b,r) equals polynomial(c,ell,Q,b,r). Then a common law in Catalog true L realizes these probabilities if and only if H(r) is at most c(r) at every label and beta is at most one. These are the original operands and both original non-strict conditions from Acquisition Resources Continuation, Definitions 108.1/108.2 and Theorem 109.1.

Necessity chooses one representing schedule and entire terminal table for each function in the existing finite catalog, once and independently of the input word. It aggregates their common distribution into nonnegative vectors for every schedule and terminal cell. Summing labels gives the same unnormalized schedule mass for all of that schedule's cells, and all schedule masses together sum to one. Write A_i as singleton-zero plus outgoing pair-zero vectors and B_i as singleton-one plus outgoing pair-10 vectors. The all-word expansion gives c as the empty vector plus the sum of A_i, ell_i as B_i-A_i, and Q_ij as pair-11 minus pair-10. Hence pair-10 dominates the negative part of Q_ij, B_i dominates V_i, and A_i dominates h_i. The equal masses of A_i and B_i dominate m_i; summing these common schedule masses proves beta at most one.

Sufficiency uses the literal allocation of 109.7–109.13. Put d_i=h_i, m_i=mass h_i and the empty vector r=c-H. For each increasing pair put pair-10 equal to the negative part of Q_ij, pair-11 equal to that vector plus Q_ij, and t_ij equal to its label mass. Put pair-zero equal to (t_ij/m_i)d_i, singleton-zero equal to (1-mass(V_i)/m_i)d_i, and singleton-one equal to d_i+ell_i-V_i. Their masses are respectively t_ij and s_i=m_i-mass(V_i), and the empty mass is one minus beta. All vectors are nonnegative. Singleton-zero plus outgoing pair-zero equals d_i; singleton-one plus outgoing pair-10 equals d_i+ell_i. Thus the mixture has constant c, linear coefficients ell and pair coefficients Q at every word.

The zero-row case is proved explicitly. If m_i is zero, nonnegativity and zero mass force h_i=V_i=0; h_i then forces ell_i nonnegative, and its zero signed mass forces ell_i=0. Every outgoing negative part is zero, so every outgoing Q_ij is nonnegative with zero signed mass and therefore zero. The displayed allocation formulas evaluate to zero for all those cells using Lean's total real division; the proof never assumes a nonzero denominator in this case. Positive denominators are used only in the positive-weight probability normalization branches.

To form a genuine common law, first draw one schedule according to its mass. For that schedule draw all three stored terminal labels using the normalized terminal vectors and PMF.bind/map, and map the complete table into the existing catalog. Empty schedules use the same vector in each stored cell. For singleton schedules, the unused third stored label has the same marginal distribution as the singleton-one label. Zero-weight schedules receive a fixed fallback PMF that contributes no mass. A bind marginal calculation proves each terminal law and therefore every word law. Runtime does not draw new randomness at a visited cell: the entire table has already been drawn.

The theorem includes L=0, arbitrary terminal labels, zero singleton and pair weights, beta=1, and multiple-zero words. For L=0 only the empty schedule remains. At beta=1 the nonnegative empty vector has zero mass, so it contributes no schedule. Degree at most two alone is insufficient: the two-bit deterministic XOR kernel has a valid quadratic expansion but violates H at most c.

For original-source use, p is the finite law at each low word, address i is original prime index i+1, and label r is the actual mark theta_r on the full original tape carrier. OriginalScheduledRealization.original_scheduled_realization supplies the source-free interpreter, actual paid read log, first-zero stopping, finite handoff, same-source pair and unchanged consumer. The owning realization exposition supplies whole-table Ico sampling from one source-independent uniform seed and common refinement. Applying those suppliers to the w produced here yields the original stopped law at every actual low word. No countable or computable internal-state restriction or global joint measurability is added.

For the closed-cap application of Theorem 110.2, the finite cap must hold for the mixed kernel at every word, including the independent pair TV row. Activity is strict: a_i exceeds epsilon exactly on the retained low addresses, with epsilon=1 and L=0 allowed. On every actual first absence beyond L, including the endpoint a_n=epsilon, the supplied full-tail identity gives error equal to the maximum of one minus the all-positive-word base mass and a_n. The finite all-positive word is represented by actual finite-pattern sources with later zeros; it is not an infinite all-positive source. Necessity transports feasibility rather than exact laws of an arbitrary original competitor. Composition uses the existing original-to-finite bridge and this iff; it makes no unrestricted N/O separation claim or general hard-two cap-intersection assertion.

The probability-vector allocation is distinct from scalar nonnegative query-in-expectation representations: those do not enforce the common schedule mass across terminal labels and stopped cells. The supplied PMF operations and finite-sum identities are reused from pinned Mathlib. This result does not claim a literature novelty classification.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Labels`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Pair`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Realizes`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.Schedule`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.budget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.cell`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.label`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.mass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.outgoing`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.polynomial`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.rowDemand`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.stopped_coefficient_realization_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.table`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization.totalDemand`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledRealization](OriginalScheduledRealization.md)
