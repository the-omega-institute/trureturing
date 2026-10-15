# Reset codebook: Finite

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Theorem 1.1 (common memory cutoff).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (height eps : ℝ) (hh : 0 < height) (heps : 0 < eps) : ∃ n : ℕ, K ≤ n ∧ height*rho^n < eps

**Definition 1.2 (step).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.step`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by step(low : Bool) (D : ℝ) := A low+rho*D.

**Definition 1.3 (run).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by run(low : Bool) (a : Return) (D : ℝ) := (step low)^[a.val.1] (chi^a.val.2*D).

**Theorem 1.4 (parameters).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) : 0 < rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧ 0 < h low ∧ h low < E low ∧ E low ≤ 1/4

**Definition 1.5 (execute).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.execute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by execute(low : Bool) (as : List Return) (D : ℝ) := as.foldl (fun x a => run low a x) D.

**Theorem 1.6 (run bounds).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ run low a D ∧ run low a D ≤ h low

**Theorem 1.7 (execute bounds).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : 0 ≤ D) (hh : D ≤ h low) : 0 ≤ execute low as D ∧ execute low as D ≤ h low

**Definition 1.8 (initial).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.initial`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by initial(low anchor : Bool) := if anchor then Y low else X low.

**Definition 1.9 (closedRun).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by closedRun(low : Bool) (m r : ℕ) (D : ℝ) := h low-rho^m*(h low-chi^r*D).

**Theorem 1.10 (run closed).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (a : Return) (D : ℝ) : run low a D=closedRun low a.val.1 a.val.2 D

**Theorem 1.11 (reset lifts).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (M : ℕ) (z : ℝ) (hz : A false ≤ z) : resetFloor M ≤ closedRun false M 1 z

**Theorem 1.12 (execute floor).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) (as : List Return) (D : ℝ) (hD : A low ≤ D) (hh : D ≤ h low) : A low ≤ execute low as D

**Theorem 1.13 (weak run).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d : ℝ) (a : Return) (as : List Return) (D : ℝ) : Statement.weak K d (a::as) D ↔ a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ Statement.weak K d as (run false a D)

**Theorem 1.14 (weak gain).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K : ℕ) (d delta x y : ℝ) (as : List Return) (hd : 0 < delta) (hxy : x+delta ≤ y) (hw : Statement.weak K d as x) : Statement.weak K (d+delta*g^(totalWeight as)) as y

**Theorem 1.15 (A nonneg).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: 0 ≤ A false

**Theorem 1.16 (weak append).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two weak runs meet at the state produced by executing the first list, their concatenation is weak from the initial state.

**Theorem 1.17 (finite reset weak state).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite list of codeword lists, the reset-prefixed concatenation satisfies the strengthened weak guard at every state between A false and h false, provided each codeword has weight N and satisfies the original weak guard.

**Theorem 1.18 (reset actual family).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hb : lambda-g^2*chi^K*h false < b) (hd : d=(lambda-b)/(g^2*chi^K)) (hreset : max (X false) (Y false) < Statement.B M) : 0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM

Uniform-reset application to the original literal sources. The following construction composes the existing suppliers; it is an application exposition, with no additional mathematical declaration. Fix an arbitrary boundary ownership o, a real budget b and a natural K ≥ 2. Write H = h false, A = A false, X = X false, Y = Y false and S = g²χᴷ. Retain the complete original budget interval λ − S H < b < λ − S(A/(1 − ρχᴷ)). Set d = (λ − b)/S, equal to the original successive quotient (λ − b)/g²/χᴷ. The reset is chosen before the source model, weight, target model and list of codewords.

The parameter correspondence is exact. The literal high/low sides map to low = false/true, and the original/anchored models map to anchor = false/true. Literal t, g, ρ, χ and lam agree with the fixed scalars t, g, rho, chi and lambda, where ρ = g⁶ and χ = g²⁰; the literal c0 is 2t/5. For either side, hSide, aSide, xSide, ySide and initial become h, A, X, Y and initial under these Boolean maps. The labels L3, L0, L5, L2 and L25 map respectively to threeLabel, nullLabel, fiveLabel, twoLabel and twoFiveLabel. A positive literal return (m,r) maps to ResetCodebook.Return with the same coordinates and positivity proofs. GuardTrace K d false high becomes Statement.weak K d, and listWeight becomes Statement.weight, retaining the weight 6m + 20r of each return. Execution order is preserved: the literal observed prefix and the fixed sourcePrefix both reverse the return list, and mapping commutes with reset-prefixed concatenation. The original actualAutomaticCost K is exactly Statement.autoCost K, after reassociating its maximum and identifying g⁶ with rho.

To obtain one reset, put L = max (max X Y) d. The parameter bounds, including X_bounds and the definitions of Y and A, give L < H and H − χA > 0. The lower-budget hypothesis gives d < H. Apply common_memory_cutoff with lower index 1, height H − χA and tolerance H − L. It supplies M ≥ 1 with (H − χA)ρᴹ < H − L. Thus the positive return R = (M,1), mapped to Statement.reset M, has reset floor B = H − ρᴹ(H − χA) = Statement.B M > L. In particular B exceeds both model initial states and d. This same R works for every source model and positive weight N.

For a source model s and N > 0, let Dₛ = initial false s and let V be the complete dictionary of positive-return lists v with Statement.weak K d v Dₛ and Statement.weight v = N. Define δ = B − Dₛ, γ = δgᴺ and ε = min (b − Statement.autoCost K) (Sγ)/2. The reset bound gives δ > 0 and γ > 0. The existing automatic_strict gives Statement.autoCost K < λ − S H < b, hence ε > 0. This is the exact original source-dependent margin, even when the target model differs from the source model.

For every target model t and every finite list of words from V, let execution be the concatenation of R :: word for those words, in list order. Apply finite_reset_weak_state with source anchor s and starting state initial false t; initial_floor and initial_bounds put that state between A and H. The result is Statement.weak K (d + γ) execution (initial false t), hence the original strengthened GuardTrace under the exact map. The gain still uses Dₛ, not the target initial state. No nonempty-dictionary or nonempty-list hypothesis enters this argument. If V is empty, the empty word list remains covered; its execution is empty and its actual literal sources still contain the prescribed stem, optional anchor and tail. The declaration reset_actual_family itself uses a single anchor; the arbitrary-target conclusion here is obtained by the stated application of finite_reset_weak_state and the budget and source suppliers.

The exact budget identity b = λ − S d lets fullBudget_guard, applied with target anchor t and gain γ, bound fullBudget on both literal sides by max (Statement.autoCost K) (b − Sγ). The existing full_departure_cost bounds each prescribed sourcePrefix wordCost by that fullBudget. Since 2ε ≤ b − Statement.autoCost K and 2ε ≤ Sγ, both word costs are at most b − 2ε. The existing auto_nonneg also gives b − ε > 0. These inequalities discharge the cost and positivity premises of actual_errors; no two-sided cost bound is assumed as an extra hypothesis.

The supplier actual_pair constructs the legal, finite-tail source pair for this target model and execution. FixedTailClosedBudget.prefix_scalar, literal_tail_spec and the original_t_shift and window_shift identities identify the complete original sources at every natural position. More explicitly, the literal observedPrefix maps to the fixed sourcePrefix, while the literal tailPrefix maps to tailWord followed by nullLabel; this added null label fixes the zero address. At position p the mapped literal source label equals the window of the same legal source, and the literal suffix coordinate equals kappa of its p-fold originalT shift, equivalently its bit shift by 3p. The literal history maps exactly to colors, including the stem and optional anchor, and its length equals the observed-prefix length. Literal clipping agrees with the clipping in actual_errors, and every boundary ownership readout agrees with the prescribed color on each open cell interior. Thus the transport concerns the original literal sources and their successive suffixes.

For each literal side, actual_errors supplies the finite error list for those history observations. Extend it by zero to an error function err on all natural positions. It satisfies |err p| < b − ε for every p; observe o (coordinate (sourcePrefix side t execution) p) (err p) equals history t execution at every history index; and err p = 0 whenever history.length ≤ p. For every natural q, the observation at observedPrefix.length + q, with that zero error, equals observe o (coordinate (tailPrefix side) q) 0 exactly. These are all four clauses of the original ActualPairSupply t o (b − ε) strict execution, including its zero-error future. They also cover the empty execution without deleting its stem or anchor.

Memory and bilateral blocks retain their original meanings. A second application of common_memory_cutoff, now with lower index K, height H and tolerance χᴷ⁻¹γ, gives n ≥ K with Hρⁿ < χᴷ⁻¹γ. For every choice function choices : ℤ → V, take precisely W j = executionWord (R :: choices j), where each return contributes r copies of CuLetter.c followed by m copies of CuLetter.u in execution order. These are execution letters, distinct from the literal source labels. Use the original zero-anchored signed cumulative cuts: c(0) = 0, c(j) is the sum of block lengths from 0 to j − 1 for j > 0, and c(j) is minus the sum from j to −1 for j < 0. Positive block lengths give c(j + 1) = c(j) + length(W j) and StrictMono c, including the seam from −1 to 0. Monotone.pairwise_disjoint_on_Ico_succ makes (j,k) ↦ c(j) + k injective for k : Fin (W j).length. Function.Injective.extend_apply then yields a total ω : ℤ → CuLetter with ω(c(j) + k) = (W j)[k] for every block and offset. This is exact realization at the prescribed bilateral cuts. It does not assert an integer-indexed choice exists when V is empty.

Together these applications give the complete uniform-reset construction: one reset, the exact source-dependent δ, γ and ε, the strengthened guard for every target and finite word list, full original ActualPairSupply, the memory inequality and exact bilateral block realization. The original upper-budget and N > 0 hypotheses remain in that statement, although this sufficient construction does not use them. The application supplies no positive dictionary count, injection of original sources, all-even counting or rate bound, decoder storage bound or optimality result. The cutoff and block realization alone do not assert the stronger bilateral auxiliary-language or lower-memory-language membership conclusions. This exposition adds no mathematical content or completion claim for the full original Fibonacci theory.

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.A_nonneg`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.closedRun`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.common_memory_cutoff`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_bounds`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.execute_floor`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.finite_reset_weak_state`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.initial`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.parameters`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_actual_family`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.reset_lifts`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_bounds`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.run_closed`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.step`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_append`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_gain`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookFinite.weak_run`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookGrowth](ResetCodebookGrowth.md)
