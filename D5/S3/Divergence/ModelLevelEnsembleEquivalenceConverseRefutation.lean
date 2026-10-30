/- GID: D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.claim; result=D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result; claim=D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.claim
   digest: A scalar dyadic statistic separates model and measure ensemble equivalence. -/

/-
admission_basis: open-problem-resolution (#18580; Refuted).
escape_witness: none.
The source exponential formula is inlined in the public definitions. The private
expectation composes meanEnergy with gibbs, and the dyadic statistic composes
meanEnergy with its fixed bounded weights. Its fractional part uses Nat.ofDigits;
occupationCount supplies its integer part. The public NML laws are the source
likelihood-over-sum formulas. Consumed private bridges identify them with
DomiRankEntropyRefutation.normalized on their nonnegative likelihoods.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
Direct frozen declaration identities:
  D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.clipped
    statement_id sha256:b2ffdfc200a436c0a1a4cbc67a06eacf0e6d019ce38e49368431f82129c4c525
  D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.normalized
    statement_id sha256:827ae10dc47bf8d9de81c4ebb7189aa91a1ee4d77236f049729357214a06c556
  D5/S3/Divergence/ClassicalDPI.klDivergence
    statement_id sha256:5439abc1162340dc8a960e26ac9ec0e06ba733ba3a848aa4ce21aefc7592d01e
  D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg
    statement_id sha256:2811f2905b53f8e74c7c7d666dc0dbc01e24ea1c0f503af4120dd64befc22259
  D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount.eq_1
    statement_id sha256:c2101561360aaaac78a2095e438a28ac1b48daea6381a5a03ac46a2cd90471e3
  D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.gibbs
    statement_id sha256:2337c9a89c0136061cb41f55918b4b0d339fd0e28802777fbfe13e1b0520c806
  D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.meanEnergy
    statement_id sha256:f56ad4bf25512379049f50a967c0cfb243b169ffc3e0f63822c8135d0dbd75ff
  D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.meanEnergy.eq_1
    statement_id sha256:90bd8a24c7499c850ab673f8a5440b82559a5d53e862bb2d9c5f3d30495bc069
Declaration classification (consumers are within this module):
  omega: proof_shape: bind-only; consumers: dyadic_uniform, lMic, measureDiv_eq_log, measure_first_col, modelDiv_bounds, nmlMic_uniform, omega_first_col, omega_pos, pMic, pMic_sum; escape_witness: none.
  pMic: proof_shape: bind-only; consumers: measureDiv, measureDiv_eq_log, pMic_sum; escape_witness: none.
  IsMatched: proof_shape: bind-only; consumers: claim, dyadic_exists_match, isMatched_first_col, matchedTheta, matchedTheta_eventually; escape_witness: none.
  measureDiv: proof_shape: bind-only; consumers: checker_measure_lower, checker_scaled_lower, claim, measureDiv_eq_log, measure_first_col, result; escape_witness: none.
  lMic: proof_shape: bind-only; consumers: nmlMic, nmlMic_uniform; escape_witness: none.
  lCan: proof_shape: bind-only; consumers: dyadic_model_bounds, lCan_pos, modelDiv_bounds, nmlCan, nmlCan_pos, nmlCan_sum, pCan_le_lCan; escape_witness: none.
  nmlMic: proof_shape: bind-only; consumers: modelDiv, modelDiv_bounds, nmlMic_uniform; escape_witness: none.
  nmlCan: proof_shape: bind-only; consumers: modelDiv, modelDiv_bounds, nmlCan_pos, nmlCan_sum; escape_witness: none.
  nmlMic_eq_normalized: proof_shape: bind-only; consumers: nmlMic_uniform; escape_witness: none.
  nmlCan_eq_normalized: proof_shape: bind-only; consumers: nmlCan_pos, nmlCan_sum, modelDiv_bounds; escape_witness: none.
  modelDiv: proof_shape: bind-only; consumers: claim, dyadic_model_bounds, dyadic_model_tendsto, modelDiv_bounds; escape_witness: none.
  claim: proof_shape: bind-only; consumers: result; escape_witness: none.
  canonical_eq_gibbs: proof_shape: bind-only; consumers: mean_eq_sum, q_sum; escape_witness: none.
  q_pos: proof_shape: bind-only; consumers: checker_measure_lower, lCan_pos, nmlCan_pos, pCan_le_one, q_rank_left, q_rank_right; escape_witness: none.
  q_sum: proof_shape: bind-only; consumers: mean_sub_min_bounds, nmlCan_sum, pCan_le_one, q_rank_left, q_rank_right; escape_witness: none.
  pCan_le_one: proof_shape: bind-only; consumers: pCan_bdd; escape_witness: none.
  pCan_zero: proof_shape: bind-only; consumers: modelDiv_bounds; escape_witness: none.
  pCan_bdd: proof_shape: bind-only; consumers: pCan_le_lCan; escape_witness: none.
  pCan_le_lCan: proof_shape: bind-only; consumers: lCan_pos, modelDiv_bounds; escape_witness: none.
  lCan_pos: proof_shape: bind-only; consumers: dyadic_model_bounds, modelDiv_bounds, nmlCan_pos, nmlCan_sum; escape_witness: none.
  fraction: proof_shape: bind-only; consumers: dyadic_exists_match, energy_decomp, energy_floor, energy_injective, energy_lt_of_hamming_lt, fraction_bounds, fraction_formula, fraction_injective, fraction_succ; escape_witness: none.
  energy: proof_shape: bind-only; consumers: checker_measure_lower, dyadicStat, dyadicStat_succ, dyadic_exists_match, dyadic_uniform, energy_decomp, energy_floor, energy_formula, energy_injective, energy_le_top, energy_lt_of_hamming_lt, energy_zero, isMatched_first_col, measure_first_col, q_checker_even; escape_witness: none.
  fraction_succ: proof_shape: bind-only; consumers: fraction_bounds, fraction_formula, fraction_injective; escape_witness: none.
  fraction_formula: proof_shape: bind-only; consumers: energy_decomp; escape_witness: none.
  fraction_bounds: proof_shape: bind-only; consumers: dyadic_exists_match, energy_floor, energy_lt_of_hamming_lt, fraction_injective; escape_witness: none.
  fraction_injective: proof_shape: content; consumers: energy_injective; escape_witness: none.
  energy_formula: proof_shape: bind-only; consumers: energy_decomp, energy_le_top, energy_zero, q_checker_even; escape_witness: none.
  energy_decomp: proof_shape: bind-only; consumers: dyadic_exists_match, energy_floor, energy_injective, energy_lt_of_hamming_lt; escape_witness: none.
  energy_floor: proof_shape: bind-only; consumers: energy_injective; escape_witness: none.
  energy_injective: proof_shape: content; consumers: dyadic_uniform; escape_witness: none.
  energy_lt_of_hamming_lt: proof_shape: bind-only; consumers: dyadic_exists_match; escape_witness: none.
  splitMat: proof_shape: bind-only; consumers: omega_first_col, sum_first_col; escape_witness: none.
  sum_first_col: proof_shape: bind-only; consumers: isMatched_first_col, pCan_first_col; escape_witness: none.
  omega_first_col: proof_shape: bind-only; consumers: dyadic_uniform; escape_witness: none.
  pCan_first_col: proof_shape: bind-only; consumers: isMatched_first_col, measure_first_col; escape_witness: none.
  omega_pos: proof_shape: bind-only; consumers: pMic_sum; escape_witness: none.
  pMic_sum: proof_shape: bind-only; consumers: measureDiv_eq_log; escape_witness: none.
  measureDiv_eq_log: proof_shape: bind-only; consumers: measure_first_col; escape_witness: none.
  q_antitone: proof_shape: bind-only; consumers: q_rank_left; escape_witness: none.
  q_monotone: proof_shape: bind-only; consumers: q_rank_right; escape_witness: none.
  q_rank_left: proof_shape: bind-only; consumers: w_rank; escape_witness: none.
  q_rank_right: proof_shape: bind-only; consumers: w_rank; escape_witness: none.
  w_rank: proof_shape: bind-only; consumers: w_sum_le; escape_witness: none.
  harmonic_fin: proof_shape: bind-only; consumers: harmonic_fin_rev, w_sum_le; escape_witness: none.
  harmonic_fin_rev: proof_shape: bind-only; consumers: w_sum_le; escape_witness: none.
  w_sum_le: proof_shape: bind-only; consumers: w_sum_any; escape_witness: none.
  nmlCan_pos: proof_shape: bind-only; consumers: modelDiv_bounds; escape_witness: none.
  nmlCan_sum: proof_shape: bind-only; consumers: modelDiv_bounds; escape_witness: none.
  nmlMic_uniform: proof_shape: bind-only; consumers: modelDiv_bounds; escape_witness: none.
  modelDiv_bounds: proof_shape: bind-only; consumers: dyadic_model_bounds; escape_witness: none.
  w_equiv: proof_shape: bind-only; consumers: w_sum_any; escape_witness: none.
  w_sum_any: proof_shape: content; consumers: dyadic_model_bounds; escape_witness: none.
  mean: proof_shape: bind-only; consumers: dyadic_exists_match, exists_matched_mean, isMatched_first_col, mean_continuous, mean_eq_sum, mean_neg, mean_sub_min_bounds, mean_tendsto_max, mean_tendsto_min; escape_witness: none.
  mean_eq_sum: proof_shape: bind-only; consumers: isMatched_first_col, mean_continuous, mean_neg, mean_sub_min_bounds; escape_witness: none.
  q_shift: proof_shape: bind-only; consumers: mean_sub_min_bounds; escape_witness: none.
  mean_continuous: proof_shape: bind-only; consumers: exists_matched_mean; escape_witness: none.
  mean_sub_min_bounds: proof_shape: bind-only; consumers: mean_tendsto_min; escape_witness: none.
  mean_tendsto_min: proof_shape: content; consumers: exists_matched_mean, mean_tendsto_max; escape_witness: none.
  mean_neg: proof_shape: bind-only; consumers: mean_tendsto_max; escape_witness: none.
  mean_tendsto_max: proof_shape: content; consumers: exists_matched_mean; escape_witness: none.
  exists_matched_mean: proof_shape: content; consumers: dyadic_exists_match; escape_witness: none.
  exp_linearEnergy: proof_shape: bind-only; consumers: partition_product, q_product; escape_witness: none.
  partition_product: proof_shape: bind-only; consumers: q_product; escape_witness: none.
  q_product: proof_shape: bind-only; consumers: q_hamming_neg, q_hamming_pos; escape_witness: none.
  q_bit_bound_pos: proof_shape: bind-only; consumers: q_hamming_pos; escape_witness: none.
  q_bit_bound_neg: proof_shape: bind-only; consumers: q_hamming_neg; escape_witness: none.
  q_hamming_pos: proof_shape: bind-only; consumers: q_checker_even; escape_witness: none.
  q_hamming_neg: proof_shape: bind-only; consumers: q_checker_even; escape_witness: none.
  checker: proof_shape: bind-only; consumers: checkerMat_first, checker_measure_lower, dyadic_exists_match, hamming_checker, q_checker_even; escape_witness: none.
  hamming_checker: proof_shape: bind-only; consumers: dyadic_exists_match, q_checker_even; escape_witness: none.
  hamming_compl: proof_shape: bind-only; consumers: q_checker_even; escape_witness: none.
  q_checker_even: proof_shape: bind-only; consumers: checker_measure_lower; escape_witness: none.
  log_polynomial_div_tendsto: proof_shape: bind-only; consumers: dyadic_model_tendsto; escape_witness: none.
  even_tendsto: proof_shape: bind-only; consumers: result; escape_witness: none.
  dyadicStat: proof_shape: bind-only; consumers: checker_measure_lower, checker_scaled_lower, dyadicStat_succ, dyadic_exists_match, dyadic_model_bounds, dyadic_model_tendsto, dyadic_uniform, isMatched_first_col, matchedTheta, matchedTheta_eventually, measure_first_col, result; escape_witness: none.
  checkerMat: proof_shape: bind-only; consumers: checkerMat_first, checker_measure_lower, checker_scaled_lower, dyadic_exists_match, matchedTheta, matchedTheta_eventually, result; escape_witness: none.
  dyadicStat_succ: proof_shape: bind-only; consumers: dyadic_uniform, isMatched_first_col, measure_first_col; escape_witness: none.
  checkerMat_first: proof_shape: bind-only; consumers: checker_measure_lower, dyadic_exists_match; escape_witness: none.
  dyadic_uniform: proof_shape: content; consumers: dyadic_model_bounds, measure_first_col; escape_witness: none.
  cardMat_log: proof_shape: bind-only; consumers: dyadic_model_bounds; escape_witness: none.
  dyadic_model_bounds: proof_shape: content; consumers: dyadic_model_tendsto; escape_witness: none.
  dyadic_model_tendsto: proof_shape: content; consumers: result; escape_witness: none.
  measure_first_col: proof_shape: content; consumers: checker_measure_lower; escape_witness: none.
  energy_zero: proof_shape: bind-only; consumers: dyadic_exists_match; escape_witness: none.
  energy_le_top: proof_shape: bind-only; consumers: dyadic_exists_match; escape_witness: none.
  isMatched_first_col: proof_shape: bind-only; consumers: dyadic_exists_match; escape_witness: none.
  dyadic_exists_match: proof_shape: content; consumers: matchedTheta, matchedTheta_eventually; escape_witness: none.
  matchedTheta: proof_shape: bind-only; consumers: checker_scaled_lower, matchedTheta_eventually, result; escape_witness: none.
  matchedTheta_eventually: proof_shape: content; consumers: result; escape_witness: none.
  checker_measure_lower: proof_shape: content; consumers: checker_scaled_lower; escape_witness: none.
  checker_scaled_lower: proof_shape: content; consumers: result; escape_witness: none.
  result: proof_shape: content; consumers: none (settling result); escape_witness: none.
-/

import D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Divergence.ClassicalDPI
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation

set_option autoImplicit false

namespace D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation

open D5.S3.Divergence.ClassicalDPI (klDivergence)
open Filter Topology
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

variable {n : ℕ}

/-- `Ω(c)`, the number of configurations with `c(G) = c` (eq. (15)). -/
noncomputable def omega (stat : (Fin n → Fin n → Bool) → ℝ) (c : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun G : (Fin n → Fin n → Bool) => stat G = c).card

/-- The microcanonical law `P_mic(G; c)` (eq. (16)). -/
noncomputable def pMic (stat : (Fin n → Fin n → Bool) → ℝ) (c : ℝ) (G : (Fin n → Fin n → Bool)) : ℝ := by
  classical
  exact if stat G = c then 1 / (omega stat c : ℝ) else 0

/-- The maximum-likelihood condition `⟨c⟩_θ = c(G)` (eq. (21)). -/
def IsMatched (stat : (Fin n → Fin n → Bool) → ℝ) (θ : ℝ) (G : (Fin n → Fin n → Bool)) : Prop :=
  ∑ G' : (Fin n → Fin n → Bool), (Real.exp (-θ * stat G') / ∑ H, Real.exp (-θ * stat H)) * stat G' = stat G

/-- The measure-level divergence `D_KL(c*) = S(P_mic ‖ P_can)|_{c*, θ*}` at the observed matrix `G*`,
for a parameter `θ*` (eq. (22); `θ* = θ̂(c*)` when `IsMatched stat θ* G*`). -/
noncomputable def measureDiv (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) (θ : ℝ) : ℝ :=
  klDivergence (pMic stat (stat G)) (fun H => Real.exp (-θ * stat H) / ∑ K, Real.exp (-θ * stat K))

/-- The maximized microcanonical likelihood `L_mic(G) = 1 / Ω(c(G))` (eq. (17)). -/
noncomputable def lMic (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : ℝ :=
  1 / (omega stat (stat G) : ℝ)

/-- The maximized canonical likelihood `L_can(G) = sup_θ P_can(G; θ)`. -/
noncomputable def lCan (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : ℝ :=
  ⨆ θ : ℝ, Real.exp (-θ * stat G) / ∑ H, Real.exp (-θ * stat H)

/-- The NML distribution of the microcanonical model, `L_mic(G) / Σ_{G'} L_mic(G')`. -/
noncomputable def nmlMic (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : ℝ :=
  lMic stat G / ∑ H : (Fin n → Fin n → Bool), lMic stat H

/-- The NML distribution of the canonical model, `L_can(G) / Σ_{G'} L_can(G')`. -/
noncomputable def nmlCan (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : ℝ :=
  lCan stat G / ∑ H : (Fin n → Fin n → Bool), lCan stat H

/-- The model-level divergence `D_KL^NML = S(P̄_mic^NML ‖ P̄_can^NML)` (eq. (69)). -/
noncomputable def modelDiv (stat : (Fin n → Fin n → Bool) → ℝ) : ℝ :=
  klDivergence (nmlMic stat) (nmlCan stat)

/-- The reverse of implication (71), for scalar statistics on binary `n × n` matrices: model-level
equivalence (eq. (70)) implies measure-level equivalence (eq. (35)) along every sequence of observed
matrices that eventually admits the maximum-likelihood parameter of eq. (21). -/
def claim : Prop :=
  ∀ stat : ∀ n : ℕ, (Fin n → Fin n → Bool) → ℝ,
    Tendsto (fun n : ℕ => modelDiv (stat n) / n) atTop (𝓝 0) →
      ∀ (obs : ∀ n : ℕ, (Fin n → Fin n → Bool)) (θ : ℕ → ℝ),
        (∀ᶠ n in atTop, IsMatched (stat n) (θ n) (obs n)) →
          Tendsto (fun n : ℕ => measureDiv (stat n) (obs n) (θ n) / n) atTop (𝓝 0)

variable {n : ℕ}

private lemma canonical_eq_gibbs {X : Type*} [Fintype X]
    (e : X → ℝ) (θ : ℝ) (x : X) :
    Real.exp (-θ * e x) / (∑ y, Real.exp (-θ * e y)) =
      D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs
        (fun j => e ((Fintype.equivFin X).symm j)) θ (Fintype.equivFin X x) := by
  unfold D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs
  simp only [Equiv.symm_apply_apply]
  rw [(Fintype.equivFin X).symm.sum_comp (fun y => Real.exp (-θ * e y))]

private lemma q_pos {X : Type*} [Fintype X] [Nonempty X] (e : X → ℝ) (θ : ℝ) (x : X) : 0 < (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ x := by
  exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
private lemma q_sum {X : Type*} [Fintype X] [Nonempty X] (e : X → ℝ) (θ : ℝ) : ∑ x, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ x = 1 := by
  have : Nonempty (Fin (Fintype.card X)) := inferInstance
  dsimp only
  simp_rw [canonical_eq_gibbs]
  rw [← (Fintype.equivFin X).symm.sum_comp]
  unfold D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs
  simp only [Equiv.apply_symm_apply]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun (j : Fin (Fintype.card X)) _ =>
    Real.exp_pos (-θ * e ((Fintype.equivFin X).symm j))) Finset.univ_nonempty).ne'
private lemma pCan_le_one (stat : (Fin n → Fin n → Bool) → ℝ) (θ : ℝ) (G : (Fin n → Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ G ≤ 1 := by
  rw [← q_sum stat θ]
  exact Finset.single_le_sum (fun H _ => (q_pos stat θ H).le) (Finset.mem_univ G)

private lemma pCan_zero (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat 0 G = 1 / (Fintype.card ((Fin n → Fin n → Bool)) : ℝ) := by
  simp []

private lemma pCan_bdd (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) :
    BddAbove (Set.range (fun θ => (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ G)) := by
  exact ⟨1, by rintro _ ⟨θ,rfl⟩; exact pCan_le_one stat θ G⟩

private lemma pCan_le_lCan (stat : (Fin n → Fin n → Bool) → ℝ) (θ : ℝ) (G : (Fin n → Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ G ≤ lCan stat G := by
  exact le_ciSup (pCan_bdd stat G) θ

private lemma lCan_pos (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) :
    0 < lCan stat G := by
  exact lt_of_lt_of_le (q_pos stat 0 G) (pCan_le_lCan stat 0 G)

private noncomputable def fraction {n : ℕ} (x : (Fin n → Bool)) : ℝ :=
  Nat.ofDigits (1 / 2 : ℝ) (List.ofFn fun i => (x i).toNat) / 2
private noncomputable def energy {n : ℕ} (x : (Fin n → Bool)) : ℝ :=
  D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy
    (fun i => 1 + (1 / 2 : ℝ) ^ (i.val + 1)) (fun i => (x i).toNat)

private lemma fraction_succ {n : ℕ} (x : (Fin (n + 1) → Bool)) :
    fraction x = (x 0).toNat / 2 + fraction (fun i => x i.succ) / 2 := by
  simp only [fraction, List.ofFn_succ, Nat.ofDigits]
  ring

private lemma fraction_formula {n : ℕ} (x : Fin n → Bool) :
    fraction x = ∑ i, (1 / 2 : ℝ) ^ (i.val + 1) * (x i).toNat := by
  induction n with
  | zero => simp [fraction, Nat.ofDigits]
  | succ n ih =>
    rw [fraction_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
    rw [ih, Finset.sum_div]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      simp only [pow_succ]
      ring

private lemma fraction_bounds {n : ℕ} (x : (Fin n → Bool)) : 0 ≤ fraction x ∧ fraction x < 1 := by
  induction n with
  | zero => simp [fraction, Nat.ofDigits]
  | succ n ih =>
    rw [fraction_succ]
    have ht := ih (fun i => x i.succ)
    cases x 0 <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero,
      Nat.cast_one, zero_div, zero_add] <;> constructor <;> linarith

private lemma fraction_injective (n : ℕ) : Function.Injective (@fraction n) := by
  induction n with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro x y h
    have hx := fraction_bounds (fun i => x i.succ)
    have hy := fraction_bounds (fun i => y i.succ)
    rw [fraction_succ, fraction_succ] at h
    have head : x 0 = y 0 := by
      cases hx0 : x 0 <;> cases hy0 : y 0 <;>
        simp only [hx0, hy0, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero,
          Nat.cast_one, zero_div, zero_add] at h ⊢ <;> first | rfl | exfalso; linarith
    have tail : (fun i : Fin n => x i.succ) = (fun i => y i.succ) := by
      apply ih
      rw [head] at h
      linarith
    funext i
    exact Fin.cases head (fun i => congrFun tail i) i

private lemma energy_formula {n : ℕ} (x : (Fin n → Bool)) :
    energy x = ∑ i, (1 + (1 / 2 : ℝ) ^ (i.val + 1)) * (x i).toNat := by
  rfl

private lemma energy_decomp {n : ℕ} (x : Fin n → Bool) :
    energy x = (occupationCount x : ℝ) + fraction x := by
  rw [energy_formula, fraction_formula]
  simp [occupationCount, add_mul, Finset.sum_add_distrib]

private lemma energy_floor {n : ℕ} (x : (Fin n → Bool)) : ⌊energy x⌋₊ = occupationCount x := by
  have hf := fraction_bounds x
  apply (Nat.floor_eq_iff (by rw [energy_decomp]; exact add_nonneg (Nat.cast_nonneg _) hf.1)).2
  rw [energy_decomp]
  exact ⟨by linarith, by linarith⟩

private lemma energy_injective (n : ℕ) : Function.Injective (@energy n) := by
  intro x y h
  have hw : occupationCount x = occupationCount y := by rw [← energy_floor x, h, energy_floor y]
  apply fraction_injective n
  rw [energy_decomp, energy_decomp] at h
  rw [hw] at h
  linarith

private lemma energy_lt_of_hamming_lt {n : ℕ} (x y : (Fin n → Bool)) (h : occupationCount x < occupationCount y) :
    energy x < energy y := by
  have hx := fraction_bounds x
  have hy := fraction_bounds y
  have hn : (occupationCount x : ℝ) + 1 ≤ occupationCount y := by exact_mod_cast (Nat.succ_le_iff.mpr h)
  rw [energy_decomp, energy_decomp]
  linarith

variable {n : ℕ}

private def splitMat (n : ℕ) :
    (Fin (n + 1) → Fin (n + 1) → Bool) ≃
      (Fin (n + 1) → Bool) × (Fin (n + 1) → Fin n → Bool) :=
  (Equiv.piCongrRight (fun _ => (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

private lemma sum_first_col (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ G : (Fin (n + 1) → Fin (n + 1) → Bool), f (fun i => G i 0)) =
      (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ) * ∑ x : (Fin (n + 1) → Bool), f x := by
  rw [← (splitMat n).symm.sum_comp]
  simp [Fintype.sum_prod_type, splitMat, Finset.mul_sum, mul_comm]

private lemma omega_first_col (n : ℕ) (e : (Fin (n + 1) → Bool) → ℝ) (he : Function.Injective e)
    (G : (Fin (n + 1) → Fin (n + 1) → Bool)) :
    omega (fun H => e (fun i => H i 0)) (e (fun i => G i 0)) = Fintype.card ((Fin (n + 1) → Fin n → Bool)) := by
  classical
  unfold omega
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  change (∑ H : (Fin (n + 1) → Fin (n + 1) → Bool), if e (fun i => H i 0) = e (fun i => G i 0) then 1 else 0) = _
  rw [← (splitMat n).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ x : (Fin (n+1) → Bool), ∑ _y : (Fin (n + 1) → Fin n → Bool), if e x = e (fun i => G i 0) then (1 : ℕ) else 0) = _
  simp [he.eq_iff]

private lemma pCan_first_col (n : ℕ) (e : (Fin (n + 1) → Bool) → ℝ) (θ : ℝ) (G : (Fin (n + 1) → Fin (n + 1) → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun H => e (fun i => H i 0)) θ G =
      (Real.exp (-θ * e (fun i => G i 0)) / ∑ x : (Fin (n + 1) → Bool), Real.exp (-θ * e x)) /
        (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ) := by
  dsimp only
  rw [sum_first_col n (fun x => Real.exp (-θ * e x))]
  ring

private lemma omega_pos (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : 0 < omega stat (stat G) := by
  classical
  exact Finset.card_pos.mpr ⟨G, by simp⟩

private lemma pMic_sum (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) :
    ∑ H : (Fin n → Fin n → Bool), pMic stat (stat G) H = 1 := by
  classical
  simp only [pMic, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (omega_pos stat G).ne')

private lemma measureDiv_eq_log (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) (θ : ℝ) :
    measureDiv stat G θ = Real.log ((1 / (omega stat (stat G) : ℝ)) / (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ G) := by
  classical
  unfold measureDiv D5.S3.Divergence.ClassicalDPI.klDivergence
  calc
    (∑ H : (Fin n → Fin n → Bool), pMic stat (stat G) H * Real.log (pMic stat (stat G) H / (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ H)) =
      ∑ H : (Fin n → Fin n → Bool), pMic stat (stat G) H * Real.log ((1 / (omega stat (stat G) : ℝ)) / (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) stat θ G) := by
      apply Finset.sum_congr rfl
      intro H _
      by_cases h : stat H = stat G
      · simp [pMic, h]
      · simp [pMic, h]
    _ = _ := by rw [← Finset.sum_mul, pMic_sum, one_mul]


variable {X : Type*} [Fintype X] [Nonempty X]

private lemma q_antitone {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) (θ : ℝ) (hθ : 0 ≤ θ) :
    Antitone ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
  apply Real.exp_le_exp.mpr
  have := he hij
  nlinarith
private lemma q_monotone {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) (θ : ℝ) (hθ : θ ≤ 0) :
    Monotone ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
  apply Real.exp_le_exp.mpr
  have := he hij
  nlinarith

private lemma q_rank_left {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) (θ : ℝ) (hθ : 0 ≤ θ)
    (k : Fin N) : (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k ≤ 1 / ((k.val : ℝ) + 1) := by
  classical
  have : Nonempty (Fin N) := ⟨k⟩
  have hs : ((k.val : ℝ) + 1) * (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k ≤ 1 := by
    calc
      ((k.val : ℝ) + 1) * (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k = ∑ j ∈ Finset.Iic k, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k := by simp
      _ ≤ ∑ j ∈ Finset.Iic k, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ j := by
        exact Finset.sum_le_sum (fun j hj => q_antitone e he θ hθ (Finset.mem_Iic.mp hj))
      _ ≤ ∑ j, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => (q_pos e θ j).le)
      _ = 1 := q_sum e θ
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (k.val : ℝ) + 1)).2
  nlinarith

private lemma q_rank_right {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) (θ : ℝ) (hθ : θ ≤ 0)
    (k : Fin N) : (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k ≤ 1 / ((N - k.val : ℕ) : ℝ) := by
  classical
  have : Nonempty (Fin N) := ⟨k⟩
  have hs : ((N - k.val : ℕ) : ℝ) * (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k ≤ 1 := by
    calc
      ((N - k.val : ℕ) : ℝ) * (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k = ∑ j ∈ Finset.Ici k, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ k := by simp
      _ ≤ ∑ j ∈ Finset.Ici k, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ j := by
        exact Finset.sum_le_sum (fun j hj => q_monotone e he θ hθ (Finset.mem_Ici.mp hj))
      _ ≤ ∑ j, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => (q_pos e θ j).le)
      _ = 1 := q_sum e θ
  apply (le_div_iff₀ (show (0 : ℝ) < (N - k.val : ℕ) by exact_mod_cast Nat.sub_pos_of_lt k.isLt)).2
  nlinarith

private lemma w_rank {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) (k : Fin N) :
    (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e k ≤ 1 / ((k.val : ℝ) + 1) + 1 / ((N - k.val : ℕ) : ℝ) := by
  apply ciSup_le
  intro θ
  rcases le_total 0 θ with hθ | hθ
  · exact (q_rank_left e he θ hθ k).trans (le_add_of_nonneg_right (by positivity))
  · exact (q_rank_right e he θ hθ k).trans (le_add_of_nonneg_left (by positivity))

private lemma harmonic_fin (N : ℕ) :
    (∑ k : Fin N, 1 / ((k.val : ℝ) + 1)) = (harmonic N : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => 1 / ((k : ℝ) + 1)) N]
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one, one_div]

private lemma harmonic_fin_rev (N : ℕ) :
    (∑ k : Fin N, 1 / ((N - k.val : ℕ) : ℝ)) = (harmonic N : ℝ) := by
  rw [← harmonic_fin]
  rw [← Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N)]
  apply Finset.sum_congr rfl
  intro k _
  have hk : N - (Fin.rev k).val = k.val + 1 := by simp only [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, hk, Nat.cast_add, Nat.cast_one]

private lemma w_sum_le {N : ℕ} (e : Fin N → ℝ) (he : Monotone e) :
    ∑ k, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e k ≤ 2 * (1 + Real.log N) := by
  calc
    ∑ k, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e k ≤ ∑ k, (1 / ((k.val : ℝ) + 1) + 1 / ((N - k.val : ℕ) : ℝ)) :=
      Finset.sum_le_sum fun k _ => w_rank e he k
    _ = 2 * (harmonic N : ℝ) := by rw [Finset.sum_add_distrib, harmonic_fin, harmonic_fin_rev]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num)

variable {n : ℕ}

private lemma nmlMic_eq_normalized (stat : (Fin n → Fin n → Bool) → ℝ)
    (G : (Fin n → Fin n → Bool)) :
    nmlMic stat G =
      D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized (lMic stat) G := by
  simp only [nmlMic, D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped,
    max_eq_left (show (0 : ℝ) ≤ lMic stat _ from one_div_nonneg.mpr (Nat.cast_nonneg _))]

private lemma nmlCan_eq_normalized (stat : (Fin n → Fin n → Bool) → ℝ)
    (G : (Fin n → Fin n → Bool)) :
    nmlCan stat G =
      D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized (lCan stat) G := by
  simp only [nmlCan, D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped,
    max_eq_left (lCan_pos stat _).le]

private lemma nmlCan_pos (stat : (Fin n → Fin n → Bool) → ℝ) (G : (Fin n → Fin n → Bool)) : 0 < nmlCan stat G := by
  rw [nmlCan_eq_normalized]
  have h := q_pos (fun H : Fin n → Fin n → Bool => -Real.log (lCan stat H)) 1 G
  dsimp only at h
  simp only [neg_mul, one_mul, neg_neg] at h
  simp_rw [Real.exp_log (lCan_pos stat _)] at h
  simpa only [D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped, max_eq_left (lCan_pos stat _).le] using h

private lemma nmlCan_sum (stat : (Fin n → Fin n → Bool) → ℝ) : ∑ G : (Fin n → Fin n → Bool), nmlCan stat G = 1 := by
  simp_rw [nmlCan_eq_normalized]
  have h := q_sum (fun H : Fin n → Fin n → Bool => -Real.log (lCan stat H)) 1
  dsimp only at h
  simp only [neg_mul, one_mul, neg_neg] at h
  simp_rw [Real.exp_log (lCan_pos stat _)] at h
  simpa only [D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped, max_eq_left (lCan_pos stat _).le] using h

private lemma nmlMic_uniform (stat : (Fin n → Fin n → Bool) → ℝ) (r : ℕ) (hr : 0 < r)
    (hom : ∀ G, omega stat (stat G) = r) (G : (Fin n → Fin n → Bool)) :
    nmlMic stat G = 1 / (Fintype.card ((Fin n → Fin n → Bool)) : ℝ) := by
  rw [nmlMic_eq_normalized]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : (Fintype.card ((Fin n → Fin n → Bool)) : ℝ) ≠ 0 := NeZero.ne _
  simp only [D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped, lMic, hom,
    max_eq_left (one_div_nonneg.mpr (show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r)),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma modelDiv_bounds (stat : (Fin n → Fin n → Bool) → ℝ) (r : ℕ) (hr : 0 < r)
    (hom : ∀ G, omega stat (stat G) = r) :
    0 ≤ modelDiv stat ∧ modelDiv stat ≤ Real.log (∑ G : (Fin n → Fin n → Bool), lCan stat G) := by
  classical
  let M : ℝ := Fintype.card ((Fin n → Fin n → Bool))
  let W : ℝ := ∑ G : (Fin n → Fin n → Bool), lCan stat G
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  have hW : 0 < W := Finset.sum_pos (fun G _ => lCan_pos stat G) Finset.univ_nonempty
  have hmic (G : (Fin n → Fin n → Bool)) : nmlMic stat G = 1 / M := nmlMic_uniform stat r hr hom G
  have hmicSum : ∑ G : (Fin n → Fin n → Bool), nmlMic stat G = 1 := by
    simp only [hmic, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hM.ne'
  constructor
  · exact D5.S3.Divergence.GrandmotherTheorem.kl_divergence_nonneg _ _
      ⟨fun G => by rw [hmic]; positivity, hmicSum⟩
      ⟨fun G => (nmlCan_pos stat G).le, nmlCan_sum stat⟩
      (fun G h => False.elim ((nmlCan_pos stat G).ne' h))
  · have hratio (G : (Fin n → Fin n → Bool)) : nmlMic stat G / nmlCan stat G ≤ W := by
      have hl : 1 / M ≤ lCan stat G := by
        rw [← pCan_zero stat G]
        exact pCan_le_lCan stat 0 G
      rw [hmic, nmlCan_eq_normalized]
      simp only [D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
        D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped, max_eq_left (lCan_pos stat _).le]
      change (1 / M) / (lCan stat G / W) ≤ W
      apply (div_le_iff₀ (div_pos (lCan_pos stat G) hW)).2
      have hid : W * (lCan stat G / W) = lCan stat G := by field_simp
      rwa [hid]
    unfold modelDiv D5.S3.Divergence.ClassicalDPI.klDivergence
    calc
      (∑ G : (Fin n → Fin n → Bool), nmlMic stat G * Real.log (nmlMic stat G / nmlCan stat G)) ≤
        ∑ G : (Fin n → Fin n → Bool), nmlMic stat G * Real.log W := by
        apply Finset.sum_le_sum
        intro G _
        apply mul_le_mul_of_nonneg_left _ (by rw [hmic]; positivity)
        apply Real.log_le_log (div_pos (by rw [hmic]; positivity) (nmlCan_pos stat G))
        exact hratio G
      _ = Real.log W := by rw [← Finset.sum_mul, hmicSum, one_mul]

private lemma w_equiv {X Y : Type*} [Fintype X] [Fintype Y] (v : X ≃ Y) (e : Y → ℝ) (x : X) :
    (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun x => e (v x)) x = (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e (v x) := by
  have h (θ : ℝ) : (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun x => e (v x)) θ x = (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ (v x) := by
    dsimp only
    rw [v.sum_comp (fun y => Real.exp (-θ * e y))]
  dsimp only
  simp_rw [h]

private lemma w_sum_any {X : Type*} [Fintype X] [Nonempty X] (e : X → ℝ) :
    ∑ x, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e x ≤ 2 * (1 + Real.log (Fintype.card X)) := by
  classical
  let idx := Fintype.equivFin X
  let key (x : X) : ℝ ×ₗ Fin (Fintype.card X) := toLex (e x, idx x)
  have hi : Function.Injective key := by
    intro x y h
    apply idx.injective
    exact congrArg (fun z => (ofLex z).2) h
  let : LinearOrder X := LinearOrder.lift' key hi
  let v := Fintype.orderIsoFinOfCardEq X rfl
  have hv : Monotone (fun k => e (v k)) := by
    intro i j hij
    exact Prod.Lex.monotone_fst _ _ (v.monotone hij)
  calc
    ∑ x, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e x = ∑ k, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e (v k) := v.toEquiv.sum_comp _ |>.symm
    _ = ∑ k, (fun (e : _ → ℝ) x => ⨆ θ : ℝ, Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun k => e (v k)) k := by
      apply Finset.sum_congr rfl
      intro k _
      exact (w_equiv v.toEquiv e k).symm
    _ ≤ _ := w_sum_le _ hv

open Filter Topology
variable {X : Type*} [Fintype X] [Nonempty X]

private noncomputable def mean (e : X → ℝ) (θ : ℝ) : ℝ :=
  D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy
    (D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs (fun i => e ((Fintype.equivFin X).symm i)) θ)
    (fun i => e ((Fintype.equivFin X).symm i))

omit [Nonempty X] in
private lemma mean_eq_sum (e : X → ℝ) (θ : ℝ) :
    mean e θ = ∑ x, (Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) * e x := by
  unfold mean D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy
  rw [← (Fintype.equivFin X).sum_comp (fun j =>
    D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs (fun i => e ((Fintype.equivFin X).symm i)) θ j *
      e ((Fintype.equivFin X).symm j))]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← canonical_eq_gibbs e θ]


omit [Nonempty X] in
private lemma q_shift (e : X → ℝ) (c θ : ℝ) (x : X) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ x = (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun y => e y - c) θ x := by
  have hh (y : X) : Real.exp (-θ * (e y - c)) = Real.exp (θ * c) * Real.exp (-θ * e y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  simp_rw [hh]
  rw [← Finset.mul_sum]
  exact (mul_div_mul_left _ _ (Real.exp_ne_zero _)).symm

private lemma mean_continuous (e : X → ℝ) : Continuous (mean e) := by
  classical
  change Continuous (fun θ : ℝ => mean e θ)
  simp only [mean_eq_sum]
  apply continuous_finsetSum
  intro x _
  apply Continuous.mul
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      exact (Finset.sum_pos (fun (_ : X) _ => Real.exp_pos (-θ * e _)) Finset.univ_nonempty).ne'
  · exact continuous_const

private lemma mean_sub_min_bounds (e : X → ℝ) (a : X) (ha : ∀ x, e a ≤ e x) (θ : ℝ) :
    0 ≤ mean e θ - e a ∧
      mean e θ - e a ≤ ∑ x, Real.exp (-θ * (e x - e a)) * (e x - e a) := by
  classical
  let d : X → ℝ := fun x => e x - e a
  have hd (x : X) : 0 ≤ d x := sub_nonneg.mpr (ha x)
  have hz : 1 ≤ ∑ x, Real.exp (-θ * d x) := by
    calc
      1 = Real.exp (-θ * d a) := by simp [d]
      _ ≤ ∑ x, Real.exp (-θ * d x) := Finset.single_le_sum
        (f := fun x => Real.exp (-θ * d x))
        (fun x _ => (Real.exp_pos _).le) (Finset.mem_univ a)
  have hn : 0 ≤ ∑ x, Real.exp (-θ * d x) * d x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (Real.exp_pos _).le (hd x)
  have hid : mean e θ - e a =
      (∑ x, Real.exp (-θ * d x) * d x) / (∑ x, Real.exp (-θ * d x)) := by
    calc
      mean e θ - e a = ∑ x, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) e θ x * (e x - e a) := by
        simp only [mean_eq_sum, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, q_sum, one_mul]
      _ = ∑ x, (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) d θ x * d x := by simp_rw [q_shift e (e a) θ]; rfl
      _ = _ := by simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hid]
  constructor
  · exact div_nonneg hn (by linarith)
  · exact div_le_self hn hz

private lemma mean_tendsto_min (e : X → ℝ) (a : X) (ha : ∀ x, e a ≤ e x) :
    Tendsto (mean e) atTop (𝓝 (e a)) := by
  have hterm (x : X) : Tendsto (fun θ : ℝ => Real.exp (-θ * (e x - e a)) * (e x - e a)) atTop (𝓝 0) := by
    rcases (ha x).eq_or_lt with hx | hx
    · simp [← hx]
    · have hd : 0 < e x - e a := sub_pos.mpr hx
      have ht : Tendsto (fun θ : ℝ => -θ * (e x - e a)) atTop atBot := by
        have h := tendsto_id.atTop_mul_const hd
        simpa only [Function.comp_def, id_eq, neg_mul] using tendsto_neg_atTop_atBot.comp h
      simpa using (Real.tendsto_exp_atBot.comp ht).mul_const (e x - e a)
  have hnum : Tendsto (fun θ : ℝ => ∑ x, Real.exp (-θ * (e x - e a)) * (e x - e a)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun x _ => hterm x)
  have hs : Tendsto (fun θ : ℝ => mean e θ - e a) atTop (𝓝 0) :=
    squeeze_zero (fun θ => (mean_sub_min_bounds e a ha θ).1)
      (fun θ => (mean_sub_min_bounds e a ha θ).2) hnum
  simpa using hs.add_const (e a)

omit [Nonempty X] in
private lemma mean_neg (e : X → ℝ) (θ : ℝ) : mean (fun x => -e x) (-θ) = -mean e θ := by
  simp [mean_eq_sum, ← Finset.sum_neg_distrib]

private lemma mean_tendsto_max (e : X → ℝ) (b : X) (hb : ∀ x, e x ≤ e b) :
    Tendsto (mean e) atBot (𝓝 (e b)) := by
  have h := mean_tendsto_min (fun x => -e x) b (fun x => neg_le_neg (hb x))
  have hn := (h.comp tendsto_neg_atBot_atTop).neg
  convert hn using 1
  · funext θ
    change mean e θ = -mean (fun x => -e x) (-θ)
    rw [mean_neg, neg_neg]
  · simp

private lemma exists_matched_mean (e : X → ℝ) (a b : X) (ha : ∀ x, e a ≤ e x)
    (hb : ∀ x, e x ≤ e b) (c : ℝ) (hc : e a < c ∧ c < e b) :
    ∃ θ : ℝ, mean e θ = c := by
  have hlo : ∀ᶠ θ : ℝ in atTop, mean e θ ≤ c :=
    (mean_tendsto_min e a ha).eventually (eventually_le_nhds hc.1)
  have hhi : ∀ᶠ θ : ℝ in atBot, c ≤ mean e θ :=
    (mean_tendsto_max e b hb).eventually (eventually_ge_nhds hc.2)
  obtain ⟨θ,hθ⟩ := intermediate_value_univ₂_eventually₂ (mean_continuous e)
    continuous_const hlo hhi
  exact ⟨θ,hθ⟩

variable {n : ℕ}
private lemma exp_linearEnergy (a : Fin n → ℝ) (θ : ℝ) (x : (Fin n → Bool)) :
    Real.exp (-θ * D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat)) = ∏ i, Real.exp (-θ * a i * (x i).toNat) := by
  rw [D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

private lemma partition_product (a : Fin n → ℝ) (θ : ℝ) :
    (∑ x : (Fin n → Bool), Real.exp (-θ * D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat))) = ∏ i, (1 + Real.exp (-θ * a i)) := by
  simp_rw [exp_linearEnergy]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => Real.exp (-θ * a i * b.toNat))]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

private lemma q_product (a : Fin n → ℝ) (θ : ℝ) (x : (Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun x : Fin n → Bool => D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat)) θ x =
      ∏ i, Real.exp (-θ * a i * (x i).toNat) / (1 + Real.exp (-θ * a i)) := by
  dsimp only
  rw [exp_linearEnergy, partition_product, Finset.prod_div_distrib]

private lemma q_bit_bound_pos (a θ : ℝ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) (b : Bool) :
    Real.exp (-θ * a * b.toNat) / (1 + Real.exp (-θ * a)) ≤
      (1 / 2 : ℝ) ^ b.toNat := by
  have he := Real.exp_pos (-θ * a)
  have hle : Real.exp (-θ * a) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
    mul_zero, mul_one, Real.exp_zero, pow_zero, pow_one]
  · exact (div_le_one (by linarith)).2 (by linarith)
  · apply (div_le_iff₀ (by linarith : 0 < 1 + Real.exp (-θ * a))).2
    linarith

private lemma q_bit_bound_neg (a θ : ℝ) (ha : 0 ≤ a) (hθ : θ ≤ 0) (b : Bool) :
    Real.exp (-θ * a * b.toNat) / (1 + Real.exp (-θ * a)) ≤
      (1 / 2 : ℝ) ^ (!b).toNat := by
  have he := Real.exp_pos (-θ * a)
  have hge : 1 ≤ Real.exp (-θ * a) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true,
    Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, Real.exp_zero, pow_zero, pow_one]
  · apply (div_le_iff₀ (by linarith : 0 < 1 + Real.exp (-θ * a))).2
    linarith
  · exact (div_le_one (by linarith)).2 (by linarith)

private lemma q_hamming_pos (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (θ : ℝ) (hθ : 0 ≤ θ) (x : (Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun x : Fin n → Bool => D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat)) θ x ≤ (1 / 2 : ℝ) ^ occupationCount x := by
  rw [q_product, occupationCount, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ => (div_pos (Real.exp_pos _)
    (by positivity : 0 < 1 + Real.exp (-θ * a i))).le)
    (fun i _ => q_bit_bound_pos (a i) θ (ha i) hθ (x i))

private lemma q_hamming_neg (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (θ : ℝ) (hθ : θ ≤ 0) (x : (Fin n → Bool)) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (fun x : Fin n → Bool => D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat)) θ x ≤ (1 / 2 : ℝ) ^ occupationCount (fun i => !(x i)) := by
  rw [q_product, occupationCount, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ => (div_pos (Real.exp_pos _)
    (by positivity : 0 < 1 + Real.exp (-θ * a i))).le)
    (fun i _ => q_bit_bound_neg (a i) θ (ha i) hθ (x i))

private def checker (n : ℕ) : (Fin n → Bool) := fun i => decide (i.val % 2 = 0)

private lemma hamming_checker (n : ℕ) : occupationCount (checker n) = (n + 1) / 2 := by
  induction n with
  | zero => simp [occupationCount]
  | succ n ih =>
    have hs : occupationCount (checker (n + 1)) = occupationCount (checker n) + if n % 2 = 0 then 1 else 0 := by
      simp [occupationCount, checker, Fin.sum_univ_castSucc]
      split_ifs <;> simp_all
    rw [hs, ih]
    split_ifs with h <;> omega

private lemma hamming_compl {n : ℕ} (x : (Fin n → Bool)) : occupationCount x + occupationCount (fun i => !(x i)) = n := by
  rw [occupationCount, occupationCount, ← Finset.sum_add_distrib]
  have h (i : Fin n) : (x i).toNat + (!(x i)).toNat = 1 := by cases x i <;> rfl
  simp_rw [h]
  simp

private lemma q_checker_even (m : ℕ) (θ : ℝ) :
    (fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (@energy (2 * m)) θ (checker (2 * m)) ≤ (1 / 2 : ℝ) ^ m := by
  let a : Fin (2*m) → ℝ := fun i => 1 + (1 / 2 : ℝ) ^ (i.val + 1)
  have he : @energy (2 * m) = (fun x => D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy a (fun i => (x i).toNat)) := by
    funext x
    exact energy_formula x
  have ha : ∀ i, 0 ≤ a i := fun i => by dsimp [a]; positivity
  have hc : occupationCount (checker (2*m)) = m := by rw [hamming_checker]; omega
  rw [he]
  rcases le_total 0 θ with hθ | hθ
  · simpa only [hc] using q_hamming_pos a ha θ hθ (checker (2*m))
  · have hd : occupationCount (fun i => !(checker (2*m) i)) = m := by
      have h := hamming_compl (checker (2*m))
      rw [hc] at h
      omega
    simpa only [hd] using q_hamming_neg a ha θ hθ (checker (2*m))

open Filter Topology

private lemma log_polynomial_div_tendsto :
    Tendsto (fun n : ℕ => Real.log (4 * ((n : ℝ) + 1) ^ 2) / n) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by simp) tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hx using 1 <;> simp [Function.comp_def]
  have hc : Tendsto (fun n : ℕ => Real.log 4 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  convert hc.add (hl.const_mul 2) using 1
  · funext n
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  · norm_num

private lemma even_tendsto : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
  exact tendsto_id.const_mul_atTop' (by decide : 0 < (2 : ℕ))

open Filter Topology

private noncomputable def dyadicStat (n : ℕ) (G : (Fin n → Fin n → Bool)) : ℝ :=
  if hn : 0 < n then energy (fun i => G i ⟨0,hn⟩) else 0

private def checkerMat (n : ℕ) : (Fin n → Fin n → Bool) := fun i j => decide ((i.val + j.val) % 2 = 0)

private lemma dyadicStat_succ (n : ℕ) :
    dyadicStat (n + 1) = fun G => energy (fun i => G i 0) := by
  rfl

private lemma checkerMat_first (n : ℕ) :
    (fun i : Fin (n+1) => checkerMat (n+1) i 0) = checker (n+1) := by
  rfl

private lemma dyadic_uniform (n : ℕ) : ∀ G : (Fin (n+1) → Fin (n+1) → Bool),
    omega (dyadicStat (n+1)) (dyadicStat (n+1) G) = Fintype.card ((Fin (n + 1) → Fin n → Bool)) := by
  rw [dyadicStat_succ]
  exact omega_first_col n energy (energy_injective (n+1))

private lemma cardMat_log (n : ℕ) : Real.log (Fintype.card ((Fin n → Fin n → Bool))) = (n : ℝ)^2 * Real.log 2 := by
  simp [Real.log_pow]
  ring

private lemma dyadic_model_bounds (n : ℕ) (hn : 0 < n) :
    0 ≤ modelDiv (dyadicStat n) ∧ modelDiv (dyadicStat n) ≤ Real.log (4 * ((n:ℝ)+1)^2) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := modelDiv_bounds (dyadicStat (m+1)) (Fintype.card ((Fin (m + 1) → Fin m → Bool))) Fintype.card_pos (dyadic_uniform m)
  refine ⟨h.1,h.2.trans ?_⟩
  apply Real.log_le_log
    (Finset.sum_pos (fun G _ => lCan_pos _ G) Finset.univ_nonempty)
  have hw := w_sum_any (dyadicStat (m+1))
  change (∑ G, lCan (dyadicStat (m+1)) G) ≤ 2 * (1 + Real.log (Fintype.card ((Fin (m+1) → Fin (m+1) → Bool)))) at hw
  rw [cardMat_log] at hw
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  push_cast at hw ⊢
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((m:ℝ)+1))
  nlinarith [sq_nonneg (m:ℝ)]

private lemma dyadic_model_tendsto :
    Tendsto (fun n : ℕ => modelDiv (dyadicStat n) / n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ log_polynomial_div_tendsto
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_nonneg (dyadic_model_bounds n hn).1 (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_le_div_of_nonneg_right (dyadic_model_bounds n hn).2 (Nat.cast_nonneg n)

private lemma measure_first_col (n : ℕ) (G : (Fin (n+1) → Fin (n+1) → Bool)) (θ : ℝ) :
    measureDiv (dyadicStat (n+1)) G θ = -Real.log ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ (fun i => G i 0)) := by
  rw [measureDiv_eq_log, dyadic_uniform, dyadicStat_succ, pCan_first_col]
  change Real.log ((1 / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ)) /
    ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ (fun i => G i 0) / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ))) = _
  have hr : (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ) ≠ 0 := NeZero.ne _
  have hq := (q_pos energy θ (fun i => G i 0)).ne'
  have hid : (1 / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ)) /
      ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ (fun i => G i 0) / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ)) =
      ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ (fun i => G i 0))⁻¹ := by field_simp
  rw [hid,Real.log_inv]

private lemma energy_zero (n : ℕ) : energy (fun _ : Fin n => false) = 0 := by
  rw [energy_formula]
  simp

private lemma energy_le_top {n : ℕ} (x : (Fin n → Bool)) : energy x ≤ energy (fun _ : Fin n => true) := by
  rw [energy_formula,energy_formula]
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp <;> positivity

private lemma isMatched_first_col (n : ℕ) (G : (Fin (n+1) → Fin (n+1) → Bool)) (θ : ℝ) :
    IsMatched (dyadicStat (n+1)) θ G ↔ mean (@energy (n+1)) θ = energy (fun i => G i 0) := by
  unfold IsMatched
  rw [dyadicStat_succ]
  simp_rw [pCan_first_col]
  change ((∑ H : (Fin (n+1) → Fin (n+1) → Bool),
    ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) (@energy (n+1)) θ (fun i => H i 0) / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ)) *
      energy (fun i => H i 0)) = energy (fun i => G i 0)) ↔
    mean (@energy (n+1)) θ = energy (fun i => G i 0)
  rw [sum_first_col n (fun x : (Fin (n+1) → Bool) =>
    ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ x / (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ)) * energy x)]
  have hr : (Fintype.card ((Fin (n + 1) → Fin n → Bool)) : ℝ) ≠ 0 := NeZero.ne _
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_div_cancel₀ _ hr]
  simp only [mean_eq_sum, div_mul_eq_mul_div, ← Finset.sum_div]

private lemma dyadic_exists_match (n : ℕ) (hn : 2 ≤ n) :
    ∃ θ : ℝ, IsMatched (dyadicStat n) θ (checkerMat n) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let a : (Fin (m+1) → Bool) := fun _ => false
  let b : (Fin (m+1) → Bool) := fun _ => true
  have ha (x : (Fin (m+1) → Bool)) : energy a ≤ energy x := by
    rw [energy_zero, energy_decomp]
    exact add_nonneg (Nat.cast_nonneg _) (fraction_bounds x).1
  have hb (x : (Fin (m+1) → Bool)) : energy x ≤ energy b := energy_le_top x
  have hha : occupationCount a = 0 := by simp [a,occupationCount]
  have hhb : occupationCount b = m+1 := by simp [b,occupationCount]
  have hhc := hamming_checker (m+1)
  have hc : energy a < energy (checker (m+1)) ∧ energy (checker (m+1)) < energy b := by
    constructor <;> apply energy_lt_of_hamming_lt <;> omega
  obtain ⟨θ,hθ⟩ := exists_matched_mean energy a b ha hb _ hc
  refine ⟨θ,?_⟩
  rw [isMatched_first_col, checkerMat_first]
  exact hθ

private noncomputable def matchedTheta (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then Classical.choose (dyadic_exists_match n hn) else 0

private lemma matchedTheta_eventually :
    ∀ᶠ n in atTop, IsMatched (dyadicStat n) (matchedTheta n) (checkerMat n) := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [matchedTheta,dite_eq_left hn]
  exact Classical.choose_spec (dyadic_exists_match n hn)

private lemma checker_measure_lower (m : ℕ) (hm : 0 < m) (θ : ℝ) :
    (m:ℝ) * Real.log 2 ≤ measureDiv (dyadicStat (2*m)) (checkerMat (2*m)) θ := by
  have hn : 0 < 2*m := by omega
  have heq : measureDiv (dyadicStat (2*m)) (checkerMat (2*m)) θ =
      -Real.log ((fun (e : _ → ℝ) (θ : ℝ) x => Real.exp (-θ * e x) / ∑ y, Real.exp (-θ * e y)) energy θ (checker (2*m))) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk,measure_first_col,checkerMat_first]
  rw [heq]
  have hp := q_pos energy θ (checker (2*m))
  have hl := Real.log_le_log hp (q_checker_even m θ)
  rw [Real.log_pow] at hl
  simp only [one_div, Real.log_inv] at hl
  nlinarith

private lemma checker_scaled_lower (m : ℕ) (hm : 0 < m) :
    Real.log 2 / 2 ≤
      measureDiv (dyadicStat (2*m)) (checkerMat (2*m)) (matchedTheta (2*m)) / (2*m) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hl := checker_measure_lower m hm (matchedTheta (2*m))
  have hn' : (0:ℝ) < 2 * (m:ℝ) := by positivity
  apply (le_div_iff₀ hn').2
  nlinarith

theorem result : ¬ claim := by
  intro h
  have ht := h dyadicStat dyadic_model_tendsto checkerMat matchedTheta matchedTheta_eventually
  have hs := ht.comp even_tendsto
  have hle : Real.log 2 / 2 ≤ 0 := by
    apply ge_of_tendsto hs
    filter_upwards [eventually_gt_atTop 0] with m hm
    simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat] using checker_scaled_lower m hm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation
