/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordConditionalMemoryGap
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: [lake/module/D5.S3.Quantum.Information.StrongSubadditivity]
   utility: none
   digest: Exact memory gain and conditional mutual information of the primitive periodic record. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordDiamondCoefficient
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Information.StrongSubadditivity
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.PrimitiveRecordConditionalMemoryGap

open _root_.Matrix Filter Asymptotics
open scoped BigOperators Kronecker _root_.Matrix Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
  (recordState mixtureState pointerState marginalLeft_mixture)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (productState marginalLeft marginalLeft_productState)
open D5.S3.Quantum.Information.StrongSubadditivity
  (entropy_toMState toMState_marginalLeft)
open PeriodicMPSPrimitiveCollision (collisionNormalizedOverlap)
open PeriodicMPSParentIntersection (Word)
open ComplementaryRecordRate (collisionAlpha collisionAlpha_lt_one collisionFlattening environmentDensity)
open PrimitiveHiddenLabelEntropy
  (Visible matrix pureDensity fairMixture collisionAmplitude collisionPure collisionMixture collisionMixture_entropy)
open PrimitiveComplementaryEntropyExpansion
  (matrixEntropy matrixEntropy_eq_density matrixEntropy_gram matrixEntropy_blocks
    matrixEntropy_reindex collisionComplementaryEntropy collision_complementary_entropy_asymptotic)
open PrimitiveRecordDiamondCoefficient (discardedPair_overlap_asymptotic)

open private negMulLog_symmetric_quadratic from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveComplementaryEntropyExpansion

private lemma fair_nonneg (b : Bool) : 0 ≤ (fun _ : Bool => (1 / 2 : ℝ)) b := by
  norm_num

private lemma fair_sum : ∑ _b : Bool, (1 / 2 : ℝ) = 1 := by
  norm_num

/-- The literal fair c-q label and the complete normalized ring state. -/
def collisionLabelState (m : ℕ) (hm : 5 ≤ m) : DensityState (Bool × (Visible × Word m)) :=
  recordState (fun _ => 1 / 2) fair_nonneg fair_sum (fun b => collisionPure b m hm)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma fair_record_matrix (P : Bool → DensityState ι) (b c : Bool) (i j : ι) :
    matrix (recordState (fun _ => 1 / 2) fair_nonneg fair_sum P) (b, i) (c, j) =
      if b = c then ((1 / 2 : ℝ) • matrix (P b)) i j else 0 := by
  change (∑ x : Bool, (1 / 2 : ℝ) •
    (Matrix.diagonal (fun y : Bool => if y = x then (1 : ℂ) else 0) ⊗ₖ matrix (P x)))
      (b, i) (c, j) = _
  cases b <;> cases c <;>
    simp [Matrix.sum_apply, Matrix.smul_apply]

private lemma fair_record_entropy (P : Bool → DensityState ι) :
    matrixEntropy (matrix (recordState (fun _ => 1 / 2) fair_nonneg fair_sum P)) =
      matrixEntropy (fromBlocks ((1 / 2 : ℝ) • matrix (P false)) 0 0
        ((1 / 2 : ℝ) • matrix (P true))) := by
  rw [← matrixEntropy_reindex (Equiv.boolProdEquivSum ι)]
  congr 1
  ext (i | i) (j | j) <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.boolProdEquivSum, Equiv.coe_fn_symm_mk,
      Sum.elim_inl, Sum.elim_inr, fair_record_matrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, Matrix.zero_apply]

private lemma fair_record_marginal (P : Bool → DensityState ι) :
    marginalLeft (recordState (fun _ => 1 / 2) fair_nonneg fair_sum P) =
      fairMixture (P false) (P true) := by
  unfold recordState
  rw [marginalLeft_mixture]
  simp only [marginalLeft_productState]
  apply Subtype.ext
  change (∑ b : Bool, (1 / 2 : ℝ) • (P b).1) = (1 / 2 : ℝ) • ((P false).1 + (P true).1)
  rw [Fintype.sum_bool, smul_add, add_comm]

private lemma conditional_eq_matrix_entropies {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ρ : DensityState (A × B)) :
    qConditionalEnt (toMState ρ) =
      matrixEntropy (matrix ρ) - matrixEntropy (matrix (marginalLeft ρ)) := by
  unfold qConditionalEnt
  rw [← toMState_marginalLeft, entropy_toMState, entropy_toMState,
    matrixEntropy_eq_density, matrixEntropy_eq_density]

private lemma matrixEntropy_half_pure (u : ι → ℂ) (hu : u ⬝ᵥ star u = 1) :
    matrixEntropy ((1 / 2 : ℝ) • matrix (pureDensity u hu)) = Real.negMulLog (1 / 2) := by
  let W : Matrix ι (Fin 1) ℂ := Matrix.of (fun i _ => Real.sqrt (1 / 2 : ℝ) • u i)
  have hsq : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = 1 / 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hentry (i j : ι) :
      W i 0 * star (W j 0) = (1 / 2 : ℝ) • (u i * star (u j)) := by
    change ((Real.sqrt (1 / 2 : ℝ)) • u i) * star ((Real.sqrt (1 / 2 : ℝ)) • u j) = _
    rw [star_smul, star_trivial, smul_mul_smul_comm, hsq]
  have houter : W * Wᴴ = (1 / 2 : ℝ) • matrix (pureDensity u hu) := by
    ext i j
    change (W * Wᴴ) i j = (1 / 2 : ℝ) • (u i * star (u j))
    simpa only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply] using hentry i j
  have hinner : Wᴴ * W = Matrix.diagonal (fun _ : Fin 1 => ((1 / 2 : ℝ) : ℂ)) := by
    ext i j
    have hzero (k : Fin 1) : k = 0 := Subsingleton.elim _ _
    rw [hzero i, hzero j, Matrix.mul_apply, Matrix.diagonal_apply_eq]
    simp only [Matrix.conjTranspose_apply, mul_comm (star _), hentry, ← Finset.smul_sum]
    change (1 / 2 : ℝ) • (u ⬝ᵥ star u) = _
    rw [hu]
    simp [Complex.real_smul]
  rw [← houter, ← matrixEntropy_gram W, hinner]
  simp [matrixEntropy, Matrix.charpoly_diagonal]

/-- The conditional entropy of the literal c-q state is the deficiency of its binary mixture
entropy from the fair-label entropy, in nats. -/
theorem collision_full_memory_conditional_entropy (m : ℕ) (hm : 5 ≤ m) :
    qConditionalEnt (toMState (collisionLabelState m hm)) =
      Real.log 2 - Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2) := by
  rw [conditional_eq_matrix_entropies, collisionLabelState, fair_record_entropy,
    fair_record_marginal, matrixEntropy_blocks]
  change _ - matrixEntropy (matrix (collisionMixture m hm)) = _
  rw [matrixEntropy_eq_density, collisionMixture_entropy]
  have h (b : Bool) : matrixEntropy ((1 / 2 : ℝ) • matrix (collisionPure b m hm)) =
      Real.negMulLog (1 / 2) := by
    unfold collisionPure
    apply matrixEntropy_half_pure
  rw [h false, h true]
  have hhalf : Real.negMulLog (1 / 2) + Real.negMulLog (1 / 2) = Real.log 2 := by
    rw [← Real.binEntropy_two_inv, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num
  rw [hhalf]

private lemma binary_entropy_remainder :
    (fun t : ℝ => Real.log 2 - Real.binEntropy ((1 + t) / 2) - t ^ 2 * (1 / 2)) =o[𝓝 0]
      (fun t => t ^ 2) := by
  have h := (negMulLog_symmetric_quadratic (1 / 2) (1 / 2) (by norm_num)).neg_left
  refine h.congr_left (fun t => ?_)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show (1 + t) / 2 = 1 / 2 + t * (1 / 2) by ring,
    show 1 - (1 / 2 + t * (1 / 2)) = 1 / 2 - t * (1 / 2) by ring]
  have hhalf : Real.log 2 = 2 * Real.negMulLog (1 / 2) := by
    rw [← Real.binEntropy_two_inv, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num
    ring
  rw [hhalf]
  ring

private lemma alpha_pos : 0 < collisionAlpha := by
  unfold collisionAlpha
  positivity

private lemma binary_entropy_scaled_limit :
    Tendsto (fun m : ℕ =>
      (Real.log 2 - Real.binEntropy ((1 + ‖collisionNormalizedOverlap (2 + m)‖) / 2)) /
        collisionAlpha ^ (2 * (2 + m))) atTop (𝓝 (1 / 2)) := by
  let a : ℕ → ℝ := fun m => collisionAlpha ^ (2 + m)
  let t : ℕ → ℝ := fun m => ‖collisionNormalizedOverlap (2 + m)‖
  have ha (m : ℕ) : a m ≠ 0 := (pow_pos alpha_pos _).ne'
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa only [a, Nat.add_comm 2, Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one alpha_pos.le collisionAlpha_lt_one).comp
        (tendsto_add_atTop_nat 2)
  have hratio : Tendsto (fun m => t m / a m) atTop (𝓝 1) :=
    discardedPair_overlap_asymptotic
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [one_mul] using (hratio.mul ha0).congr (fun m => div_mul_cancel₀ _ (ha m))
  have hrem := (binary_entropy_remainder.comp_tendsto ht0).tendsto_div_nhds_zero
  have hcoef : Tendsto (fun m =>
      ((Real.log 2 - Real.binEntropy ((1 + t m) / 2) - t m ^ 2 * (1 / 2)) / t m ^ 2 +
        (1 / 2 : ℝ))) atTop (𝓝 (1 / 2)) := by
    simpa only [Function.comp_apply, zero_add] using hrem.add_const (1 / 2 : ℝ)
  have hlimit := hcoef.mul (hratio.pow 2)
  simp only [one_pow, mul_one] at hlimit
  refine hlimit.congr' ?_
  filter_upwards [hratio.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))]
    with m hm
  have ht : t m ≠ 0 := fun h => by simp [h] at hm
  change _ = (Real.log 2 - Real.binEntropy ((1 + t m) / 2)) / collisionAlpha ^ (2 * (2 + m))
  rw [mul_comm 2 (2 + m), pow_mul]
  change _ = _ / a m ^ 2
  field_simp [ht, ha m]
  ring

/-- The rings are indexed by their environmental length `m = k + 5`, so their full length is
`2 + (k + 5)`. -/
theorem collision_full_memory_entropy_asymptotic :
    Tendsto (fun k : ℕ =>
      qConditionalEnt (toMState (collisionLabelState (k + 5) (by omega))) /
        collisionAlpha ^ (2 * (2 + (k + 5)))) atTop (𝓝 (1 / 2)) := by
  refine (binary_entropy_scaled_limit.comp (tendsto_add_atTop_nat 5)).congr (fun k => ?_)
  simp [Function.comp_apply, collision_full_memory_conditional_entropy]


private lemma collision_environment_matrix (b : Bool) (m : ℕ) (hm : 5 ≤ m) :
    matrix (marginalLeft (collisionPure b m hm)) =
      environmentDensity (collisionFlattening b m) := rfl

private lemma complementary_conditional_entropy_eq (m : ℕ) (hm : 5 ≤ m) :
    qConditionalEnt (toMState (recordState (fun _ => 1 / 2) fair_nonneg fair_sum
      (fun b => marginalLeft (collisionPure b m hm)))) = collisionComplementaryEntropy m := by
  rw [conditional_eq_matrix_entropies, fair_record_entropy, fair_record_marginal]
  change matrixEntropy (fromBlocks ((1 / 2 : ℝ) • matrix (marginalLeft (collisionPure false m hm)))
    0 0 ((1 / 2 : ℝ) • matrix (marginalLeft (collisionPure true m hm)))) -
    matrixEntropy ((1 / 2 : ℝ) • (matrix (marginalLeft (collisionPure false m hm)) +
      matrix (marginalLeft (collisionPure true m hm)))) = _
  rw [collision_environment_matrix, collision_environment_matrix, collisionComplementaryEntropy]

/-- After ordering the state as `X,E,O`, the two literal conditional entropies
give the existing quantum conditional mutual information `I(X:O|E)`. -/
theorem collision_cmi_eq_memory_gap (m : ℕ) (hm : 5 ≤ m) :
    qcmi ((toMState (collisionLabelState m hm)).relabel
      ((Equiv.refl Bool).prodCongr (Equiv.prodComm (Word m) Visible))) =
      collisionComplementaryEntropy m - qConditionalEnt (toMState (collisionLabelState m hm)) := by
  let ρ := toMState (collisionLabelState m hm)
  let e := (Equiv.refl Bool).prodCongr (Equiv.prodComm (Word m) Visible)
  let P := fun b => marginalLeft (collisionPure b m hm)
  have hXE : (ρ.relabel e).assoc'.traceRight =
      toMState (recordState (fun _ => 1 / 2) fair_nonneg fair_sum P) := by
    apply MState.ext_m
    ext ⟨b, i⟩ ⟨c, j⟩
    change (∑ o : Visible, matrix (collisionLabelState m hm) (b, (o, i)) (c, (o, j))) =
      matrix (recordState (fun _ => 1 / 2) fair_nonneg fair_sum P) (b, i) (c, j)
    simp only [collisionLabelState, fair_record_matrix]
    split_ifs with h
    · simp only [Matrix.smul_apply, ← Finset.smul_sum]
      rfl
    · simp
  have hEO : (ρ.relabel e).traceLeft =
      ρ.traceLeft.relabel (Equiv.prodComm (Word m) Visible) := MState.ext_m rfl
  have hfull : qConditionalEnt (ρ.relabel e) = qConditionalEnt ρ := by
    rw [qConditionalEnt, hEO, Sᵥₙ_relabel, Sᵥₙ_relabel, qConditionalEnt]
  change qConditionalEnt (ρ.relabel e).assoc'.traceRight - qConditionalEnt (ρ.relabel e) = _
  rw [hXE, complementary_conditional_entropy_eq, hfull]

/-- The difference of the two literal conditional entropies has a positive exact leading
coefficient at the scale of the full ring. The same difference is strictly positive for all
sufficiently large rings. -/
theorem collision_memory_gap_asymptotic :
    0 < (302433 - 46875 * Real.sqrt 41) / (16384 : ℝ) ∧
    Tendsto (fun k : ℕ =>
      (collisionComplementaryEntropy (k + 5) -
        qConditionalEnt (toMState (collisionLabelState (k + 5) (by omega)))) /
        collisionAlpha ^ (2 * (2 + (k + 5))))
      atTop (𝓝 ((302433 - 46875 * Real.sqrt 41) / 16384)) ∧
    ∀ᶠ k : ℕ in atTop,
      qConditionalEnt (toMState (collisionLabelState (k + 5) (by omega))) <
        collisionComplementaryEntropy (k + 5) := by
  have hs : Real.sqrt 41 < 129 / 20 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hp : 0 < (302433 - 46875 * Real.sqrt 41) / (16384 : ℝ) := by linarith
  have hdiff := (collision_complementary_entropy_asymptotic.comp (tendsto_add_atTop_nat 5)).sub
    collision_full_memory_entropy_asymptotic
  have heq : (310625 - 46875 * Real.sqrt 41) / 16384 - 1 / 2 =
      (302433 - 46875 * Real.sqrt 41) / 16384 := by ring
  rw [heq] at hdiff
  simp only [Function.comp_apply, ← sub_div] at hdiff
  refine ⟨hp, hdiff, ?_⟩
  filter_upwards [hdiff.eventually (eventually_gt_nhds hp)] with k hk
  exact sub_pos.mp ((div_pos_iff_of_pos_right (pow_pos alpha_pos _)).mp hk)

#print axioms collision_full_memory_conditional_entropy
#print axioms collision_full_memory_entropy_asymptotic
#print axioms collision_cmi_eq_memory_gap
#print axioms collision_memory_gap_asymptotic

end D5.S3.Quantum.TensorNetworks.PrimitiveRecordConditionalMemoryGap
