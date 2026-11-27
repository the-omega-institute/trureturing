import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.ThetaGaussianPairing

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.ThetaGaussianTail
noncomputable section

abbrev tailSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ _ v => gaussianTail v) (fun e => nomatch e)

def tailRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => 1) (fun e => nomatch e)

def boundArena : Arena where
  signature := tailSignature
  Law R := ∀ {v : ℝ}, 1 / 2 ≤ v →
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ 2 *
      Real.exp (-Real.pi * v * (((k : ℝ) + 2) ^ 2 - 1))) ∧
    R.readout () () v ≤ (4 * Real.exp (-3 * Real.pi * v)) /
      (1 - 4 * Real.exp (-3 * Real.pi * v)) ∧ R.readout () () v < 1 / 15

def scaledArena : Arena where
  signature := tailSignature
  Law R := ∀ {s v : ℝ}, 0 < s → s ≤ Real.pi / 6 → 3 / (4 * s) ≤ v →
    Real.exp (Real.pi / (4 * s)) * R.readout () () v < 1 / 39999

private theorem bound_bridge : (type_of% (@gaussian_tail_bound)) ↔
    boundArena.Law tailActual := Iff.rfl

private theorem scaled_bridge : (type_of% (@gaussian_tail_scaled_bound)) ↔
    scaledArena.Law tailActual := Iff.rfl

private theorem tail_dependence : ObservationalDependence tailSignature tailActual := by
  intro i
  refine ⟨(), 2, 1, ne_of_lt ?_⟩
  change gaussianTail 2 < gaussianTail 1
  unfold gaussianTail
  apply Summable.tsum_lt_tsum (i := 0)
  · intro k
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn2 : 0 ≤ ((k : ℝ) + 2) ^ 2 - 1 := by nlinarith
    have hpos := mul_nonneg Real.pi_pos.le hn2
    nlinarith
  · norm_num only [Nat.cast_zero, zero_add, show (2 : ℝ) ^ 2 = 4 by norm_num]
    apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 4)
    apply Real.exp_lt_exp.mpr
    linarith [Real.pi_pos]
  · exact (gaussian_tail_bound (v := 2) (by norm_num)).1
  · exact (gaussian_tail_bound (v := 1) (by norm_num)).1

private theorem bound_rejected : ¬ boundArena.Law tailRejected := by
  intro h
  have h1 := (h (v := 1) (by norm_num)).2.2
  norm_num [tailRejected, realize] at h1

private theorem scaled_rejected : ¬ scaledArena.Law tailRejected := by
  intro h
  have h1 := h (s := 1 / 2) (v := 2) (by norm_num) (by linarith [Real.pi_gt_three]) (by norm_num)
  have hp : 1 ≤ Real.exp (Real.pi / (4 * (1 / 2))) :=
    Real.one_le_exp (by positivity)
  norm_num only [tailRejected, realize, mul_one] at h1
  linarith

def boundRegistration : Registration boundArena (type_of% (@gaussian_tail_bound)) where
  actual := tailActual
  bridge := bound_bridge
  variation := ⟨@gaussian_tail_bound, tailRejected, bound_rejected⟩
  sensitivity := ⟨fun i => ⟨tailRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, bound_rejected⟩, fun e => nomatch e⟩
  dependence := tail_dependence

def scaledRegistration : Registration scaledArena (type_of% (@gaussian_tail_scaled_bound)) where
  actual := tailActual
  bridge := scaled_bridge
  variation := ⟨@gaussian_tail_scaled_bound, tailRejected, scaled_rejected⟩
  sensitivity := ⟨fun i => ⟨tailRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, scaled_rejected⟩, fun e => nomatch e⟩
  dependence := tail_dependence

def pairActual : Realization tailSignature :=
  realize tailSignature (fun _ _ a => gaussianPairTail a) (fun e => nomatch e)

def pairArena : Arena where
  signature := tailSignature
  Law R := ∀ {a : ℝ}, 6 ≤ a →
    Summable (fun k : ℕ => 4 * a * ((k : ℝ) + 3 / 4) ^ 2 *
      Real.exp (-a * (((k : ℝ) + 1) ^ 2 - ((k : ℝ) + 1) / 2))) ∧
    R.readout () () a ≤ (27 / 2) * Real.exp (-3) +
      96 * Real.exp (-18) / (1 - 4 * Real.exp (-9))

private theorem pair_bridge : (type_of% (@gaussian_pair_tail_bound)) ↔
    pairArena.Law pairActual := Iff.rfl

private theorem pair_dependence : ObservationalDependence tailSignature pairActual := by
  intro i
  refine ⟨(), 0, 6, ?_⟩
  change gaussianPairTail 0 ≠ gaussianPairTail 6
  have hz : gaussianPairTail 0 = 0 := by simp [gaussianPairTail]
  rw [hz]
  apply ne_of_lt
  unfold gaussianPairTail
  exact ((gaussian_pair_tail_bound (a := 6) (by norm_num)).1).tsum_pos
    (fun k => by positivity) 0 (by positivity)

def pairRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => (27 / 2) * Real.exp (-3) +
    96 * Real.exp (-18) / (1 - 4 * Real.exp (-9)) + 1) (fun e => nomatch e)

private theorem pair_rejected : ¬ pairArena.Law pairRejected := by
  intro h
  have h1 := (h (a := 6) (by norm_num)).2
  change (27 / 2) * Real.exp (-3) +
    96 * Real.exp (-18) / (1 - 4 * Real.exp (-9)) + 1 ≤ _ at h1
  linarith

def pairRegistration : Registration pairArena (type_of% (@gaussian_pair_tail_bound)) where
  actual := pairActual
  bridge := pair_bridge
  variation := ⟨@gaussian_pair_tail_bound, pairRejected, pair_rejected⟩
  sensitivity := ⟨fun i => ⟨pairRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, pair_rejected⟩, fun e => nomatch e⟩
  dependence := pair_dependence

end
end Reg.Support.ThetaGaussianTail

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.ThetaGaussianPairing
noncomputable section

abbrev momentSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def momentActual : Realization momentSignature :=
  realize momentSignature
    (fun _ p m => (p.2 - m) * Real.exp (-p.1 * (p.2 - m) ^ 2))
    (fun e => nomatch e)

def momentRejected : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => 1) (fun e => nomatch e)

def momentArena : Arena where
  signature := momentSignature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ b : ℝ,
    Summable (fun m : ℤ => R.readout () ⟨a, b⟩ m)

private theorem moment_bridge : (type_of% (@summable_gaussian_force)) ↔
    momentArena.Law momentActual := Iff.rfl

private theorem moment_dependence :
    ObservationalDependence momentSignature momentActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  have hp := Real.exp_pos (-1 : ℝ)
  norm_num [momentActual, realize] <;> linarith

private theorem moment_rejected : ¬ momentArena.Law momentRejected := by
  intro h
  have hh := h (a := 1) (by norm_num) 0
  simp [momentRejected, realize, summable_const_iff] at hh

def momentRegistration : Registration momentArena
    (type_of% (@summable_gaussian_force)) where
  actual := momentActual
  bridge := moment_bridge
  variation := ⟨@summable_gaussian_force, momentRejected, moment_rejected⟩
  sensitivity := ⟨fun i => ⟨momentRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, moment_rejected⟩, fun e => nomatch e⟩
  dependence := moment_dependence

abbrev forceSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def forceActual : Realization forceSignature :=
  realize forceSignature (fun _ a b => gaussianForce a b) (fun e => nomatch e)

def forceRejected : Realization forceSignature :=
  realize forceSignature (fun _ _ _ => -1) (fun e => nomatch e)

def lowerArena : Arena where
  signature := forceSignature
  Law R := ∀ {a b : ℝ}, 6 ≤ a → 0 ≤ b → b ≤ 1 / 2 →
    (3 / (20 * Real.pi)) * Real.exp (-a / 4) * Real.sin (2 * Real.pi * b) ≤
      R.readout () a b

private theorem lower_bridge : (type_of% (@gaussian_force_lower)) ↔
    lowerArena.Law forceActual := Iff.rfl

private theorem force_zero (a : ℝ) : gaussianForce a 0 = 0 := by
  unfold gaussianForce
  have he : (∑' m : ℤ, ((0 : ℝ) - m) * Real.exp (-a * ((0 : ℝ) - m) ^ 2)) =
      -(∑' m : ℤ, ((0 : ℝ) - m) * Real.exp (-a * ((0 : ℝ) - m) ^ 2)) := by
    rw [← tsum_neg, ← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro m
    simp only [Equiv.neg_apply, Int.cast_neg, zero_sub, neg_neg, neg_sq]
    ring
  linarith

private theorem force_quarter_pos : 0 < gaussianForce 6 (1 / 4) := by
  have h := gaussian_force_lower (a := 6) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [he, mul_one] at h
  exact lt_of_lt_of_le (by positivity) h

private theorem force_dependence : ObservationalDependence forceSignature forceActual := by
  intro i
  refine ⟨6, 0, 1 / 4, ?_⟩
  change gaussianForce 6 0 ≠ gaussianForce 6 (1 / 4)
  rw [force_zero]
  exact ne_of_lt force_quarter_pos

private theorem lower_rejected : ¬ lowerArena.Law forceRejected := by
  intro h
  have hh := h (a := 6) (b := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp only [forceRejected, realize, he, mul_one] at hh
  have hp : 0 < (3 / (20 * Real.pi)) * Real.exp (-(6 : ℝ) / 4) := by positivity
  linarith

def lowerRegistration : Registration lowerArena (type_of% (@gaussian_force_lower)) where
  actual := forceActual
  bridge := lower_bridge
  variation := ⟨@gaussian_force_lower, forceRejected, lower_rejected⟩
  sensitivity := ⟨fun i => ⟨forceRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, lower_rejected⟩, fun e => nomatch e⟩
  dependence := force_dependence

end
end Reg.Support.ThetaGaussianPairing
