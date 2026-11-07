/- GID: D5/S3/Quantum/SpinChains/DiamondSingletExclusion
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/DiamondSingletExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every positive integer-spin diamond has no singlet zero-weight ground vector. -/

import D5.S3.Quantum.SpinChains.DiamondSpinBounds

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix Complex
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)
open D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation (siteOperator)
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (raising_entry)

open D5.S3.Quantum.SpinChains.DiamondSpinBounds

namespace D5.S3.Quantum.SpinChains.DiamondSingletExclusion

def groundEnergy (S : ℕ) : ℝ := sInf (spectrum ℝ (restrictedHamiltonian S))

def groundSpace (S : ℕ) : Submodule ℂ (Configuration S → ℂ) :=
  LinearMap.ker (Matrix.toLin' (hamiltonian S - (groundEnergy S : ℂ) • 1)) ⊓
    zeroWeightSpace S

def singletLowerBound (S : ℕ) : ℝ := -4 * (S : ℝ) ^ 2 - 8 / 3 * S

def claim : Prop := ∀ S : ℕ, 1 ≤ S →
  (∀ v : State S, v.ofLp ∈ singletSpace S → ‖v‖ = 1 →
    singletLowerBound S ≤ (star v.ofLp ⬝ᵥ (hamiltonian S *ᵥ v.ofLp)).re) ∧
  groundEnergy S < singletLowerBound S ∧
  groundSpace S ⊓ singletSpace S = ⊥


private lemma pair_upper_bound : (∀ (S : ℕ) (hS : 1 ≤ S) (i j : Fin 4) (hij : i ≠ j),
    ((S : ℂ)^2 • (1 : Operator S) - dot S i j).PosSemidef) :=
  native_relations.1

private lemma binomialProduct_positive : (∀ (S : ℕ) (x : Configuration S),
    0 < binomialProductReal S x) :=
  native_relations.2.1

private lemma binomialProduct_real : (∀ (S : ℕ) (x : Configuration S),
    binomialProduct S x = (binomialProductReal S x : ℂ)) :=
  native_relations.2.2.1

private lemma commutator_product : (∀ {S : ℕ} (Q A B : Operator S),
    Q * (A * B) - (A * B) * Q = (Q * A - A * Q) * B + A * (Q * B - B * Q)) :=
  native_relations.2.2.2.1

private lemma hamiltonian_ladder : (∀ (S : ℕ),
    hamiltonian S = ∑ e ∈ edges,
      (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2)) :=
  native_relations.2.2.2.2.1

private lemma lowering_product : (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (lowering S i *ᵥ binomialProduct S) x =
      ((x i).val : ℂ) * binomialProduct S x) :=
  native_relations.2.2.2.2.2.1

private lemma lowering_raising_commutator : (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * raising S i - raising S i * totalLowering S =
      (-2 : ℂ) • z S i) :=
  native_relations.2.2.2.2.2.2.1

private lemma lowering_times_raising : (∀ (n : ℕ),
    (Jplus n)ᴴ * Jplus n = diagonal (fun i : Fin (n + 1) =>
      (((i.val : ℝ) * ((n : ℝ) + 1 - i.val) : ℝ) : ℂ))) :=
  native_relations.2.2.2.2.2.2.2.1

private lemma lowering_z_commutator : (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * z S i - z S i * totalLowering S = lowering S i) :=
  native_relations.2.2.2.2.2.2.2.2.1

private lemma raising_product : (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (raising S i *ᵥ binomialProduct S) x =
      ((2 * S : ℂ) - (x i).val) * binomialProduct S x) :=
  native_relations.2.2.2.2.2.2.2.2.2.1

private lemma raising_times_lowering : (∀ (n : ℕ),
    Jplus n * (Jplus n)ᴴ = diagonal (fun i : Fin (n + 1) =>
      ((((i.val : ℝ) + 1) * ((n : ℝ) - i.val) : ℝ) : ℂ))) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.1

private lemma restricted_hermitian : (∀ (S : ℕ),
    (restrictedHamiltonian S).IsHermitian) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.1

private lemma singlet_has_zero_weight : (∀ (S : ℕ),
    singletSpace S ≤ zeroWeightSpace S) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma singlet_isotropy : (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S),
    expect v (hamiltonian S) = (4 / 3 : ℂ) * expect v (isotropic S)) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_action : (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ) (x : Configuration S),
    (site S i A *ᵥ v) x = ∑ a : Weight S, A (x i) a * v (Function.update x i a)) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_add : (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A + B) = site S i A + site S i B) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_adjoint : (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ),
    (site S i A)ᴴ = site S i Aᴴ) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_commute : (∀ (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i A * site S j B = site S j B * site S i A) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_mul : (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A * B) = site S i A * site S i B) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma site_smul : (∀ (S : ℕ) (i : Fin 4) (c : ℂ)
    (A : Matrix (Weight S) (Weight S) ℂ),
    site S i (c • A) = c • site S i A) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma z_action : (∀ (S : ℕ) (i : Fin 4) (v : Configuration S → ℂ) (x : Configuration S),
    (z S i *ᵥ v) x = ((S : ℂ) - (x i).val) * v x) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma z_diagonal : (∀ (S : ℕ) (i : Fin 4),
    z S i = diagonal (fun x : Configuration S => (S : ℂ) - (x i).val)) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma zero_weight_coordinates : (∀ (S : ℕ) (v : Configuration S → ℂ),
    v ∈ zeroWeightSpace S ↔
      ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → v x = 0) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private lemma zero_weight_invariant : (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S),
    hamiltonian S *ᵥ v ∈ zeroWeightSpace S) :=
  native_relations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private lemma site_one (S : ℕ) (i : Fin 4) : site S i 1 = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp [site_action, Matrix.one_apply]

private lemma local_casimir (S : ℕ) :
    Jz (2 * S) * Jz (2 * S) + (1 / 2 : ℂ) •
      (Jplus (2 * S) * (Jplus (2 * S))ᴴ + (Jplus (2 * S))ᴴ * Jplus (2 * S)) =
      ((S : ℂ) * (S + 1)) • (1 : Matrix (Weight S) (Weight S) ℂ) := by
  rw [raising_times_lowering, lowering_times_raising]
  simp only [Jz, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    push_cast
    ring
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private lemma site_casimir (S : ℕ) (i : Fin 4) :
    z S i * z S i + (1 / 2 : ℂ) •
      (raising S i * lowering S i + lowering S i * raising S i) =
      ((S : ℂ) * (S + 1)) • (1 : Operator S) := by
  have hh := congrArg (site S i) (local_casimir S)
  simpa only [site_add, site_mul, site_smul, site_one, z, raising, lowering] using hh

private lemma isotropic_expansion (S : ℕ) :
    isotropic S = dot S 0 1 + dot S 0 2 + dot S 0 3 + dot S 1 2 + dot S 1 3 := by
  simp [isotropic, edges]
  abel

private lemma central_identity (S : ℕ) :
    isotropic S + dot S 0 1 + (2 * (S : ℂ) * (S + 1)) • 1 =
      (z S 0 + z S 1) * totalWeight S + (1 / 2 : ℂ) •
        ((raising S 0 + raising S 1) * totalLowering S +
          (lowering S 0 + lowering S 1) * totalRaising S) := by
  have hzz : z S 1 * z S 0 = z S 0 * z S 1 := site_commute S 1 0 (by decide) _ _
  have hpq : raising S 1 * lowering S 0 = lowering S 0 * raising S 1 :=
    site_commute S 1 0 (by decide) _ _
  have hqp : lowering S 1 * raising S 0 = raising S 0 * lowering S 1 :=
    site_commute S 1 0 (by decide) _ _
  have h : (z S 0 + z S 1) * totalWeight S + (1 / 2 : ℂ) •
        ((raising S 0 + raising S 1) * totalLowering S +
          (lowering S 0 + lowering S 1) * totalRaising S) =
      (z S 0 * z S 0 + (1 / 2 : ℂ) •
        (raising S 0 * lowering S 0 + lowering S 0 * raising S 0)) +
      (z S 1 * z S 1 + (1 / 2 : ℂ) •
        (raising S 1 * lowering S 1 + lowering S 1 * raising S 1)) +
      (isotropic S + dot S 0 1) := by
    simp only [totalWeight, totalLowering, totalRaising, Fin.sum_univ_four]
    change (z S 0 + z S 1) * (z S 0 + z S 1 + z S 2 + z S 3) +
      (1 / 2 : ℂ) • ((raising S 0 + raising S 1) *
        (lowering S 0 + lowering S 1 + lowering S 2 + lowering S 3) +
        (lowering S 0 + lowering S 1) *
        (raising S 0 + raising S 1 + raising S 2 + raising S 3)) = _
    rw [isotropic_expansion]
    simp only [dot, xy, zz, Matrix.mul_add, Matrix.add_mul, smul_add]
    rw [hzz, hpq, hqp]
    module
  rw [h, site_casimir S 0, site_casimir S 1]
  module

private lemma isotropic_on_singlet (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S) :
    isotropic S *ᵥ v = (-2 * (S : ℂ) * (S + 1)) • v - dot S 0 1 *ᵥ v := by
  have hp : totalRaising S *ᵥ v = 0 := hv.1
  have hm : totalLowering S *ᵥ v = 0 := hv.2
  have hz : totalWeight S *ᵥ v = 0 := singlet_has_zero_weight S hv
  have hh := congrArg (fun A : Operator S => A *ᵥ v) (central_identity S)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hp, hm, hz, Matrix.mulVec_zero, add_zero,
    smul_zero] at hh
  have h : isotropic S *ᵥ v + dot S 0 1 *ᵥ v = (-2 * (S : ℂ) * (S + 1)) • v := by
    calc
      _ = -(2 * (S : ℂ) * (S + 1)) • v := by
        simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hh
      _ = _ := by ring_nf
  exact eq_sub_iff_add_eq.mpr h

private lemma singlet_lower_bound (S : ℕ) (hS : 1 ≤ S) (v : State S)
    (hv : v.ofLp ∈ singletSpace S) (hn : ‖v‖ = 1) :
    singletLowerBound S ≤ (expect v.ofLp (hamiltonian S)).re := by
  have hnorm : star v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hn]
    norm_num
  have hpair := (pair_upper_bound S hS 0 1 (by decide)).dotProduct_mulVec_nonneg v.ofLp
  have hi : expect v.ofLp (isotropic S) =
      -2 * (S : ℂ) * (S + 1) - expect v.ofLp (dot S 0 1) := by
    unfold expect
    rw [isotropic_on_singlet S v.ofLp hv, dotProduct_sub, dotProduct_smul,
      hnorm, smul_eq_mul, mul_one]
  have hp : (expect v.ofLp (dot S 0 1)).re ≤ (S : ℝ)^2 := by
    have hh := hpair.1
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hnorm, smul_eq_mul, pow_two, Complex.mul_re] at hh
    unfold expect
    nlinarith [hh]
  have he := singlet_isotropy S v.ofLp hv
  rw [hi] at he
  have he' := congrArg Complex.re he
  norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re,
    Complex.div_re, Complex.div_im] at he'
  unfold singletLowerBound
  linarith

private def degree {S : ℕ} (x : Configuration S) : ℕ := ∑ i : Fin 4, (x i).val
private def pairDegree {S : ℕ} (x : Configuration S) : ℕ := (x 0).val + (x 1).val
private def central (i : Fin 4) : ℕ := if i.val < 2 then 1 else 0

private def pairCoefficient (S p : ℕ) : ℂ := (-1 : ℂ)^p / (Nat.choose (4 * S) p : ℂ)

private def singletMultiplier (S : ℕ) (x : Configuration S) : ℂ :=
  if degree x = 4 * S then pairCoefficient S (pairDegree x) else 0

private def trialSinglet (S : ℕ) : Configuration S → ℂ :=
  fun x => singletMultiplier S x * binomialProduct S x

private def raiseMultiplier (S : ℕ) (i : Fin 4) (x : Configuration S) : ℂ :=
  if degree x + 1 = 4 * S then pairCoefficient S (pairDegree x + central i) else 0

private def lowerMultiplier (S : ℕ) (i : Fin 4) (x : Configuration S) : ℂ :=
  if degree x = 4 * S + 1 then pairCoefficient S (pairDegree x - central i) else 0

private lemma degree_update_up {S : ℕ} (x : Configuration S) (i : Fin 4) (a : Weight S)
    (h : (x i).val + 1 = a.val) :
    degree (Function.update x i a) = degree x + 1 ∧
      pairDegree (Function.update x i a) = pairDegree x + central i := by
  fin_cases i <;>
    simp [degree, pairDegree, central, Fin.sum_univ_four] at * <;> omega

private lemma degree_update_down {S : ℕ} (x : Configuration S) (i : Fin 4) (a : Weight S)
    (h : a.val + 1 = (x i).val) :
    degree (Function.update x i a) + 1 = degree x ∧
      pairDegree (Function.update x i a) + central i = pairDegree x := by
  fin_cases i <;>
    simp [degree, pairDegree, central, Fin.sum_univ_four] at * <;> omega

private lemma raising_factor (S : ℕ) (i : Fin 4) (f v : Configuration S → ℂ)
    (x : Configuration S) (c : ℂ)
    (hf : ∀ a : Weight S, (x i).val + 1 = a.val → f (Function.update x i a) = c) :
    (raising S i *ᵥ (fun y => f y * v y)) x = c * (raising S i *ᵥ v) x := by
  simp only [raising, site_action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : (x i).val + 1 = a.val
  · rw [hf a ha]
    ring
  · simp [raising_entry, ha]

private lemma lowering_factor (S : ℕ) (i : Fin 4) (f v : Configuration S → ℂ)
    (x : Configuration S) (c : ℂ)
    (hf : ∀ a : Weight S, a.val + 1 = (x i).val → f (Function.update x i a) = c) :
    (lowering S i *ᵥ (fun y => f y * v y)) x = c * (lowering S i *ᵥ v) x := by
  simp only [lowering, site_action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val + 1 = (x i).val
  · rw [hf a ha]
    ring
  · simp [Matrix.conjTranspose_apply, raising_entry, ha]

private lemma trial_raising (S : ℕ) (i : Fin 4) (x : Configuration S) :
    (raising S i *ᵥ trialSinglet S) x =
      raiseMultiplier S i x * ((2 * S : ℂ) - (x i).val) * binomialProduct S x := by
  unfold trialSinglet
  rw [raising_factor S i (singletMultiplier S) (binomialProduct S) x (raiseMultiplier S i x)]
  · rw [raising_product]
    ring
  · intro a ha
    obtain ⟨ht, hp⟩ := degree_update_up x i a ha
    simp only [singletMultiplier, raiseMultiplier, ht, hp]

private lemma trial_lowering (S : ℕ) (i : Fin 4) (x : Configuration S) :
    (lowering S i *ᵥ trialSinglet S) x =
      lowerMultiplier S i x * ((x i).val : ℂ) * binomialProduct S x := by
  unfold trialSinglet
  rw [lowering_factor S i (singletMultiplier S) (binomialProduct S) x (lowerMultiplier S i x)]
  · rw [lowering_product]
    ring
  · intro a ha
    obtain ⟨ht, hp⟩ := degree_update_down x i a ha
    have ht' : degree (Function.update x i a) = 4 * S ↔ degree x = 4 * S + 1 := by omega
    have hp' : pairDegree (Function.update x i a) = pairDegree x - central i := by omega
    simp only [singletMultiplier, lowerMultiplier, ht', hp']

private lemma pairCoefficient_raise (S p : ℕ) (hp : p < 4 * S) :
    ((4 * S : ℂ) - p) * pairCoefficient S (p + 1) +
      ((p : ℂ) + 1) * pairCoefficient S p = 0 := by
  have h0 : (Nat.choose (4 * S) p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp.le).ne'
  have h1 : (Nat.choose (4 * S) (p + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  have hh := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_succ_right_eq (4 * S) p)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.le] at hh
  unfold pairCoefficient
  rw [pow_succ]
  field_simp
  linear_combination (-1 : ℂ)^p * hh

private lemma pairCoefficient_lower (S p : ℕ) (hp : 0 < p) (hp' : p ≤ 4 * S) :
    (p : ℂ) * pairCoefficient S (p - 1) +
      ((4 * S : ℂ) + 1 - p) * pairCoefficient S p = 0 := by
  have hh := pairCoefficient_raise S (p - 1) (by omega)
  have hp1 : p - 1 + 1 = p := by omega
  rw [hp1] at hh
  have hc : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by rw [Nat.cast_sub hp, Nat.cast_one]
  rw [hc] at hh
  linear_combination hh

private lemma trial_total_raising (S : ℕ) : totalRaising S *ᵥ trialSinglet S = 0 := by
  ext x
  simp only [totalRaising, Fin.sum_univ_four, Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply]
  rw [trial_raising, trial_raising, trial_raising, trial_raising]
  by_cases ht : degree x + 1 = 4 * S
  · have hsum : (x 0).val + (x 1).val + (x 2).val + (x 3).val + 1 = 4 * S := by
      simpa [degree, Fin.sum_univ_four] using ht
    have hp : pairDegree x < 4 * S := by unfold pairDegree; omega
    have hc := pairCoefficient_raise S (pairDegree x) hp
    have hsumC : ((x 0).val : ℂ) + (x 1).val + (x 2).val + (x 3).val + 1 = 4 * (S : ℂ) := by
      exact_mod_cast hsum
    simp [raiseMultiplier, central, ht]
    simp only [pairDegree, Nat.cast_add] at hc
    simp only [pairDegree] at *
    linear_combination binomialProduct S x * hc -
      pairCoefficient S ((x 0).val + (x 1).val) * binomialProduct S x * hsumC
  · simp [raiseMultiplier, ht]

private lemma trial_total_lowering (S : ℕ) : totalLowering S *ᵥ trialSinglet S = 0 := by
  ext x
  simp only [totalLowering, Fin.sum_univ_four, Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply]
  rw [trial_lowering, trial_lowering, trial_lowering, trial_lowering]
  by_cases ht : degree x = 4 * S + 1
  · have hsum : (x 0).val + (x 1).val + (x 2).val + (x 3).val = 4 * S + 1 := by
      simpa [degree, Fin.sum_univ_four] using ht
    have hle (i : Fin 4) : (x i).val ≤ 2 * S := Nat.le_of_lt_succ (x i).isLt
    have hp : 0 < pairDegree x := by unfold pairDegree; have := hle 2; have := hle 3; omega
    have hp' : pairDegree x ≤ 4 * S := by unfold pairDegree; have := hle 0; have := hle 1; omega
    have hc := pairCoefficient_lower S (pairDegree x) hp hp'
    have hsumC : ((x 0).val : ℂ) + (x 1).val + (x 2).val + (x 3).val = 4 * (S : ℂ) + 1 := by
      exact_mod_cast hsum
    simp [lowerMultiplier, central, ht]
    simp only [pairDegree, Nat.cast_add] at hc
    simp only [pairDegree] at *
    linear_combination binomialProduct S x * hc +
      pairCoefficient S ((x 0).val + (x 1).val) * binomialProduct S x * hsumC
  · simp [lowerMultiplier, ht]

private lemma trial_is_singlet (S : ℕ) : trialSinglet S ∈ singletSpace S :=
  ⟨trial_total_raising S, trial_total_lowering S⟩

private lemma trial_pair_eigenvector (S : ℕ) :
    dot S 0 1 *ᵥ trialSinglet S = (S : ℂ)^2 • trialSinglet S := by
  have hA (x : Configuration S) :
      (raising S 0 *ᵥ (lowering S 1 *ᵥ trialSinglet S)) x =
        singletMultiplier S x * ((x 1).val : ℂ) *
          ((2 * S : ℂ) - (x 0).val) * binomialProduct S x := by
    rw [show lowering S 1 *ᵥ trialSinglet S =
        (fun y => (lowerMultiplier S 1 y * ((y 1).val : ℂ)) * binomialProduct S y) by
      ext y; exact trial_lowering S 1 y]
    rw [raising_factor S 0 (fun y => lowerMultiplier S 1 y * ((y 1).val : ℂ))
      (binomialProduct S) x (singletMultiplier S x * ((x 1).val : ℂ))]
    · rw [raising_product]
      ring
    · intro a ha
      obtain ⟨ht, hp⟩ := degree_update_up x 0 a ha
      have ht' : degree (Function.update x 0 a) = 4 * S + 1 ↔ degree x = 4 * S := by omega
      simp [central] at hp
      simp [lowerMultiplier, singletMultiplier, central, ht', hp]
  have hB (x : Configuration S) :
      (lowering S 0 *ᵥ (raising S 1 *ᵥ trialSinglet S)) x =
        singletMultiplier S x * ((2 * S : ℂ) - (x 1).val) *
          ((x 0).val : ℂ) * binomialProduct S x := by
    rw [show raising S 1 *ᵥ trialSinglet S =
        (fun y => (raiseMultiplier S 1 y * ((2 * S : ℂ) - (y 1).val)) * binomialProduct S y) by
      ext y; exact trial_raising S 1 y]
    rw [lowering_factor S 0 (fun y => raiseMultiplier S 1 y * ((2 * S : ℂ) - (y 1).val))
      (binomialProduct S) x (singletMultiplier S x * ((2 * S : ℂ) - (x 1).val))]
    · rw [lowering_product]
      ring
    · intro a ha
      obtain ⟨ht, hp⟩ := degree_update_down x 0 a ha
      have ht' : degree (Function.update x 0 a) + 1 = 4 * S ↔ degree x = 4 * S := by omega
      simp [central] at hp
      simp [raiseMultiplier, singletMultiplier, central, ht', hp]
  ext x
  simp only [dot, xy, zz, Matrix.add_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hA, hB, z_action, z_action]
  unfold trialSinglet
  ring

private lemma trial_middle_nonzero (S : ℕ) : trialSinglet S (middleConfiguration S) ≠ 0 := by
  have ht : degree (middleConfiguration S) = 4 * S := by simp [degree, middleConfiguration]
  have hp : pairDegree (middleConfiguration S) = 2 * S := by
    simp [pairDegree, middleConfiguration]
    omega
  have hc : pairCoefficient S (2 * S) ≠ 0 := by
    apply div_ne_zero (pow_ne_zero _ (by norm_num))
    exact_mod_cast (Nat.choose_pos (by omega : 2 * S ≤ 4 * S)).ne'
  have hb : binomialProduct S (middleConfiguration S) ≠ 0 := by
    rw [binomialProduct_real]
    exact_mod_cast (binomialProduct_positive S (middleConfiguration S)).ne'
  simpa only [trialSinglet, singletMultiplier, ht, ite_true, hp] using mul_ne_zero hc hb

private lemma trial_expectation (S : ℕ) :
    expect (trialSinglet S) (hamiltonian S) =
      (singletLowerBound S : ℂ) * (star (trialSinglet S) ⬝ᵥ trialSinglet S) := by
  have hi : isotropic S *ᵥ trialSinglet S =
      (-3 * (S : ℂ)^2 - 2 * S) • trialSinglet S := by
    rw [isotropic_on_singlet S _ (trial_is_singlet S), trial_pair_eigenvector]
    module
  have hh := singlet_isotropy S _ (trial_is_singlet S)
  unfold expect at hh ⊢
  rw [hi, dotProduct_smul, smul_eq_mul] at hh
  rw [hh]
  unfold singletLowerBound
  push_cast
  ring

private lemma lowering_lowering_commutator (S : ℕ) (i : Fin 4) :
    totalLowering S * lowering S i - lowering S i * totalLowering S = 0 := by
  unfold totalLowering
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst j
    exact sub_self _
  · exact sub_eq_zero.mpr (site_commute S j i hji _ _)

private lemma raising_lowering_commutator (S : ℕ) (i : Fin 4) :
    totalRaising S * lowering S i - lowering S i * totalRaising S = (2 : ℂ) • z S i := by
  have hh := congrArg Matrix.conjTranspose (lowering_raising_commutator S i)
  have hQ : (totalLowering S)ᴴ = totalRaising S := by
    simp [totalLowering, totalRaising, lowering, raising, Matrix.conjTranspose_sum, site_adjoint]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_smul, hQ,
    show (raising S i)ᴴ = lowering S i from site_adjoint S i _,
    show (z S i)ᴴ = z S i from by simp [z_diagonal]] at hh
  norm_num [Complex.star_def] at hh
  calc
    _ = -(lowering S i * totalRaising S - totalRaising S * lowering S i) := by abel
    _ = _ := by rw [hh]; module

private lemma raising_z_commutator (S : ℕ) (i : Fin 4) :
    totalRaising S * z S i - z S i * totalRaising S = -raising S i := by
  have hh := congrArg Matrix.conjTranspose (lowering_z_commutator S i)
  have hQ : (totalLowering S)ᴴ = totalRaising S := by
    simp [totalLowering, totalRaising, lowering, raising, Matrix.conjTranspose_sum, site_adjoint]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hQ,
    show (lowering S i)ᴴ = raising S i from by simp [lowering, raising, site_adjoint],
    show (z S i)ᴴ = z S i from by simp [z_diagonal]] at hh
  calc
    _ = -(z S i * totalRaising S - totalRaising S * z S i) := by abel
    _ = _ := congrArg Neg.neg hh

private lemma lowering_xy_commutator (S : ℕ) (i j : Fin 4) :
    totalLowering S * xy S i j - xy S i j * totalLowering S =
      (-2 : ℂ) • (z S i * lowering S j + lowering S i * z S j) := by
  have h : totalLowering S * xy S i j - xy S i j * totalLowering S =
      (totalLowering S * (raising S i * lowering S j) -
        (raising S i * lowering S j) * totalLowering S) +
      (totalLowering S * (lowering S i * raising S j) -
        (lowering S i * raising S j) * totalLowering S) := by unfold xy; noncomm_ring
  rw [h, commutator_product, commutator_product,
    lowering_raising_commutator, lowering_lowering_commutator,
    lowering_lowering_commutator, lowering_raising_commutator]
  simp only [zero_mul, mul_zero, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul]
  module

private lemma raising_mixed_commutator (S : ℕ) (i j : Fin 4) :
    totalRaising S * (z S i * lowering S j + lowering S i * z S j) -
      (z S i * lowering S j + lowering S i * z S j) * totalRaising S =
        -xy S i j + (4 : ℂ) • zz S i j := by
  have h : totalRaising S * (z S i * lowering S j + lowering S i * z S j) -
      (z S i * lowering S j + lowering S i * z S j) * totalRaising S =
      (totalRaising S * (z S i * lowering S j) - z S i * lowering S j * totalRaising S) +
      (totalRaising S * (lowering S i * z S j) - lowering S i * z S j * totalRaising S) := by
    noncomm_ring
  rw [h, commutator_product, commutator_product, raising_z_commutator,
    raising_lowering_commutator, raising_lowering_commutator, raising_z_commutator]
  unfold xy zz
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg]
  module

private lemma double_edge_commutator (S : ℕ) (i j : Fin 4) :
    totalRaising S * (totalLowering S * xy S i j - xy S i j * totalLowering S) -
      (totalLowering S * xy S i j - xy S i j * totalLowering S) * totalRaising S =
        (2 : ℂ) • xy S i j - (8 : ℂ) • zz S i j := by
  rw [lowering_xy_commutator]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
  rw [raising_mixed_commutator]
  module

private lemma commutator_sum {S : ℕ} {κ : Type*} (Q : Operator S)
    (s : Finset κ) (A : κ → Operator S) :
    Q * (∑ k ∈ s, A k) - (∑ k ∈ s, A k) * Q = ∑ k ∈ s, (Q * A k - A k * Q) := by
  simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

private lemma double_commutator (S : ℕ) :
    totalRaising S * (totalLowering S * hamiltonian S - hamiltonian S * totalLowering S) -
      (totalLowering S * hamiltonian S - hamiltonian S * totalLowering S) * totalRaising S =
        (2 : ℂ) • hamiltonian S - (8 : ℂ) • vertical S := by
  rw [hamiltonian_ladder]
  change totalRaising S * (totalLowering S * (∑ e ∈ edges, xy S e.1 e.2) -
      (∑ e ∈ edges, xy S e.1 e.2) * totalLowering S) -
      (totalLowering S * (∑ e ∈ edges, xy S e.1 e.2) -
      (∑ e ∈ edges, xy S e.1 e.2) * totalLowering S) * totalRaising S = _
  rw [commutator_sum, commutator_sum]
  simp_rw [double_edge_commutator]
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum]
  rfl

private lemma singlet_eigen_vertical (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S) (e : ℂ) (he : hamiltonian S *ᵥ v = e • v) :
    vertical S *ᵥ v = (e / 4) • v := by
  have hp : totalRaising S *ᵥ v = 0 := hv.1
  have hm : totalLowering S *ᵥ v = 0 := hv.2
  have hC : (totalLowering S * hamiltonian S - hamiltonian S * totalLowering S) *ᵥ v = 0 := by
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, he,
      Matrix.mulVec_smul, hm, Matrix.mulVec_zero, smul_zero, sub_self]
  have hD := congrArg (fun A : Operator S => A *ᵥ v) (double_commutator S)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hC, hp,
    Matrix.mulVec_zero, sub_self, Matrix.smul_mulVec, he] at hD
  have h8 : (8 : ℂ) • (vertical S *ᵥ v) = (2 * e) • v := by
    have hh := (sub_eq_zero.mp hD.symm).symm
    simpa only [smul_smul] using hh
  calc
    _ = (1 / 8 : ℂ) • ((8 : ℂ) • (vertical S *ᵥ v)) := by module
    _ = (1 / 8 : ℂ) • ((2 * e) • v) := by rw [h8]
    _ = _ := by module

private lemma vertical_middle (S : ℕ) (v : Configuration S → ℂ) :
    (vertical S *ᵥ v) (middleConfiguration S) = 0 := by
  unfold vertical
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e _
  simp only [zz, ← Matrix.mulVec_mulVec, z_action]
  simp [middleConfiguration]

private lemma lower_bound_negative (S : ℕ) (hS : 1 ≤ S) : singletLowerBound S < 0 := by
  have hp : (0 : ℝ) < S := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hS
  unfold singletLowerBound
  nlinarith [sq_nonneg (S : ℝ)]

private lemma trial_not_eigenvector (S : ℕ) (hS : 1 ≤ S) :
    hamiltonian S *ᵥ trialSinglet S ≠ (singletLowerBound S : ℂ) • trialSinglet S := by
  intro he
  have hh := singlet_eigen_vertical S _ (trial_is_singlet S) _ he
  have hc := congrFun hh (middleConfiguration S)
  rw [vertical_middle] at hc
  have hn : (singletLowerBound S : ℂ) / 4 ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (lower_bound_negative S hS).ne
    · norm_num
  exact mul_ne_zero hn (trial_middle_nonzero S) hc.symm

private lemma sum_zero_weight (S : ℕ) (f : Configuration S → ℂ)
    (hf : ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → f x = 0) :
    (∑ x : Configuration S, f x) = ∑ x : ZeroConfiguration S, f x.val := by
  have hh := Fintype.sum_subtype_add_sum_subtype
    (fun x : Configuration S => (∑ i : Fin 4, (x i).val) = 4 * S) f
  have hz : (∑ x : {x : Configuration S // (∑ i : Fin 4, (x i).val) ≠ 4 * S}, f x.val) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hf x.val x.property
  rw [hz, add_zero] at hh
  exact hh.symm

private lemma restriction_mul (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) :
    restrictedHamiltonian S *ᵥ (fun x : ZeroConfiguration S => v x.val) =
      (fun x : ZeroConfiguration S => (hamiltonian S *ᵥ v) x.val) := by
  ext x
  simp only [restrictedHamiltonian, Matrix.submatrix_apply, Matrix.mulVec, dotProduct]
  symm
  apply sum_zero_weight
  intro y hy
  rw [(zero_weight_coordinates S v).mp hv y hy, mul_zero]

private lemma restriction_inner (S : ℕ) (v w : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) :
    star (fun x : ZeroConfiguration S => v x.val) ⬝ᵥ (fun x : ZeroConfiguration S => w x.val) =
      star v ⬝ᵥ w := by
  symm
  apply sum_zero_weight
  intro x hx
  simp [(zero_weight_coordinates S v).mp hv x hx]

private lemma restriction_expectation (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) :
    star (fun x : ZeroConfiguration S => v x.val) ⬝ᵥ
      (restrictedHamiltonian S *ᵥ (fun x : ZeroConfiguration S => v x.val)) =
      expect v (hamiltonian S) := by
  rw [restriction_mul S v hv]
  exact restriction_inner S v _ hv

private lemma lift_restricted_eigenvector (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) (e : ℂ)
    (he : restrictedHamiltonian S *ᵥ (fun x : ZeroConfiguration S => v x.val) =
      e • (fun x : ZeroConfiguration S => v x.val)) : hamiltonian S *ᵥ v = e • v := by
  have hH := zero_weight_invariant S v hv
  rw [restriction_mul S v hv] at he
  ext x
  by_cases hx : (∑ i : Fin 4, (x i).val) = 4 * S
  · exact congrFun he ⟨x, hx⟩
  · rw [(zero_weight_coordinates S _).mp hH x hx,
      show (e • v) x = e * v x from rfl, (zero_weight_coordinates S _).mp hv x hx, mul_zero]

private lemma ground_energy_isLeast (S : ℕ) :
    IsLeast (spectrum ℝ (restrictedHamiltonian S)) (groundEnergy S) := by
  unfold groundEnergy
  rw [(restricted_hermitian S).spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).isClosed.isLeast_csInf (Set.range_nonempty _)
    (Set.finite_range _).bddBelow

open scoped MatrixOrder in
private lemma restriction_positive_shift (S : ℕ) (L : ℝ) (hL : L ≤ groundEnergy S) :
    (restrictedHamiltonian S - (L : ℂ) • 1).PosSemidef := by
  have hh : algebraMap ℝ (Matrix (ZeroConfiguration S) (ZeroConfiguration S) ℂ) L ≤
      restrictedHamiltonian S := by
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (a := restrictedHamiltonian S)
      (restricted_hermitian S).isSelfAdjoint).mpr
    intro x hx
    exact hL.trans ((ground_energy_isLeast S).2 hx)
  change (restrictedHamiltonian S - algebraMap ℝ (Matrix _ _ ℂ) L).PosSemidef at hh
  have hs : algebraMap ℝ (Matrix (ZeroConfiguration S) (ZeroConfiguration S) ℂ) L =
      (L : ℂ) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext x y
    exact RCLike.real_smul_eq_coe_mul L
      ((1 : Matrix (ZeroConfiguration S) (ZeroConfiguration S) ℂ) x y)
  rw [hs] at hh
  exact hh

private lemma ground_strict (S : ℕ) (hS : 1 ≤ S) : groundEnergy S < singletLowerBound S := by
  by_contra hn
  have hL : singletLowerBound S ≤ groundEnergy S := le_of_not_gt hn
  have hv : trialSinglet S ∈ zeroWeightSpace S := singlet_has_zero_weight S (trial_is_singlet S)
  let u : ZeroConfiguration S → ℂ := fun x => trialSinglet S x.val
  have hpos := restriction_positive_shift S (singletLowerBound S) hL
  have hquad : star u ⬝ᵥ ((restrictedHamiltonian S - (singletLowerBound S : ℂ) • 1) *ᵥ u) = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    dsimp [u]
    rw [restriction_expectation S _ hv, restriction_inner S _ _ hv, trial_expectation, sub_self]
  have hker := hpos.dotProduct_mulVec_zero_iff.mp hquad
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hker
  exact trial_not_eigenvector S hS
    (lift_restricted_eigenvector S _ hv _ (sub_eq_zero.mp hker))

private lemma ground_singlet_trivial (S : ℕ) (hS : 1 ≤ S) :
    groundSpace S ⊓ singletSpace S = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  by_contra hv0
  let w : State S := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro h
    apply hv0
    exact congrArg WithLp.ofLp h
  let u : State S := (‖w‖⁻¹ : ℂ) • w
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, Complex.norm_real, norm_ne_zero_iff.mpr hw]
  have hsing : u.ofLp ∈ singletSpace S := (singletSpace S).smul_mem _ hv.2
  have he : hamiltonian S *ᵥ v = (groundEnergy S : ℂ) • v := by
    have hh := hv.1.1
    change (hamiltonian S - (groundEnergy S : ℂ) • 1) *ᵥ v = 0 at hh
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] using hh
  have heu : hamiltonian S *ᵥ u.ofLp = (groundEnergy S : ℂ) • u.ofLp := by
    change hamiltonian S *ᵥ ((‖w‖⁻¹ : ℂ) • v) = (groundEnergy S : ℂ) • ((‖w‖⁻¹ : ℂ) • v)
    rw [Matrix.mulVec_smul, he, smul_comm]
  have hnorm : star u.ofLp ⬝ᵥ u.ofLp = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hbound := singlet_lower_bound S hS u hsing hu
  have hexp : expect u.ofLp (hamiltonian S) = (groundEnergy S : ℂ) := by
    simp only [expect, heu, dotProduct_smul, hnorm, smul_eq_mul, mul_one]
  rw [hexp, Complex.ofReal_re] at hbound
  exact not_le_of_gt (ground_strict S hS) hbound

theorem result : claim := by
  intro S hS
  refine ⟨?_, ground_strict S hS, ground_singlet_trivial S hS⟩
  intro v hv hn
  exact singlet_lower_bound S hS v hv hn

end D5.S3.Quantum.SpinChains.DiamondSingletExclusion
