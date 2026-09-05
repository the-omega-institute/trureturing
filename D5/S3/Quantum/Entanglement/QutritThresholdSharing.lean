/- GID: D5/S3/Quantum/Entanglement/QutritThresholdSharing
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/QutritThresholdSharing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three qutrit shares hide every input singly and reconstruct it in pairs. -/

import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
import D5.S3.Quantum.Foundation.FiniteStateChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.QutritThresholdSharing

open Matrix
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
open D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped BigOperators ComplexOrder MatrixOrder

/-- The three-share encoding, in computational-basis amplitudes over ZMod 3. -/
def qutritEncoding : Matrix (ZMod 3 × ZMod 3 × ZMod 3) (ZMod 3) ℂ :=
  fun q s => (1 / (Real.sqrt 3 : ℂ)) *
    ∑ j : ZMod 3, if q = (j, j + s, j + 2 * s) then 1 else 0

/-- Ordered coordinates for share pairs (1,2), (2,3), and (3,1). -/
def cyclicShares (i : Fin 3) (q : ZMod 3 × ZMod 3 × ZMod 3) :
    ZMod 3 × ZMod 3 × ZMod 3 :=
  if i = 0 then q else if i = 1 then (q.2.2, q.1, q.2.1)
    else (q.2.1, q.2.2, q.1)

/-- Retain share i by tracing out the other two coordinates. -/
def singleShareMarginal (i : Fin 3)
    (M : Matrix (ZMod 3 × ZMod 3 × ZMod 3) (ZMod 3 × ZMod 3 × ZMod 3) ℂ) :
    Matrix (ZMod 3) (ZMod 3) ℂ :=
  partialTraceFirst (fun p q : (ZMod 3 × ZMod 3) × ZMod 3 =>
    M (cyclicShares i (p.2, p.1.1, p.1.2))
      (cyclicShares i (q.2, q.1.1, q.1.2)))

/-- The decoder sends (a,b) to (b-a,2b-a); its inverse is derived algebraically. -/
def qutritDecoder : Equiv.Perm (ZMod 3 × ZMod 3) where
  toFun p := (p.2 - p.1, 2 * p.2 - p.1)
  invFun p := (p.2 - 2 * p.1, p.2 - p.1)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring

private theorem qutrit_index_system (j k s t : ZMod 3) :
    (j + s = k + t ∧ j + 2 * s = k + 2 * t) ↔ s = t ∧ j = k := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have hs : s = t := by linear_combination h₂ - h₁
    exact ⟨hs, by simpa [hs] using h₁⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem encoding_entry (a b c s : ZMod 3) :
    qutritEncoding (a, b, c) s =
      if b = a + s ∧ c = a + 2 * s then 1 / (Real.sqrt 3 : ℂ) else 0 := by
  rw [qutritEncoding, Finset.sum_eq_single a]
  · simp only [Prod.mk.injEq, true_and]
    split_ifs <;> simp
  · intro j _ hja
    simp [Prod.mk.injEq, Ne.symm hja]
  · simp

private theorem normalization :
    (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = (3 : ℂ)⁻¹ := by
  have h : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [← _root_.mul_inv_rev, h]

private theorem encoding_cyclic (i : Fin 3) (q : ZMod 3 × ZMod 3 × ZMod 3)
    (s : ZMod 3) : qutritEncoding (cyclicShares i q) s = qutritEncoding q s := by
  rcases q with ⟨a, b, c⟩
  fin_cases i <;> norm_num [cyclicShares, encoding_entry]
  all_goals congr 1; apply propext; revert a b c s; decide

private theorem encoding_overlap (a b s t : ZMod 3) :
    (∑ u : ZMod 3, ∑ v : ZMod 3,
      qutritEncoding (a, u, v) s * star (qutritEncoding (b, u, v) t)) =
        if s = t then (1 / 3 : ℂ) * (if a = b then 1 else 0) else 0 := by
  by_cases hst : s = t
  · subst t
    by_cases hab : a = b
    · subst b
      simp [encoding_entry, ite_and, ite_mul, apply_ite, normalization]
    · have hh : b + s ≠ a + s := by simpa using Ne.symm hab
      simp [encoding_entry, ite_and, ite_mul, apply_ite, hab, hh]
  · have hh : ¬(b + t = a + s ∧ b + 2 * t = a + 2 * s) := by
      intro h
      exact hst ((qutrit_index_system b a t s).mp h).1.symm
    simp [encoding_entry, ite_and, ite_mul, apply_ite, hst]
    exact fun h₁ h₂ => hh ⟨h₁, h₂⟩

/-- Every encoded matrix unit has the same scalar-identity marginal on each share. -/
theorem qutrit_matrix_unit_marginal (i : Fin 3) (s t : ZMod 3) :
    singleShareMarginal i
      (qutritEncoding * Matrix.single s t (1 : ℂ) * qutritEncoding.conjTranspose) =
        (if s = t then (1 / 3 : ℂ) else 0) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) := by
  ext a b
  simp only [singleShareMarginal, partialTraceFirst, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply, encoding_cyclic]
  simp only [Matrix.single_apply, ite_and, ite_mul, mul_ite,
    zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [encoding_overlap]
  by_cases hst : s = t <;> by_cases hab : a = b <;> simp [hst, hab]

private theorem marginal_expansion (i : Fin 3) (rho : Matrix (ZMod 3) (ZMod 3) ℂ)
    (a b : ZMod 3) :
    singleShareMarginal i (qutritEncoding * rho * qutritEncoding.conjTranspose) a b =
      ∑ s : ZMod 3, ∑ t : ZMod 3,
        rho s t * singleShareMarginal i
          (qutritEncoding * Matrix.single s t (1 : ℂ) * qutritEncoding.conjTranspose) a b := by
  simp only [singleShareMarginal, partialTraceFirst, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply, encoding_cyclic, Finset.sum_mul]
  simp only [Matrix.single_apply, ite_and, ite_mul, mul_ite,
    zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [Finset.mul_sum]
  let f := fun u v t s : ZMod 3 =>
    qutritEncoding (a, u, v) s * rho s t * star (qutritEncoding (b, u, v) t)
  change (∑ u, ∑ v, ∑ t, ∑ s, f u v t s) = _
  calc
    _ = ∑ u, ∑ v, ∑ s, ∑ t, f u v t s := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      exact Finset.sum_comm
    _ = ∑ u, ∑ s, ∑ v, ∑ t, f u v t s := by
      apply Finset.sum_congr rfl; intro u _
      exact Finset.sum_comm
    _ = ∑ s, ∑ u, ∑ v, ∑ t, f u v t s := Finset.sum_comm
    _ = ∑ s, ∑ u, ∑ t, ∑ v, f u v t s := by
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro u _
      exact Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ u, ∑ v, f u v t s := by
      apply Finset.sum_congr rfl; intro s _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      dsimp [f]
      ring

/-- Every single share of every input density state is maximally mixed. -/
theorem qutrit_single_share_maximally_mixed (rho : DensityState (ZMod 3)) (i : Fin 3) :
    singleShareMarginal i
      (qutritEncoding * CStarMatrix.ofMatrix.symm rho.1 * qutritEncoding.conjTranspose) =
        (1 / 3 : ℂ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) := by
  ext a b
  rw [marginal_expansion]
  simp_rw [qutrit_matrix_unit_marginal]
  simp only [Matrix.smul_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  have htrace : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 :=
    DensityState.trace_eq_one rho
  simpa [Matrix.trace, mul_assoc] using congrArg (fun z : ℂ => z * (1 / 3) *
    (1 : Matrix (ZMod 3) (ZMod 3) ℂ) a b) htrace

private theorem decoded_encoding_entry (a b r s : ZMod 3) :
    qutritEncoding ((qutritDecoder.symm (a, b)).1,
      (qutritDecoder.symm (a, b)).2, r) s =
        if s = a then (if b = r then 1 / (Real.sqrt 3 : ℂ) else 0) else 0 := by
  change qutritEncoding (b - 2 * a, b - a, r) s = _
  rw [encoding_entry]
  have hc : (b - a = b - 2 * a + s ∧ r = b - 2 * a + 2 * s) ↔
      s = a ∧ b = r := by
    constructor
    · rintro ⟨h₁, h₂⟩
      have hs : s = a := by linear_combination -h₁
      exact ⟨hs, by linear_combination -h₂ - 2 * hs⟩
    · rintro ⟨rfl, rfl⟩
      constructor <;> ring
  simp only [hc, ite_and]

private theorem pair_delta (b r : ZMod 3) :
    (∑ j : ZMod 3, if (b, r) = (j, j) then (1 : ℂ) else 0) =
      if b = r then 1 else 0 := by
  rw [Finset.sum_eq_single b]
  · simp [Prod.mk.injEq, eq_comm]
  · intro j _ hj
    simp [Prod.mk.injEq, Ne.symm hj]
  · simp

/-- For each cyclic pair, its permutation unitary recovers every input amplitude
and leaves the other two output coordinates in the fixed maximally entangled state. -/
theorem qutrit_two_share_reconstruction (psi : ZMod 3 → ℂ) (i : Fin 3) (r : ZMod 3) :
    (qutritDecoder⁻¹).permMatrix ℂ *ᵥ
      (fun p : ZMod 3 × ZMod 3 =>
        (qutritEncoding *ᵥ psi) (cyclicShares i (p.1, p.2, r))) =
      fun p : ZMod 3 × ZMod 3 => psi p.1 *
        ((1 / (Real.sqrt 3 : ℂ)) *
          ∑ j : ZMod 3, if (p.2, r) = (j, j) then 1 else 0) := by
  rw [Matrix.permMatrix_mulVec]
  funext p
  rcases p with ⟨a, b⟩
  simp only [Function.comp_apply, Matrix.mulVec, dotProduct, encoding_cyclic]
  change (∑ s : ZMod 3, qutritEncoding ((qutritDecoder.symm (a, b)).1,
    (qutritDecoder.symm (a, b)).2, r) s * psi s) = _
  simp only [decoded_encoding_entry, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [pair_delta]
  by_cases h : b = r <;> simp [h, mul_comm]

#print axioms qutrit_matrix_unit_marginal
#print axioms qutrit_single_share_maximally_mixed
#print axioms qutrit_two_share_reconstruction

end D5.S3.Quantum.Entanglement.QutritThresholdSharing
