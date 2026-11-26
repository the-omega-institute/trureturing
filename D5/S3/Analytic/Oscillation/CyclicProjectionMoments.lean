/- GID: D5/S3/Analytic/Oscillation/CyclicProjectionMoments
   generality: I
   mirror-B: D5/B/S3/Analytic/Oscillation/CyclicProjectionMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier-column overlap determines the exact second moment of a projection ensemble. -/

import Mathlib.Analysis.Fourier.ZMod
import D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap

/-! Character sums of subsets under the squared-minor law of a cyclic Fourier projection. -/

open BigOperators Finset Matrix ZMod
open D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV

noncomputable section

namespace D5.S3.Analytic.Oscillation.CyclicProjectionMoments

variable {m : ℕ} [NeZero m]

private lemma characterSum (u : ZMod m) :
    (∑ x : ZMod m, stdAddChar (u * x)) = if u = 0 then (m : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m h)

private lemma characterDifferenceSum (u : ZMod m) :
    (∑ x : ZMod m, ∑ y : ZMod m, stdAddChar (u * (x - y))) =
      if u = 0 then (m : ℂ)^2 else 0 := by
  classical
  rw [Finset.sum_comm]
  have h (y : ZMod m) :
      (∑ x : ZMod m, stdAddChar (u * (x - y))) = ∑ x : ZMod m, stdAddChar (u * x) :=
    Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
  simp_rw [h, characterSum]
  split_ifs <;> simp [pow_two]

private theorem overlap (A : Finset (ZMod m)) (r : ZMod m) :
    (∑ a ∈ A, ∑ b ∈ A, ∑ x : ZMod m, ∑ y : ZMod m,
      stdAddChar ((a - b - r) * (x - y))) =
    (m : ℂ)^2 * ((A.filter (fun a => a - r ∈ A)).card : ℂ) := by
  classical
  simp_rw [characterDifferenceSum]
  have h (a b : ZMod m) : a - b - r = 0 ↔ b = a - r := by
    constructor <;> intro h <;> linear_combination -h
  simp_rw [h]
  have hb (a : ZMod m) :
      (∑ b ∈ A, if b = a - r then (m : ℂ)^2 else 0) =
      if a - r ∈ A then (m : ℂ)^2 else 0 := by simp
  simp_rw [hb]
  rw [← Finset.sum_filter]
  simp [mul_comm]

private lemma norm_character (u : ZMod m) : ‖stdAddChar u‖ = 1 := by
  rw [stdAddChar_apply]
  exact Circle.norm_coe _

private lemma star_character (u : ZMod m) : star (stdAddChar u) = stdAddChar (-u) := by
  have hN := norm_character u
  apply mul_left_cancel₀ (norm_pos_iff.mp (by rw [hN]; norm_num))
  calc
    stdAddChar u * star (stdAddChar u) = ‖stdAddChar u‖ ^ 2 := Complex.mul_conj' _
    _ = 1 := by rw [hN]; simp
    _ = stdAddChar u * stdAddChar (-u) := by simp [← AddChar.map_add_eq_mul]

open Matrix

/-- Fourier columns indexed by an embedding into the cyclic frequency group. -/
def selectedColumns {k : ℕ} (a : Fin k ↪ ZMod m) (s : ℂ) :
    Matrix (Fin m) (Fin k) ℂ :=
  fun x j => s * stdAddChar (a j * finEquiv m x)

private theorem selectedColumns_orthonormal {k : ℕ} (a : Fin k ↪ ZMod m) {s : ℂ}
    (hs : star s * s = (m : ℂ)⁻¹) :
    (selectedColumns a s)ᴴ * selectedColumns a s = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  have hχ (x : Fin m) :
      star ((selectedColumns a s) x i) * (selectedColumns a s) x j =
      (star s * s) * stdAddChar ((a j - a i) * finEquiv m x) := by
    dsimp [selectedColumns]
    rw [map_mul]
    change star s * star (stdAddChar (a i * finEquiv m x)) *
      (s * stdAddChar (a j * finEquiv m x)) = _
    rw [star_character, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
    change star s * stdAddChar (-(a i * finEquiv m x)) *
      (s * stdAddChar (a j * finEquiv m x)) =
      star s * s * (stdAddChar (a j * finEquiv m x) * stdAddChar (-(a i * finEquiv m x)))
    ring
  simp_rw [Matrix.conjTranspose_apply, hχ]
  rw [← Finset.mul_sum, hs, Matrix.one_apply]
  have hh : (∑ x : Fin m, stdAddChar ((a j - a i) * finEquiv m x)) =
      ∑ x : ZMod m, stdAddChar ((a j - a i) * x) :=
    Fintype.sum_equiv (finEquiv m).toEquiv _ _ (fun _ => rfl)
  rw [hh, characterSum]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  by_cases hij : i = j
  · subst j
    simp [hm]
  · have ha : a j - a i ≠ 0 := sub_ne_zero.mpr (fun h => hij (a.injective h).symm)
    simp [ha, hij]


variable {k : ℕ}

private def pairCharacter (r : ZMod m) (x y : Fin m) : ℂ :=
  stdAddChar (-r * (finEquiv m y - finEquiv m x))

private theorem characterProduct (r : ZMod m) (x y : Fin m) :
    stdAddChar (r * finEquiv m x) * star (stdAddChar (r * finEquiv m y)) =
      pairCharacter r x y := by
  rw [star_character, pairCharacter, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem subsetScore (r : ZMod m) (S : {S : Finset (Fin m) // S.card = k}) :
    (Complex.normSq (∑ x ∈ S.1, stdAddChar (r * finEquiv m x)) : ℂ) =
      (k : ℂ) + score (pairCharacter r) S := by
  classical
  rw [Complex.normSq_eq_conj_mul_self, mul_comm, map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  change (∑ x ∈ S.1, ∑ y ∈ S.1,
    stdAddChar (r * finEquiv m x) * star (stdAddChar (r * finEquiv m y))) = _
  simp_rw [characterProduct]
  unfold score
  have h (x : Fin m) (hx : x ∈ S.1) :
      (∑ y ∈ S.1, pairCharacter r x y) =
        1 + ∑ y ∈ S.1, if x = y then 0 else pairCharacter r x y := by
    calc
      _ = ∑ y ∈ S.1, ((if x = y then 1 else 0) +
          (if x = y then 0 else pairCharacter r x y)) := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with hxy
        · subst y
          simp [pairCharacter]
        · simp
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hx]
  calc
    _ = ∑ x ∈ S.1, (1 + ∑ y ∈ S.1, if x = y then 0 else pairCharacter r x y) :=
      Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_add_distrib]; simp [S.2]

private theorem expectedSubsetScore (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (r : ZMod m) :
    let U := selectedColumns a s
    (∑ S : {S : Finset (Fin m) // S.card = k},
      (prob U S : ℂ) * (Complex.normSq (∑ x ∈ S.1, stdAddChar (r * finEquiv m x)) : ℂ)) =
      (k : ℂ) + ∑ x : Fin m, ∑ y : Fin m,
        (((star (U x)) ⬝ᵥ (U x)) * ((star (U y)) ⬝ᵥ (U y)) -
          ((star (U x)) ⬝ᵥ (U y)) * ((star (U y)) ⬝ᵥ (U x))) * pairCharacter r x y := by
  intro U
  have hU : Uᴴ * U = 1 := selectedColumns_orthonormal a hs
  simp_rw [subsetScore, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, expected_score U hU]
  have hmass : (∑ S : {S : Finset (Fin m) // S.card = k}, (prob U S : ℂ)) = 1 := by
    exact_mod_cast total_prob U hU
  rw [hmass, one_mul]

private theorem rowEntry (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (x y : Fin m) :
    ((star (selectedColumns a s x)) ⬝ᵥ (selectedColumns a s y)) =
      (m : ℂ)⁻¹ * ∑ i : Fin k, stdAddChar (a i * (finEquiv m y - finEquiv m x)) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change star (s * stdAddChar (a i * finEquiv m x)) *
    (s * stdAddChar (a i * finEquiv m y)) = _
  rw [star_mul, star_character, mul_sub,
    sub_eq_add_neg, AddChar.map_add_eq_mul, ← hs]
  ring

private theorem diagonalEntry (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (x : Fin m) :
    ((star (selectedColumns a s x)) ⬝ᵥ (selectedColumns a s x)) = (k : ℂ) / (m : ℂ) := by
  rw [rowEntry a s hs]
  simp [div_eq_mul_inv, mul_comm]

private theorem rowEntryProduct (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (r : ZMod m) (x y : Fin m) :
    ((star (selectedColumns a s x)) ⬝ᵥ (selectedColumns a s y)) *
      ((star (selectedColumns a s y)) ⬝ᵥ (selectedColumns a s x)) *
      pairCharacter r x y =
    ((m : ℂ)⁻¹)^2 * ∑ i : Fin k, ∑ j : Fin k,
      stdAddChar ((a i - a j - r) * (finEquiv m y - finEquiv m x)) := by
  rw [rowEntry a s hs, rowEntry a s hs]
  calc
    _ = ((m : ℂ)⁻¹)^2 *
        ((∑ i : Fin k, stdAddChar (a i * (finEquiv m y - finEquiv m x))) *
          (∑ j : Fin k, stdAddChar (a j * (finEquiv m x - finEquiv m y))) *
          pairCharacter r x y) := by ring
    _ = _ := by
      congr 1
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      unfold pairCharacter
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring

private theorem sumCharacterAcrossSites (u : ZMod m) :
    (∑ x : Fin m, ∑ y : Fin m, stdAddChar (u * (finEquiv m y - finEquiv m x))) =
      if u = 0 then (m : ℂ)^2 else 0 := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : ZMod m, ∑ y : ZMod m, stdAddChar (u * (x - y)) := by
      apply Fintype.sum_equiv (finEquiv m).toEquiv
      intro x
      exact Fintype.sum_equiv (finEquiv m).toEquiv _ _ (fun y => rfl)
    _ = _ := characterDifferenceSum u

private theorem constantPairSum (k : ℕ) (r : ZMod m) :
    (∑ x : Fin m, ∑ y : Fin m, ((k : ℂ) / (m : ℂ)) *
      ((k : ℂ) / (m : ℂ)) * pairCharacter r x y) =
    if r = 0 then (k : ℂ)^2 else 0 := by
  classical
  unfold pairCharacter
  simp_rw [← Finset.mul_sum]
  rw [sumCharacterAcrossSites]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  by_cases hr : r = 0
  · subst r
    simp only [neg_zero, ite_true]
    field_simp
  · simp [hr]

private theorem kernelPairSum (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (r : ZMod m) :
    (∑ x : Fin m, ∑ y : Fin m, ((star (selectedColumns a s x)) ⬝ᵥ (selectedColumns a s y)) *
      ((star (selectedColumns a s y)) ⬝ᵥ (selectedColumns a s x)) * pairCharacter r x y) =
    (((univ.map a).filter (fun b => b - r ∈ univ.map a)).card : ℂ) := by
  classical
  simp_rw [rowEntryProduct a s hs r, ← Finset.mul_sum]
  have hreorder :
      (∑ x : Fin m, ∑ y : Fin m, ∑ i : Fin k, ∑ j : Fin k,
        stdAddChar ((a i - a j - r) * (finEquiv m y - finEquiv m x))) =
      ∑ i : Fin k, ∑ j : Fin k, ∑ x : Fin m, ∑ y : Fin m,
        stdAddChar ((a i - a j - r) * (finEquiv m y - finEquiv m x)) := by
    simp_rw [Finset.sum_comm (s := (univ : Finset (Fin m))) (t := (univ : Finset (Fin k)))]
  rw [hreorder]
  have hsite (u : ZMod m) :
      (∑ x : Fin m, ∑ y : Fin m, stdAddChar (u * (finEquiv m y - finEquiv m x))) =
      ∑ x : ZMod m, ∑ y : ZMod m, stdAddChar (u * (x-y)) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_equiv (finEquiv m).toEquiv
    intro x
    exact Fintype.sum_equiv (finEquiv m).toEquiv _ _ (fun y => rfl)
  simp_rw [hsite]
  have h := overlap (univ.map a) r
  simp_rw [Finset.sum_map] at h
  rw [h]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  field_simp

/-- The expected squared character sum equals the diagonal plus the zero-frequency
contribution minus the number of selected columns whose backward shift is selected. -/
theorem cyclic_projection_second_moment (a : Fin k ↪ ZMod m) (s : ℂ)
    (hs : star s * s = (m : ℂ)⁻¹) (r : ZMod m) :
    let U := selectedColumns a s
    (∑ S : {S : Finset (Fin m) // S.card = k},
      (prob U S : ℂ) * (Complex.normSq (∑ x ∈ S.1, stdAddChar (r * finEquiv m x)) : ℂ)) =
      (k : ℂ) + (if r = 0 then (k : ℂ)^2 else 0) -
        (((univ.map a).filter (fun b => b - r ∈ univ.map a)).card : ℂ) := by
  classical
  dsimp only
  rw [expectedSubsetScore a s hs r]
  simp_rw [sub_mul, Finset.sum_sub_distrib, diagonalEntry a s hs]
  rw [constantPairSum, kernelPairSum a s hs r, add_sub_assoc]

end D5.S3.Analytic.Oscillation.CyclicProjectionMoments

#print axioms D5.S3.Analytic.Oscillation.CyclicProjectionMoments.cyclic_projection_second_moment
