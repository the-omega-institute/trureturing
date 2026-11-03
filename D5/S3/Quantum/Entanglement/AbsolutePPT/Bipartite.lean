/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/Bipartite
   mirror-E: none(waiver:shared-generic-primitives)
   anchors: []
   utility: none
   digest: Shared partial transpose, all-unitary APPT and orthonormal cyclic Fourier sectors. -/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Second-factor partial transpose and all-unitary APPT on product-indexed matrices.
Cyclic sectors on residue strings carry normalized Fourier vectors, with mutually
orthogonal frequencies and disjoint normalized sector labels.
-/

set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

/-- Transpose only the second factor, with no finiteness or dimension assumption. -/
abbrev partialTranspose {A B : Type*} (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun p q => ρ (p.1,q.2) (q.1,p.2)

/-- Positivity of the second-factor partial transpose after every global unitary. -/
abbrev APPT {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ U : unitaryGroup (A × B) ℂ, partialTranspose ((U : Matrix _ _ ℂ) * M * (U : Matrix _ _ ℂ)ᴴ) |>.PosSemidef

noncomputable section

def sectorPoint {n d : ℕ} (t : ZMod d) (r : (Fin n → ZMod d)) : (Fin n → ZMod d) :=
  fun k => t + r k

def sectorCoordinate {n d : ℕ} [NeZero n] (i : (Fin n → ZMod d)) : (Fin n → ZMod d) :=
  fun k => i k - i 0

def fourierVector {n d : ℕ} [NeZero n] [NeZero d]
    (a : ZMod d) (r : (Fin n → ZMod d)) : (Fin n → ZMod d) → ℂ := by
  classical
  exact fun i => if i = sectorPoint (i 0) r then
    (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * i 0) else 0

theorem sector_coordinates {n d : ℕ} [NeZero n] (i : (Fin n → ZMod d)) :
    sectorCoordinate i 0 = 0 ∧ sectorPoint (i 0) (sectorCoordinate i) = i := by
  constructor
  · change i 0 - i 0 = 0
    exact sub_self _
  · funext k
    change i 0 + (i k - i 0) = i k
    abel

theorem sectorPoint_injective {n d : ℕ} [NeZero n]
    (r s : (Fin n → ZMod d)) (hr : r 0 = 0) (hs : s 0 = 0) (t u : ZMod d)
    (h : sectorPoint t r = sectorPoint u s) : t = u ∧ r = s := by
  have ht : t = u := by
    have h0 := congrFun h 0
    change t + r 0 = u + s 0 at h0
    simpa only [hr, hs, add_zero] using h0
  refine ⟨ht, ?_⟩
  funext k
  have hk := congrFun h k
  change t + r k = u + s k at hk
  rw [ht] at hk
  exact add_left_cancel hk

theorem fourier_at_point {n d : ℕ} [NeZero n] [NeZero d]
    (a t : ZMod d) (r : (Fin n → ZMod d)) (hr : r 0 = 0) :
    fourierVector a r (sectorPoint t r) =
      (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * t) := by
  classical
  change (if sectorPoint t r = sectorPoint (t + r 0) r then
    (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (a * (t + r 0)) else 0) = _
  rw [hr, add_zero, ite_eq_left rfl]

theorem fourier_off_sector {n d : ℕ} [NeZero n] [NeZero d]
    (a : ZMod d) (r i : (Fin n → ZMod d)) (hi : i ≠ sectorPoint (i 0) r) :
    fourierVector a r i = 0 := by
  classical
  exact ite_eq_right hi

private theorem sector_sum {n d : ℕ} [NeZero n] [NeZero d]
    (r : (Fin n → ZMod d)) (hr : r 0 = 0) (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ i, i ≠ sectorPoint (i 0) r → f i = 0) :
    ∑ i, f i = ∑ t, f (sectorPoint t r) := by
  classical
  symm
  apply Fintype.sum_of_injective (sectorPoint · r)
    (fun t u h => (sectorPoint_injective r r hr hr t u h).1) _ _
  · intro i hi
    apply hf i
    intro h
    exact hi ⟨i 0, h.symm⟩
  · intro t
    rfl

theorem sector_basis (n d : ℕ) [NeZero n] [NeZero d]
    (_hn : 2 ≤ n) (hd : 2 ≤ d) (a c : ZMod d) (r s : (Fin n → ZMod d))
    (hr : r 0 = 0) (hs : s 0 = 0) :
    star (fourierVector a r) ⬝ᵥ fourierVector c s =
      if a = c ∧ r = s then 1 else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    change (∑ i, star (fourierVector a r i) * fourierVector c r i) = _
    rw [sector_sum r hr _ (by
      intro i hi
      rw [fourier_off_sector a r i hi, star_zero, zero_mul])]
    have heach (t : ZMod d) :
        star (fourierVector a r (sectorPoint t r)) *
          fourierVector c r (sectorPoint t r) =
        ((Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
          ZMod.stdAddChar (t * (c - a)) := by
      rw [fourier_at_point a t r hr, fourier_at_point c t r hr]
      simp only [star_mul, star_inv₀]
      have hstar : star (Real.sqrt d : ℂ) = (Real.sqrt d : ℂ) :=
        Complex.conj_ofReal _
      rw [hstar]
      have hchar : star (ZMod.stdAddChar (a * t)) =
          ZMod.stdAddChar (-(a * t)) :=
        (AddChar.map_neg_eq_conj _ _).symm
      rw [hchar]
      calc
        _ = ((Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹) *
            (ZMod.stdAddChar (-(a * t)) * ZMod.stdAddChar (c * t)) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul]
          congr 2
          ring
    rw [Finset.sum_congr rfl (fun t _ => heach t)]
    rw [← Finset.mul_sum,
      AddChar.sum_mulShift (c - a) (ZMod.isPrimitive_stdAddChar d), ZMod.card]
    by_cases hac : a = c
    · subst c
      simp only [sub_self, and_true, ↓reduceIte]
      have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        apply Real.sqrt_ne_zero'.mpr
        exact_mod_cast (show 0 < d by omega)
      have hsq : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
      rw [← hsq]
      field_simp [hsqrt]
    · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hac)), ite_eq_right (by tauto)]
      simp only [Nat.cast_zero, mul_zero]
  · rw [ite_eq_right (fun h => hrs h.2)]
    change (∑ i, star (fourierVector a r i) * fourierVector c s i) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = sectorPoint (i 0) r
    · have his : i ≠ sectorPoint (i 0) s := by
        intro his
        exact hrs (sectorPoint_injective r s hr hs (i 0) (i 0) (hi.symm.trans his)).2
      rw [fourier_off_sector c s i his, mul_zero]
    · rw [fourier_off_sector a r i hi, star_zero, zero_mul]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
