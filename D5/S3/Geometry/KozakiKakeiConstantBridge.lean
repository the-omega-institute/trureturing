/- GID: D5/S3/Geometry/KozakiKakeiConstantBridge
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiConstantBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The admissible constant-matrix level implication forces a scalar polynomial multiple. -/
import D5.S3.Geometry.KozakiKakeiPrimitive
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.FieldSimp

namespace D5.S3.Geometry.KozakiKakei
open MvPolynomial
open scoped BigOperators
noncomputable section

private def insertCoord {V : Type*} [DecidableEq V] (w : V) (t : Rest w → ℂ) (z : ℂ) (i : V) :
    ℂ :=
  Option.elim ((Equiv.optionSubtypeNe w).symm i) z t

private theorem eval_linear {V : Type*} [DecidableEq V] {w : V} {p : MvPolynomial V ℂ}
    {a b : Coeff w}
    (hp : isolate w p = Polynomial.C a * Polynomial.X + Polynomial.C b)
    (t : Rest w → ℂ) (z : ℂ) :
    eval (insertCoord w t z) p = eval t a * z + eval t b := by
  unfold insertCoord
  rw [eval_isolate, hp]
  simp

private theorem insertCoord_injective {V : Type*} [DecidableEq V] {w : V} {t : Rest w → ℂ}
    {z : ℂ} (ht : Function.Injective t) (hz : ∀ i, z ≠ t i) :
    Function.Injective (insertCoord w t z) := by
  change Function.Injective ((fun i : Option (Rest w) => i.elim z t) ∘ (Equiv.optionSubtypeNe w).symm)
  apply Function.Injective.comp _ (Equiv.optionSubtypeNe w).symm.injective
  intro i j h
  cases i <;> cases j
  · rfl
  · exact (hz _ h).elim
  · exact (hz _ h.symm).elim
  · exact congrArg some (ht h)

private theorem collision_polynomial_ne_zero {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (i : Rest (first hm)) : A hm * X i + B hm ≠ 0 := by
  intro h
  have hdiv : A hm ∣ B hm := by
    refine ⟨-X i, ?_⟩
    rw [mul_neg, eq_neg_iff_add_eq_zero, add_comm]
    exact h
  exact A_not_unit hm ((primitive_coefficients hm hm3).2 dvd_rfl hdiv)

private def exclusionPolynomial {m : ℕ} (hm : 2 ≤ m) : Coeff (first hm) :=
  A hm *
    (∏ i : Rest (first hm), ∏ j ∈ Finset.univ.erase i, diff i j) *
    (∏ i : Rest (first hm), (A hm * X i + B hm))

private theorem exclusionPolynomial_ne_zero {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3) :
    exclusionPolynomial hm ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (primitive_coefficients hm hm3).1 ?_) ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact (diff_prime (Finset.mem_erase.mp hj).1.symm).ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => collision_polynomial_ne_zero hm hm3 i

private theorem cross_identity {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (σ : Equiv.Perm (Col m))
    (h : ∀ t : Col m → ℂ, Function.Injective t → eval t (F m) = 0 →
      eval t (rename σ (F m)) = 0)
    {a b : Coeff (first hm)}
    (hq : isolate (first hm) (rename σ (F m)) = Polynomial.C a * Polynomial.X + Polynomial.C b) :
    A hm * b = B hm * a := by
  apply sub_eq_zero.mp
  have hH : exclusionPolynomial hm * (A hm * b - B hm * a) = 0 := by
    apply MvPolynomial.funext
    intro t
    rw [map_zero, map_mul]
    by_cases he : eval t (exclusionPolynomial hm) = 0
    · rw [he, zero_mul]
    have he' := he
    simp only [exclusionPolynomial, map_mul, map_prod, map_add, map_sub, diff, eval_X] at he'
    obtain ⟨he₁, he₂⟩ := mul_ne_zero_iff.mp he'
    obtain ⟨hA, hSep⟩ := mul_ne_zero_iff.mp he₁
    let z : ℂ := -(eval t (B hm)) / eval t (A hm)
    have ht : Function.Injective t := by
      intro i j htij
      by_contra hij
      exact (Finset.prod_ne_zero_iff.mp
        (Finset.prod_ne_zero_iff.mp hSep i (Finset.mem_univ _)) j
          (Finset.mem_erase.mpr ⟨fun heq => hij heq.symm, Finset.mem_univ _⟩))
            (sub_eq_zero.mpr htij.symm)
    have hzF : eval t (A hm) * z + eval t (B hm) = 0 := by
      dsimp [z]
      field_simp [hA]
      ring
    have hz : ∀ i, z ≠ t i := by
      intro i hi
      exact Finset.prod_ne_zero_iff.mp he₂ i (Finset.mem_univ _) (by rwa [← hi])
    have hq' := h (insertCoord (first hm) t z) (insertCoord_injective ht hz)
      ((eval_linear (isolate_F hm) t z).trans hzF)
    rw [eval_linear hq t z] at hq'
    have hcross :
        eval t (A hm) * eval t b - eval t (B hm) * eval t a = 0 := by
      calc
        _ = eval t (A hm) * (eval t a * z + eval t b) -
              eval t a * (eval t (A hm) * z + eval t (B hm)) := by ring
        _ = 0 := by rw [hq', hzF, mul_zero, mul_zero, sub_self]
    rw [map_sub, map_mul, map_mul, hcross, mul_zero]
  exact (mul_eq_zero.mp hH).resolve_left (exclusionPolynomial_ne_zero hm hm3)

theorem F_ne_zero {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3) : F m ≠ 0 := by
  intro h
  have he := isolate_F hm
  rw [h, map_zero] at he
  have hc := congrArg (fun p : Polynomial (Coeff (first hm)) => p.coeff 1) he
  exact (primitive_coefficients hm hm3).1 (by simpa [Polynomial.coeff_C_mul] using hc.symm)

theorem affine_polynomial_scalar {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (σ : Equiv.Perm (Col m))
    (h : ∀ t : Col m → ℂ, Function.Injective t → eval t (F m) = 0 →
      eval t (rename σ (F m)) = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ rename σ (F m) = MvPolynomial.C c * F m := by
  obtain ⟨a, b, hq⟩ := rename_F_exists_linear σ (first hm)
  have hab := cross_identity hm hm3 σ h hq
  obtain ⟨hA, hPrime⟩ := primitive_coefficients hm hm3
  have had : A hm ∣ a := hPrime.dvd_of_dvd_mul_left (hab ▸ dvd_mul_right _ _)
  obtain ⟨d, hd⟩ := had
  have hb : b = B hm * d := by
    apply mul_left_cancel₀ hA
    rw [hab, hd]
    ring
  have hmultiple : rename σ (F m) = F m * (isolate (first hm)).symm (Polynomial.C d) := by
    apply (isolate (first hm)).injective
    rw [hq, map_mul, AlgEquiv.apply_symm_apply, isolate_F hm, hd, hb, map_mul, map_mul]
    ring
  have hf := F_ne_zero hm hm3
  have hqne : rename σ (F m) ≠ 0 := by
    change (renameEquiv ℂ σ) (F m) ≠ 0
    intro hzero
    apply hf
    exact (renameEquiv ℂ σ).injective (hzero.trans (map_zero _).symm)
  let q := (isolate (first hm)).symm (Polynomial.C d)
  have hq0 : q ≠ 0 := by
    intro hzero
    exact hqne (by rw [hmultiple]; change F m * q = 0; rw [hzero, mul_zero])
  have hdegree : (rename σ (F m)).totalDegree = (F m).totalDegree :=
    totalDegree_renameEquiv σ (F m)
  rw [hmultiple, totalDegree_mul_of_isDomain hf hq0] at hdegree
  change (F m).totalDegree + q.totalDegree = (F m).totalDegree at hdegree
  have hdeg : q.totalDegree = 0 := by omega
  let c := q.coeff 0
  have hc : q = MvPolynomial.C c := totalDegree_eq_zero_iff_eq_C.mp hdeg
  refine ⟨c, ?_, ?_⟩
  · intro hzero
    exact hq0 (hc.trans (by simp [hzero]))
  · rw [hmultiple]
    change F m * q = _
    rw [hc, mul_comm]

theorem admissible_constant_matrix_scalar {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (σ : Equiv.Perm (Col m)) (hp : PreservesLevel σ) :
    ∃ c : ℂ, c ≠ 0 ∧ rename σ (F m) = MvPolynomial.C c * F m :=
  affine_polynomial_scalar hm hm3 σ (constant_matrix_implication hp)

end
end D5.S3.Geometry.KozakiKakei
