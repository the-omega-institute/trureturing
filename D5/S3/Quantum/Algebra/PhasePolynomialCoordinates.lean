/- GID: D5/S3/Quantum/Algebra/PhasePolynomialCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PhasePolynomialCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-coordinate and conjugate-coordinate polynomial correspondence with faithful evaluation. -/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

noncomputable section
open MvPolynomial Complex

namespace D5.S3.Quantum.Algebra.PhasePolynomial

abbrev Poly (ι : Type*) := MvPolynomial (ι ⊕ ι) ℂ

variable {ι : Type*}

/-- Evaluation on the actual conjugate diagonal. -/
def actual (p : Poly ι) (z : ι → ℂ) : ℂ :=
  eval (Sum.elim z (fun i => star (z i))) p

/-- Cartesian coordinates of a complex vector. -/
def cartesian (z : ι → ℂ) : ι ⊕ ι → ℂ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

/-- Substitute z=x+iy and its conjugate x-iy. -/
def toCartesian : Poly ι →ₐ[ℂ] Poly ι :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C I * X (Sum.inr i))
    (fun i => X (Sum.inl i) - C I * X (Sum.inr i)))

/-- Substitute x=(z+w)/2 and y=(z-w)/(2i). -/
def fromCartesian : Poly ι →ₐ[ℂ] Poly ι :=
  aeval (Sum.elim (fun i => C (1/2) * (X (Sum.inl i) + X (Sum.inr i)))
    (fun i => C (1/(2*I)) * (X (Sum.inl i) - X (Sum.inr i))))

private theorem cartesian_inverse_left (p : Poly ι) : fromCartesian (toCartesian p) = p := by
  have h : (fromCartesian : Poly ι →ₐ[ℂ] Poly ι).comp toCartesian = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    have hI : (C I : Poly ι)^2 = -1 := by rw [← map_pow]; norm_num
    have htwo : (2 : Poly ι) * C (1/2 : ℂ) = 1 := by
      calc
        _ = C ((2 : ℂ) * (1/2)) := by simp
        _ = 1 := by norm_num
    cases v with
    | inl i =>
      simp [toCartesian, fromCartesian, AlgHom.comp_apply]
      ring_nf
      rw [hI]
      linear_combination (X (Sum.inl i) : Poly ι) * htwo
    | inr i =>
      simp [toCartesian, fromCartesian, AlgHom.comp_apply]
      ring_nf
      rw [hI]
      linear_combination (X (Sum.inr i) : Poly ι) * htwo
  exact DFunLike.congr_fun h p

private theorem cartesian_inverse_right (p : Poly ι) : toCartesian (fromCartesian p) = p := by
  have h : (toCartesian : Poly ι →ₐ[ℂ] Poly ι).comp fromCartesian = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    have hI : (C I : Poly ι)^2 = -1 := by rw [← map_pow]; norm_num
    have htwo : (2 : Poly ι) * C (1/2 : ℂ) = 1 := by
      calc
        _ = C ((2 : ℂ) * (1/2)) := by simp
        _ = 1 := by norm_num
    cases v with
    | inl i =>
      simp [toCartesian, fromCartesian, AlgHom.comp_apply]
      ring_nf
      linear_combination (X (Sum.inl i) : Poly ι) * htwo
    | inr i =>
      simp [toCartesian, fromCartesian, AlgHom.comp_apply]
      ring_nf
      rw [hI]
      linear_combination (X (Sum.inr i) : Poly ι) * htwo
  exact DFunLike.congr_fun h p

/-- The unique change of polynomial coordinates; coefficients may be arbitrary complex numbers. -/
def cartesianEquiv : Poly ι ≃ₐ[ℂ] Poly ι :=
  AlgEquiv.ofAlgHom toCartesian fromCartesian
    (by ext p; exact cartesian_inverse_right p)
    (by ext p; exact cartesian_inverse_left p)

private theorem eval_toCartesian (p : Poly ι) (x : ι ⊕ ι → ℂ) :
    eval x (toCartesian p) =
      eval (Sum.elim (fun i => x (.inl i) + I*x (.inr i))
        (fun i => x (.inl i) - I*x (.inr i))) p := by
  have h : (aeval x).comp (toCartesian : Poly ι →ₐ[ℂ] Poly ι) =
      aeval (Sum.elim (fun i => x (.inl i) + I*x (.inr i))
        (fun i => x (.inl i) - I*x (.inr i))) := by
    apply MvPolynomial.algHom_ext
    intro v; cases v <;> simp [toCartesian]
  exact DFunLike.congr_fun h p

/-- The coordinate equivalence agrees with evaluation on every actual complex vector. -/
theorem actual_cartesian (p : Poly ι) (z : ι → ℂ) :
    eval (cartesian z) (toCartesian p) = actual p z := by
  rw [eval_toCartesian]
  apply congrArg (fun f : ι ⊕ ι → ℂ => eval f p)
  funext v
  cases v with
  | inl i => exact Complex.re_add_im (z i)
  | inr i => simp [cartesian, Complex.conj_eq_re_sub_im]

/-- No polynomial information is lost by restricting paired variables to actual conjugates. -/
theorem actual_injective : Function.Injective (actual : Poly ι → (ι → ℂ) → ℂ) := by
  intro p q hpq
  apply (cartesianEquiv : Poly ι ≃ₐ[ℂ] Poly ι).injective
  apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  have hxreal (v) : (x v).im = 0 := by
    obtain ⟨r, hr⟩ := hx v (Set.mem_univ v)
    rw [← hr]; simp
  let z : ι → ℂ := fun i => x (.inl i) + I*x (.inr i)
  have hc : cartesian z = x := by
    funext v
    cases v <;> apply Complex.ext <;> simp [cartesian, z, hxreal]
  change eval x (toCartesian p) = eval x (toCartesian q)
  rw [← hc, actual_cartesian, actual_cartesian]
  exact congrFun hpq z

private theorem totalDegree_aeval_linear (f : (ι ⊕ ι) → Poly ι)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (p : Poly ι) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  have hd := le_totalDegree hm
  rw [aeval_monomial]
  apply le_trans (totalDegree_mul _ _) ?_
  have hprod : (m.prod fun v n => f v ^ n).totalDegree ≤ m.sum (fun _ n => n) := by
    apply le_trans (totalDegree_finsetProd _ _) ?_
    apply Finset.sum_le_sum
    intro v hv
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m v) (hf v))
  simpa using hprod.trans hd

/-- Total degree is preserved, including the zero polynomial and constants. -/
theorem cartesian_totalDegree (p : Poly ι) : (toCartesian p).totalDegree = p.totalDegree := by
  have hm (i : ι) : (C I * X (Sum.inr i) : Poly ι).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  have hto (p : Poly ι) : (toCartesian p).totalDegree ≤ p.totalDegree := by
    apply totalDegree_aeval_linear
    intro v
    cases v with
    | inl i => exact (totalDegree_add _ _).trans (max_le (by simp) (hm i))
    | inr i => exact (totalDegree_sub _ _).trans (max_le (by simp) (hm i))
  have hfrom (p : Poly ι) : (fromCartesian p).totalDegree ≤ p.totalDegree := by
    apply totalDegree_aeval_linear
    intro v
    cases v with
    | inl i => exact (totalDegree_mul _ _).trans (by
        simpa using (totalDegree_add (X (Sum.inl i) : Poly ι) (X (Sum.inr i))))
    | inr i => exact (totalDegree_mul _ _).trans (by
        simpa using (totalDegree_sub (X (Sum.inl i) : Poly ι) (X (Sum.inr i))))
  exact le_antisymm (hto p) (by simpa [cartesian_inverse_left] using hfrom (toCartesian p))

end D5.S3.Quantum.Algebra.PhasePolynomial
