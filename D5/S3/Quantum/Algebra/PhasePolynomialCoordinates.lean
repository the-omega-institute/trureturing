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

/-! Inverse linear polynomial substitutions and their actual evaluations. -/

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
      have hh : (C (2 : ℂ) : Poly ι) * C (1/2 : ℂ) = 1 := by
        rw [← map_mul]
        norm_num
      simpa only [map_ofNat] using hh
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
      have hh : (C (2 : ℂ) : Poly ι) * C (1/2 : ℂ) = 1 := by
        rw [← map_mul]
        norm_num
      simpa only [map_ofNat] using hh
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
    (by apply DFunLike.ext; intro p; exact cartesian_inverse_right p)
    (by apply DFunLike.ext; intro p; exact cartesian_inverse_left p)

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
  | inl i => simpa [cartesian, mul_comm] using Complex.re_add_im (z i)
  | inr i => apply Complex.ext <;> simp [cartesian]

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
        rw [totalDegree_C, zero_add]
        simpa using (totalDegree_add (X (Sum.inl i) : Poly ι) (X (Sum.inr i))))
    | inr i => exact (totalDegree_mul _ _).trans (by
        rw [totalDegree_C, zero_add]
        simpa using (totalDegree_sub (X (Sum.inl i) : Poly ι) (X (Sum.inr i))))
  exact le_antisymm (hto p) (by simpa [cartesian_inverse_left] using hfrom (toCartesian p))

/-- Every polynomial in real coordinates has one faithful expansion in z and its conjugate. -/
theorem real_coordinates_unique (q : Poly ι) :
    ∃! p : Poly ι, ∀ z, actual p z = eval (cartesian z) q := by
  have he (z) : actual (fromCartesian q) z = eval (cartesian z) q := by
    rw [← actual_cartesian, cartesian_inverse_right]
  refine ⟨fromCartesian q, he, ?_⟩
  intro p hp
  apply actual_injective
  funext z
  exact (hp z).trans (he z).symm

/-- Homogeneous degree is preserved by the two inverse linear substitutions. -/
theorem cartesian_homogeneous (p : Poly ι) (n : ℕ) :
    (toCartesian p).IsHomogeneous n ↔ p.IsHomogeneous n := by
  have hto (p : Poly ι) (hp : p.IsHomogeneous n) : (toCartesian p).IsHomogeneous n := by
    have hg (v : ι ⊕ ι) :
        (Sum.elim (fun i => X (Sum.inl i) + C I * X (Sum.inr i))
          (fun i => X (Sum.inl i) - C I * X (Sum.inr i)) v : Poly ι).IsHomogeneous 1 := by
      cases v
      · exact (isHomogeneous_X ℂ _).add ((isHomogeneous_X ℂ _).C_mul I)
      · exact (isHomogeneous_X ℂ _).sub ((isHomogeneous_X ℂ _).C_mul I)
    simpa [toCartesian] using hp.aeval _ hg
  have hfrom (p : Poly ι) (hp : p.IsHomogeneous n) : (fromCartesian p).IsHomogeneous n := by
    have hg (v : ι ⊕ ι) :
        (Sum.elim (fun i => C (1/2) * (X (Sum.inl i) + X (Sum.inr i)))
          (fun i => C (1/(2*I)) * (X (Sum.inl i) - X (Sum.inr i))) v : Poly ι).IsHomogeneous 1 := by
      cases v
      · exact ((isHomogeneous_X ℂ _).add (isHomogeneous_X ℂ _)).C_mul _
      · exact ((isHomogeneous_X ℂ _).sub (isHomogeneous_X ℂ _)).C_mul _
    simpa [fromCartesian] using hp.aeval _ hg
  exact ⟨fun hp => by simpa [cartesian_inverse_left] using hfrom _ hp, hto p⟩

end D5.S3.Quantum.Algebra.PhasePolynomial
