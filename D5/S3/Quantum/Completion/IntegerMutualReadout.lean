/- GID: D5/S3/Quantum/Completion/IntegerMutualReadout
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/IntegerMutualReadout
   mirror-E: none(waiver:universal-kernel-budget)
   anchors: []
   utility: none
   digest: Gaussian integer mutual budgets characterize the original positive kernel. -/

import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Finsupp.Basic

/-! Mutual budgets on arbitrary raw complex kernels. -/

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.IntegerMutualReadout

/-- Comparison of two formal recipes, with conjugation in the first argument. -/
def readout {X R : Type*} [Zero R] (e : R → ℂ) (K : X → X → ℂ)
    (f g : X →₀ R) : ℂ :=
  f.sum fun x a => g.sum fun y b => star (e a) * K x y * e b

/-- All finite supports and every coefficient in the indicated coordinate domain. -/
def Budget {X R : Type*} [Zero R] (e : R → ℂ) (K : X → X → ℂ) : Prop :=
  ∀ f g : X →₀ R,
    2 * (readout e K f g).re ≤ (readout e K f f).re + (readout e K g g).re

/-- Rational real and imaginary coordinates for the coefficient field Q(i). -/
def rationalComplex (r : ℚ × ℚ) : ℂ := (r.1 : ℂ) + (r.2 : ℂ) * Complex.I

private def form {I : Type*} [Fintype I] (M : Matrix I I ℂ) (u v : I → ℂ) : ℂ :=
  ∑ i, ∑ j, star (u i) * M i j * v j

private theorem form_scale {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (a b : ℂ) (u v : I → ℂ) :
    form M (fun i => a * u i) (fun i => b * v i) = star a * b * form M u v := by
  simp only [form, star_mul, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  ring

private theorem rational_budget {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (h : ∀ u v : I → GaussianInt,
      2 * (form M (fun i => (u i : ℂ)) (fun i => (v i : ℂ))).re ≤
        (form M (fun i => (u i : ℂ)) (fun i => (u i : ℂ))).re +
        (form M (fun i => (v i : ℂ)) (fun i => (v i : ℂ))).re)
    (u v : I → ℚ × ℚ) :
    2 * (form M (fun i => rationalComplex (u i)) (fun i => rationalComplex (v i))).re ≤
      (form M (fun i => rationalComplex (u i)) (fun i => rationalComplex (u i))).re +
      (form M (fun i => rationalComplex (v i)) (fun i => rationalComplex (v i))).re := by
  classical
  let A : Matrix (I × Bool) Bool ℚ := fun p b =>
    let r := if p.2 then v p.1 else u p.1
    if b then r.2 else r.1
  let d : ℝ := A.den
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast A.den_ne_zero
  have hs (p : I × Bool) (b : Bool) :
      (A.num p b : ℝ) = d * (A p b : ℝ) := by
    have hq : (A.num p b : ℝ) / (A.den : ℝ) = (A p b : ℝ) := by
      exact_mod_cast A.num_div_den p b
    exact ((div_eq_iff hd).mp hq).trans (mul_comm _ _)
  let U : I → GaussianInt := fun i => ⟨A.num (i, false) false, A.num (i, false) true⟩
  let V : I → GaussianInt := fun i => ⟨A.num (i, true) false, A.num (i, true) true⟩
  have hU (i : I) : (U i : ℂ) = (d : ℂ) * rationalComplex (u i) := by
    apply Complex.ext <;> simp [U, rationalComplex, GaussianInt.toComplex_def,
      Complex.mul_re, Complex.mul_im, hs, A]
  have hV (i : I) : (V i : ℂ) = (d : ℂ) * rationalComplex (v i) := by
    apply Complex.ext <;> simp [V, rationalComplex, GaussianInt.toComplex_def,
      Complex.mul_re, Complex.mul_im, hs, A]
  have hh := h U V
  simp_rw [hU, hV, form_scale] at hh
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  have hd2 : 0 < d * d := mul_self_pos.mpr hd
  nlinarith

private theorem complex_budget {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (h : ∀ u v : I → GaussianInt,
      2 * (form M (fun i => (u i : ℂ)) (fun i => (v i : ℂ))).re ≤
        (form M (fun i => (u i : ℂ)) (fun i => (u i : ℂ))).re +
        (form M (fun i => (v i : ℂ)) (fun i => (v i : ℂ))).re) :
    ∀ u v : I → ℂ, 2 * (form M u v).re ≤ (form M u u).re + (form M v v).re := by
  let ratVector : (I → ℚ × ℚ) → (I → ℂ) := fun r i => rationalComplex (r i)
  have hd : DenseRange rationalComplex := by
    have he : rationalComplex = Complex.equivRealProdCLM.symm ∘
        Prod.map (fun r : ℚ => (r : ℝ)) (fun r : ℚ => (r : ℝ)) := by
      funext r
      apply Complex.ext <;> simp [rationalComplex]
    rw [he]
    exact (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
      Complex.equivRealProdCLM.symm.continuous
  have hv : DenseRange ratVector := DenseRange.piMap (fun _ => hd)
  have hc : IsClosed {p : (I → ℂ) × (I → ℂ) |
      2 * (form M p.1 p.2).re ≤ (form M p.1 p.1).re + (form M p.2 p.2).re} := by
    apply isClosed_le <;> unfold form <;> fun_prop
  intro u v
  exact (hv.prodMap hv).induction_on
    (p := fun p => 2 * (form M p.1 p.2).re ≤
      (form M p.1 p.1).re + (form M p.2 p.2).re)
    (u, v) hc (fun p => rational_budget M h p.1 p.2)

private theorem budget_self_real {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (h : ∀ u v : I → ℂ, 2 * (form M u v).re ≤ (form M u u).re + (form M v v).re)
    (u : I → ℂ) : (form M u u).im = 0 := by
  let z := form M u u
  have ht (t : ℝ) : 0 ≤ z.re + 2 * t * z.im := by
    have hh := h (fun i => (t : ℂ) * u i)
      (fun i => ((t : ℂ) + Complex.I) * u i)
    simp only [form_scale, Complex.star_def, map_add, Complex.conj_ofReal, Complex.conj_I,
      Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hh
    dsimp [z]
    nlinarith [hh]
  by_contra hn
  have hh := ht (-(z.re + 1) / (2 * z.im))
  have he : 2 * (-(z.re + 1) / (2 * z.im)) * z.im = -(z.re + 1) := by
    have hz : z.im ≠ 0 := hn
    field_simp [hz]
  rw [he] at hh
  linarith

private theorem finite_positive_of_budget {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (h : ∀ u v : I → ℂ, 2 * (form M u v).re ≤ (form M u u).re + (form M v v).re) :
    M.PosSemidef := by
  classical
  have hreal := budget_self_real M h
  have hh : M.IsHermitian := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
    intro v
    apply Complex.conj_eq_iff_im.mpr
    have hv := hreal (WithLp.ofLp v)
    have he : inner ℂ (M.toEuclideanLin v) v =
        star (form M (WithLp.ofLp v) (WithLp.ofLp v)) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, form, Matrix.toEuclideanLin,
        Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm]
    rw [he]
    simpa using hv
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro u
  have hp := h u 0
  have hp' : 0 ≤ (form M u u).re := by simpa [form] using hp
  apply Complex.nonneg_iff.mpr
  simpa [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    And.intro hp' (hreal u).symm

private theorem finite_budget_of_positive {I : Type*} [Fintype I] (M : Matrix I I ℂ)
    (hM : M.PosSemidef) (u v : I → ℂ) :
    2 * (form M u v).re ≤ (form M u u).re + (form M v v).re := by
  have hp := hM.dotProduct_mulVec_nonneg (u - v)
  have hr := hp.1
  have hs : (form M v u).re = (form M u v).re := by
    have he : star (form M u v) = form M v u := by
      simp only [form, star_sum, star_mul, star_star]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hM.isHermitian.apply i j]
      ring
    exact congrArg Complex.re he |>.symm
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.sub_apply, star_sub,
    Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, mul_sub] at hr
  have hr' : 0 ≤ (form M u u - form M v u - (form M u v - form M v v)).re := by
    simpa only [form, mul_assoc, Complex.zero_re] using hr
  simp only [Complex.sub_re] at hr'
  linarith

private theorem readout_on_support {X R : Type*} [Zero R] (e : R → ℂ) (he : e 0 = 0)
    (K : X → X → ℂ) (f g : X →₀ R) (S : Finset X)
    (hf : f.support ⊆ S) (hg : g.support ⊆ S) :
    readout e K f g = form (Matrix.of (fun i j : S => K i j))
      (fun i => e (f i)) (fun i => e (g i)) := by
  classical
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, star (e (f i)) * K i j * e (g j) := by
      unfold readout
      rw [Finsupp.sum_of_support_subset f hf _ (by intro i hi; simp [he])]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finsupp.sum_of_support_subset g hg _ (by intro j hj; simp [he])
    _ = _ := by
      unfold form
      symm
      calc
        _ = ∑ i : S, ∑ j ∈ S, star (e (f i)) * K i j * e (g j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_coe_sort S (fun j => star (e (f i.val)) * K i.val j * e (g j))
        _ = _ := Finset.sum_coe_sort S
          (fun i => ∑ j ∈ S, star (e (f i)) * K i j * e (g j))

private theorem readout_embedded {X R I : Type*} [Zero R] [Fintype I]
    (e : R → ℂ) (he : e 0 = 0) (K : X → X → ℂ) (L : I ↪ X) (u v : I → R) :
    readout e K ((Finsupp.equivFunOnFinite.symm u).embDomain L)
      ((Finsupp.equivFunOnFinite.symm v).embDomain L) =
      form (Matrix.of (fun i j => K (L i) (L j))) (fun i => e (u i)) (fun i => e (v i)) := by
  classical
  simp only [readout, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by intro i; simp [he])]
  unfold form
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.sum_fintype _ _ (by intro j; simp [he])]
  rfl

private theorem positive_of_integer_budget {X : Type*} (K : X → X → ℂ)
    (h : Budget (fun z : GaussianInt => (z : ℂ)) K) : (Matrix.of K).PosSemidef := by
  classical
  have hfin (S : Finset X) : (Matrix.of (fun i j : S => K i j)).PosSemidef := by
    apply finite_positive_of_budget
    apply complex_budget
    intro u v
    let L : S ↪ X := Function.Embedding.subtype _
    have hh := h ((Finsupp.equivFunOnFinite.symm u).embDomain L)
      ((Finsupp.equivFunOnFinite.symm v).embDomain L)
    simpa only [readout_embedded _ GaussianInt.toComplex_zero, L,
      Function.Embedding.subtype_apply] using hh
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    have hh := (hfin {x, y}).isHermitian
    exact hh.apply ⟨x, by simp⟩ ⟨y, by simp⟩
  · intro f
    change 0 ≤ readout id K f f
    rw [readout_on_support id rfl K f f f.support (Finset.Subset.refl _)
      (Finset.Subset.refl _)]
    simpa only [form, dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply,
      Finset.mul_sum, mul_assoc, id_eq] using
      (hfin f.support).dotProduct_mulVec_nonneg (fun i : f.support => f i)

private theorem budget_of_positive {X R : Type*} [Zero R]
    (e : R → ℂ) (he : e 0 = 0) (K : X → X → ℂ)
    (hK : (Matrix.of K).PosSemidef) : Budget e K := by
  classical
  intro f g
  let S := f.support ∪ g.support
  have hf : f.support ⊆ S := Finset.subset_union_left
  have hg : g.support ⊆ S := Finset.subset_union_right
  rw [readout_on_support e he K f g S hf hg,
    readout_on_support e he K f f S hf hf, readout_on_support e he K g g S hg hg]
  exact finite_budget_of_positive _ (hK.submatrix (fun i : S => i.val)) _ _

private theorem budget_transfer {X R S : Type*} [Zero R] [Zero S]
    (e : R → ℂ) (d : S → ℂ) (hd : d 0 = 0) (c : R → S) (hc : c 0 = 0)
    (he : ∀ r, d (c r) = e r) (K : X → X → ℂ) (h : Budget d K) : Budget e K := by
  have hx (f g : X →₀ R) :
      readout d K (f.mapRange c hc) (g.mapRange c hc) = readout e K f g := by
    unfold readout
    rw [Finsupp.sum_mapRange_index (by intro x; simp [hd])]
    apply Finsupp.sum_congr
    intro x hx
    rw [Finsupp.sum_mapRange_index (by intro y; simp [hd])]
    simp only [he]
  intro f g
  simpa only [hx] using h (f.mapRange c hc) (g.mapRange c hc)

/-- C130 Theorem 2.3: all three coefficient budgets characterize the same
Hermitian positive-type raw kernel on an arbitrary, possibly empty label type. -/
theorem mutual_budget_iff_positive_type {X : Type*} (K : X → X → ℂ) :
    (Budget (fun z : GaussianInt => (z : ℂ)) K ↔ (Matrix.of K).PosSemidef) ∧
    (Budget rationalComplex K ↔ (Matrix.of K).PosSemidef) ∧
    (Budget id K ↔ (Matrix.of K).PosSemidef) := by
  have hi := positive_of_integer_budget K
  have hr : Budget rationalComplex K → Budget (fun z : GaussianInt => (z : ℂ)) K := by
    apply budget_transfer _ rationalComplex (by simp [rationalComplex])
      (fun z : GaussianInt => ((z.re : ℚ), (z.im : ℚ)))
    · rfl
    · intro z
      simp [rationalComplex, GaussianInt.toComplex_def]
  have hc : Budget id K → Budget (fun z : GaussianInt => (z : ℂ)) K :=
    budget_transfer _ id rfl (fun z : GaussianInt => (z : ℂ))
      GaussianInt.toComplex_zero (fun _ => rfl) K
  exact ⟨⟨hi, budget_of_positive _ GaussianInt.toComplex_zero K⟩,
    ⟨fun h => hi (hr h), budget_of_positive _ (by simp [rationalComplex]) K⟩,
    ⟨fun h => hi (hc h), budget_of_positive (id : ℂ → ℂ) rfl K⟩⟩

end D5.S3.Quantum.Completion.IntegerMutualReadout
