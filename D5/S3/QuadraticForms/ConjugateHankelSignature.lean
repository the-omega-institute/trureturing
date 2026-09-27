/- GID: D5/S3/QuadraticForms/ConjugateHankelSignature
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ConjugateHankelSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Hankel signature equals the signed count of real-node weights. -/

import D5.S3.Constants.NewtonHankelRealRootCriterion
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Real polynomial evaluation identifies the weighted Hankel form with a form on
conjugation-compatible values and a zero form on its kernel. Real nodes give
one-dimensional blocks; every nonreal pair gives a zero or hyperbolic block.
-/

open Polynomial
open scoped BigOperators ComplexConjugate
open D5.S3.Constants.NewtonHankelRealRootCriterion
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.QuadraticForms.ConjugateHankelSignature

/-- Values on distinct nodes that respect complex conjugation. -/
def CompatibleValues (s : Finset ℂ) : Submodule ℝ (s → ℂ) where
  carrier := {v | ∀ z w : s, (w : ℂ) = conj (z : ℂ) → v w = conj (v z)}
  zero_mem' := by simp
  add_mem' := by
    intro v u hv hu z w hw
    simp only [Pi.add_apply, hv z w hw, hu z w hw, map_add]
  smul_mem' := by
    intro a v hv z w hw
    simp [Pi.smul_apply, hv z w hw, Complex.real_smul]

def evaluation (s : Finset ℂ) (d : ℕ) :
    (Fin d → ℝ) →ₗ[ℝ] CompatibleValues s where
  toFun c := ⟨fun z => vectorPolynomialValue c z, by
    intro z w hw
    simp [vectorPolynomialValue, hw, map_sum, map_mul, map_pow]⟩
  map_add' := by
    intro c b
    apply Subtype.ext
    funext z
    simp [vectorPolynomialValue, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    apply Subtype.ext
    funext z
    simp [vectorPolynomialValue, Finset.mul_sum, mul_assoc, Complex.real_smul]

def valueForm (s : Finset ℂ) (w : s → ℂ) : QuadraticForm ℝ (CompatibleValues s) :=
  Complex.reLm.compQuadraticMap (∑ z : s,
    w z • QuadraticMap.linMulLin
      ((LinearMap.proj z : (s → ℂ) →ₗ[ℝ] ℂ).comp (CompatibleValues s).subtype)
      ((LinearMap.proj z : (s → ℂ) →ₗ[ℝ] ℂ).comp (CompatibleValues s).subtype))

def weightedHankel (s : Finset ℂ) (w : s → ℂ) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ z : s, w z * (z : ℂ) ^ (i.val + j.val)).re


def conjugateBlockForm (s : Finset ℂ) (w : s → ℂ) :
    QuadraticForm ℝ (({z : s // (z : ℂ).im = 0} → ℝ) ×
      ({z : s // 0 < (z : ℂ).im} → ℂ)) :=
  (QuadraticMap.weightedSumSquares ℝ (fun z : {z : s // (z : ℂ).im = 0} =>
    (w z.val).re)).prod
    (Complex.reLm.compQuadraticMap (∑ z : {z : s // 0 < (z : ℂ).im},
      (2 * w z.val) • QuadraticMap.linMulLin
        (LinearMap.proj z : ({z : s // 0 < (z : ℂ).im} → ℂ) →ₗ[ℝ] ℂ)
        (LinearMap.proj z : ({z : s // 0 < (z : ℂ).im} → ℂ) →ₗ[ℝ] ℂ)))

def complexSquareForm (a : ℂ) : QuadraticForm ℝ ℂ :=
  Complex.reLm.compQuadraticMap
    (a • QuadraticMap.linMulLin (LinearMap.id : ℂ →ₗ[ℝ] ℂ) LinearMap.id)


/-- The integer signature is the sum of the signs of the real-node weights. -/
theorem weighted_hankel_signature (s : Finset ℂ)
    (hs : ∀ z ∈ s, conj z ∈ s) (d : ℕ) (hd : s.card ≤ d)
    (w : s → ℂ)
    (hw : ∀ z u : s, (u : ℂ) = conj (z : ℂ) → w u = conj (w z)) :
    (sigPos (weightedHankel s w d).toQuadraticForm' : ℤ) -
      (sigNeg (weightedHankel s w d).toQuadraticForm' : ℤ) =
    ∑ r : {z : s // (z : ℂ).im = 0},
      ((if 0 < (w r.val).re then (1 : ℤ) else 0) -
      (if (w r.val).re < 0 then (1 : ℤ) else 0)) := by
  classical
  have hEvaluation : Module.finrank ℝ (LinearMap.ker (evaluation s d)) = d - s.card ∧
      QuadraticMap.Equivalent (weightedHankel s w d).toQuadraticForm'
      ((valueForm s w).prod (0 : QuadraticForm ℝ (LinearMap.ker (evaluation s d)))) := by
    classical
    let Q := valueForm s w
    have hsurj : ∀ m : ℕ, s.card ≤ m → Function.Surjective (evaluation s m) := by
      intro m hm v
      let values : ℂ → ℂ := fun z => if h : z ∈ s then v.val ⟨z, h⟩ else 0
      let f : ℂ[X] := Lagrange.interpolate s id values
      have hf : ∀ z ∈ s, f.eval z = values z :=
        fun z hz => Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hz
      have hdeg : f.degree < s.card :=
        Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
      have hreal : f.map (Complex.conjAe : ℂ →+* ℂ) = f := by
        apply Lagrange.eq_interpolate_of_eval_eq _ (Set.injOn_id _)
        · rw [Polynomial.degree_map_eq_of_injective
            (f := (Complex.conjAe : ℂ →+* ℂ)) Complex.conjAe.injective f]
          exact hdeg
        · intro z hz
          have hcz := hs z hz
          have heval : (f.map (Complex.conjAe : ℂ →+* ℂ)).eval z =
              conj (f.eval (conj z)) := by
            simpa using Polynomial.eval_map_apply (p := f) (Complex.conjAe : ℂ →+* ℂ) (conj z)
          change (f.map (Complex.conjAe : ℂ →+* ℂ)).eval z = values z
          rw [heval, hf (conj z) hcz]
          have hv := v.property ⟨z, hz⟩ ⟨conj z, hcz⟩ rfl
          simp only [values, dif_pos hz, dif_pos hcz, hv]
          simp
      have hcoeff : ∀ i, ((f.coeff i).re : ℂ) = f.coeff i := by
        intro i
        apply Complex.conj_eq_iff_re.mp
        have hi := congrArg (fun p : ℂ[X] => p.coeff i) hreal
        simp only [Polynomial.coeff_map] at hi
        exact hi
      refine ⟨fun i => (f.coeff i).re, ?_⟩
      apply Subtype.ext
      funext z
      change vectorPolynomialValue (fun i : Fin m => (f.coeff i).re) z = v.val z
      have hfd : f.degree < m := hdeg.trans_le (by exact_mod_cast hm)
      have hsum := Polynomial.eval_eq_sum_degreeLTEquiv (Polynomial.mem_degreeLT.mpr hfd) (z : ℂ)
      change f.eval (z : ℂ) = ∑ i : Fin m, f.coeff i * (z : ℂ) ^ (i : ℕ) at hsum
      simp only [vectorPolynomialValue, hcoeff]
      rw [← hsum, hf (z : ℂ) z.property]
      simp [values]
    have hinj : Function.Injective (evaluation s s.card) := by
      intro a b hab
      let f : ℂ[X] := Polynomial.ofFn s.card (fun i => ((a i - b i : ℝ) : ℂ))
      have hf : f = 0 := by
        apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
          (Polynomial.ofFn_degree_lt _)
        intro z hz
        have hzv := congrArg (fun v : CompatibleValues s => v.val ⟨z, hz⟩) hab
        change vectorPolynomialValue a z = vectorPolynomialValue b z at hzv
        simp only [vectorPolynomialValue] at hzv
        simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
          Polynomial.eval_monomial, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr hzv
      funext i
      have hi := congrArg (fun p : ℂ[X] => p.coeff i.val) hf
      have hzero : ((a i - b i : ℝ) : ℂ) = 0 := by
        simpa only [f, Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt,
          Polynomial.coeff_zero] using hi
      exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hzero)
    let es := LinearEquiv.ofBijective (evaluation s s.card) ⟨hinj, hsurj _ le_rfl⟩
    have hdim : Module.finrank ℝ (CompatibleValues s) = s.card := by
      simpa using es.finrank_eq.symm
    have hker : Module.finrank ℝ (LinearMap.ker (evaluation s d)) = d - s.card := by
      have hr := (evaluation s d).finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr (hsurj d hd)] at hr
      simp [hdim] at hr
      omega
    refine ⟨hker, ?_⟩
    obtain ⟨g, hg⟩ := (evaluation s d).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (hsurj d hd))
    have hfg : ∀ v, evaluation s d (g v) = v := LinearMap.congr_fun hg
    let e : (Fin d → ℝ) ≃ₗ[ℝ] (CompatibleValues s × LinearMap.ker (evaluation s d)) :=
      { toFun := fun c => (evaluation s d c, ⟨c - g (evaluation s d c), by
          simp only [LinearMap.mem_ker, map_sub, hfg, sub_self]⟩)
        invFun := fun v => g v.1 + v.2
        left_inv := by intro c; simp
        right_inv := by
          intro v
          apply Prod.ext
          · simp [hfg]
          · apply Subtype.ext
            simp [hfg]
        map_add' := by
          intro c b
          apply Prod.ext
          · simp
          · apply Subtype.ext
            simp
            abel
        map_smul' := by
          intro a c
          apply Prod.ext
          · simp
          · apply Subtype.ext
            simp [smul_sub] }
    refine ⟨{ e with map_app' := ?_ }⟩
    intro c
    change Q (evaluation s d c) + 0 = (weightedHankel s w d).toQuadraticForm' c
    rw [add_zero]
    simp only [Q, valueForm, LinearMap.compQuadraticMap_apply, sum_apply,
      smul_apply, QuadraticMap.linMulLin_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply, Complex.reLm_coe, smul_eq_mul]
    change (∑ z : s, w z * (vectorPolynomialValue c z * vectorPolynomialValue c z)).re = _
    simp only [vectorPolynomialValue, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, smul_eq_mul]
    change (∑ z : s, ∑ i : Fin d, ∑ j : Fin d,
      (w z * ((c j : ℂ) * (z : ℂ) ^ j.val * ((c i : ℂ) * (z : ℂ) ^ i.val))).re) =
        ∑ i : Fin d, ∑ j : Fin d, c i * (c j * (weightedHankel s w d i j))
    simp only [weightedHankel, Complex.re_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro z _
    rw [pow_add]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hBlocks : QuadraticMap.Equivalent (valueForm s w) (conjugateBlockForm s w) := by
    classical
    let R := {z : s // (z : ℂ).im = 0}
    let U := {z : s // 0 < (z : ℂ).im}
    let f : CompatibleValues s →ₗ[ℝ] ((R → ℝ) × (U → ℂ)) :=
      { toFun := fun v => (fun z => (v.val z.val).re, fun z => v.val z.val)
        map_add' := by intro v b; ext z <;> simp
        map_smul' := by intro a v; ext z <;> simp }
    have hinj : Function.Injective f := by
      intro v b hvb
      apply Subtype.ext
      funext z
      by_cases hz : (z : ℂ).im = 0
      · have hcz : (z : ℂ) = conj (z : ℂ) := by apply Complex.ext <;> simp [hz]
        have hv := Complex.conj_eq_iff_re.mp (v.property z z hcz).symm
        have hb := Complex.conj_eq_iff_re.mp (b.property z z hcz).symm
        have he := congrArg (fun t : (R → ℝ) × (U → ℂ) => t.1 ⟨z, hz⟩) hvb
        change (v.val z).re = (b.val z).re at he
        rw [← hv, ← hb, he]
      · by_cases hp : 0 < (z : ℂ).im
        · exact congrArg (fun t : (R → ℝ) × (U → ℂ) => t.2 ⟨z, hp⟩) hvb
        · let cz : s := ⟨conj z, hs z z.property⟩
          have hcp : 0 < (cz : ℂ).im := by
            simp only [cz, Complex.conj_im]
            exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hz)
          have he := congrArg (fun t : (R → ℝ) × (U → ℂ) => t.2 ⟨cz, hcp⟩) hvb
          change v.val cz = b.val cz at he
          rw [v.property z cz rfl, b.property z cz rfl] at he
          exact (starRingEnd ℂ).injective he
    have hsurj : Function.Surjective f := by
      intro t
      let v : s → ℂ := fun z =>
        if hz : (z : ℂ).im = 0 then (t.1 ⟨z, hz⟩ : ℂ)
        else if hp : 0 < (z : ℂ).im then t.2 ⟨z, hp⟩
        else conj (t.2 ⟨⟨conj z, hs z z.property⟩, by
          simp only [Complex.conj_im]; exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hz)⟩)
      have hv : v ∈ CompatibleValues s := by
        intro z u hu
        have hi : (u : ℂ).im = -(z : ℂ).im := by rw [hu, Complex.conj_im]
        by_cases hz : (z : ℂ).im = 0
        · have hu0 : (u : ℂ).im = 0 := by rw [hi, hz]; simp
          have huz : u = z := by apply Subtype.ext; rw [hu]; apply Complex.ext <;> simp [hz]
          subst u
          simp [v, hz]
        · have hu0 : (u : ℂ).im ≠ 0 := by rw [hi]; exact neg_ne_zero.mpr hz
          by_cases hp : 0 < (z : ℂ).im
          · have hun : ¬ 0 < (u : ℂ).im := by rw [hi]; linarith
            have hcz : (⟨conj u, hs u u.property⟩ : s) = z := by
              apply Subtype.ext
              simp [hu]
            simp only [v, dif_neg hu0, dif_neg hun, dif_neg hz, dif_pos hp]
            exact congrArg (fun a : U => conj (t.2 a)) (Subtype.ext hcz)
          · have hup : 0 < (u : ℂ).im := by
              rw [hi]
              exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hz)
            have hcz : (⟨conj z, hs z z.property⟩ : s) = u := Subtype.ext hu.symm
            simp only [v, dif_neg hu0, dif_pos hup, dif_neg hz, dif_neg hp]
            rw [starRingEnd_self_apply]
            apply congrArg t.2
            apply Subtype.ext
            exact hcz.symm
      refine ⟨⟨v, hv⟩, ?_⟩
      apply Prod.ext
      · funext z
        change (v z.val).re = t.1 z
        simp [v, z.property]
      · funext z
        change v z.val = t.2 z
        have hz : (z.val : ℂ).im ≠ 0 := ne_of_gt z.property
        simp [v, hz, z.property]
    let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨{ e with map_app' := ?_ }⟩
    intro v
    let L := {z : s // (z : ℂ).im < 0}
    let F : s → ℝ := fun z => (w z * (v.val z)^2).re
    let ec : L ≃ U :=
      { toFun := fun z => ⟨⟨conj z.val, hs z.val z.val.property⟩, by
          simp only [Complex.conj_im]; exact neg_pos.mpr z.property⟩
        invFun := fun z => ⟨⟨conj z.val, hs z.val z.val.property⟩, by
          simp only [Complex.conj_im]; exact neg_neg_of_pos z.property⟩
        left_inv := by intro z; apply Subtype.ext; apply Subtype.ext; simp
        right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; simp }
    have hpair : (∑ z : L, F z.val) = ∑ z : U, F z.val := by
      apply Fintype.sum_equiv ec
      intro z
      dsimp [F]
      have hwu := hw z.val (ec z).val rfl
      have hvu := v.property z.val (ec z).val rfl
      rw [hwu, hvu, ← map_pow, ← map_mul, Complex.conj_re]
    have hparts : (∑ z : R, F z.val) + (∑ z : U, F z.val) +
        (∑ z : L, F z.val) = ∑ z : s, F z := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun z : s => (z : ℂ).im = 0))
        (by simp) F,
        ← Finset.sum_subtype (Finset.univ.filter (fun z : s => 0 < (z : ℂ).im))
        (by simp) F,
        ← Finset.sum_subtype (Finset.univ.filter (fun z : s => (z : ℂ).im < 0))
        (by simp) F]
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rcases lt_trichotomy (z : ℂ).im 0 with hz | hz | hz
      · simp [hz, ne_of_lt hz, not_lt.mpr hz.le]
      · simp [hz]
      · simp [hz, ne_of_gt hz, not_lt.mpr hz.le]
    have hreal (z : R) : F z.val = (w z.val).re * (v.val z.val).re ^ 2 := by
      have hcz : (z.val : ℂ) = conj (z.val : ℂ) := by
        apply Complex.ext <;> simp [z.property]
      have hv := Complex.conj_eq_iff_re.mp (v.property z.val z.val hcz).symm
      dsimp [F]
      rw [← hv]
      simp [pow_two]
    have heq : (valueForm s w) v = (∑ z : R, (w z.val).re * (v.val z.val).re ^ 2) +
        2 * ∑ z : U, (w z.val * (v.val z.val)^2).re := by
      have hp := hparts
      rw [hpair] at hp
      simp only [hreal] at hp
      have hvapp : (valueForm s w) v = ∑ z : s, F z := by
        simp [valueForm, F, pow_two]
      rw [hvapp]
      dsimp only [F] at hp ⊢
      linarith
    rw [heq]
    change conjugateBlockForm s w ((fun z : R => (v.val z.val).re),
      (fun z : U => v.val z.val)) = _
    simp only [conjugateBlockForm, QuadraticMap.prod_apply,
      QuadraticMap.weightedSumSquares_apply, LinearMap.compQuadraticMap_apply,
      sum_apply, smul_apply, QuadraticMap.linMulLin_apply,
      LinearMap.proj_apply, Complex.reLm_coe, smul_eq_mul, pow_two,
      Complex.re_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro z _
      simp [mul_assoc]
  have hComplex (a : ℂ) : QuadraticMap.Equivalent (complexSquareForm a)
      (QuadraticMap.weightedSumSquares ℝ
        (fun i : Fin 2 => if a = 0 then (0 : ℝ) else if i = 0 then 1 else -1)) := by
    classical
    obtain ⟨b, hb, hbn⟩ : ∃ b : ℂ, (a ≠ 0 → b^2 = a) ∧ b ≠ 0 := by
      by_cases ha : a = 0
      · exact ⟨1, fun h => (h ha).elim, one_ne_zero⟩
      · obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by decide)
        refine ⟨b, fun _ => hb, ?_⟩
        intro h
        simp [h] at hb
        exact ha hb.symm
    let e : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun z => ![(b*z).re, (b*z).im]
        invFun := fun c => b⁻¹ * ((c 0 : ℂ) + (c 1 : ℂ) * Complex.I)
        left_inv := by
          intro z
          change b⁻¹ * (((b*z).re : ℂ) + ((b*z).im : ℂ)*Complex.I) = z
          rw [Complex.re_add_im, ← mul_assoc, inv_mul_cancel₀ hbn, one_mul]
        right_inv := by
          intro c
          funext i
          fin_cases i <;> simp [hbn]
        map_add' := by intro z u; ext i; fin_cases i <;> simp [mul_add]
        map_smul' := by
          intro r z
          ext i
          fin_cases i <;> simp [Complex.real_smul, mul_left_comm] <;> ring }
    refine ⟨{ e with map_app' := ?_ }⟩
    intro z
    by_cases ha : a = 0
    · simp [complexSquareForm, ha, QuadraticMap.weightedSumSquares_apply]
    · have heval : (a * (z*z)).re = (b*z).re^2 - (b*z).im^2 := by
        rw [← hb ha]
        have hc : b^2 * (z*z) = (b*z)*(b*z) := by ring
        rw [hc, Complex.mul_re]
        ring
      simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two,
        ha, if_false, if_true, smul_eq_mul, (by decide : (1 : Fin 2) ≠ 0)]
      change 1 * ((b*z).re * (b*z).re) + (-1) * ((b*z).im * (b*z).im) =
        (a * (z*z)).re
      rw [heval]
      ring
  classical
  let R := {z : s // (z : ℂ).im = 0}
  let U := {z : s // 0 < (z : ℂ).im}
  let K := LinearMap.ker (evaluation s d)
  let N := d - s.card
  let I := R ⊕ ((U × Fin 2) ⊕ Fin N)
  let a : U → ℂ := fun u => 2 * w u.val
  let b : U → Fin 2 → ℝ := fun u i =>
    if a u = 0 then 0 else if i = 0 then 1 else -1
  let W : I → ℝ := Sum.elim (fun r : R => (w r.val).re)
    (Sum.elim (fun j : U × Fin 2 => b j.1 j.2) (fun _ => 0))
  have hlocal (u : U) : QuadraticMap.Equivalent (complexSquareForm (a u))
      (QuadraticMap.weightedSumSquares ℝ (b u)) := hComplex (a u)
  let eu (u : U) := (Classical.choice (hlocal u)).toLinearEquiv
  let ek : K ≃ₗ[ℝ] (Fin N → ℝ) := by
    change K ≃ₗ[ℝ] (Fin (d - s.card) → ℝ)
    rw [← hEvaluation.1]
    exact (Module.finBasis ℝ K).equivFun
  let e : (((R → ℝ) × (U → ℂ)) × K) ≃ₗ[ℝ] (I → ℝ) :=
    { toFun := fun v => Sum.elim v.1.1
        (Sum.elim (fun j : U × Fin 2 => eu j.1 (v.1.2 j.1) j.2) (ek v.2))
      invFun := fun f => ((fun r => f (.inl r),
        fun u => (eu u).symm (fun i => f (.inr (.inl (u,i))))),
        ek.symm (fun j => f (.inr (.inr j))))
      left_inv := by intro v; simp
      right_inv := by
        intro f
        funext i
        rcases i with r | (⟨u,i⟩ | j) <;> simp
      map_add' := by
        intro v x
        funext i
        rcases i with r | (⟨u,i⟩ | j) <;> simp
      map_smul' := by
        intro c v
        funext i
        rcases i with r | (⟨u,i⟩ | j)
        · rfl
        · exact congrFun ((eu u).map_smul c (v.1.2 u)) i
        · exact congrFun (ek.map_smul c v.2) j }
  have hdiag : QuadraticMap.Equivalent
      ((conjugateBlockForm s w).prod (0 : QuadraticForm ℝ K))
      (QuadraticMap.weightedSumSquares ℝ W) := by
    refine ⟨{ e with map_app' := ?_ }⟩
    intro v
    have hb (u : U) : ∑ i : Fin 2, b u i * (eu u (v.1.2 u) i * eu u (v.1.2 u) i) =
        (a u * (v.1.2 u * v.1.2 u)).re := by
      exact (Classical.choice (hlocal u)).map_app (v.1.2 u)
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    change (∑ i : I, W i * (e v i * e v i)) = _
    simp only [I, Fintype.sum_sum_type, Fintype.sum_prod_type, W, e,
      LinearEquiv.coe_mk, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero]
    change (∑ r : R, (w r.val).re * (v.1.1 r * v.1.1 r)) +
      (∑ u : U, ∑ i : Fin 2, b u i * (eu u (v.1.2 u) i * eu u (v.1.2 u) i)) = _
    simp_rw [hb]
    simp [conjugateBlockForm, QuadraticMap.weightedSumSquares_apply,
      K, a, mul_assoc]
    rfl
  have hE := hEvaluation.2.trans ((hBlocks.prod (QuadraticMap.Equivalent.refl
    (0 : QuadraticForm ℝ K))).trans hdiag)
  have hc (P : I → Prop) : (({i | P i}.ncard : ℕ) : ℤ) =
      ∑ i : I, if P i then (1 : ℤ) else 0 := by
    simp [Set.ncard_eq_toFinset_card']
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hE,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares hE, hc, hc,
    ← Finset.sum_sub_distrib]
  simp only [I, Fintype.sum_sum_type, Fintype.sum_prod_type, W,
    Sum.elim_inl, Sum.elim_inr, lt_self_iff_false, if_false,
    sub_self, Finset.sum_const_zero, add_zero]
  have hz : ∑ u : U, ∑ i : Fin 2,
      ((if 0 < b u i then (1 : ℤ) else 0) -
      (if b u i < 0 then (1 : ℤ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    rw [Fin.sum_univ_two]
    by_cases ha : a u = 0 <;> norm_num [b, ha]
  change (∑ r : R, ((if 0 < (w r.val).re then (1 : ℤ) else 0) -
    (if (w r.val).re < 0 then (1 : ℤ) else 0))) +
    (∑ u : U, ∑ i : Fin 2, ((if 0 < b u i then (1 : ℤ) else 0) -
      (if b u i < 0 then (1 : ℤ) else 0))) = _
  rw [hz, add_zero]

end D5.S3.QuadraticForms.ConjugateHankelSignature
