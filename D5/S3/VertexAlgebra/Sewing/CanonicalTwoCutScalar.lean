/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutScalar
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalTwoCutScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute summability of the literal canonical two-cut scalar. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutOccupation
import Batteries.Tactic.OpenPrivate

/-! Factorial cancellation and absolute convergence for two internal occupations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalTwoCutScalar

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial LatticeAllStateField
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents FieldNormalProduct
open CanonicalOccupationSewing
open scoped BigOperators VertexOperator

open private wordMap wordCoeff rowWeight rowWeight_nonneg word_row_bound
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private factorialEnvelope factorialEnvelope_nonneg factorialEnvelope_summable
  factorialEnvelope_mul polynomial_geometric_bound columnWeight columnWeight_nonneg
  word_column_bound canonical_basis_input_expansion canonical_coefficient_expansion
  inner_coefficient_expansion
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
open private mixedEnvelope overlapBinomial chooseKernel chooseKernel_eq_prod
  mixedEnvelope_eq_sum translationEnvelope translationEnvelope_zero
  mixedConstant mixedRadius mixedEnergy mixedConstant_nonneg mixed_descendant_bound
  from D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutOccupation

noncomputable section

private theorem factorialEnvelope_prod (D : LatticeData) (B : ℝ) (d : Occ D)
    (S : Finset (Index D)) (hS : d.support ⊆ S) :
    factorialEnvelope D B d = ∏ x ∈ S,
      (B / (x.2+1 : ℝ)) ^ d x / ((d x).factorial : ℝ) := by
  classical
  have hh : factorialEnvelope D B d = d.prod (fun x n =>
      (B / (x.2+1 : ℝ)) ^ n / (n.factorial : ℝ)) := by
    unfold factorialEnvelope FactorialFockMetric.weight Finsupp.prod
    rw [Nat.cast_prod, Finset.prod_div_distrib]
  rw [hh]
  exact Finsupp.prod_of_support_subset d hS _ (by simp)

private theorem factorial_binomial_cancel (D : LatticeData) (B : ℝ) (u w : Occ D) :
    chooseKernel D (u+w) u * factorialEnvelope D B (u+w) =
      factorialEnvelope D B u * factorialEnvelope D B w := by
  classical
  let S := u.support ∪ w.support
  have hu : u.support ⊆ S := Finset.subset_union_left
  have hw : w.support ⊆ S := Finset.subset_union_right
  have hs : (u+w).support ⊆ S := Finsupp.support_add
  rw [chooseKernel_eq_prod D (u+w) u S hu,
    factorialEnvelope_prod D B (u+w) S hs, factorialEnvelope_prod D B u S hu,
    factorialEnvelope_prod D B w S hw, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Finsupp.add_apply, pow_add]
  have hfact : ((u x + w x).choose (u x) : ℝ) *
      ((u x).factorial : ℝ) * ((w x).factorial : ℝ) =
      ((u x + w x).factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using
      Nat.add_choose_mul_factorial_mul_factorial (w x) (u x))
  have hu0 : ((u x).factorial : ℝ) ≠ 0 := by positivity
  have hw0 : ((w x).factorial : ℝ) ≠ 0 := by positivity
  have he0 : ((u x + w x).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← hfact]
  ring

private theorem overlap_cancellation (D : LatticeData) (L B A T : ℝ) (u v w : Occ D) :
    L ^ (u+v).degree * factorialEnvelope D B (u+w) *
        (translationEnvelope D T (u+w) u * factorialEnvelope D A ((u+v)-u)) =
      factorialEnvelope D (L*B) u * factorialEnvelope D (L*A) v *
        factorialEnvelope D (B*T) w := by
  simp only [translationEnvelope, add_tsub_cancel_left, map_add, pow_add]
  calc
    _ = (chooseKernel D (u+w) u * factorialEnvelope D B (u+w)) *
        (L^u.degree * L^v.degree) * T^w.degree * factorialEnvelope D A v := by ring
    _ = _ := by
      rw [factorial_binomial_cancel, ← factorialEnvelope_mul D L B u,
        ← factorialEnvelope_mul D L A v, ← factorialEnvelope_mul D T B w]
      congr 1 <;> ring

private theorem overlap_summable (D : LatticeData) (L B A T : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (r1 r2 : ℝ) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hr1' : r1 < 1) (hr2' : r2 < 1) :
    Summable (fun z : Occ D × Occ D =>
      r1 ^ level D z.1 * r2 ^ level D z.2 * L ^ z.1.degree *
        factorialEnvelope D B z.2 * mixedEnvelope D A T z.1 z.2) := by
  classical
  have hr12 : r1*r2 < 1 := calc
    r1*r2 ≤ r1*1 := mul_le_mul_of_nonneg_left hr2'.le hr1
    _ < 1 := by simpa using hr1'
  have hs (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr' : r < 1) :
      Summable (fun d : Occ D => r ^ level D d * factorialEnvelope D C d) := by
    simpa [abs_of_nonneg hr] using factorialEnvelope_summable D C hC (r : ℂ)
      (by simpa [abs_of_nonneg hr] using hr')
  let fu := fun u : Occ D => (r1*r2)^level D u * factorialEnvelope D (L*B) u
  let fv := fun v : Occ D => r1^level D v * factorialEnvelope D (L*A) v
  let fw := fun w : Occ D => r2^level D w * factorialEnvelope D (B*T) w
  have hu : Summable fu := hs _ _ (mul_nonneg hL hB) (mul_nonneg hr1 hr2) hr12
  have hv : Summable fv := hs _ _ (mul_nonneg hL hA) hr1 hr1'
  have hw : Summable fw := hs _ _ (mul_nonneg hB hT) hr2 hr2'
  have hfu (u : Occ D) : 0 ≤ fu u := mul_nonneg (by positivity)
    (factorialEnvelope_nonneg D _ (mul_nonneg hL hB) _)
  have hfv (v : Occ D) : 0 ≤ fv v := mul_nonneg (by positivity)
    (factorialEnvelope_nonneg D _ (mul_nonneg hL hA) _)
  have hfw (w : Occ D) : 0 ≤ fw w := mul_nonneg (by positivity)
    (factorialEnvelope_nonneg D _ (mul_nonneg hB hT) _)
  let f := fun z : Occ D × Occ D × Occ D => fu z.1 * (fv z.2.1 * fw z.2.2)
  have hsum : Summable f := hu.mul_of_nonneg (hv.mul_of_nonneg hw hfv hfw) hfu
    (fun z => mul_nonneg (hfv z.1) (hfw z.2))
  let g := fun z : Occ D × Occ D × Occ D => (z.1+z.2.1,z.1+z.2.2)
  have hg := (hsum.hasSum.tsum_fiberwise g).summable
  apply hg.congr
  rintro ⟨d,e⟩
  let S := (Finset.Iic d).filter (fun u : Occ D => u ≤ e)
  let equiv : S ≃ {z : Occ D × Occ D × Occ D // g z = (d,e)} := {
    toFun := fun u => ⟨(u.1,d-u.1,e-u.1), by
      dsimp [g]
      rw [add_tsub_cancel_of_le (Finset.mem_Iic.mp (Finset.mem_filter.mp u.2).1),
        add_tsub_cancel_of_le (Finset.mem_filter.mp u.2).2]⟩
    invFun := fun z => ⟨z.1.1, by
      have hd : z.1.1+z.1.2.1 = d := congrArg Prod.fst z.2
      have he : z.1.1+z.1.2.2 = e := congrArg Prod.snd z.2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Iic.mpr (by rw [←hd]; exact le_self_add),
        by rw [←he]; exact le_self_add⟩⟩
    left_inv := fun u => by apply Subtype.ext; rfl
    right_inv := by
      rintro ⟨⟨u,v,w⟩,hz⟩
      apply Subtype.ext
      have hd : u+v=d := congrArg Prod.fst hz
      have he : u+w=e := congrArg Prod.snd hz
      dsimp only
      simp [←hd,←he]
  }
  rw [← equiv.tsum_eq]
  rw [tsum_fintype]
  symm
  unfold mixedEnvelope
  rw [Finset.mul_sum, Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro u huS
  have hud : u ≤ d := Finset.mem_Iic.mp (Finset.mem_filter.mp huS).1
  have hue : u ≤ e := (Finset.mem_filter.mp huS).2
  have hd : u+(d-u)=d := add_tsub_cancel_of_le hud
  have he : u+(e-u)=e := add_tsub_cancel_of_le hue
  have hc := overlap_cancellation D L B A T u (d-u) (e-u)
  rw [hd,he] at hc
  dsimp [f,fu,fv,fw,equiv]
  rw [← chooseKernel_eq D e u hue]
  change _ = _
  have hl1 : level D d = level D u + level D (d-u) := by
    rw [←hd, level, map_add]
  have hl2 : level D e = level D u + level D (e-u) := by
    rw [←he, level, map_add]
  simp only [translationEnvelope] at hc
  rw [hl1,hl2,pow_add,pow_add,mul_pow]
  linear_combination r1 ^ level D u * r1 ^ level D (d-u) *
    r2 ^ level D u * r2 ^ level D (e-u) * hc

end
end D5.S3.VertexAlgebra.CanonicalTwoCutScalar
