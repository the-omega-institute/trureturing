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
open private mixedEnvelope mixedEnvelope_nonneg overlapBinomial chooseKernel chooseKernel_eq chooseKernel_eq_prod
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
        ← factorialEnvelope_mul D L A v, mul_comm B T,
        ← factorialEnvelope_mul D T B w]
      ring

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
  let equiv : S ≃ (g ⁻¹' {(d,e)}) := {
    toFun := fun u => ⟨(u.1,d-u.1,e-u.1), by
      change (u.1+(d-u.1),u.1+(e-u.1)) = (d,e)
      rw [add_tsub_cancel_of_le (Finset.mem_Iic.mp (Finset.mem_filter.mp u.2).1),
        add_tsub_cancel_of_le (Finset.mem_filter.mp u.2).2]⟩
    invFun := fun z => ⟨z.1.1, by
      have hd : z.1.1+z.1.2.1 = d := congrArg Prod.fst z.2
      have he : z.1.1+z.1.2.2 = e := congrArg Prod.snd z.2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Iic.mpr ((le_self_add : z.1.1 ≤ z.1.1+z.1.2.1).trans_eq hd),
        (le_self_add : z.1.1 ≤ z.1.1+z.1.2.2).trans_eq he⟩⟩
    left_inv := fun u => by apply Subtype.ext; rfl
    right_inv := by
      rintro ⟨⟨u,v,w⟩,hz⟩
      apply Subtype.ext
      have hd : u+v=d := congrArg Prod.fst hz
      have he : u+w=e := congrArg Prod.snd hz
      dsimp only
      simp [←hd,←he]
  }
  rw [← equiv.tsum_eq (fun z => f z.1)]
  rw [tsum_fintype]
  symm
  unfold mixedEnvelope
  rw [Finset.mul_sum]
  rw [Finset.sum_coe_sort_eq_attach]
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro U hU
  let u : Occ D := U.1
  have huS : u ∈ S := U.2
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
    have hh : level D (u+(d-u)) = level D u + level D (d-u) := by
      simp only [level,LatticePositiveEnergy.oscillatorEnergy,map_add]
    exact (congrArg (level D) hd).symm.trans hh
  have hl2 : level D e = level D u + level D (e-u) := by
    have hh : level D (u+(e-u)) = level D u + level D (e-u) := by
      simp only [level,LatticePositiveEnergy.oscillatorEnergy,map_add]
    exact (congrArg (level D) he).symm.trans hh
  simp only [translationEnvelope] at hc
  rw [hl1,hl2,pow_add,pow_add,mul_pow]
  linear_combination r1 ^ level D u * r1 ^ level D (d-u) *
    r2 ^ level D u * r2 ^ level D (e-u) * hc

private theorem radial_polynomial_bound (J : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      r^n * (1+(n : ℝ))^J ≤ C * ((1+r)/2)^n := by
  let ρ := (1+r)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  obtain ⟨C,hC,hb⟩ := polynomial_geometric_bound J (r/ρ)
    (div_nonneg hr hρ.le) ((div_lt_one hρ).mpr hrρ)
  refine ⟨C,hC,fun n => ?_⟩
  calc
    _ = ((1+(n : ℝ))^J * (r/ρ)^n) * ρ^n := by
      rw [div_pow]
      field_simp
    _ ≤ C*ρ^n := mul_le_mul_of_nonneg_right (hb n) (pow_nonneg hρ.le _)

private theorem mixed_pair_summable (D : LatticeData) (a b : Charge D)
    (ω : List (Index D)) (s : ℤ) (L B : ℝ) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (K1 K2 : ℕ) (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Occ D × Occ D =>
      ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 * rowWeight D L K1 z.1 *
        ‖wordCoeff D a b ω (s+(level D z.2 : ℤ)-(level D z.1 : ℤ)) z.1 z.2‖ *
          columnWeight D B K2 z.2) := by
  classical
  let A : ℝ := 1+∑ i : Fin D.rank, ‖(a i : ℂ)‖
  let T : ℝ := 1+∑ i : Fin D.rank, ‖(bilinear D a (unitCharge D i) : ℂ)‖
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have hT : 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have ha (i : Fin D.rank) : ‖(a i : ℂ)‖ ≤ A := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ => norm_nonneg (a j : ℂ))
      (Finset.mem_univ i)
    dsimp [A]; linarith
  have ht (i : Fin D.rank) : ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ =>
      norm_nonneg (bilinear D a (unitCharge D j) : ℂ)) (Finset.mem_univ i)
    dsimp [T]; linarith
  let C := mixedConstant D a b A T ω
  let R := mixedRadius D ω
  have hC : 0 ≤ C := mixedConstant_nonneg D a b ω A T hA hT
  let ρ1 := (1+‖q1‖)/2
  let ρ2 := (1+‖q2‖)/2
  have hρ1 : 0 < ρ1 := by dsimp [ρ1]; positivity
  have hρ2 : 0 < ρ2 := by dsimp [ρ2]; positivity
  have hρ1' : ρ1 < 1 := by dsimp [ρ1]; linarith
  have hρ2' : ρ2 < 1 := by dsimp [ρ2]; linarith
  obtain ⟨C1,hC1,hb1⟩ := radial_polynomial_bound (K1+R) ‖q1‖ (norm_nonneg _) hq1
  obtain ⟨C2,hC2,hb2⟩ := radial_polynomial_bound (K2+R) ‖q2‖ (norm_nonneg _) hq2
  have hs := (overlap_summable D L B A T (by linarith) (by linarith)
    (by linarith) (by linarith) ρ1 ρ2 hρ1.le hρ2.le hρ1' hρ2').mul_left (C*C1*C2)
  refine hs.of_nonneg_of_le (fun z => by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (rowWeight_nonneg D L hL K1 z.1)) (norm_nonneg _))
      (columnWeight_nonneg D B hB K2 z.2)) ?_
  rintro ⟨d,e⟩
  have hM : 0 ≤ mixedEnvelope D A T d e := mixedEnvelope_nonneg D A T
    (by linarith) (by linarith) d e
  have hb := mixed_descendant_bound D a b A T hA hT ha ht ω
    (s+(level D e : ℤ)-(level D d : ℤ)) d e
  have hpoly : mixedEnergy D d e ^ R ≤
      (1+(level D d : ℝ))^R * (1+(level D e : ℝ))^R := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by dsimp [mixedEnergy]; positivity)
    dsimp [mixedEnergy]
    nlinarith [Nat.cast_nonneg (α := ℝ) (level D d),
      Nat.cast_nonneg (α := ℝ) (level D e)]
  calc
    _ ≤ ‖q1‖^level D d * ‖q2‖^level D e * rowWeight D L K1 d *
        (C*mixedEnergy D d e^R*mixedEnvelope D A T d e) * columnWeight D B K2 e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb
        (mul_nonneg (by positivity) (rowWeight_nonneg D L hL K1 d)))
          (columnWeight_nonneg D B hB K2 e)
    _ = (C * ‖q1‖^level D d * ‖q2‖^level D e * (1+(level D d : ℝ))^K1 *
        L^d.degree * (1+(level D e : ℝ))^K2 * factorialEnvelope D B e *
        mixedEnvelope D A T d e) * mixedEnergy D d e^R := by
      dsimp [rowWeight,columnWeight]; ring
    _ ≤ (C * ‖q1‖^level D d * ‖q2‖^level D e * (1+(level D d : ℝ))^K1 *
        L^d.degree * (1+(level D e : ℝ))^K2 * factorialEnvelope D B e *
        mixedEnvelope D A T d e) *
          ((1+(level D d : ℝ))^R * (1+(level D e : ℝ))^R) := by
      apply mul_le_mul_of_nonneg_left hpoly
      have hF := factorialEnvelope_nonneg D B (by linarith) e
      positivity
    _ = C * (‖q1‖^level D d * (1+(level D d : ℝ))^(K1+R)) *
        (‖q2‖^level D e * (1+(level D e : ℝ))^(K2+R)) *
          L^d.degree * factorialEnvelope D B e * mixedEnvelope D A T d e := by
      rw [pow_add,pow_add]; ring
    _ ≤ C * (C1*ρ1^level D d) * (C2*ρ2^level D e) *
        L^d.degree * factorialEnvelope D B e * mixedEnvelope D A T d e := by
      have hF := factorialEnvelope_nonneg D B (by linarith) e
      apply mul_le_mul_of_nonneg_right _ hM
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb1 (level D d)) hC)
        (hb2 (level D e)) (by positivity) (by positivity)
    _ = _ := by ring

private theorem word_two_cut_summable (D : LatticeData) (α β γ δ : Charge D)
    (ω ν ξ : List (Index D)) (P W : Occ D) (r s k : ℤ)
    (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Occ D × Occ D => ‖q1 ^ level D z.1 * q2 ^ level D z.2 *
      wordCoeff D α (β+(γ+δ)) ω (r+(level D z.1 : ℤ)) P z.1 *
      wordCoeff D β (γ+δ) ν (s+(level D z.2 : ℤ)-(level D z.1 : ℤ)) z.1 z.2 *
      wordCoeff D γ δ ξ (k-(level D z.2 : ℤ)) z.2 W‖) := by
  obtain ⟨L,hL,hr⟩ := word_row_bound D α (β+(γ+δ))
  obtain ⟨K,hr⟩ := hr ω
  obtain ⟨C,hC,hr⟩ := hr P
  obtain ⟨B,hB,hc⟩ := word_column_bound D γ δ
  obtain ⟨J,hc⟩ := hc ξ
  obtain ⟨S,hS,hc⟩ := hc W
  have hs := (mixed_pair_summable D β (γ+δ) ν s L B hL hB K (J+W.degree)
    q1 q2 hq1 hq2).mul_left (C*S)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨d,e⟩
  simp only [norm_mul,norm_pow]
  calc
    _ ≤ ‖q1‖^level D d * ‖q2‖^level D e *
        (C*rowWeight D L K d) *
        ‖wordCoeff D β (γ+δ) ν (s+(level D e : ℤ)-(level D d : ℤ)) d e‖ *
        (S*columnWeight D B (J+W.degree) e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hr d _) (by positivity)) (norm_nonneg _)
      · exact hc e _
      · exact norm_nonneg _
      · exact mul_nonneg (mul_nonneg (by positivity)
          (mul_nonneg hC (rowWeight_nonneg D L hL K d))) (norm_nonneg _)
    _ = _ := by ring

private theorem scalar_expansion (D : LatticeData) (α β γ δ : Charge D)
    (u v t w p : Oscillator D) (r s k : ℤ) (q1 q2 : ℂ) (d e : Occ D) :
    q1^level D d * q2^level D e *
      H D p (canonical D α (β+(γ+δ)) u (r+(level D d : ℤ)) (b D d)) *
      (canonical D β (γ+δ) v (s+(level D e : ℤ)-(level D d : ℤ)) (b D e)).coeff d *
      (canonical D γ δ t (k-(level D e : ℤ)) w).coeff e =
    ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support,
      ∑ T ∈ t.support, ∑ W ∈ w.support,
        ((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * t.coeff T * w.coeff W) *
        (q1^level D d * q2^level D e *
          wordCoeff D α (β+(γ+δ)) (occurrences D U) (r+(level D d : ℤ)) P d *
          wordCoeff D β (γ+δ) (occurrences D V)
            (s+(level D e : ℤ)-(level D d : ℤ)) d e *
          wordCoeff D γ δ (occurrences D T) (k-(level D e : ℤ)) e W) := by
  classical
  simp only [inner_coefficient_expansion, canonical_basis_input_expansion]
  rw [canonical_coefficient_expansion]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := v.support) (t := p.support),
    Finset.sum_comm (s := w.support) (t := p.support)]
  rw [Finset.sum_comm (s := t.support) (t := p.support)]
  simp_rw [Finset.sum_comm (s := v.support) (t := u.support),
    Finset.sum_comm (s := w.support) (t := u.support),
    Finset.sum_comm (s := t.support) (t := u.support),
    Finset.sum_comm (s := w.support) (t := v.support),
    Finset.sum_comm (s := t.support) (t := v.support)]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro W hW
  ring

/-- Absolute summability of the literal canonical two-cut scalar for arbitrary
external oscillator polynomials, signed offsets and both open unit disks. -/
theorem canonical_two_cut_summable (D : LatticeData) (α β γ δ : Charge D)
    (u v t w p : Oscillator D) (r s k : ℤ) (q1 q2 : ℂ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Occ D × Occ D =>
      ‖q1^level D z.1 * q2^level D z.2 *
        H D p (canonical D α (β+(γ+δ)) u (r+(level D z.1 : ℤ)) (b D z.1)) *
        (canonical D β (γ+δ) v
          (s+(level D z.2 : ℤ)-(level D z.1 : ℤ)) (b D z.2)).coeff z.1 *
        (canonical D γ δ t (k-(level D z.2 : ℤ)) w).coeff z.2‖) := by
  classical
  have hs : Summable (fun z : Occ D × Occ D =>
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support,
        ∑ T ∈ t.support, ∑ W ∈ w.support,
          ‖((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
              u.coeff U * v.coeff V * t.coeff T * w.coeff W) *
            (q1^level D z.1 * q2^level D z.2 *
              wordCoeff D α (β+(γ+δ)) (occurrences D U) (r+(level D z.1 : ℤ)) P z.1 *
              wordCoeff D β (γ+δ) (occurrences D V)
                (s+(level D z.2 : ℤ)-(level D z.1 : ℤ)) z.1 z.2 *
              wordCoeff D γ δ (occurrences D T) (k-(level D z.2 : ℤ)) z.2 W)‖) := by
    apply summable_sum
    intro P hP
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    apply summable_sum
    intro T hT
    apply summable_sum
    intro W hW
    simpa only [norm_mul] using
      (word_two_cut_summable D α β γ δ (occurrences D U) (occurrences D V)
        (occurrences D T) P W r s k q1 q2 hq1 hq2).mul_left
          ‖(FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
            u.coeff U * v.coeff V * t.coeff T * w.coeff W‖
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨d,e⟩
  rw [scalar_expansion]
  apply norm_sum_le_of_le
  intro P hP
  apply norm_sum_le_of_le
  intro U hU
  apply norm_sum_le_of_le
  intro V hV
  apply norm_sum_le_of_le
  intro T hT
  exact norm_sum_le _ _

end
end D5.S3.VertexAlgebra.CanonicalTwoCutScalar
