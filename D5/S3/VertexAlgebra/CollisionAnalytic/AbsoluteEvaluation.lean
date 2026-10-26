/- GID: D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute evaluation of collision-localized labelled Hahn expansions. -/

import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import D5.S3.VertexAlgebra.CollisionRationalExpansions

/-!
Formal Hahn summability and complex absolute summability are distinct.  The
coefficient-fiber argument below connects them for monomial families, retaining
all exponents. Hahn series and formal summable families are due to Aaron Anderson;
the numerical infinite-sum and geometric-series tools are from mathlib
(Apache 2.0). No point evaluation of an entire fraction field is used.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Topology
namespace D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation

variable {Γ α β : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Absolute evaluation of a Hahn series with a quantitative norm bound. -/
structure Evaluates (w : Γ → ℂ) (f : HahnSeries Γ ℂ) (v : ℂ) (M : ℝ) : Prop where
  summable_norm : Summable (fun g => ‖f.coeff g * w g‖)
  hasSum : HasSum (fun g => f.coeff g * w g) v
  norm_sum_le : (∑' g, ‖f.coeff g * w g‖) ≤ M

/-- The finite formal coefficient fibers are exactly the numerical exponent
fibers. Absolute summability is required only of the ungrouped monomials. -/
theorem monomial_family (w : Γ → ℂ) (s : HahnSeries.SummableFamily Γ ℂ α)
    (e : α → Γ) (c : α → ℂ) (hs : ∀ i, s i = HahnSeries.single (e i) (c i))
    (ha : Summable (fun i => ‖c i * w (e i)‖))
    {v : ℂ} (hv : HasSum (fun i => c i * w (e i)) v) :
    Evaluates w s.hsum v (∑' i, ‖c i * w (e i)‖) := by
  classical
  have fiber (g : Γ) : s.hsum.coeff g * w g =
      ∑' i : e ⁻¹' {g}, c i * w (e i) := by
    rw [tsum_subtype (e ⁻¹' {g}) (fun i => c i * w (e i))]
    have eqfun : (e ⁻¹' {g}).indicator (fun i => c i * w (e i)) =
        fun i => (s i).coeff g * w g := by
      funext i
      by_cases hi : e i = g
      · simp [Set.indicator, hi, hs i, HahnSeries.coeff_single]
      · simp [Set.indicator, hi, hs i, HahnSeries.coeff_single, Ne.symm hi]
    rw [eqfun, tsum_mul_right, tsum_eq_finsum (s.finite_co_support g)]
    rfl
  have hnorm := ha.hasSum.tsum_fiberwise e
  have bound (g : Γ) : ‖s.hsum.coeff g * w g‖ ≤
      ∑' i : e ⁻¹' {g}, ‖c i * w (e i)‖ := by
    rw [fiber]
    exact norm_tsum_le_tsum_norm (ha.subtype _)
  have habs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound hnorm.summable
  exact ⟨habs, (hv.tsum_fiberwise e).congr_fun (fun g => fiber g),
    (habs.tsum_le_tsum bound hnorm.summable).trans_eq hnorm.tsum_eq⟩

/-- A Hahn series as its formally summable family of coefficient monomials. -/
def coefficientFamily (f : HahnSeries Γ ℂ) : HahnSeries.SummableFamily Γ ℂ Γ where
  toFun g := HahnSeries.single g (f.coeff g)
  isPWO_iUnion_support' := f.isPWO_support.mono (by
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    have hgi := HahnSeries.eq_of_mem_support_single hi
    subst g
    simpa only [HahnSeries.mem_support, HahnSeries.coeff_single_same] using hi)
  finite_co_support' g := (Set.finite_singleton g).subset (by
    intro i hi
    by_contra h
    exact hi (HahnSeries.coeff_single_of_ne (Ne.symm h)))

private lemma coefficientFamily_hsum (f : HahnSeries Γ ℂ) :
    (coefficientFamily f).hsum = f := by
  ext g
  simp only [HahnSeries.SummableFamily.coeff_hsum, coefficientFamily,
    HahnSeries.SummableFamily.coe_mk, HahnSeries.coeff_single]
  rw [finsum_eq_single _ g]
  · simp
  · intro i hi
    simp [hi, Ne.symm hi]

private lemma single_evaluates (w : Γ → ℂ) (g : Γ) (c : ℂ) :
    Evaluates w (HahnSeries.single g c) (c * w g) ‖c * w g‖ := by
  classical
  have eqfun : (fun h => (HahnSeries.single g c).coeff h * w h) =
      Pi.single g (c * w g) := by
    funext h
    by_cases hh : h = g <;> simp [hh, HahnSeries.coeff_single, Pi.single_apply]
  have hn : (fun h => ‖(HahnSeries.single g c).coeff h * w h‖) =
      Pi.single g ‖c * w g‖ := by
    funext h
    rw [congrFun eqfun h]
    by_cases hh : h = g <;> simp [Pi.single_apply, hh]
  constructor
  · rw [hn]
    exact (hasSum_pi_single g ‖c*w g‖).summable
  · rw [eqfun]
    exact hasSum_pi_single g (c*w g)
  · rw [hn, (hasSum_pi_single g ‖c * w g‖).tsum_eq]

private lemma mul_evaluates {w : Γ → ℂ} (hw : ∀ g h, w (g+h) = w g * w h)
    {f k : HahnSeries Γ ℂ} {v u : ℂ} {M N : ℝ}
    (hf : Evaluates w f v M) (hk : Evaluates w k u N) :
    Evaluates w (f*k) (v*u) (M*N) := by
  let s := (coefficientFamily f).mul (coefficientFamily k)
  have hs (p : Γ × Γ) : s p = HahnSeries.single (p.1+p.2)
      (f.coeff p.1*k.coeff p.2) := by
    exact HahnSeries.single_mul_single ..
  have term (p : Γ × Γ) : (f.coeff p.1*k.coeff p.2) * w (p.1+p.2) =
      (f.coeff p.1*w p.1) * (k.coeff p.2*w p.2) := by rw [hw]; ring
  have ha : Summable (fun p : Γ × Γ =>
      ‖(f.coeff p.1*k.coeff p.2) * w (p.1+p.2)‖) := by
    simpa only [term] using hf.summable_norm.mul_norm hk.summable_norm
  have hv : HasSum (fun p : Γ × Γ =>
      (f.coeff p.1*k.coeff p.2) * w (p.1+p.2)) (v*u) := by
    have hp := (summable_mul_of_summable_norm hf.summable_norm hk.summable_norm).hasSum
    rw [← tsum_mul_tsum_of_summable_norm hf.summable_norm hk.summable_norm,
      hf.hasSum.tsum_eq, hk.hasSum.tsum_eq] at hp
    simpa only [term] using hp
  have h := monomial_family w s (fun p => p.1+p.2)
    (fun p => f.coeff p.1*k.coeff p.2) hs ha hv
  rw [HahnSeries.SummableFamily.hsum_mul, coefficientFamily_hsum,
    coefficientFamily_hsum] at h
  refine ⟨h.summable_norm, h.hasSum, h.norm_sum_le.trans ?_⟩
  simp_rw [term]
  rw [show (∑' p : Γ × Γ, ‖(f.coeff p.1 * w p.1) * (k.coeff p.2 * w p.2)‖) =
      (∑' g, ‖f.coeff g * w g‖) * (∑' g, ‖k.coeff g * w g‖) from by
    simp_rw [norm_mul]
    simpa only [norm_mul] using (tsum_mul_tsum_of_summable_norm
      (f := fun g => ‖f.coeff g * w g‖) (g := fun g => ‖k.coeff g * w g‖)
      (by simpa only [Real.norm_eq_abs, abs_norm] using hf.summable_norm)
      (by simpa only [Real.norm_eq_abs, abs_norm] using hk.summable_norm)).symm]
  exact mul_le_mul hf.norm_sum_le hk.norm_sum_le (tsum_nonneg (fun _ => norm_nonneg _))
    ((tsum_nonneg (fun _ => norm_nonneg _)).trans hf.norm_sum_le)

private lemma add_evaluates {w : Γ → ℂ} {f k : HahnSeries Γ ℂ}
    {v u : ℂ} {M N : ℝ} (hf : Evaluates w f v M) (hk : Evaluates w k u N) :
    Evaluates w (f+k) (v+u) (M+N) := by
  have bound (g : Γ) : ‖(f+k).coeff g*w g‖ ≤ ‖f.coeff g*w g‖+‖k.coeff g*w g‖ := by
    simpa [add_mul] using norm_add_le (f.coeff g*w g) (k.coeff g*w g)
  have ha := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound
    (hf.summable_norm.add hk.summable_norm)
  refine ⟨ha, ?_, ?_⟩
  · simpa [add_mul] using hf.hasSum.add hk.hasSum
  · exact (ha.tsum_le_tsum bound (hf.summable_norm.add hk.summable_norm)).trans
      (by rw [hf.summable_norm.tsum_add hk.summable_norm];
          exact add_le_add hf.norm_sum_le hk.norm_sum_le)

private lemma sum_evaluates {ι : Type*} (s : Finset ι) {w : Γ → ℂ}
    (f : ι → HahnSeries Γ ℂ) (v : ι → ℂ) (M : ι → ℝ)
    (h : ∀ i ∈ s, Evaluates w (f i) (v i) (M i)) :
    Evaluates w (∑ i ∈ s, f i) (∑ i ∈ s, v i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simp, by simp⟩
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact add_evaluates (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma one_evaluates (w : Γ → ℂ) (hw : w 0 = 1) :
    Evaluates w 1 1 1 := by
  simpa [hw] using single_evaluates w 0 1

private lemma pow_evaluates {w : Γ → ℂ} (hw0 : w 0 = 1)
    (hw : ∀ g h, w (g + h) = w g * w h) {f : HahnSeries Γ ℂ}
    {v : ℂ} {M : ℝ} (hf : Evaluates w f v M) (m : ℕ) :
    Evaluates w (f^m) (v^m) (M^m) := by
  induction m with
  | zero => simpa using one_evaluates w hw0
  | succ m ih => simpa [pow_succ] using mul_evaluates hw ih hf

private lemma geometric_evaluates (w : Γ → ℂ) (hw0 : w 0 = 1)
    (hw : ∀ g h, w (g + h) = w g * w h) (g : Γ) (hg : 0 < g)
    (hz : ‖w g‖ < 1) :
    Evaluates w ((1-HahnSeries.single g 1)⁻¹) ((1-w g)⁻¹)
      ((1-‖w g‖)⁻¹) := by
  have ho : 0 < (HahnSeries.single g (1 : ℂ)).orderTop :=
    HahnSeries.lt_orderTop_single hg
  let s := HahnSeries.SummableFamily.powers (HahnSeries.single g (1 : ℂ))
  have hs (m : ℕ) : s m = HahnSeries.single (m • g) 1 := by
    simp [s, HahnSeries.SummableFamily.powers_of_orderTop_pos ho, HahnSeries.single_pow]
  have wn (m : ℕ) : w (m • g) = w g ^ m := by
    induction m with
    | zero => simpa using hw0
    | succ m ih => simp [succ_nsmul, hw, ih, pow_succ]
  have ha : Summable (fun m : ℕ => ‖(1 : ℂ) * w (m • g)‖) := by
    simpa [wn] using summable_norm_geometric_of_norm_lt_one hz
  have hv : HasSum (fun m : ℕ => (1 : ℂ) * w (m • g)) ((1-w g)⁻¹) := by
    simpa [wn] using hasSum_geometric_of_norm_lt_one hz
  have he := monomial_family w s (fun m => m • g) (fun _ => 1) hs ha hv
  have hinv : s.hsum = (1-HahnSeries.single g 1)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right
      (HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers ho)
  rw [hinv] at he
  refine ⟨he.summable_norm, he.hasSum, he.norm_sum_le.trans_eq ?_⟩
  simp only [one_mul, wn, norm_pow]
  exact (hasSum_geometric_of_norm_lt_one (by simpa using hz : ‖‖w g‖‖ < 1)).tsum_eq

end D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation


namespace D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.Labelled
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution UniformGradedLocalCorrelator

/-- Numerical value of an integer Laurent monomial. -/
def monomial {n : ℕ} (z : Fin n → ℂ) (e : Fin n → ℤ) : ℂ := ∏ i, z i ^ e i

/-- Sufficient radial chamber for the complete ordered expansion. -/
def RadialChamber {n : ℕ} (sigma : Equiv.Perm (Fin n)) (z : Fin n → ℂ) : Prop :=
  (∀ i, z i ≠ 0) ∧ ∀ i j, i < j → ‖z (sigma j)‖ < ‖z (sigma i)‖

def laurentValue {n : ℕ} (P : LabelledPolynomial ℂ n) (z : Fin n → ℂ) : ℂ :=
  ∑ e ∈ P.coeff.support, P.coeff e * monomial z e

def laurentMajorant {n : ℕ} (P : LabelledPolynomial ℂ n) (z : Fin n → ℂ) : ℝ :=
  ∑ e ∈ P.coeff.support, ‖P.coeff e * monomial z e‖

private def weight {n : ℕ} (sigma : Equiv.Perm (Fin n)) (z : Fin n → ℂ)
    (g : Indices n) : ℂ := monomial z ((orderExponents n sigma).symm g)

private lemma monomial_zero {n : ℕ} (z : Fin n → ℂ) : monomial z 0 = 1 := by
  simp [monomial]

private lemma monomial_add {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0)
    (e f : Fin n → ℤ) : monomial z (e+f) = monomial z e * monomial z f := by
  simp only [monomial, Pi.add_apply, zpow_add₀ (hz _), Finset.prod_mul_distrib]

private lemma weight_zero {n : ℕ} (sigma : Equiv.Perm (Fin n)) (z : Fin n → ℂ) :
    weight sigma z 0 = 1 := by simp [weight, monomial_zero]

private lemma weight_add {n : ℕ} (sigma : Equiv.Perm (Fin n)) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) (g h : Indices n) :
    weight sigma z (g+h) = weight sigma z g * weight sigma z h := by
  simp only [weight, map_add]
  exact monomial_add z hz _ _

private lemma monomial_unit {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    monomial z (Pi.single i 1) = z i := by
  classical
  simp [monomial, Pi.single_apply]

private lemma ordered_single {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (e : Fin n → ℤ) (c : ℂ) :
    orderedPolynomialFor ℂ n sigma (AddMonoidAlgebra.single e c) =
      HahnSeries.single (orderExponents n sigma e) c := by
  simp [orderedPolynomialFor, scalarPolynomial_single]

private lemma numerator_evaluates {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (P : LabelledPolynomial ℂ n) :
    Evaluates (weight sigma z) (orderedPolynomialFor ℂ n sigma P)
      (laurentValue P z) (laurentMajorant P z) := by
  classical
  have h := sum_evaluates P.coeff.support
    (fun e => HahnSeries.single (orderExponents n sigma e) (P.coeff e))
    (fun e => P.coeff e * monomial z e) (fun e => ‖P.coeff e * monomial z e‖)
    (fun e _ => by simpa [weight] using
      single_evaluates (weight sigma z) (orderExponents n sigma e) (P.coeff e))
  have hP : orderedPolynomialFor ℂ n sigma P =
      ∑ e ∈ P.coeff.support, HahnSeries.single (orderExponents n sigma e) (P.coeff e) := by
    conv_lhs => rw [← P.sum_coeff_single]
    simp only [Finsupp.sum, map_sum, ordered_single]
  simpa only [hP, laurentValue, laurentMajorant] using h

private lemma exponents_single_lt (n : ℕ) : ∀ i j : Fin n, i < j →
    exponents n (Pi.single i (1 : ℤ)) < exponents n (Pi.single j (1 : ℤ)) := by
  classical
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij
      have hi : i ≠ Fin.last n := ne_of_lt hij
      simp only [exponents]
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      simp [Pi.single_apply, hi, Ne.symm hi]
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
      · intro hij
        have rest (k : Fin n) : (fun r : Fin n =>
            (Pi.single k.castSucc (1 : ℤ) : Fin (n+1) → ℤ) r.castSucc) = Pi.single k 1 := by
          funext r
          simp [Pi.single_apply]
        simp only [exponents]
        apply Prod.Lex.toLex_lt_toLex.mpr
        right
        refine ⟨by simp [Pi.single_apply], ?_⟩
        rw [rest, rest]
        exact ih i j (by simpa using hij)

private lemma label_single (n : ℕ) (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    orderExponents n sigma (Pi.single i (1 : ℤ)) =
      exponents n (Pi.single (sigma.symm i) 1) := by
  unfold orderExponents
  change exponents n (fun j => (Pi.single i (1 : ℤ) : Fin n → ℤ) (sigma j)) = _
  congr 1
  funext j
  by_cases hj : j = sigma.symm i
  · subst j; simp
  · have hji : sigma j ≠ i := by
      intro h
      apply hj
      simpa only [Equiv.symm_apply_apply] using congrArg sigma.symm h
    simp [Pi.single_apply, hj, hji]

private lemma ratio_positive {n : ℕ} (sigma : Equiv.Perm (Fin n)) (i j : Fin n)
    (hij : sigma.symm i < sigma.symm j) :
    0 < orderExponents n sigma (Pi.single j (1 : ℤ)-Pi.single i 1) := by
  rw [map_sub, sub_pos, label_single, label_single]
  exact exponents_single_lt n _ _ hij

private lemma weight_single {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (i : Fin n) :
    weight sigma z (orderExponents n sigma (Pi.single i 1)) = z i := by
  simp [weight, monomial_unit]

private lemma weight_neg {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0) (g : Indices n) :
    weight sigma z (-g) = (weight sigma z g)⁻¹ := by
  have hn : weight sigma z g * weight sigma z (-g) = 1 := by
    rw [← weight_add sigma z hz, add_neg_cancel, weight_zero]
  exact eq_inv_of_mul_eq_one_right hn

private lemma weight_sub {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0) (g h : Indices n) :
    weight sigma z (g-h) = weight sigma z g / weight sigma z h := by
  rw [sub_eq_add_neg, weight_add sigma z hz, weight_neg sigma z hz, div_eq_mul_inv]

private lemma oriented_inverse_evaluates {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (hz : RadialChamber sigma z) (i j : Fin n)
    (hij : sigma.symm i < sigma.symm j) :
    Evaluates (weight sigma z)
      ((orderedPolynomialFor ℂ n sigma (pairPolynomial i j))⁻¹)
      ((z i-z j)⁻¹) ((‖z i‖-‖z j‖)⁻¹) := by
  let gi := orderExponents n sigma (Pi.single i (1 : ℤ))
  let gj := orderExponents n sigma (Pi.single j (1 : ℤ))
  have hrad : ‖z j‖ < ‖z i‖ := by simpa using hz.2 _ _ hij
  have hratio : ‖weight sigma z (gj-gi)‖ < 1 := by
    rw [weight_sub sigma z hz.1, weight_single, weight_single, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr (hz.1 i))).mpr hrad
  have hpos : 0 < gj-gi := by
    simpa only [map_sub] using ratio_positive sigma i j hij
  have hg := geometric_evaluates (weight sigma z) (weight_zero sigma z)
    (weight_add sigma z hz.1) (gj-gi) hpos hratio
  have hs := single_evaluates (weight sigma z) (-gi) (1 : ℂ)
  have h := mul_evaluates (weight_add sigma z hz.1) hs hg
  have hformal : HahnSeries.single (-gi) (1 : ℂ) *
      (1-HahnSeries.single (gj-gi) 1)⁻¹ =
      (orderedPolynomialFor ℂ n sigma (pairPolynomial i j))⁻¹ := by
    have hfactor : orderedPolynomialFor ℂ n sigma (pairPolynomial i j) =
        HahnSeries.single gi 1 * (1-HahnSeries.single (gj-gi) 1) := by
      simp only [pairPolynomial, variablePolynomial, map_sub, ordered_single]
      rw [mul_sub, mul_one, HahnSeries.single_mul_single]
      simp [gi, gj]
    rw [hfactor, mul_inv_rev]
    have hmono : (HahnSeries.single gi (1 : ℂ))⁻¹ = HahnSeries.single (-gi) 1 := by
      symm
      apply eq_inv_of_mul_eq_one_right
      rw [HahnSeries.single_mul_single]
      simp
    rw [hmono, mul_comm]
  have hvalue : (1 : ℂ)*weight sigma z (-gi) * (1-weight sigma z (gj-gi))⁻¹ =
      (z i-z j)⁻¹ := by
    rw [one_mul, weight_neg sigma z hz.1, weight_single,
      weight_sub sigma z hz.1, weight_single, weight_single]
    have hdiff : z i-z j ≠ 0 := sub_ne_zero.mpr (by
      intro heq
      simp only [heq, lt_self_iff_false] at hrad)
    field_simp [hz.1 i, hdiff]
  have hmajorant : ‖(1 : ℂ)*weight sigma z (-gi)‖ *
      (1-‖weight sigma z (gj-gi)‖)⁻¹ = (‖z i‖-‖z j‖)⁻¹ := by
    rw [one_mul, weight_neg sigma z hz.1, weight_single,
      weight_sub sigma z hz.1, weight_single, weight_single, norm_inv, norm_div]
    field_simp [norm_ne_zero_iff.mpr (hz.1 i), ne_of_gt (sub_pos.mpr hrad)]
  simpa only [hformal, hvalue, hmajorant] using h

private lemma neg_evaluates {n : ℕ} {w : Indices n → ℂ} {f : HahnSeries (Indices n) ℂ}
    {v : ℂ} {M : ℝ} (hf : Evaluates w f v M) : Evaluates w (-f) (-v) M := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [HahnSeries.coeff_neg, neg_mul, norm_neg] using hf.summable_norm
  · simpa only [HahnSeries.coeff_neg, neg_mul] using hf.hasSum.neg
  · simpa only [HahnSeries.coeff_neg, neg_mul, norm_neg] using hf.norm_sum_le

private lemma pair_inverse_evaluates {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (hz : RadialChamber sigma z) (i j : Fin n) (hij : i ≠ j) :
    Evaluates (weight sigma z) (orderedPolynomialFor ℂ n sigma (pairPolynomial i j))⁻¹
      (z i-z j)⁻¹ |‖z i‖-‖z j‖|⁻¹ := by
  by_cases h : sigma.symm i < sigma.symm j
  · have hr : ‖z j‖ < ‖z i‖ := by simpa using hz.2 _ _ h
    simpa only [abs_of_pos (sub_pos.mpr hr)] using oriented_inverse_evaluates sigma z hz i j h
  · have hne : sigma.symm j ≠ sigma.symm i := fun hh => hij (sigma.symm.injective hh.symm)
    have hrev : sigma.symm j < sigma.symm i := lt_of_le_of_ne (le_of_not_gt h) hne
    have hr : ‖z i‖ < ‖z j‖ := by simpa using hz.2 _ _ hrev
    have he := neg_evaluates (oriented_inverse_evaluates sigma z hz j i hrev)
    have hp : orderedPolynomialFor ℂ n sigma (pairPolynomial i j) =
        -orderedPolynomialFor ℂ n sigma (pairPolynomial j i) := by
      simp only [pairPolynomial, map_sub]
      ring
    simpa only [hp, inv_neg, ← neg_sub (z j) (z i), inv_neg,
      abs_sub_comm ‖z i‖ ‖z j‖, abs_of_pos (sub_pos.mpr hr)] using he

private lemma prod_evaluates {n : ℕ} {ι : Type*} (s : Finset ι)
    (sigma : Equiv.Perm (Fin n)) (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0)
    (f : ι → HahnSeries (Indices n) ℂ) (v : ι → ℂ) (M : ι → ℝ)
    (h : ∀ i ∈ s, Evaluates (weight sigma z) (f i) (v i) (M i)) :
    Evaluates (weight sigma z) (∏ i ∈ s, f i) (∏ i ∈ s, v i) (∏ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_evaluates (weight sigma z) (weight_zero sigma z)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact mul_evaluates (weight_add sigma z hz) (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma denominator_ne_zero {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (m : (Fin n × Fin n) → ℕ) (z : Fin n → ℂ) (hz : RadialChamber sigma z) :
    (∏ p ∈ labelledPairs n, (z p.1-z p.2)^m p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro heq
  have hne : sigma.symm p.1 ≠ sigma.symm p.2 := fun h =>
    (ne_of_lt (Finset.mem_filter.mp hp).2) (sigma.symm.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hr := hz.2 _ _ h
    simp only [Equiv.apply_symm_apply, heq, lt_self_iff_false] at hr
  · have hr := hz.2 _ _ h
    simp only [Equiv.apply_symm_apply, heq, lt_self_iff_false] at hr

/-- All labelled integer Hahn coefficients evaluate absolutely to the displayed
collision-localized Laurent quotient. The estimate uses radial gaps. -/
theorem collision_absolute_evaluation {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (P : LabelledPolynomial ℂ n) (m : (Fin n × Fin n) → ℕ)
    (z : Fin n → ℂ) (hz : RadialChamber sigma z) :
    let Q : LabelledPolynomial ℂ n := ∏ p ∈ labelledPairs n, pairPolynomial p.1 p.2 ^ m p
    let c := fun e => (orderedRationalFor ℂ n sigma
      (algebraMap _ (CommonRational ℂ n) P / algebraMap _ (CommonRational ℂ n) Q)).coeff
        (orderExponents n sigma e)
    (∏ p ∈ labelledPairs n, (z p.1-z p.2)^m p) ≠ 0 ∧
    Summable (fun e : Fin n → ℤ => ‖c e * monomial z e‖) ∧
    HasSum (fun e : Fin n → ℤ => c e * monomial z e)
      (laurentValue P z / ∏ p ∈ labelledPairs n, (z p.1-z p.2) ^ m p) ∧
    (∑' e : Fin n → ℤ, ‖c e * monomial z e‖) ≤
      laurentMajorant P z * ∏ p ∈ labelledPairs n, |‖z p.1‖-‖z p.2‖|⁻¹ ^ m p := by
  classical
  dsimp only
  have hd := prod_evaluates (labelledPairs n) sigma z hz.1
    (fun p => (orderedPolynomialFor ℂ n sigma (pairPolynomial p.1 p.2))⁻¹ ^ m p)
    (fun p => (z p.1-z p.2)⁻¹ ^ m p)
    (fun p => |‖z p.1‖-‖z p.2‖|⁻¹ ^ m p) (by
      intro p hp
      have hne : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.mp hp).2)
      exact pow_evaluates (weight_zero sigma z) (weight_add sigma z hz.1)
        (pair_inverse_evaluates sigma z hz p.1 p.2 hne) (m p))
  have he := mul_evaluates (weight_add sigma z hz.1) (numerator_evaluates sigma z P) hd
  have hformal : orderedRationalFor ℂ n sigma
      (algebraMap _ (CommonRational ℂ n) P /
        algebraMap _ (CommonRational ℂ n)
          (∏ p ∈ labelledPairs n, pairPolynomial p.1 p.2 ^ m p)) =
      orderedPolynomialFor ℂ n sigma P *
        ∏ p ∈ labelledPairs n, (orderedPolynomialFor ℂ n sigma (pairPolynomial p.1 p.2))⁻¹ ^ m p := by
    simp only [orderedRationalFor, map_div₀, map_mul, map_inv₀,
      IsFractionRing.lift_algebraMap, map_prod, map_pow, div_eq_mul_inv,
      Finset.prod_inv_distrib, inv_pow]
    rfl
  have hvalue : laurentValue P z * (∏ p ∈ labelledPairs n, (z p.1-z p.2)⁻¹ ^ m p) =
      laurentValue P z / ∏ p ∈ labelledPairs n, (z p.1-z p.2) ^ m p := by
    simp [div_eq_mul_inv, Finset.prod_inv_distrib, inv_pow]
  rw [hvalue] at he
  have habs := (orderExponents n sigma).toEquiv.summable_iff.mpr he.summable_norm
  have hsum := (orderExponents n sigma).toEquiv.hasSum_iff.mpr he.hasSum
  refine ⟨denominator_ne_zero sigma m z hz, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← hformal, weight,
      AddEquiv.symm_apply_apply] using habs
  · simpa only [Function.comp_def, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← hformal, weight,
      AddEquiv.symm_apply_apply] using hsum
  · have ht := (orderExponents n sigma).toEquiv.tsum_eq
      (fun g => ‖(orderedPolynomialFor ℂ n sigma P *
        ∏ p ∈ labelledPairs n, (orderedPolynomialFor ℂ n sigma (pairPolynomial p.1 p.2))⁻¹ ^ m p).coeff g * weight sigma z g‖)
    have hb := he.norm_sum_le
    rw [← ht] at hb
    simpa only [Function.comp_def, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← hformal, weight,
      AddEquiv.symm_apply_apply] using hb

end D5.S3.VertexAlgebra.CollisionAbsoluteEvaluation.Labelled
