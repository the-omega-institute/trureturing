/- GID: D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage
   mirror-E: none(waiver:selected-zero-dixon-original-average)
   anchors: []
   utility: none
   digest: Selected zero Dixon maxima admit the full original sixth-height physical-weight average. -/

import D5.S3.Arith.CharacterSums.PascadiZeroDCover
import D5.S3.Arith.CharacterSums.PascadiSeventhSingularCount
import D5.S3.Arith.CharacterSums.PascadiOriginalAlignedPartners
import D5.S3.Arith.CharacterSums.PascadiOriginalGoodRecordMoment
import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage

/-! The actual zero Dixon condition is imposed only on the nonzero-reduction
bad partners of one maximizing baseline per middle. Literal word data supply
the singular cover, both endpoint counts, long-chart heights and the complete
finite physical-weight average. Empty endpoint families are included. -/

open Polynomial
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

/-- Actual Dixon residual of the baseline and two endpoint coefficient rows. -/
def actualTripleDixon (q : Coordinate) (base e e' : Endpoint) : ℤ :=
  PrimeCube.residual ![coeffL q base, coeffL q e, coeffL q e']
    ![coeffM q base, coeffM q e, coeffM q e']
    ![coeffQ base, coeffQ e, coeffQ e']
    ![coeffR base, coeffR e, coeffR e']
    ![coeffS base, coeffS e, coeffS e']

/-- One actual maximizing baseline has zero Dixon residuals among its
nonzero-reduction bad partners; the empty endpoint family is included. -/
def actualRecordZeroDixon (p : ℕ) (q R V : Coordinate) (E : Finset Endpoint) : Prop :=
  E.Nonempty → ∃ base ∈ E,
    actualRecordBadDegree p q R V E = (actualRecordBadPartners p q R V E base).card ∧
    ∀ e ∈ (actualRecordBadPartners p q R V E base).filter
      (fun e => (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0),
    ∀ e' ∈ (actualRecordBadPartners p q R V E base).filter
      (fun e => (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0),
      actualTripleDixon q base e e' = 0

/-- The coefficient height is eighteen, independently of the physical height. -/
def sixthHeightConstant : ℝ := max 6804 (24 * (8 * (18 : ℝ)) ^ 4)

private theorem sixth_height_basic_bounds (p I J : ℝ) (hp : 0 < p)
    (hJI : J ≤ I) (hJ : 1 ≤ J)
    (hgap : sixthHeightConstant * (I * J) ^ 6 < p ^ 5) :
    18 ≤ p ∧ 8 * I * J < p ∧ 6 * I ^ 3 < p ^ 3 ∧ I ≤ p := by
  have hI : 1 ≤ I := hJ.trans hJI
  have hI0 : 0 ≤ I := by linarith
  have hB : 1 ≤ I * J := one_le_mul_of_one_le_of_one_le hI hJ
  have hK18 : (18 : ℝ) ^ 5 ≤ sixthHeightConstant := by
    norm_num [sixthHeightConstant]
  have hK8 : (8 : ℝ) ^ 6 ≤ sixthHeightConstant := by
    norm_num [sixthHeightConstant]
  have hK0 : 0 ≤ sixthHeightConstant := hK18.trans' (by norm_num)
  have h18pow : (18 : ℝ) ^ 5 < p ^ 5 :=
    (hK18.trans (le_mul_of_one_le_right hK0 (one_le_pow₀ hB))).trans_lt hgap
  have hp18 : 18 < p :=
    (pow_lt_pow_iff_left₀ (by norm_num) hp.le (by decide : 5 ≠ 0)).mp h18pow
  have hp1 : 1 ≤ p := by linarith
  have h8pow : (8 * (I * J)) ^ 6 < p ^ 6 := by
    calc
      _ = (8 : ℝ) ^ 6 * (I * J) ^ 6 := mul_pow _ _ _
      _ ≤ sixthHeightConstant * (I * J) ^ 6 :=
        mul_le_mul_of_nonneg_right hK8 (by positivity)
      _ < p ^ 5 := hgap
      _ ≤ p ^ 6 := pow_le_pow_right₀ hp1 (by decide : 5 ≤ 6)
  have hsmall : 8 * (I * J) < p :=
    (pow_lt_pow_iff_left₀ (by positivity) hp.le (by decide : 6 ≠ 0)).mp h8pow
  have hIB : I ≤ I * J := le_mul_of_one_le_right hI0 hJ
  have htwo : 2 * I < p := by linarith only [hsmall, hIB, hI]
  have hcubed := pow_lt_pow_left₀ htwo (by positivity : 0 ≤ 2 * I) (by decide : 3 ≠ 0)
  refine ⟨hp18.le, by nlinarith only [hsmall], ?_, by linarith only [htwo, hI]⟩
  nlinarith only [hcubed, pow_nonneg hI0 3]


private theorem original_zero_dixon_singular_cover (p : ℕ) (hp : p.Prime)
    (J₁ J₂ : ℝ) (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint) (S : Finset Endpoint) (e₀ : Endpoint)
    (he₀ : e₀ ∈ S) (hr : IsUnit (R.1 : ZMod (p^3)))
    (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hbase : WordSolution (p^3) a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical R V base.2).1 : ZMod (p^3)))
    (hk : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂)
    (hq : CoordinateBound J₁ J₂ q)
    (hb₁ : CoordinateBound J₁ J₂ base.1) (hb₂ : CoordinateBound J₁ J₂ base.2)
    (hS : ∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2)
    (hword : ∀ e ∈ S, WordSolution (p^3) a₁ a₂ R V q e)
    (hred : ∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hderiv : ∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
      ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
        ((V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0)
    (hzero : ∀ e ∈ S, ∀ e' ∈ S, actualTripleDixon q base e e' = 0)
    (hgap : sixthHeightConstant*(J₁*J₂)^6 < (p : ℝ)^5) :
    let b : ℤ := ((V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))).val
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧ f ∣ pencil q base e₀ ∧
        ((f.eval b : ℤ) : ZMod p) = 0 ∧ f.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ e ∈ S, ∃ f ∈ F, f ∣ pencil q base e) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let β := (V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q base hr ht hbase hx hy hk
  have hL : IsUnit ((((endpointL q base).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction (endpointL q base) β b hb]
    exact hu.1.map reduction
  let row : Option {e // e ∈ S} → Endpoint := fun i => i.elim base Subtype.val
  let l := fun i => coeffL q (row i)
  let m := fun i => coeffM q (row i)
  let u := fun i => coeffQ (row i)
  let v := fun i => coeffR (row i)
  let w := fun i => coeffS (row i)
  have hfamily (e : {e // e ∈ S}) : PrimeCube.familyPolynomial l m u v w e =
      pencil q base e.val := rfl
  have hrow (i : Option {e // e ∈ S}) :
      CoordinateBound J₁ J₂ (row i).1 ∧ CoordinateBound J₁ J₂ (row i).2 := by
    cases i with
    | none => exact ⟨hb₁, hb₂⟩
    | some e => exact hS e.val e.property
  have hcoeffs (i : Option {e // e ∈ S}) :=
    actual_coefficient_bounds J₁ J₂ q (row i) hq (hrow i).1 (hrow i).2
  obtain ⟨F, hcard, hF, hcover⟩ := PrimeCube.actual_zero_dixon_singular_factor_cover l m u v w
    (⟨e₀, he₀⟩ : {e // e ∈ S}) p b J₁ J₂ 18 h₁₂ h₂ (by norm_num)
    (fun i => (hcoeffs i).1) (fun i => (hcoeffs i).2.1)
    (fun i => (hcoeffs i).2.2.1)
    (fun i => (hcoeffs i).2.2.2.1)
    (fun i => (hcoeffs i).2.2.2.2)
    (by simpa only [l, m, row, coeffL, coeffM, endpointL, PrimeCube.linear,
      eval_add, eval_C, eval_mul, eval_X, Option.elim_none, mul_comm] using hL)
    (by intro e; simpa only [hfamily] using hred e.val e.property)
    (by intro e; simpa only [hfamily] using pencil_natDegree q base e.val)
    (by
      intro e
      rw [hfamily]
      exact actual_pencil_weighted_coeff J₁ J₂ q base e.val
        (h₂.trans h₁₂) h₂ hq hb₁ hb₂ (hS e.val e.property).1 (hS e.val e.property).2)
    (by
      intro e
      rw [hfamily]
      exact original_pencil_dvd hp a₁ a₂ ha₁ ha₂ R V q base e.val
        hr ht hbase (hword e.val e.property))
    (by
      intro e
      rw [hfamily]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      change (Int.castRingHom (ZMod p)) ((pencil q base e.val).derivative.eval b) = 0
      rw [← Polynomial.eval₂_at_apply]
      simp only [Int.coe_castRingHom, hb]
      exact hderiv e.val e.property)
    (by intro e e'; exact hzero e.val e.property e'.val e'.property)
    (by simpa only [sixthHeightConstant] using hgap)
  refine ⟨F, hcard, ?_, ?_⟩
  · intro f hf
    simpa only [hfamily] using hF f hf
  · intro e he
    simpa only [hfamily] using hcover (⟨e, he⟩ : {e // e ∈ S})

/-- The full actual nonzero-reduction derivative-zero partner stratum obeys
its original physical-weight bound under the sixth-height zero Dixon gap. -/
private theorem actual_nonzero_singular_partners_zero_dixon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ X Y H : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3))),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → physical B.R B.V q = (-w, -t) →
      J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0) →
      (∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
        ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
          ((B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0) →
      (∀ e ∈ S, ∀ e' ∈ S, actualTripleDixon q base e e' = 0) →
      sixthHeightConstant*(J₁*J₂)^6 < (p : ℝ)^5 →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε*
        (1 + 6*H / ((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_fixed_factor_value_pairs_subpower ε hε
  refine ⟨3*C, by positivity, ?_⟩
  intro p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk
    hqc hb₁ hb₂ hS hword hbox hred hderiv hzero hgap
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have htu : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by
    simpa only [hq, Int.cast_neg, neg_neg] using ht
  have htuval : (htu.unit : ZMod (p^3)) = t := by
    rw [htu.unit_spec]
    simp only [hq, Int.cast_neg, neg_neg]
  have hk' : IsUnit (1-a₁*a₂*(htu.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [htuval, ht.unit_spec] using hk
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hSempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
  obtain ⟨F, hcard, hF, hcover⟩ := original_zero_dixon_singular_cover p hp J₁ J₂
    a₁ a₂ ha₁ ha₂ B.R B.V q base S e₀ he₀ hr htu hbase hx hy hk'
    h₁₂ h₂ hqc hb₁ hb₂ hS hword hred hderiv hzero hgap
  let β := (B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hnum := sixth_height_basic_bounds (p : ℝ) J₁ J₂
    (by exact_mod_cast hp.pos) h₁₂ h₂ hgap
  have hbound (z : Coordinate) (hz : CoordinateBound J₁ J₂ z) : CoordinateBound p p z :=
    ⟨hz.1.trans hnum.2.2.2, hz.2.trans (h₁₂.trans hnum.2.2.2)⟩
  have hP : pencil q base e₀ ≠ 0 := by
    intro hz
    simpa only [hz, Polynomial.map_zero, ne_eq, not_true_eq_false] using hred e₀ he₀
  have hFQ (f : ℤ[X]) (hf : f ∈ F) : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hF f hf).2.1).mp
      (hF f hf).1
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ B.R B.V q base
    hr htu hbase hx hy hk'
  have hQu : IsUnit ((((endpointQ base).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction (endpointQ base) β b hb]
    exact hu.2.1.map reduction
  have hQZu : IsUnit
      ((((endpointQ base-endpointL q base*coordinateLinear q).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction _ β b hb]
    exact hu.2.2.map reduction
  let W : ℝ := 1 + 6*H / ((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hfactor (f : ℤ[X]) (hf : f ∈ F) :
      ((singularFactorEndpoints f q base S).card : ℝ) ≤ C*(p : ℝ)^ε*W := by
    letI : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨hFQ f hf⟩
    have hpoint := actual_singular_factor_partner_count hp hX hY hXsmall hYsmall
      B B₂ H hH hHsq a₁ a₂ ha₁ ha₂ q hq hr ht hw hk base hbase hx hy
      f (hF f hf).2.1 b hb (hF f hf).2.2.2.1 S hword hbox
    have hvalues := hcount p hnum.1 q base S e₀ he₀ (hbound q hqc)
      (hbound base.1 hb₁) (hbound base.2 hb₂)
      (fun e he => ⟨hbound e.1 (hS e he).1, hbound e.2 (hS e he).2⟩)
      hP f (hF f hf).2.1 (hF f hf).2.2.1 b (hF f hf).2.2.2.1 hQu hQZu
    exact hpoint.trans (mul_le_mul_of_nonneg_right hvalues hW)
  have hsubset : S ⊆ F.biUnion (fun f => singularFactorEndpoints f q base S) := by
    intro e he
    obtain ⟨f, hf, hfe⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_filter.mpr ⟨he, hfe⟩⟩
  have hScard : S.card ≤ ∑ f ∈ F, (singularFactorEndpoints f q base S).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  calc
    (S.card : ℝ) ≤ ∑ f ∈ F, ((singularFactorEndpoints f q base S).card : ℝ) := by
      exact_mod_cast hScard
    _ ≤ ∑ _f ∈ F, C*(p : ℝ)^ε*W := Finset.sum_le_sum hfactor
    _ = (F.card : ℝ)*(C*(p : ℝ)^ε*W) := by simp
    _ ≤ 3*(C*(p : ℝ)^ε*W) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ = (3*C)*(p : ℝ)^ε*W := by ring

private theorem actual_derivative_zero_partners_subpower_zero_dixon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ X Y H : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3))),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → physical B.R B.V q = (-w, -t) →
      J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
        ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
          ((B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0) →
      (∀ e ∈ (S.filter fun e => (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0), ∀ e' ∈ (S.filter fun e => (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0),
        actualTripleDixon q base e e' = 0) →
      sixthHeightConstant*(J₁*J₂)^6 < (p : ℝ)^5 →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C₀, hC₀, hzeroCount⟩ := actual_zero_reduction_partners_subpower_seventh ε hε
  obtain ⟨C₁, hC₁, hnonzero⟩ := actual_nonzero_singular_partners_zero_dixon ε hε
  refine ⟨C₀+C₁, by positivity, ?_⟩
  intro p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk
    hqc hb₁ hb₂ hS hword hbox hderiv hzero hgap
  have hnum := sixth_height_basic_bounds (p : ℝ) J₁ J₂
    (by exact_mod_cast hp.pos) h₁₂ h₂ hgap
  let Z := fun e : Endpoint => (pencil q base e).map (Int.castRingHom (ZMod p)) = 0
  let S₀ := S.filter Z
  let S₁ := S.filter fun e => ¬ Z e
  have hrestrict₀ {P : Endpoint → Prop} (h : ∀ e ∈ S, P e) : ∀ e ∈ S₀, P e :=
    fun e he => h e (Finset.mem_filter.mp he).1
  have hrestrict₁ {P : Endpoint → Prop} (h : ∀ e ∈ S, P e) : ∀ e ∈ S₁, P e :=
    fun e he => h e (Finset.mem_filter.mp he).1
  have htu : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by
    simpa only [hq, Int.cast_neg, neg_neg] using ht
  have htuval : (htu.unit : ZMod (p^3)) = t := by
    rw [htu.unit_spec]
    simp only [hq, Int.cast_neg, neg_neg]
  have hk' : IsUnit (1-a₁*a₂*(htu.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [htuval, ht.unit_spec] using hk
  have h₀ : (S₀.card : ℝ) ≤ C₀*(p : ℝ)^ε :=
    hzeroCount p hp J₁ J₂ X Y t w B a₁ a₂ ha₁ ha₂ q base S₀ hr htu hw
      hq hXsmall hYsmall h₁₂ h₂ hbase hx hy hk' hqc hb₁ hb₂
      (hrestrict₀ hS) (hrestrict₀ hword) (hrestrict₀ hbox)
      (fun _ he => (Finset.mem_filter.mp he).2) hnum.2.1 hnum.2.2.1 hnum.2.2.2
  have h₁ : (S₁.card : ℝ) ≤ C₁*(p : ℝ)^ε*
      (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) :=
    hnonzero p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S₁ hr ht hw
      hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk hqc hb₁ hb₂
      (hrestrict₁ hS) (hrestrict₁ hword) (hrestrict₁ hbox)
      (fun _ he => (Finset.mem_filter.mp he).2) (hrestrict₁ hderiv) hzero hgap
  let W : ℝ := 1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))
  have hW : 1 ≤ W := by
    have hh : 0 ≤ 6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R)) := by positivity
    dsimp only [W]
    linarith
  have hcard : (S.card : ℝ) = (S₀.card : ℝ)+(S₁.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) Z).symm
  calc
    (S.card : ℝ) = (S₀.card : ℝ)+(S₁.card : ℝ) := hcard
    _ ≤ C₀*(p : ℝ)^ε+C₁*(p : ℝ)^ε*W := add_le_add h₀ h₁
    _ ≤ C₀*(p : ℝ)^ε*W+C₁*(p : ℝ)^ε*W := add_le_add
      (show C₀*(p : ℝ)^ε ≤ C₀*(p : ℝ)^ε*W from
        le_mul_of_one_le_right (by positivity) hW) le_rfl
    _ = (C₀+C₁)*(p : ℝ)^ε*W := by ring


private theorem actual_record_bad_degree_subpower_zero_dixon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ X Y H : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (E : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3))),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → physical B.R B.V q = (-w, -t) →
      J₂ ≤ J₁ → 1 ≤ J₂ →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q →
      (∀ e ∈ E, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ E, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ E, IsUnit ((physical B.R B.V e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical B.R B.V e.2).1 : ZMod (p^3))) →
      (∀ e ∈ E, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      actualRecordZeroDixon p q B.R B.V E →
      sixthHeightConstant*(J₁*J₂)^6 < (p : ℝ)^5 →
      (actualRecordBadDegree p q B.R B.V E : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_derivative_zero_partners_subpower_zero_dixon ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q E hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hk hqc hE hword hunit hbox
    hzero hgap
  by_cases hne : E.Nonempty
  · obtain ⟨base, hb, hmax, hbasezero⟩ := hzero hne
    rw [hmax]
    let S := actualRecordBadPartners p q B.R B.V E base
    have hmem (e : Endpoint) (he : e ∈ S) : e ∈ E := (Finset.mem_filter.mp he).1
    apply hcount p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
      hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ (hword base hb)
      (hunit base hb).1 (hunit base hb).2 hk hqc (hE base hb).1 (hE base hb).2
      (fun e he => hE e (hmem e he)) (fun e he => hword e (hmem e he))
      (fun e he => hbox e (hmem e he)) ?_ hbasezero hgap
    intro e he
    have hd := (Finset.mem_filter.mp he).2
    have hinv : (↑hr.unit⁻¹ : ZMod (p^3)) = (B.R.1 : ZMod (p^3))⁻¹ := by
      rw [← ZMod.inv_coe_unit, hr.unit_spec]
    simpa only [recordBeta, hinv] using hd
  · have hEzero : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hdegree : actualRecordBadDegree p q B.R B.V ∅ = 0 := by
      simp [actualRecordBadDegree]
    rw [hEzero, hdegree, Nat.cast_zero]
    positivity


private theorem actual_long_bad_degree_subpower_zero_dixon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ) (t w : ℤ)
      (B : ReducedMiddleBasis (p^3) t w X Y)
      (B₂ : ReducedMiddleBasis (p^2) t w X Y)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (E : Finset Endpoint),
      0 < X → 0 < Y → 2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) →
      0 < H → H^2 = X*Y → (w,t) ∈ literalBox X Y →
      physical B.R B.V q = (-w,-t) →
      ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R →
      IsUnit (B.R.1 : ZMod (p^3)) →
      IsUnit (t : ZMod (p^3)) → IsUnit (w : ZMod (p^3)) →
      IsUnit (1+a₁*a₂*(t : ZMod (p^3))*(w : ZMod (p^3))) →
      (∀ e ∈ E, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ E, IsUnit ((physical B.R B.V e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical B.R B.V e.2).1 : ZMod (p^3))) →
      (∀ e ∈ E, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      actualRecordZeroDixon p q B.R B.V E →
      sixthHeightConstant*(32*(X*Y/(p : ℝ)^3))^6 < (p : ℝ)^5 →
      (actualRecordBadDegree p q B.R B.V E : ℝ) ≤ C*(p : ℝ)^ε*
        (1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hdegree⟩ := actual_record_bad_degree_subpower_zero_dixon ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q E hX hY hXsmall hYsmall
    hH hHsq hparameter hq hlong hr ht hw hk hword heunit hebox hzero hgap
  have hc : 0 < p^3 := pow_pos hp.pos _
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hQ : 0 < weightedSq X Y B.R := weightedSq_pos hX hY (B.first_ne_zero hc)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hQ
  have hσsq : σ^2 = weightedSq X Y B.R := Real.sq_sqrt hQ.le
  have hσhi : weightedSq X Y B.R < 4*σ^2 := by rw [hσsq]; linarith
  let J₁ := 8*H/σ
  let J₂ := 4*H*σ/(p : ℝ)^3
  obtain ⟨horder, hJ₂, hprod, _⟩ := B.long_scale_bounds hc hX hY H σ
    hH hHsq hσ hσsq.le hσhi hlong
  have horder' : J₂ ≤ J₁ := by simpa only [J₁, J₂, Nat.cast_pow] using horder
  have hJ₂' : 1 ≤ J₂ := by
    have hh : 2 < J₂ := by simpa only [J₂, Nat.cast_pow] using hJ₂
    linarith
  have hprod' : J₁*J₂ = 32*(X*Y/(p : ℝ)^3) := by
    simpa only [J₁, J₂, Nat.cast_pow] using hprod
  have hcoord (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
      CoordinateBound J₁ J₂ z := by
    simpa only [J₁, J₂, Nat.cast_pow] using
      B.coordinate_bound hc hX hY H σ hH hHsq hσ hσsq.le hσhi z hz
  have hqc : CoordinateBound J₁ J₂ q := by
    apply hcoord
    rw [hq]
    exact anchor_mem_literalBox hparameter.1 hparameter.2
  have hEc : ∀ e ∈ E, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2 := by
    intro e he
    exact ⟨hcoord _ (hebox e he).1, hcoord _ (hebox e he).2⟩
  have hk' : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [hq, ht.unit_spec, Int.cast_neg, mul_neg, sub_neg_eq_add] using hk
  have hgap' : sixthHeightConstant*(J₁*J₂)^6 < (p : ℝ)^5 := by
    rw [hprod']
    exact hgap
  exact hdegree p hp J₁ J₂ X Y H t w B.toMiddleBasis B₂ a₁ a₂ ha₁ ha₂ q E
    hr ht hw hX hY hXsmall hYsmall hH hHsq hq horder' hJ₂' hk' hqc hEc
    hword heunit hebox hzero hgap'


/-- Average the actual bad degrees over the literal original parameter set.
Reduced prime-square bases are selected only on that finite set; no coordinate,
counting, or physical-weight bound is supplied as a hypothesis. -/
theorem actual_long_bad_degree_average_zero_dixon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      1 ≤ X → X ≤ Y → 2*Y < (p : ℝ)^3 → X*Y < 2*(p : ℝ)^4 →
      0 < H → H^2 = X*Y → (p : ℝ) ≤ H → IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (1+a₁*a₂*(wt.2 : ZMod (p^3))*(wt.1 : ZMod (p^3)))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) →
      (∀ wt ∈ s, actualRecordZeroDixon p (q wt) (RV wt).1 (RV wt).2 (E wt)) →
      sixthHeightConstant*(32*(X*Y/(p : ℝ)^3))^6 < (p : ℝ)^5 →
      (∑ wt ∈ s, (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) ≤
        C*(p : ℝ)^ε*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
          (X*Y)^2/(p : ℝ)^4) := by
  classical
  obtain ⟨C, hC, hdegree⟩ := actual_long_bad_degree_subpower_zero_dixon ε hε
  refine ⟨12288*C, by positivity, ?_⟩
  intro p hp X Y H a₁ a₂ q RV s E hX1 hXY hYsmall hAcut hH hHsq hHp ha₁ ha₂
    hsbox hred hanchor hlong hr hunit hrhs hword heunit hebox hzero hgap
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY : 0 < Y := hX.trans_le hXY
  have hp2 : 0 < p^2 := pow_pos hp.pos _
  letI : NeZero (p^2) := ⟨hp2.ne'⟩
  let f : ZMod (p^3) →+* ZMod (p^2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) (ZMod (p^2))
  have hunit₂ (wt : Coordinate) (hw : wt ∈ s) :
      IsUnit (wt.2 : ZMod (p^2)) ∧ IsUnit (wt.1 : ZMod (p^2)) :=
    ⟨by simpa only [map_intCast] using (hunit wt hw).1.map f,
      by simpa only [map_intCast] using (hunit wt hw).2.map f⟩
  have hex (wt : Coordinate) (hw : wt ∈ s) :
      Nonempty (ReducedMiddleBasis (p^2) wt.2 wt.1 X Y) :=
    exists_reduced_middle_basis (p^2) wt.2 wt.1 X Y hp2 hX hY (hunit₂ wt hw).2
  let U := fun wt => if hw : wt ∈ s then (Classical.choice (hex wt hw)).R else 0
  have hB₂ (wt : Coordinate) (hw : wt ∈ s) :
      ∃ B₂ : ReducedMiddleBasis (p^2) wt.2 wt.1 X Y, U wt = B₂.R :=
    ⟨Classical.choice (hex wt hw), dif_pos hw⟩
  have hYcut : Y < (p : ℝ)^3 := by linarith
  have hYcube : 2*Y < (p^3 : ℕ) := by exact_mod_cast hYsmall
  have hXcube : 2*X < (p^3 : ℕ) := (by linarith : 2*X ≤ 2*Y).trans_lt hYcube
  let W := fun wt => 1+H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))
  have hD (wt : Coordinate) (hw : wt ∈ s) :
      (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ) ≤
        (6*C)*(p : ℝ)^ε*W wt := by
    obtain ⟨B, hBR, hBV⟩ := hred wt hw
    obtain ⟨B₂, hBU⟩ := hB₂ wt hw
    have hq : physical B.R B.V (q wt) = (-wt.1,-wt.2) := by
      rw [hBR, hBV]
      exact (hanchor wt hw).trans (Prod.ext (Prod.fst_neg wt) (Prod.snd_neg wt))
    have hlongB : ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R := by
      rw [hHsq, hBR]
      simpa only [Nat.cast_pow] using hlong wt hw
    have hd := hdegree p hp X Y H wt.2 wt.1 B B₂ a₁ a₂ ha₁ ha₂ (q wt) (E wt)
      hX hY hXcube hYcube hH hHsq (hsbox wt hw) hq hlongB
      (by simpa only [hBR] using hr wt hw) (hunit wt hw).1 (hunit wt hw).2 (hrhs wt hw)
      (by simpa only [hBR, hBV] using hword wt hw)
      (by simpa only [hBR, hBV] using heunit wt hw)
      (by simpa only [hBR, hBV] using hebox wt hw)
      (by simpa only [hBR, hBV] using hzero wt hw) hgap
    have hd' : (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ) ≤
        C*(p : ℝ)^ε*(1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))) := by
      simpa only [hBR, hBV, ← hBU] using hd
    have hwscale : 1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt))) ≤ 6*W wt := by
      dsimp only [W]
      simp only [mul_div_assoc]
      linarith
    calc
      _ ≤ C*(p : ℝ)^ε*(1+6*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))) := hd'
      _ ≤ C*(p : ℝ)^ε*(6*W wt) := mul_le_mul_of_nonneg_left hwscale (by positivity)
      _ = _ := by ring
  have hweight := actual_physical_weight_average hp hX1 hXY hYcut hAcut hH hHsq hHp
    s hsbox hunit₂ U hB₂
  change (∑ wt ∈ s, W wt) ≤ _ at hweight
  calc
    _ ≤ ∑ wt ∈ s, (6*C)*(p : ℝ)^ε*W wt := Finset.sum_le_sum hD
    _ = ((6*C)*(p : ℝ)^ε)*(∑ wt ∈ s, W wt) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((6*C)*(p : ℝ)^ε)*(2048*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
        (X*Y)^2/(p : ℝ)^4)) := mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring


end
end D5.S3.Arith.CharacterSums.Original
