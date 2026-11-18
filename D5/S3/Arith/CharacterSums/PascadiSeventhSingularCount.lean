/- GID: D5/S3/Arith/CharacterSums/PascadiSeventhSingularCount
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSeventhSingularCount
   mirror-E: none(waiver:actual-seventh-height-singular-count)
   anchors: []
   utility: none
   digest: Actual singular partners satisfy the physical bound under seventh height. -/

import D5.S3.Arith.CharacterSums.PascadiSeventhHeightCover
import D5.S3.Arith.CharacterSums.PascadiSeventhHeightRange
import D5.S3.Arith.CharacterSums.PascadiSingularValueEnvelope
import D5.S3.Arith.CharacterSums.PascadiOriginalSingularCount

/-! The actual endpoint realization follows the original singular count, with
its cover replaced by structural seventh-height elimination and its algebraic
value estimate replaced by the enlarged field-uniform envelope. -/

open Polynomial
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem original_seventh_singular_cover (p : ℕ) (hp : p.Prime)
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
    (hgap : seventhHeightConstant*(J₁*J₂)^7 < (p : ℝ)^5) :
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
  obtain ⟨F, hcard, hF, hcover⟩ := PrimeCube.actual_seventh_height_singular_factor_cover l m u v w
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
    (by simpa only [seventhHeightConstant] using hgap)
  refine ⟨F, hcard, ?_, ?_⟩
  · intro f hf
    simpa only [hfamily] using hF f hf
  · intro e he
    simpa only [hfamily] using hcover (⟨e, he⟩ : {e // e ∈ S})

/-- The full actual nonzero-reduction derivative-zero partner stratum obeys
its original physical-weight bound under the structural seventh-height gap. -/
theorem actual_nonzero_singular_partners_seventh (ε : ℝ) (hε : 0 < ε) :
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
      seventhHeightConstant*(J₁*J₂)^7 < (p : ℝ)^5 →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε*
        (1 + 6*H / ((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_fixed_factor_value_pairs_subpower ε hε
  refine ⟨3*C, by positivity, ?_⟩
  intro p hp J₁ J₂ X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk
    hqc hb₁ hb₂ hS hword hbox hred hderiv hgap
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
  obtain ⟨F, hcard, hF, hcover⟩ := original_seventh_singular_cover p hp J₁ J₂
    a₁ a₂ ha₁ ha₂ B.R B.V q base S e₀ he₀ hr htu hbase hx hy hk'
    h₁₂ h₂ hqc hb₁ hb₂ hS hword hred hderiv hgap
  let β := (B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hnum := seventh_height_basic_bounds (p : ℝ) J₁ J₂
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

end
end D5.S3.Arith.CharacterSums.Original
