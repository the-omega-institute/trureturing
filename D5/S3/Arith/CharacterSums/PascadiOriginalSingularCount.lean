/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalSingularCount
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalSingularCount
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: Actual nonzero singular partners have a subpower bound with one physical weight. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalSingularPartners
import D5.S3.Arith.CharacterSums.PascadiOriginalLinearFibers

/-! Algebraic values count actual original partners with one physical linear-fiber weight. -/

open Polynomial NumberField
open scoped NumberField BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

private theorem singular_value_injective {p : ℕ} [Fact p.Prime]
    (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hprim : F.IsPrimitive) (hdeg : 2 ≤ F.natDegree)
    (b : ℤ) (hFb : ((F.eval b : ℤ) : ZMod p) = 0)
    (q : Coordinate) (base : Endpoint)
    (hL : IsUnit (((endpointL q base).eval b : ℤ) : ZMod p)) :
    Function.Injective (singularFactorValue F q base) := by
  intro x y hxy
  have hdvd := singular_value_coordinate_divisibility F hprim b hFb q base hL x y hxy
  have hd : (coordinateLinear x-coordinateLinear y).natDegree ≤ 1 := by
    unfold coordinateLinear PrimeCube.linear
    compute_degree
  have hz : coordinateLinear x-coordinateLinear y = 0 := by
    by_contra hn
    have hh := (natDegree_le_of_dvd hdvd hn).trans hd
    omega
  have h₀ := congrArg (fun P : ℤ[X] => P.coeff 0) hz
  have h₁ := congrArg (fun P : ℤ[X] => P.coeff 1) hz
  simp only [coordinateLinear, PrimeCube.linear, coeff_sub, coeff_add,
    coeff_C, coeff_C_mul_X, coeff_zero] at h₀ h₁
  norm_num at h₀ h₁
  exact Prod.ext (sub_eq_zero.mp h₀) (sub_eq_zero.mp h₁)

private theorem primitive_linear_coefficients (F : ℤ[X])
    (hprim : F.IsPrimitive) (hd : F.natDegree = 1) :
    Int.gcd (F.coeff 1) (F.coeff 0) = 1 := by
  let g := Int.gcd (F.coeff 1) (F.coeff 0)
  have hg : IsUnit (g : ℤ) := hprim _ ((C_dvd_iff_dvd_coeff _ _).mpr (by
    intro j
    rcases j with _ | j
    · exact Int.gcd_dvd_right _ _
    rcases j with _ | j
    · exact Int.gcd_dvd_left _ _
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _))
  simpa only [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] using hg

private theorem linear_divisor_coordinate_value (F : ℤ[X]) (hd : F.natDegree = 1)
    (x y : Coordinate) (hxy : F ∣ coordinateLinear x-coordinateLinear y) :
    F.coeff 1*x.1-F.coeff 0*x.2 = F.coeff 1*y.1-F.coeff 0*y.2 := by
  obtain ⟨U, hU⟩ := hxy
  by_cases hz : coordinateLinear x-coordinateLinear y = 0
  · have h₀ := congrArg (fun P : ℤ[X] => P.coeff 0) hz
    have h₁ := congrArg (fun P : ℤ[X] => P.coeff 1) hz
    simp only [coordinateLinear, PrimeCube.linear, coeff_sub, coeff_add,
      coeff_C, coeff_C_mul_X, coeff_zero] at h₀ h₁
    norm_num at h₀ h₁
    linear_combination F.coeff 1*h₀-F.coeff 0*h₁
  have hFn : F ≠ 0 := by intro h; simp [h] at hd
  have hUn : U ≠ 0 := by intro h; rw [h, mul_zero] at hU; exact hz hU
  have hUdeg : U.natDegree = 0 := by
    have hdxy : (coordinateLinear x-coordinateLinear y).natDegree ≤ 1 := by
      unfold coordinateLinear PrimeCube.linear
      compute_degree
    rw [hU, natDegree_mul hFn hUn, hd] at hdxy
    omega
  rw [eq_C_of_natDegree_eq_zero hUdeg] at hU
  have h₀ := congrArg (fun P : ℤ[X] => P.coeff 0) hU
  have h₁ := congrArg (fun P : ℤ[X] => P.coeff 1) hU
  simp only [coordinateLinear, PrimeCube.linear, coeff_sub, coeff_add,
    coeff_C, coeff_C_mul_X, coeff_mul_C] at h₀ h₁
  norm_num at h₀ h₁
  linear_combination F.coeff 1*h₀-F.coeff 0*h₁

/-- For a genuine relevant factor, passing from its algebraic value pairs to
actual original partners costs the physical linear-fiber weight only once.
Factors of degree at least two are injective on both actual coordinates;
linear factors use the original word to recover the second endpoint. -/
theorem actual_singular_factor_partner_count {p : ℕ} (hp : p.Prime) {t w : ℤ}
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hXsmall : 2 * X < (p^3 : ℕ)) (hYsmall : 2 * Y < (p^3 : ℕ))
    (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
    (H : ℝ) (hH : 0 < H) (hHsq : H^2 = X*Y)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (q : Coordinate) (hq : physical B.R B.V q = (-w, -t))
    (hr : IsUnit (B.R.1 : ZMod (p^3)))
    (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3)))
    (hk : IsUnit (1 - a₁ * a₂ * (ht.unit : ZMod (p^3)) *
      ((physical B.R B.V q).1 : ZMod (p^3))))
    (base : Endpoint) (hbase : WordSolution (p^3) a₁ a₂ B.R B.V q base)
    (hx : IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)))
    (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hprim : F.IsPrimitive) (b : ℤ)
    (hb : (b : ZMod p) =
      (ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
        ((B.V.1 : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3))))
    (hFb : ((F.eval b : ℤ) : ZMod p) = 0)
    (S : Finset Endpoint)
    (hword : ∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e)
    (hbox : ∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
      physical B.R B.V e.2 ∈ literalBox X Y) :
    ((singularFactorEndpoints F q base S).card : ℝ) ≤
      (singularFactorValuePairs F q base S).card *
        (1 + 6 * H / ((p : ℝ) * Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let reduction : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  let β := (B.V.1 : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3))
  have htu : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by
    simpa only [hq, Int.cast_neg, neg_neg] using ht
  have htuval : (htu.unit : ZMod (p^3)) = t := by
    rw [htu.unit_spec]
    simp only [hq, Int.cast_neg, neg_neg]
  have hk' : IsUnit (1 - a₁ * a₂ * (htu.unit : ZMod (p^3)) *
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [htuval, ht.unit_spec] using hk
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂
    B.R B.V q base hr htu hbase hx hy hk'
  have hLu : IsUnit (((endpointL q base).eval b : ℤ) : ZMod p) := by
    rw [← reduce_eval_at_lift reduction (endpointL q base) β b hb]
    exact hu.1.map reduction
  let W : ℝ := 1 + 6 * H / ((p : ℝ) * Real.sqrt (weightedSq X Y B₂.R))
  have hW : 1 ≤ W := by
    have hh : 0 ≤ 6 * H / ((p : ℝ) * Real.sqrt (weightedSq X Y B₂.R)) :=
      div_nonneg (by positivity) (by positivity)
    dsimp only [W]
    linarith
  let s := S.filter (fun e => F ∣ pencil q base e)
  let value (e : Endpoint) :=
    (singularFactorValue F q base e.1, singularFactorValue F q base e.2)
  change (s.card : ℝ) ≤ (s.image value).card * W
  by_cases hd : 2 ≤ F.natDegree
  · have hinj : Function.Injective value := by
      intro e e' he
      exact Prod.ext
        (singular_value_injective F hprim hd b hFb q base hLu (congrArg Prod.fst he))
        (singular_value_injective F hprim hd b hFb q base hLu (congrArg Prod.snd he))
    rw [Finset.card_image_of_injective _ hinj]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hW
  have hdpos : 1 ≤ F.natDegree := by
    by_contra hn
    have hd0 : F.natDegree = 0 := by omega
    have hconst := eq_C_of_natDegree_eq_zero hd0
    have hc : C (F.coeff 0) ∣ F := ⟨1, by simpa only [mul_one] using hconst⟩
    have hunit : IsUnit F := hconst.symm ▸ (isUnit_C.mpr (hprim _ hc))
    have hi : Irreducible F :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mpr
        (Fact.out : Irreducible (F.map (Int.castRingHom ℚ)))
    exact hi.not_isUnit hunit
  have hd1 : F.natDegree = 1 := by omega
  have hab := primitive_linear_coefficients F hprim hd1
  have hFlinear : (F.coeff 1 : ZMod p) * (b : ZMod p) + F.coeff 0 = 0 := by
    have hshape := eq_X_add_C_of_natDegree_le_one hd1.le
    have hFb' := hFb
    rw [hshape] at hFb'
    simpa only [eval_add, eval_mul, eval_C, eval_X, Int.cast_add, Int.cast_mul] using hFb'
  have hβ : (B.R.1 : ZMod p) * (b : ZMod p) = B.V.1 := by
    have hcancel : (B.R.1 : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3)) = 1 := by
      calc
        _ = (hr.unit : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3)) :=
          congrArg (fun z : ZMod (p^3) => z * (↑hr.unit⁻¹ : ZMod (p^3))) hr.unit_spec.symm
        _ = 1 := by simp
    have hh : (B.R.1 : ZMod (p^3)) * β = B.V.1 := by
      dsimp only [β]
      calc
        _ = (B.V.1 : ZMod (p^3)) * ((B.R.1 : ZMod (p^3)) * ↑hr.unit⁻¹) := by ring
        _ = B.V.1 := by rw [hcancel, mul_one]
    have hh' := congrArg reduction hh
    have hredβ : reduction β = (b : ZMod p) := hb.symm
    simpa only [map_mul, map_intCast, hredβ] using hh'
  have hroot : ((F.coeff 1 * B.V.1 + F.coeff 0 * B.R.1 : ℤ) : ZMod p) = 0 := by
    push_cast
    linear_combination (B.R.1 : ZMod p)*hFlinear-(F.coeff 1 : ZMod p)*hβ
  have hfiber (v) (hv : v ∈ s.image value) :
      ((s.filter (fun e => value e = v)).card : ℝ) ≤ W := by
    obtain ⟨e₀, he₀, he₀v⟩ := Finset.mem_image.mp hv
    apply actual_linear_factor_partner_count hp hX hY hXsmall hYsmall B B₂ H hH hHsq
      (F.coeff 1) (F.coeff 0) (F.coeff 1*e₀.1.1-F.coeff 0*e₀.1.2) hab
      a₁ a₂ ha₁ ha₂ q hq ht hw hk hroot (s.filter (fun e => value e = v))
    · intro e he
      exact hword e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    · intro e he
      exact hbox e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    · intro e he
      have heq : value e = value e₀ := (Finset.mem_filter.mp he).2.trans he₀v.symm
      exact linear_divisor_coordinate_value F hd1 e.1 e₀.1
        (singular_value_coordinate_divisibility F hprim b hFb q base hLu e.1 e₀.1
          (congrArg Prod.fst heq))
  calc
    (s.card : ℝ) = ∑ v ∈ s.image value,
        ((s.filter (fun e => value e = v)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image value s
    _ ≤ ∑ _v ∈ s.image value, W := Finset.sum_le_sum hfiber
    _ = _ := by simp

/-- The actual nonzero singular stratum of the original word problem has a
uniform subpower partner bound, with the rational physical multiplicity paid
once. The factors, their relevance, their algebraic values and their height
bounds are all constructed from the retained original endpoints. -/
theorem actual_nonzero_singular_partners_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y H : ℝ) (t w : ℤ)
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
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε*
        (1 + 6*H / ((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_singular_value_pairs_subpower ε hε
  refine ⟨3*C, by positivity, ?_⟩
  intro p hp J₁ J₂ M X Y H t w B B₂ a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hX hY hXsmall hYsmall hH hHsq hq h₁₂ h₂ hbase hx hy hk
    hqc hb₁ hb₂ hS hword hbox hred hderiv hcap hlargeR hlargeQ
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have htu : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by
    simpa only [hq, Int.cast_neg, neg_neg] using ht
  have htuval : (htu.unit : ZMod (p^3)) = t := by
    rw [htu.unit_spec]
    simp only [hq, Int.cast_neg, neg_neg]
  have hk' : IsUnit (1-a₁*a₂*(htu.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    simpa only [htuval, ht.unit_spec] using hk
  obtain ⟨F, hcard, hF, hcover, hvalues⟩ := hcount p hp J₁ J₂ M a₁ a₂ ha₁ ha₂
    B.R B.V q base S hr htu h₁₂ h₂ hbase hx hy hk'
    hqc hb₁ hb₂ hS hword hred hderiv hcap hlargeR hlargeQ
  let β := (B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  let W : ℝ := 1 + 6*H / ((p : ℝ)*Real.sqrt (weightedSq X Y B₂.R))
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hfactor (f : ℤ[X]) (hf : f ∈ F) :
      ((singularFactorEndpoints f q base S).card : ℝ) ≤ C*(p : ℝ)^ε*W := by
    letI : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨(hF f hf).2.2.1⟩
    have hpoint := actual_singular_factor_partner_count hp hX hY hXsmall hYsmall
      B B₂ H hH hHsq a₁ a₂ ha₁ ha₂ q hq hr ht hw hk base hbase hx hy
      f (hF f hf).2.1 b hb (hF f hf).2.2.2.2 S hword hbox
    exact hpoint.trans (mul_le_mul_of_nonneg_right
      (hvalues f hf (hF f hf).2.2.1) hW)
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
