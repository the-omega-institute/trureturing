/- GID: D5/S3/TotalVariation/QuotientParitySpectrum
   generality: G
   mirror-B: D5/B/S3/TotalVariation/QuotientParitySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fair subgroup and the shifted quotient spectrum characterize affine parity laws. -/

import D5.S3.TotalVariation.PositiveParitySpectrum
import D5.S3.Entropy.Forgetting.CapacityMonotone
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Affine parity realizability for normalized masses with arbitrary signed and zero moments. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.QuotientParitySpectrum

open D5.S3.TotalVariation.GroupedParityBias
open D5.S3.TotalVariation.PositiveParitySpectrum
  (orderedMomentProducts positive_moment_realizability)
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

universe u v
variable {A : Type u} {I : Type v} [AddCommGroup A] [Fintype A] [Fintype I]

theorem moment_from_inputs (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ) (χ : AddChar A ℂ) :
    moment (law c s q) χ = sign χ s * ∏ i, if sign χ (c i) = -1 then q i else 1 := by
  classical
  rw [moment_factor two, ← Finset.prod_fiberwise Finset.univ c, Finset.prod_filter]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : sign χ a = -1
  · rw [ite_eq_left ha, groupBias]
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_filter.mp hi).2, ha]
  · rw [ite_eq_right ha]
    symm
    apply Finset.prod_eq_one
    intro i hi
    simp [(Finset.mem_filter.mp hi).2, ha]

theorem sign_phase_and_magnitude (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ) :
    let s' := s + ∑ i with q i < 0, c i
    ∀ χ, moment (law c s q) χ =
      sign χ s' * moment (law c (0 : A) (fun i => |q i|)) χ := by
  classical
  intro s' χ
  have h0 : sign χ (0 : A) = 1 := by simp [sign]
  have hphase : sign χ s' = sign χ s * ∏ i, if q i < 0 then sign χ (c i) else 1 := by
    dsimp only [s']
    rw [sign_add two, sign_sum two, Finset.prod_filter]
  rw [moment_from_inputs two, hphase, moment_from_inputs two, h0, one_mul, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases value_cases two χ (c i) with hs | hs
  · norm_num [sign, hs]
  · have hs' : sign χ (c i) = -1 := by simp [sign, hs]
    rcases lt_or_ge (q i) 0 with hq | hq
    · simp [hs', hq, abs_of_neg hq]
    · simp [hs', not_lt.mpr hq, abs_of_nonneg hq]

theorem support_iff_trivial_on_fair_columns (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ) (χ : AddChar A ℂ) :
    moment (law c s q) χ ≠ 0 ↔ ∀ i, q i = 0 → χ (c i) = 1 := by
  classical
  have hs : sign χ s ≠ 0 := by
    rcases value_cases two χ s with h | h <;> simp [sign, h]
  constructor
  · intro h i hi
    rcases value_cases two χ (c i) with hχ | hχ
    · exact hχ
    · have hz (j : I) := Finset.mem_univ j
      have hsel : sign χ (c i) = -1 := by simp [sign, hχ]
      have hprod : (∏ j, if sign χ (c j) = -1 then q j else 1) = 0 :=
        Finset.prod_eq_zero (hz i) (by simp [hsel, hi])
      rw [moment_from_inputs two, hprod, mul_zero] at h
      exact (h rfl).elim
  · intro h
    rw [moment_from_inputs two]
    refine mul_ne_zero hs ?_
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hi : sign χ (c i) = -1
    · rw [ite_eq_left hi]
      intro hq
      have hχ := h i hq
      norm_num [sign, hχ] at hi
    · simp [hi]

omit [Fintype A] in
theorem quotient_two (H : AddSubgroup A) (two : ∀ a : A, a + a = 0)
    (x : A ⧸ H) : x + x = 0 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective H x
  rw [← map_add, two, map_zero]

omit [Fintype A] in
theorem trivial_character_descends (H : AddSubgroup A) (χ : AddChar A ℂ)
    (hχ : ∀ a ∈ H, χ a = 1) :
    ∃ φ : AddChar (A ⧸ H) ℂ, φ.compAddMonoidHom (QuotientAddGroup.mk' H) = χ := by
  let hom : A →+ Additive ℂ := AddChar.toAddMonoidHomEquiv χ
  have hker : H ≤ hom.ker := fun a ha => hχ a ha
  let φ : AddChar (A ⧸ H) ℂ :=
    AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift H hom hker)
  refine ⟨φ, ?_⟩
  ext a
  change ((QuotientAddGroup.lift H hom hker) (QuotientAddGroup.mk' H a)).toMul = _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk]
  rfl

omit [Fintype A] in
theorem trivial_on_closure (χ : AddChar A ℂ) (S : Set A)
    (hs : ∀ a ∈ S, χ a = 1) :
    ∀ a ∈ AddSubgroup.closure S, χ a = 1 := by
  intro a ha
  induction ha using AddSubgroup.closure_induction with
  | mem a ha => exact hs a ha
  | zero => simp
  | add a b ha hb h₁ h₂ => simp [AddChar.map_add_eq_mul, h₁, h₂]
  | neg a ha h => simp [AddChar.map_neg_eq_inv, h]

theorem moment_pushforward (two : ∀ a : A, a + a = 0)
    (H : AddSubgroup A) [Fintype (A ⧸ H)] (c : I → A) (s : A) (q : I → ℝ)
    (φ : AddChar (A ⧸ H) ℂ) :
    moment (law c s q) (φ.compAddMonoidHom (QuotientAddGroup.mk' H)) =
      moment (law (QuotientAddGroup.mk' H ∘ c) (QuotientAddGroup.mk' H s) q) φ := by
  rw [moment_from_inputs two, moment_from_inputs (quotient_two H two)]
  rfl

private theorem affine_quotient_lift (two : ∀ a : A, a + a = 0)
    (H : AddSubgroup A) [Fintype H] [Fintype (A ⧸ H)]
    (c : I → A ⧸ H) (s : A) (q : I → ℝ) :
    ∃ k : H ⊕ I → A, ∃ r : H ⊕ I → ℝ,
      (∀ j : H ⊕ I, |r j| ≤ 1 ↔ match j with
        | .inl _ => True
        | .inr i => |q i| ≤ 1) ∧
      (∀ φ : AddChar (A ⧸ H) ℂ,
        let χ := φ.compAddMonoidHom (QuotientAddGroup.mk' H)
        moment (law k s r) χ = sign χ s * moment (law c (0 : A ⧸ H) q) φ) ∧
      ∀ χ : AddChar A ℂ, (∃ a ∈ H, χ a ≠ 1) → moment (law k s r) χ = 0 := by
  classical
  let π := QuotientAddGroup.mk' H
  choose l hl using QuotientAddGroup.mk'_surjective H
  let k : H ⊕ I → A := Sum.elim Subtype.val (l ∘ c)
  let r : H ⊕ I → ℝ := Sum.elim (fun _ => 0) q
  refine ⟨k, r, ?_, ?_, ?_⟩
  · intro j
    cases j <;> simp [r]
  · intro φ χ
    have hs (x : H) : π x = 0 := by
      change (x : A) ∈ π.ker
      rw [QuotientAddGroup.ker_mk']
      exact x.property
    have h0 : sign φ 0 = 1 := by simp [sign]
    have hLeft : (∏ x : H, if sign χ (k (.inl x)) = -1 then r (.inl x) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro x _
      have hx : sign χ (k (.inl x)) = 1 := by
        change (φ (π x)).re = 1
        simp [hs x]
      norm_num [hx]
    have hRight (i : I) : sign χ (k (.inr i)) = sign φ (c i) := by
      change (φ (π (l (c i)))).re = (φ (c i)).re
      rw [hl]
    rw [moment_from_inputs two, moment_from_inputs (quotient_two H two), h0, one_mul,
      Fintype.prod_sum_type, hLeft, one_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [hRight]
    rfl
  · intro χ hex
    obtain ⟨a, ha, hχ⟩ := hex
    by_contra hzero
    have h := (support_iff_trivial_on_fair_columns two k s r χ).mp hzero
    exact hχ (h (.inl ⟨a, ha⟩) rfl)


/-- Shift a mass function by the offset and sum its masses over the cosets of the fair subgroup. -/
noncomputable def shiftedQuotient (H : AddSubgroup A) (s : A) (μ : A → ℝ) :
    A ⧸ H → ℝ :=
  pushforward (fun a => QuotientAddGroup.mk' H (a + s)) μ

private theorem weighted_shiftedQuotient (H : AddSubgroup A) [Fintype (A ⧸ H)]
    (s : A) (μ : A → ℝ) (f : A ⧸ H → ℝ) :
    ∑ y, shiftedQuotient H s μ y * f y =
      ∑ a, μ a * f (QuotientAddGroup.mk' H (a + s)) := by
  classical
  let πs : A → A ⧸ H := fun a => QuotientAddGroup.mk' H (a + s)
  calc
    _ = ∑ y, ∑ a with πs a = y, μ a * f (πs a) := by
      simp only [shiftedQuotient, pushforward, Finset.sum_mul, ite_mul, zero_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : πs a = y
      · simp [πs] at h
        simp [πs, h]
      · simp [πs] at h
        simp [πs, h]
    _ = _ := Finset.sum_fiberwise Finset.univ πs _

theorem sum_shiftedQuotient (H : AddSubgroup A) [Fintype (A ⧸ H)]
    (s : A) (μ : A → ℝ) : ∑ y, shiftedQuotient H s μ y = ∑ a, μ a := by
  simpa only [mul_one] using weighted_shiftedQuotient H s μ (fun _ => 1)

theorem moment_shiftedQuotient (two : ∀ a : A, a + a = 0)
    (H : AddSubgroup A) [Fintype (A ⧸ H)] (s : A) (μ : A → ℝ)
    (φ : AddChar (A ⧸ H) ℂ) :
    let χ := φ.compAddMonoidHom (QuotientAddGroup.mk' H)
    moment (shiftedQuotient H s μ) φ = sign χ s * moment μ χ := by
  intro χ
  unfold moment
  rw [weighted_shiftedQuotient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change μ a * sign χ (a + s) = sign χ s * (μ a * sign χ a)
  rw [sign_add two]
  ring

/-- Characters nontrivial on the fair subgroup have zero moment. On the quotient,
the offset-corrected moments are strictly positive and pass the product test. -/
def quotientCriterion (H : AddSubgroup A) (s : A) (μ : A → ℝ) : Prop := by
  classical
  letI : Fintype (A ⧸ H) := Fintype.ofFinite _
  exact (∀ χ : AddChar A ℂ, (∃ a ∈ H, χ a ≠ 1) → moment μ χ = 0) ∧
    (∀ φ, 0 < moment (shiftedQuotient H s μ) φ) ∧ orderedMomentProducts (shiftedQuotient H s μ)

theorem sign_sq_eq_one (two : ∀ a : A, a + a = 0) (χ : AddChar A ℂ) (a : A) :
    sign χ a * sign χ a = 1 := by
  rcases value_cases two χ a with h | h <;> norm_num [sign, h]

private theorem law_quotient_criterion (two : ∀ a : A, a + a = 0)
    (c : I → A) (s : A) (q : I → ℝ) (hq : ∀ i, |q i| ≤ 1) :
    ∃ H : AddSubgroup A, ∃ s' : A, quotientCriterion H s' (law c s q) := by
  classical
  let H := AddSubgroup.closure {a | ∃ i, q i = 0 ∧ c i = a}
  let s' := s + ∑ i with q i < 0, c i
  let π := QuotientAddGroup.mk' H
  letI : Fintype (A ⧸ H) := Fintype.ofFinite _
  let μ := law c s q
  have hFair (i : I) (hi : q i = 0) : c i ∈ H :=
    AddSubgroup.subset_closure ⟨i, hi, rfl⟩
  let ν := law (π ∘ c) (0 : A ⧸ H) (fun i => |q i|)
  have hNorm (φ : AddChar (A ⧸ H) ℂ) :
      moment (shiftedQuotient H s' μ) φ = moment ν φ := by
    let χ := φ.compAddMonoidHom π
    rw [moment_shiftedQuotient two]
    change sign χ s' * moment (law c s q) χ = _
    rw [sign_phase_and_magnitude two c s q χ]
    change sign χ s' * (sign χ s' * moment (law c (0 : A) (fun i => |q i|)) χ) = _
    rw [← mul_assoc, sign_sq_eq_one two, one_mul, moment_pushforward two, map_zero]
  have hPos (φ : AddChar (A ⧸ H) ℂ) : 0 < moment ν φ := by
    unfold ν
    rw [moment_from_inputs (quotient_two H two)]
    have h0 : sign φ 0 = 1 := by simp [sign]
    rw [h0, one_mul]
    apply Finset.prod_pos
    intro i _
    change 0 < (if sign φ (π (c i)) = -1 then |q i| else 1)
    by_cases hsel : sign φ (π (c i)) = -1
    · rw [ite_eq_left hsel]
      apply abs_pos.mpr
      intro hz
      have hm : π (c i) = 0 := by
        change c i ∈ π.ker
        rw [QuotientAddGroup.ker_mk']
        exact hFair i hz
      norm_num [hm, h0] at hsel
    · simp [hsel]
  have hν : ∑ y, ν y = 1 := by
    have hh : moment ν 0 = 1 := by
      unfold ν
      rw [moment_from_inputs (quotient_two H two)]
      norm_num [sign]
    simpa [moment, sign] using hh
  have hAbsBounds (i : I) : |(|q i|)| ≤ 1 := by simpa only [abs_abs] using hq i
  have htest := (positive_moment_realizability (quotient_two H two) ν hν hPos).1
    (π ∘ c) 0 (fun i => |q i|) hAbsBounds rfl
  have heq := law_from_moments (quotient_two H two) _ _ hNorm
  refine ⟨H, s', ?_⟩
  unfold quotientCriterion
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    by_contra hx
    have h := (support_iff_trivial_on_fair_columns two c s q χ).mp hx
    have hs : ∀ a ∈ {a | ∃ i, q i = 0 ∧ c i = a}, χ a = 1 := by
      rintro a ⟨i, hi, rfl⟩
      exact h i hi
    obtain ⟨a, ha, hbad⟩ := hχ
    exact hbad (trivial_on_closure χ _ hs a ha)
  · intro φ
    change 0 < moment (shiftedQuotient H s' μ) φ
    rw [hNorm]
    exact hPos φ
  · rwa [heq]

private theorem realise_from_quotient_criterion (two : ∀ a : A, a + a = 0)
    (μ : A → ℝ) (hm : ∑ x, μ x = 1) (H : AddSubgroup A) (s : A)
    (h : quotientCriterion H s μ) :
    ∃ (J : Type u) (_ : Fintype J) (c : J → A) (q : J → ℝ),
      (∀ i, |q i| ≤ 1) ∧ law c s q = μ := by
  classical
  let π := QuotientAddGroup.mk' H
  letI : Fintype H := Fintype.ofFinite _
  letI : Fintype (A ⧸ H) := Fintype.ofFinite _
  obtain ⟨hVanish, hPos, hTest⟩ := h
  have hNorm : ∑ y, shiftedQuotient H s μ y = 1 := (sum_shiftedQuotient H s μ).trans hm
  obtain ⟨q, hq, hLaw⟩ := (positive_moment_realizability.{u,u} (quotient_two H two)
    (shiftedQuotient H s μ) hNorm hPos).2 hTest
  obtain ⟨k, r, hBounds, hIn, hOut⟩ := affine_quotient_lift two H id s q
  refine ⟨H ⊕ (A ⧸ H), inferInstance, k, r, ?_, law_from_moments two _ _ ?_⟩
  · intro j
    apply (hBounds j).mpr
    cases j with
    | inl _ => trivial
    | inr i =>
      change |q i| ≤ 1
      rw [abs_of_pos (hq i).1]
      exact (hq i).2
  intro χ
  by_cases hc : ∀ a ∈ H, χ a = 1
  · obtain ⟨φ, rfl⟩ := trivial_character_descends H χ hc
    rw [hIn, hLaw, moment_shiftedQuotient two, ← mul_assoc, sign_sq_eq_one two, one_mul]
  · push Not at hc
    rw [hOut _ hc, hVanish _ hc]

/-- A normalized finite binary law comes from finitely many independent bits exactly when
a subgroup and an offset satisfy the quotient criterion. All signed bias factors in
`[-1,1]` are allowed. The two trivial choices of subgroup are included. -/
theorem affine_law_iff_quotient_criterion (two : ∀ a : A, a + a = 0)
    (μ : A → ℝ) (hm : ∑ x, μ x = 1) :
    (∃ (J : Type u) (_ : Fintype J) (c : J → A) (s : A) (q : J → ℝ),
      (∀ i, |q i| ≤ 1) ∧ law c s q = μ) ↔
    ∃ H : AddSubgroup A, ∃ s : A, quotientCriterion H s μ := by
  constructor
  · rintro ⟨J, _, c, s, q, hq, rfl⟩
    exact law_quotient_criterion two c s q hq
  · rintro ⟨H, s, h⟩
    obtain ⟨J, inst, c, q, hq, hlaw⟩ := realise_from_quotient_criterion two μ hm H s h
    exact ⟨J, inst, c, s, q, hq, hlaw⟩

end D5.S3.TotalVariation.QuotientParitySpectrum
