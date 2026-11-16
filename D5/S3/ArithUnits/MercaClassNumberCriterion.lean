/- GID: D5/S3/ArithUnits/MercaClassNumberCriterion
   generality: I
   mirror-B: D5/B/S3/ArithUnits/MercaClassNumberCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The historical class-number sign and literal centered-sum criterion. -/

import D5.S3.Analytic.Zeta.MercaImaginaryClassNumber
import D5.S3.Analytic.Zeta.MercaRelativeClassNumber

/-! The historical Ma--Zhang/Farland sign condition is combined with the full
Ma--Merca--Zhang centered first moment. All field class numbers are actual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators NumberField

namespace D5.S3.ArithUnits.MercaClassNumberCriterion
open D5.S3.Analytic.Zeta MercaRelativeClassNumber
open D5.S3.Arith.CharacterSums MercaQuadraticQuarter
open D5.S3.Arith.CyclotomicFields MercaRealEulerFactors
open MercaQuarticCharacter MercaQuarticMoments

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

/-- The source integer Delta; exact evenness of the actual class number is proved upstream. -/
def delta : ℤ :=
  (NumberField.classNumber
    (D5.S3.Arith.QuadraticFields.MercaImaginaryQuadratic.Field r) : ℤ) / 2 -
      (((r - 1) / 4 : ℕ) : ℤ)

include hr in
private lemma delta_nonresidue : delta r = -2 * (nonresidueCount r : ℤ) := by
  rw [delta, (MercaImaginaryClassNumber.class_number_quarter r hr).2,
    quarter_nonresidue]
  ring

private def imagTerm (z : ℂ) : ℤ := if z = Complex.I then 1 else if z = -Complex.I then -1 else 0

private def quarterImag : ℤ :=
  ∑ a ∈ Finset.Icc 1 ((r - 1) / 4), imagTerm (character r hr (a : ZMod r))

include hr in
private lemma interval_values (a : ℕ) (ha : a ∈ Finset.Icc 1 ((r - 1) / 4)) :
    character r hr (a : ZMod r) = 1 ∨ character r hr (a : ZMod r) = Complex.I ∨
    character r hr (a : ZMod r) = -1 ∨ character r hr (a : ZMod r) = -Complex.I := by
  have hrpos := (Fact.out : r.Prime).pos
  have ha' := Finset.mem_Icc.mp ha
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  let u : (ZMod r)ˣ := Units.mk0 a ha0
  have hfour : character r hr ^ 4 = 1 :=
    (kernel_structure r hr).1 ▸ pow_orderOf_eq_one _
  apply fourth_values
  change character r hr (u : ZMod r) ^ 4 = 1
  rw [← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]

include hr in
private lemma term_parity (a : ℕ) (ha : a ∈ Finset.Icc 1 ((r - 1) / 4)) :
    ((imagTerm (character r hr (a : ZMod r)) : ℤ) : ℝ) =
      (character r hr (a : ZMod r)).im ∧
    imagTerm (character r hr (a : ZMod r)) =
      (if legendreSym r (a : ℤ) = -1 then 1 else 0) -
        2 * (if character r hr (a : ZMod r) = -Complex.I then 1 else 0) := by
  classical
  have hs := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (a : ZMod r))
    (character_sq r hr)
  rw [MulChar.pow_apply' _ (by decide : 2 ≠ 0)] at hs
  change character r hr (a : ZMod r) ^ 2 =
    (quadraticChar (ZMod r) (a : ZMod r) : ℂ) at hs
  rw [show quadraticChar (ZMod r) (a : ZMod r) = legendreSym r (a : ℤ) by
    simp only [legendreSym, Int.cast_natCast]] at hs
  rcases interval_values r hr a ha with h | h | h | h
  · norm_num [h, Complex.I_sq] at hs
    have hL : legendreSym r (a : ℤ) = 1 := by exact_mod_cast hs.symm
    norm_num [h, imagTerm, hL, Complex.ext_iff]
  · norm_num [h, Complex.I_sq] at hs
    have hL : legendreSym r (a : ℤ) = -1 := by exact_mod_cast hs.symm
    norm_num [h, imagTerm, hL, Complex.ext_iff]
  · norm_num [h, Complex.I_sq] at hs
    have hL : legendreSym r (a : ℤ) = 1 := by exact_mod_cast hs.symm
    norm_num [h, imagTerm, hL, Complex.ext_iff]
  · norm_num [h, Complex.I_sq] at hs
    have hL : legendreSym r (a : ℤ) = -1 := by exact_mod_cast hs.symm
    norm_num [h, imagTerm, hL, Complex.ext_iff]

include hr in
private lemma quarter_imaginary :
    (quarterImag r hr : ℝ) = (intervalSum r hr ((r - 1) / 4)).im ∧
    ∃ c : ℤ, quarterImag r hr = (nonresidueCount r : ℤ) - 2 * c := by
  classical
  constructor
  · simp only [quarterImag, Int.cast_sum, intervalSum, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact (term_parity r hr a ha).1
  · let c : ℤ := ((Finset.Icc 1 ((r - 1) / 4) : Finset ℕ).filter
      (fun a : ℕ => character r hr (a : ZMod r) = -Complex.I)).card
    refine ⟨c, ?_⟩
    have hc : c = ∑ a ∈ Finset.Icc 1 ((r - 1) / 4),
        if character r hr (a : ZMod r) = -Complex.I then (1 : ℤ) else 0 := by
      rw [← Finset.sum_filter]
      simp [c]
    have hN : (nonresidueCount r : ℤ) = ∑ a ∈ Finset.Icc 1 ((r - 1) / 4),
        if legendreSym r (a : ℤ) = -1 then (1 : ℤ) else 0 := by
      rw [← Finset.sum_filter]
      simp [nonresidueCount]
    rw [hc, hN, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    exact (term_parity r hr a ha).2

/-- The signed actual class-number difference agrees with k+t modulo four. -/
theorem delta_congruence (hr5 : 5 < r) :
    (realCoordinate r hr + imagCoordinate r hr) % 4 = delta r % 4 := by
  obtain ⟨hW, c, hN⟩ := quarter_imaginary r hr
  have hi := (interval_identities r hr hr5).2.2.2.2
  rw [← hW] at hi
  have hiZ : 2 * quarterImag r hr = realCoordinate r hr - 3 * imagCoordinate r hr := by
    exact_mod_cast hi
  have hD := delta_nonresidue r hr
  omega

/-- Coordinate magnitude equality is precisely the square equality for the actual quotient. -/
theorem equality_criterion (hr5 : 5 < r) :
    |realCoordinate r hr| = |imagCoordinate r hr| ↔
      relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 := by
  have hn := relative_norm r hr hr5
  constructor
  · intro he
    have hs := (sq_eq_sq_iff_abs_eq_abs _ _).mpr he
    have hsq : (realCoordinate r hr : ℚ) ^ 2 = (imagCoordinate r hr : ℚ) ^ 2 := by
      exact_mod_cast hs
    nlinarith
  · intro he
    have hsq : (realCoordinate r hr : ℚ) ^ 2 = (imagCoordinate r hr : ℚ) ^ 2 := by
      nlinarith
    have hs : realCoordinate r hr ^ 2 = imagCoordinate r hr ^ 2 := by exact_mod_cast hsq
    exact (sq_eq_sq_iff_abs_eq_abs _ _).mp hs

/-- Under magnitude equality, Delta determines exactly the two coordinate orientations. -/
theorem sign_criterion (hr5 : 5 < r)
    (heq : |realCoordinate r hr| = |imagCoordinate r hr|) :
    (delta r % 4 = 2 ↔ realCoordinate r hr = imagCoordinate r hr) ∧
    (delta r % 4 = 0 ↔ realCoordinate r hr = -imagCoordinate r hr) := by
  have hc := delta_congruence r hr hr5
  have hk := (bernoulli_coordinates r hr hr5).2.1
  obtain ⟨a, ha⟩ := hk
  have hcases := abs_eq_abs.mp heq
  constructor <;> constructor <;> intro h <;> rcases hcases with hcase | hcase <;> omega

/-- The full prime-q centered criterion uses the actual class-number square equality
before applying the signed difference, over the literal subgroup H itself. -/
theorem centered_criterion (hr5 : 5 < r) (q : ℕ) [Fact q.Prime] (hqr : q ≠ r) :
    centered r hr q ↔ character r hr (q : ZMod r) = 1 ∨
      (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 2 ∧
        character r hr (q : ZMod r) = -Complex.I) ∨
      (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 0 ∧
        character r hr (q : ZMod r) = Complex.I) := by
  have hb := (centered_coordinates r hr hr5 q hqr).2.2
  have he := equality_criterion r hr hr5
  constructor
  · intro h
    rcases hb.mp h with h | ⟨hkt, hq⟩ | ⟨hkt, hq⟩
    · exact Or.inl h
    · have hab : |realCoordinate r hr| = |imagCoordinate r hr| := by rw [hkt]
      exact Or.inr (Or.inl ⟨he.mp hab, (sign_criterion r hr hr5 hab).1.mpr hkt, hq⟩)
    · have hab : |realCoordinate r hr| = |imagCoordinate r hr| := by rw [hkt, abs_neg]
      exact Or.inr (Or.inr ⟨he.mp hab, (sign_criterion r hr hr5 hab).2.mpr hkt, hq⟩)
  · intro h
    apply hb.mpr
    rcases h with h | ⟨heq, hd, hq⟩ | ⟨heq, hd, hq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨(sign_criterion r hr hr5 (he.mpr heq)).1.mp hd, hq⟩)
    · exact Or.inr (Or.inr ⟨(sign_criterion r hr hr5 (he.mpr heq)).2.mp hd, hq⟩)

/-- Conjugation fixes the actual kernel and hence its actual cyclotomic fixed field.
The same real coordinate and actual class numbers occur; only the imaginary
coordinate changes sign. -/
theorem conjugate_invariants (hr5 : 5 < r) :
    (star (character r hr)).toUnitHom.ker = kernel r hr ∧
    IntermediateField.fixedField
      (((star (character r hr)).toUnitHom.ker).comap
        (IsCyclotomicExtension.Rat.galEquivZMod r
          (D5.S3.Arith.CyclotomicFields.MercaQuarticField.Ambient r)).toMonoidHom) =
      D5.S3.Arith.CyclotomicFields.MercaQuarticField.fixedField r hr ∧
    (realCoordinate r hr : ℚ) ^ 2 + (-imagCoordinate r hr : ℤ) ^ 2 =
      2 * relativeClassNumber r hr := by
  have hk := (conjugate_coordinates r hr hr5).2.2.1
  refine ⟨hk, ?_, ?_⟩
  · rw [hk]
    rfl
  · simpa only [Int.cast_neg, neg_sq] using relative_norm r hr hr5

/-- In the conjugate orientation the Delta-two branch uses i, and the
Delta-zero branch uses minus i; the actual class-number conditions are unchanged. -/
theorem conjugate_centered_criterion (hr5 : 5 < r) (q : ℕ) [Fact q.Prime]
    (hqr : q ≠ r) :
    centered r hr q ↔ (star (character r hr)) (q : ZMod r) = 1 ∨
      (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 2 ∧
        (star (character r hr)) (q : ZMod r) = Complex.I) ∨
      (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 0 ∧
        (star (character r hr)) (q : ZMod r) = -Complex.I) := by
  have h := centered_criterion r hr hr5 q hqr
  have hval (z : ℂ) : (star (character r hr)) (q : ZMod r) = star z ↔
      character r hr (q : ZMod r) = z := by
    rw [MulChar.star_apply]
    exact star_injective.eq_iff
  rw [← hval 1, ← hval (-Complex.I), ← hval Complex.I] at h
  simpa only [star_one, star_neg, RCLike.star_def, Complex.conj_I, neg_neg] using h

private lemma generator_period_sum (q : ℕ) [Fact q.Prime]
    (a : liftedKernel r hr q) (hgen : ∀ x, x ∈ Subgroup.zpowers a) :
    (∑ j ∈ Finset.Icc 1 (orderOf a),
      (((a ^ j).val : ZMod (r * q)).val : ℤ)) =
      ∑ u ∈ MercaCosetFiberLift.cosetFinset (liftedKernel r hr q) 1,
        ((u : ZMod (r * q)).val : ℤ) := by
  classical
  let E : Fin (orderOf a) ≃ liftedKernel r hr q :=
    (finEquivZPowers (isOfFinOrder_of_finite a)).trans
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hgen x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let f : liftedKernel r hr q → ℤ := fun u => ((u.val : ZMod (r * q)).val : ℤ)
  have hi : (∑ i : Fin (orderOf a), f (a * a ^ i.val)) =
      ∑ j ∈ Finset.Icc 1 (orderOf a), f (a ^ j) := by
    apply Finset.sum_bij (fun i _ => i.val + 1)
    · intro i _
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ he
      exact Fin.ext (by omega)
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro i _
      rw [pow_succ']
  have he : (∑ i : Fin (orderOf a), f (a * a ^ i.val)) =
      ∑ x : liftedKernel r hr q, f (a * x) := by
    exact Equiv.sum_comp E (fun x => f (a * x))
  rw [← hi, he]
  trans ∑ x : liftedKernel r hr q, f x
  · exact Equiv.sum_comp (Equiv.mulLeft a) f
  symm
  simpa only [MercaCosetFiberLift.cosetFinset, inv_one, one_mul,
    ← Set.toFinset_ofPred] using
    Finset.sum_toFinset_eq_subtype (fun u => u ∈ liftedKernel r hr q)
      (fun u => ((u : ZMod (r * q)).val : ℤ))

/-- Every eligible q admits an actual source generator. Its full period sum
has precisely the same class-number criterion as the literal subgroup H. -/
theorem generator_criterion (hr5 : 5 < r) (q : ℕ) [Fact q.Prime]
    (hq2 : 2 < q) (hqr : q ≠ r) (hcop : Nat.Coprime ((r - 1) / 4) (q - 1)) :
    ∃ a : liftedKernel r hr q,
      (∀ x, x ∈ Subgroup.zpowers a) ∧
      Nat.Coprime ((a.val : ZMod (r * q)).val - 1) (r * q) ∧
      ((2 * ∑ j ∈ Finset.Icc 1 (orderOf a),
        (((a ^ j).val : ZMod (r * q)).val : ℤ)) =
        (r : ℤ) * q * (((r - 1) / 4 : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) ↔
      character r hr (q : ZMod r) = 1 ∨
        (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 2 ∧
          character r hr (q : ZMod r) = -Complex.I) ∨
        (relativeClassNumber r hr = (realCoordinate r hr : ℚ) ^ 2 ∧ delta r % 4 = 0 ∧
          character r hr (q : ZMod r) = Complex.I)) := by
  letI : IsCyclic (liftedKernel r hr q) := (lifted_structure r hr q hqr).1.mpr hcop
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := liftedKernel r hr q)
  refine ⟨a, ha, generator_eligible r hr hr5 q hq2 hqr a ha, ?_⟩
  rw [generator_period_sum r hr q a ha]
  exact centered_criterion r hr hr5 q hqr

end D5.S3.ArithUnits.MercaClassNumberCriterion
