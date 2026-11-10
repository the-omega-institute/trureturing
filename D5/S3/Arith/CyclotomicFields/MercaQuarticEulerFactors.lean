/- GID: D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual residue Frobenius and local Euler factors for the Merca quartic field. -/

import D5.S3.Arith.CyclotomicFields.MercaQuarticDiscriminant
/-!
The existing cyclotomic stabilizer theorem identifies the ambient decomposition
subgroup. Restricting it to the actual quartic fixed field and using the genuine
unramified residue cardinality identifies its inertia degree with the character
value order. No local splitting pattern is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped NumberField Pointwise

namespace D5.S3.Arith.CyclotomicFields.MercaQuarticEulerFactors

open NumberField Ideal IsCyclotomicExtension
open MercaQuarticField
open D5.S3.ArithUnits.MercaQuarticCharacter
attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

private instance integral_fixed : Algebra.IsInvariant (𝓞 (Field r hr))
    (𝓞 (Ambient r)) (galoisKernel r hr) where
  isInvariant b hb := by
    have hfix : (b : Ambient r) ∈ fixedField r hr := by
      apply (IntermediateField.mem_fixedField_iff _ _).mpr
      intro σ hσ
      exact congrArg (fun x : 𝓞 (Ambient r) => (x : Ambient r)) (hb ⟨σ, hσ⟩)
    let a : Field r hr := ⟨b, hfix⟩
    have ha : IsIntegral ℤ a :=
      (isIntegral_algHom_iff ((fixedField r hr).val.restrictScalars ℤ)
        (fixedField r hr).val.injective).mp b.property
    exact ⟨⟨a, ha⟩, rfl⟩

private lemma restriction_order (τ : Gal(Ambient r/ℚ)) :
    orderOf (AlgEquiv.restrictNormalHom (Field r hr) τ) =
      orderOf (character r hr (Rat.galEquivZMod r (Ambient r) τ)) := by
  have hp (n : ℕ) :
      (AlgEquiv.restrictNormalHom (Field r hr) τ) ^ n = 1 ↔
        (character r hr (Rat.galEquivZMod r (Ambient r) τ)) ^ n = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker]
    change τ ^ n ∈ (IntermediateField.fixedField (galoisKernel r hr)).fixingSubgroup ↔ _
    rw [IntermediateField.fixingSubgroup_fixedField]
    change Rat.galEquivZMod r (Ambient r) (τ ^ n) ∈ kernel r hr ↔ _
    simp only [kernel, MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
      Units.val_one, map_pow, Units.val_pow_eq_pow_val]
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((hp _).mpr (pow_orderOf_eq_one _))
  · exact orderOf_dvd_of_pow_eq_one ((hp _).mp (pow_orderOf_eq_one _))


/-- Away from the conductor, the actual residue degree is the order of chi(p). -/
theorem inertia_degree (p : ℕ) [Fact p.Prime] (hne : p ≠ r)
    (P : Ideal (𝓞 (Field r hr))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertiaDeg ℤ = orderOf (character r hr (p : ZMod r)) := by
  classical
  let Q : Ideal.primesOver P (𝓞 (Ambient r)) := Classical.choice inferInstance
  letI : Q.val.IsPrime := Q.property.1
  letI : Q.val.LiesOver P := Q.property.2
  letI : Q.val.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans Q.val P (Ideal.span {(p : ℤ)})
  have hpbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hpbot P
  letI : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPbot
  have hQbot := Ideal.ne_bot_of_liesOver_of_ne_bot hpbot Q.val
  letI : Q.val.IsMaximal := (inferInstance : Q.val.IsPrime).isMaximal hQbot
  have hcop : p.Coprime r := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
    intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : r.Prime)).mp hd))
  let u := ZMod.unitOfCoprime p hcop
  let e := Rat.galEquivZMod r (Ambient r)
  let τ := e.symm u
  let f : Gal(Ambient r/ℚ) →* Gal(Field r hr/ℚ) := AlgEquiv.restrictNormalHom (Field r hr)
  let σ := f τ
  have hstabA : MulAction.stabilizer Gal(Ambient r/ℚ) Q.val = Subgroup.zpowers τ := by
    apply e.mapSubgroup.injective
    rw [Rat.galEquivZMod_stabilizer r (Ambient r) p Q.val hcop]
    change Subgroup.zpowers u = (Subgroup.zpowers τ).map e.toMonoidHom
    rw [MonoidHom.map_zpowers]
    simp [τ]
  have hker : galoisKernel r hr ≤ f.ker := by
    dsimp [f]
    rw [IntermediateField.restrictNormalHom_ker]
    change galoisKernel r hr ≤ (IntermediateField.fixedField (galoisKernel r hr)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
  have hcomm (g : Gal(Ambient r/ℚ)) (x : 𝓞 (Field r hr)) :
      algebraMap (𝓞 (Field r hr)) (𝓞 (Ambient r)) (f g • x) =
        g • algebraMap (𝓞 (Field r hr)) (𝓞 (Ambient r)) x := by
    apply RingOfIntegers.ext
    exact AlgEquiv.restrictNormal_commutes g (Field r hr) (x : Field r hr)
  have hstabF : MulAction.stabilizer Gal(Field r hr/ℚ) P = Subgroup.zpowers σ := by
    rw [← Ideal.map_stabilizer_of_surjective f (galoisKernel r hr) P Q.val
      (AlgEquiv.restrictNormalHom_surjective (K₁ := Field r hr) (E := Ambient r)) hker hcomm,
      hstabA, MonoidHom.map_zpowers]
  have hnot : ¬ (p : ℤ) ∣ NumberField.discr (Field r hr) := by
    rw [MercaQuarticDiscriminant.discriminant r hr]
    intro h
    have hd : p ∣ r := by
      exact_mod_cast (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow h
    exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : r.Prime)).mp hd)
  letI : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_liesOver (Field r hr) (𝓞 (Field r hr))
      (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))).mp hnot P inferInstance inferInstance
  have hc : Nat.card (MulAction.stabilizer Gal(Field r hr/ℚ) P) = P.inertiaDeg ℤ := by
    rw [Ideal.card_stabilizer_eq (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(Field r hr/ℚ),
      Ideal.ramificationIdx_eq_one_iff.mpr inferInstance, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(Field r hr/ℚ)]
  calc
    P.inertiaDeg ℤ = Nat.card (MulAction.stabilizer Gal(Field r hr/ℚ) P) := hc.symm
    _ = orderOf σ := by rw [hstabF, Nat.card_zpowers]
    _ = orderOf (character r hr (p : ZMod r)) := by
      rw [restriction_order r hr τ]
      change orderOf (character r hr (e (e.symm u))) = _
      rw [e.apply_symm_apply]
      simp only [u, ZMod.coe_unitOfCoprime]


/-- The actual prime-ideal Euler polynomial equals the four-character factor,
including the ramified prime and the rational prime two. -/
theorem euler_polynomial (p : ℕ) [Fact p.Prime] (z : ℂ) :
    (∏ P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr)),
      (1 - z ^ P.val.inertiaDeg ℤ)) =
    (1 - z) * (1 - character r hr (p : ZMod r) * z) *
      (1 - character r hr (p : ZMod r) ^ 2 * z) *
      (1 - character r hr (p : ZMod r) ^ 3 * z) := by
  classical
  let P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr)) :=
    Classical.choice inferInstance
  letI : P.val.IsPrime := P.property.1
  letI : P.val.LiesOver (Ideal.span {(p : ℤ)}) := P.property.2
  by_cases hpr : p = r
  · subst p
    have hdeg (Q : Ideal.primesOver (Ideal.span {(r : ℤ)}) (𝓞 (Field r hr))) :
        Q.val.inertiaDeg ℤ = 1 := by
      letI : Q.val.IsPrime := Q.property.1
      letI : Q.val.LiesOver (Ideal.span {(r : ℤ)}) := Q.property.2
      exact (MercaQuarticDiscriminant.prime_structure r hr Q.val).2.2
    simp_rw [hdeg, pow_one]
    have hc : Fintype.card (Ideal.primesOver (Ideal.span {(r : ℤ)}) (𝓞 (Field r hr))) = 1 := by
      rw [Fintype.card_eq_nat_card]
      exact (MercaQuarticDiscriminant.prime_structure r hr P.val).1
    simp only [Finset.prod_const, Finset.card_univ, hc, pow_one,
      CharP.cast_eq_zero, MulChar.map_zero, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), mul_one]
  · have hcop : p.Coprime r := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro hd
      exact hpr ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : r.Prime)).mp hd))
    have hfourχ : character r hr ^ 4 = 1 :=
      (kernel_structure r hr).1 ▸ pow_orderOf_eq_one _
    have hfour : character r hr (p : ZMod r) ^ 4 = 1 := by
      rw [← ZMod.coe_unitOfCoprime p hcop, ← MulChar.pow_apply_coe,
        hfourχ, MulChar.one_apply_coe]
    have hcases : character r hr (p : ZMod r) = 1 ∨
        character r hr (p : ZMod r) = -1 ∨
        character r hr (p : ZMod r) = Complex.I ∨
        character r hr (p : ZMod r) = -Complex.I := by
      have hs : (character r hr (p : ZMod r) ^ 2) ^ 2 = 1 := by
        simpa only [← pow_mul] using hfour
      rcases sq_eq_one_iff.mp hs with h | h
      · rcases sq_eq_one_iff.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hi : character r hr (p : ZMod r) ^ 2 = Complex.I ^ 2 := by
          rw [Complex.I_sq]; exact h
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    have hnot : ¬ (p : ℤ) ∣ NumberField.discr (Field r hr) := by
      rw [MercaQuarticDiscriminant.discriminant r hr]
      intro h
      have hd : p ∣ r := by
        exact_mod_cast (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow h
      exact hpr ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : r.Prime)).mp hd)
    letI : Algebra.IsUnramifiedAt ℤ P.val :=
      (NumberField.not_dvd_discr_iff_forall_liesOver (Field r hr) (𝓞 (Field r hr))
        (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))).mp hnot P.val inferInstance inferInstance
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr)) Gal(Field r hr/ℚ)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P.val
        Gal(Field r hr/ℚ), Ideal.ramificationIdx_eq_one_iff.mpr inferInstance, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P.val Gal(Field r hr/ℚ),
      inertia_degree r hr p hpr P.val, IsGalois.card_aut_eq_finrank,
      (field_structure r hr).1] at hfund
    have hdeg (Q : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr))) :
        Q.val.inertiaDeg ℤ = orderOf (character r hr (p : ZMod r)) := by
      letI : Q.val.IsPrime := Q.property.1
      letI : Q.val.LiesOver (Ideal.span {(p : ℤ)}) := Q.property.2
      exact inertia_degree r hr p hpr Q.val
    simp_rw [hdeg]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
    change (1 - z ^ orderOf (character r hr (p : ZMod r))) ^
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr))).ncard = _
    have hI : orderOf (Complex.I : ℂ) = 4 := Complex.isPrimitiveRoot_I.eq_orderOf.symm
    have hnI : orderOf (-Complex.I : ℂ) = 4 := by
      rw [show (-Complex.I : ℂ) = Complex.I ^ 3 by norm_num,
        orderOf_pow' _ (by decide : 3 ≠ 0), hI]
      decide
    rcases hcases with h | h | h | h
    · rw [h, orderOf_one, mul_one] at hfund
      rw [h, orderOf_one, hfund]
      ring
    · rw [h, orderOf_neg_one] at hfund
      norm_num at hfund
      have hc : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr))).ncard = 2 := by omega
      rw [h, orderOf_neg_one, hc]
      norm_num
      ring
    · rw [h, hI] at hfund
      have hc : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr))).ncard = 1 := by omega
      rw [h, hI, hc]
      norm_num [Complex.I_sq, Complex.ext_iff, pow_succ]
      <;> constructor <;> ring
    · rw [h, hnI] at hfund
      have hc : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Field r hr))).ncard = 1 := by omega
      rw [h, hnI, hc]
      norm_num [Complex.I_sq, Complex.ext_iff, pow_succ]
      <;> constructor <;> ring

end D5.S3.Arith.CyclotomicFields.MercaQuarticEulerFactors
