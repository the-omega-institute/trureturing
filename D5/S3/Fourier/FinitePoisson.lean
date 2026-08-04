/- GID: D5/S3/Fourier/FinitePoisson
   generality: G
   mirror-B: D5/B/S3/Fourier/FinitePoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite Poisson summation on every additive subgroup of ZMod. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

namespace D5.S3.Fourier.FinitePoisson

open Finset
open scoped ZMod

noncomputable section

variable {m : ℕ} [NeZero m]

local instance subgroupFintype (H : AddSubgroup (ZMod m)) : Fintype H :=
  Fintype.ofFinite H

local instance quotientFintype (H : AddSubgroup (ZMod m)) :
    Fintype ((ZMod m) ⧸ H) := Fintype.ofFinite ((ZMod m) ⧸ H)

local instance subgroupMembershipDecidable (H : AddSubgroup (ZMod m)) :
    DecidablePred (· ∈ H) := Classical.decPred _

/-- The positive standard character indexed by `k`. -/
noncomputable def character (k : ZMod m) : AddChar (ZMod m) ℂ :=
  ZMod.stdAddChar.mulShift k

@[simp] theorem character_apply (k x : ZMod m) :
    character k x = ZMod.stdAddChar (k * x) := rfl

/-- The standard characters enumerate every complex character of `ZMod m`. -/
noncomputable def characterEquiv : ZMod m ≃+ AddChar (ZMod m) ℂ := by
  let hom : ZMod m →+ AddChar (ZMod m) ℂ :=
    { toFun := character
      map_zero' := by
        ext x
        simp [character]
      map_add' := fun a b => by
        ext x
        simp [character, add_mul, AddChar.map_add_eq_mul] }
  refine AddEquiv.ofBijective hom ?_
  rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
  exact ⟨AddChar.to_mulShift_inj_of_isPrimitive (ZMod.isPrimitive_stdAddChar m), rfl⟩

@[simp] theorem characterEquiv_apply (k : ZMod m) : characterEquiv k = character k := rfl

/-- Frequencies whose standard character is trivial on `H`. -/
noncomputable def annihilator (H : AddSubgroup (ZMod m)) : AddSubgroup (ZMod m) where
  carrier := {k | ∀ h ∈ H, character k h = 1}
  zero_mem' := by simp [character_apply]
  add_mem' := by
    intro a b ha hb h hh
    rw [character_apply, add_mul, AddChar.map_add_eq_mul, ← character_apply, ← character_apply,
      ha h hh, hb h hh, one_mul]
  neg_mem' := by
    intro a ha h hh
    rw [character_apply, neg_mul, AddChar.map_neg_eq_inv, ← character_apply, ha h hh, inv_one]

@[simp] theorem mem_annihilator {H : AddSubgroup (ZMod m)} {k : ZMod m} :
    k ∈ annihilator H ↔ ∀ h ∈ H, character k h = 1 := Iff.rfl

/-- A character trivial on `H` descends to the quotient by `H`. -/
noncomputable def annihilatorToQuotient (H : AddSubgroup (ZMod m))
    (k : annihilator H) : AddChar ((ZMod m) ⧸ H) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift H (character k.1).toAddMonoidHom <| by
      intro h hh
      simpa [AddMonoidHom.mem_ker] using k.2 h hh

/-- The explicit annihilator is the full character group of the quotient. -/
noncomputable def annihilatorEquivQuotient (H : AddSubgroup (ZMod m)) :
    annihilator H ≃ AddChar ((ZMod m) ⧸ H) ℂ where
  toFun := annihilatorToQuotient H
  invFun ψ :=
    ⟨(characterEquiv (m := m)).symm (ψ.compAddMonoidHom (QuotientAddGroup.mk' H)), by
      intro h hh
      rw [show character ((characterEquiv (m := m)).symm
        (ψ.compAddMonoidHom (QuotientAddGroup.mk' H))) =
          ψ.compAddMonoidHom (QuotientAddGroup.mk' H) from
        characterEquiv_apply (m := m) _ ▸
          (characterEquiv (m := m)).apply_symm_apply _]
      simp only [AddChar.compAddMonoidHom_apply]
      rw [show QuotientAddGroup.mk' H h = 0 from QuotientAddGroup.eq_zero_iff h |>.2 hh]
      exact ψ.map_zero_eq_one⟩
  left_inv k := by
    apply Subtype.ext
    apply (characterEquiv (m := m)).injective
    ext x
    simp [annihilatorToQuotient]
  right_inv ψ := by
    ext q
    induction q using QuotientAddGroup.induction_on
    simp only [annihilatorToQuotient, AddChar.toAddMonoidHomEquiv_symm_apply,
      QuotientAddGroup.lift_mk']
    change character ((characterEquiv (m := m)).symm
      (ψ.compAddMonoidHom (QuotientAddGroup.mk' H))) _ = _
    exact DFunLike.congr_fun
      (characterEquiv_apply (m := m) _ ▸
        (characterEquiv (m := m)).apply_symm_apply
          (ψ.compAddMonoidHom (QuotientAddGroup.mk' H))) _

/- Character orthogonality over the explicit annihilator. -/
set_option maxHeartbeats 800000 in
-- Elaborating the quotient character sum expands the finite Pontryagin duality equivalence.
theorem sum_annihilator_character (H : AddSubgroup (ZMod m)) (x : ZMod m) :
    ∑ k : annihilator H, character k.1 x =
      if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 := by
  classical
  calc
    ∑ k : annihilator H, character k.1 x =
        ∑ ψ : AddChar ((ZMod m) ⧸ H) ℂ, ψ (QuotientAddGroup.mk' H x) := by
      apply Fintype.sum_equiv (annihilatorEquivQuotient H)
      intro k
      simp [annihilatorEquivQuotient, annihilatorToQuotient]
    _ = if QuotientAddGroup.mk' H x = 0 then
          (Fintype.card ((ZMod m) ⧸ H) : ℂ) else 0 :=
      AddChar.sum_apply_eq_ite _
    _ = if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 := by
      change (if (x : (ZMod m) ⧸ H) = 0 then _ else _) = _
      simp only [QuotientAddGroup.eq_zero_iff]
      congr 2
      exact_mod_cast ((Fintype.card_congr (annihilatorEquivQuotient H)).trans
        AddChar.card_eq).symm

/-- The subgroup and its explicit annihilator have complementary cardinalities. -/
theorem card_mul_card_annihilator (H : AddSubgroup (ZMod m)) :
    Fintype.card H * Fintype.card (annihilator H) = m := by
  rw [mul_comm]
  calc
    Fintype.card (annihilator H) * Fintype.card H =
        Fintype.card ((ZMod m) ⧸ H) * Fintype.card H := by
      rw [Fintype.card_congr (annihilatorEquivQuotient H), AddChar.card_eq]
    _ = Fintype.card (ZMod m) := by
      simpa only [Nat.card_eq_fintype_card] using
        (H.card_eq_card_quotient_mul_card_addSubgroup).symm
    _ = m := ZMod.card m

/-- Finite Poisson summation for every additive subgroup of `ZMod m`.
The transform is mathlib's explicit negative-exponent DFT. -/
theorem finite_poisson_summation (H : AddSubgroup (ZMod m)) (f : ZMod m → ℂ) :
    ∑ h : H, f h.1 =
      ((Fintype.card H : ℂ) / (m : ℂ)) * ∑ k : annihilator H, ZMod.dft f k.1 := by
  classical
  simp_rw [ZMod.dft_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have horth (x : ZMod m) :
      ∑ k : annihilator H, ZMod.stdAddChar (-(x * k.1)) =
        if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 := by
    calc
      ∑ k : annihilator H, ZMod.stdAddChar (-(x * k.1)) =
          ∑ k : annihilator H, character k.1 (-x) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [character_apply, mul_comm k.1, neg_mul]
      _ = if -x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 :=
        sum_annihilator_character H (-x)
      _ = if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0 := by
        simp only [H.neg_mem_iff]
  simp_rw [horth]
  have hsum :
      ∑ x : ZMod m, (if x ∈ H then (Fintype.card (annihilator H) : ℂ) else 0) • f x =
        (Fintype.card (annihilator H) : ℂ) * ∑ h : H, f h.1 := by
    rw [← Finset.sum_subtype
      (s := Finset.univ.filter (· ∈ H)) (fun x => by simp) f]
    rw [Finset.mul_sum]
    simpa [smul_eq_mul] using
      (Finset.sum_filter (s := Finset.univ) (fun x : ZMod m => x ∈ H)
        (fun x => (Fintype.card (annihilator H) : ℂ) * f x)).symm
  rw [hsum]
  have hcard : (Fintype.card H : ℂ) * (Fintype.card (annihilator H) : ℂ) = m := by
    exact_mod_cast card_mul_card_annihilator H
  rw [div_mul_eq_mul_div, ← mul_assoc, hcard]
  simp [NeZero.ne m]

/-- The nontrivial even subgroup `{0, 2}` of `ZMod 4`. -/
def evenSubgroupFour : AddSubgroup (ZMod 4) :=
  AddMonoidHom.ker (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

theorem evenSubgroupFour_nontrivial :
    (2 : ZMod 4) ∈ evenSubgroupFour ∧ (1 : ZMod 4) ∉ evenSubgroupFour := by
  change (ZMod.cast (2 : ZMod 4) : ZMod 2) = 0 ∧
    (ZMod.cast (1 : ZMod 4) : ZMod 2) ≠ 0
  decide

@[simp] theorem mem_evenSubgroupFour_iff (x : ZMod 4) :
    x ∈ evenSubgroupFour ↔ x = 0 ∨ x = 2 := by
  change (ZMod.cast x : ZMod 2) = 0 ↔ x = 0 ∨ x = 2
  rw [ZMod.cast_eq_val, CharP.cast_eq_zero_iff]
  constructor
  · intro hdvd
    have hxlt := x.val_lt
    have hval : x.val = 0 ∨ x.val = 2 := by omega
    rcases hval with hval | hval
    · left
      apply ZMod.val_injective 4
      simpa using hval
    · right
      apply ZMod.val_injective 4
      rw [hval]
      rfl
  · rintro (rfl | rfl)
    · norm_num
    · change 2 ∣ 2
      norm_num

/-- The nonzero even frequency is explicitly in the annihilator of `{0, 2}`. -/
theorem two_mem_annihilator_evenSubgroupFour :
    (2 : ZMod 4) ∈ annihilator evenSubgroupFour := by
  rw [mem_annihilator]
  intro h hh
  rcases (mem_evenSubgroupFour_iff h).1 hh with rfl | rfl
  · simp
  · rw [character_apply, show (2 : ZMod 4) * 2 = 0 by decide]
    simp

/-- The odd frequency one is explicitly excluded from the annihilator of `{0, 2}`. -/
theorem one_not_mem_annihilator_evenSubgroupFour :
    (1 : ZMod 4) ∉ annihilator evenSubgroupFour := by
  rw [mem_annihilator]
  intro h
  have hvalue := h (2 : ZMod 4) evenSubgroupFour_nontrivial.1
  have heq : ZMod.stdAddChar (2 : ZMod 4) = ZMod.stdAddChar (0 : ZMod 4) := by
    simpa [character_apply] using hvalue
  have : (2 : ZMod 4) = 0 := ZMod.injective_stdAddChar heq
  exact (by decide : (2 : ZMod 4) ≠ 0) this

theorem card_evenSubgroupFour : Fintype.card evenSubgroupFour = 2 := by
  classical
  rw [Fintype.card_subtype]
  simp_rw [mem_evenSubgroupFour_iff]
  rw [show Finset.univ.filter (fun x : ZMod 4 => x = 0 ∨ x = 2) = {0, 2} by
    ext x
    simp]
  simp [show (0 : ZMod 4) ≠ 2 by decide]

theorem card_annihilator_evenSubgroupFour :
    Fintype.card (annihilator evenSubgroupFour) = 2 := by
  have hcard := card_mul_card_annihilator evenSubgroupFour
  rw [card_evenSubgroupFour] at hcard
  omega

/-- The in-subgroup branch of annihilator orthogonality evaluates to two. -/
theorem sum_annihilator_character_even_two :
    ∑ k : annihilator evenSubgroupFour, character k.1 (2 : ZMod 4) = 2 := by
  calc
    ∑ k : annihilator evenSubgroupFour, character k.1 (2 : ZMod 4) =
        if (2 : ZMod 4) ∈ evenSubgroupFour then
          (Fintype.card (annihilator evenSubgroupFour) : ℂ) else 0 :=
      sum_annihilator_character evenSubgroupFour 2
    _ = 2 := by
      rw [if_pos evenSubgroupFour_nontrivial.1, card_annihilator_evenSubgroupFour]
      norm_num

/-- The out-of-subgroup branch of annihilator orthogonality evaluates to zero. -/
theorem sum_annihilator_character_even_one :
    ∑ k : annihilator evenSubgroupFour, character k.1 (1 : ZMod 4) = 0 := by
  rw [sum_annihilator_character]
  simp [evenSubgroupFour_nontrivial.2]

/-- Machine-checkable nontrivial witness: Poisson summation on `{0, 2} ≤ ZMod 4`. -/
theorem finite_poisson_mod_four_even (f : ZMod 4 → ℂ) :
    ∑ h : evenSubgroupFour, f h.1 =
      ((Fintype.card evenSubgroupFour : ℂ) / 4) *
        ∑ k : annihilator evenSubgroupFour, ZMod.dft f k.1 :=
  finite_poisson_summation evenSubgroupFour f

/-- A concrete input for which both sides of finite Poisson summation reduce to one. -/
theorem finite_poisson_mod_four_even_delta :
    (∑ h : evenSubgroupFour, if h.1 = 0 then (1 : ℂ) else 0) = 1 ∧
      ((Fintype.card evenSubgroupFour : ℂ) / 4) *
          ∑ k : annihilator evenSubgroupFour,
            ZMod.dft (fun x : ZMod 4 => if x = 0 then 1 else 0) k.1 = 1 := by
  have hpoisson := finite_poisson_mod_four_even
    (fun x : ZMod 4 => if x = 0 then 1 else 0)
  have hleft : (∑ h : evenSubgroupFour, if h.1 = 0 then (1 : ℂ) else 0) = 1 := by
    classical
    let z : evenSubgroupFour := ⟨0, evenSubgroupFour.zero_mem⟩
    have hz (h : evenSubgroupFour) : (h.1 = 0) ↔ h = z := by
      constructor
      · intro hh
        apply Subtype.ext
        simpa [z] using hh
      · intro hh
        simpa [z] using congrArg Subtype.val hh
    simp_rw [hz]
    simp
  exact ⟨hleft, hpoisson.symm.trans hleft⟩

end

end D5.S3.Fourier.FinitePoisson
