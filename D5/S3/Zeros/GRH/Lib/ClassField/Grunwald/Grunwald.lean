/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Grunwald/Grunwald
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Grunwald/Grunwald
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Grunwald.Grunwald. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Grunwald/Grunwald.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.WeightCongruence.WeightCongruence
import D5.S3.Zeros.GRH.Lib.ClassField.Places.Conjugation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Grunwald–Wang theorem in prime exponent (known result; see
Lib.GaloisRep.Main.AttachedDeterminant).

This file: Grunwald's theorem in prime exponent over a totally complex field; symmetrised
characters. -/

open Subgroup

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

/-- Grunwald in prime exponent: for E totally complex, S finite, ψ a ℚ/ℤ-valued character of the
finite ideles with open kernel, pψ = 0, some Galois character χ, pχ = 0, has χ∘Art = ψ on
E_u^× for u ∈ S and on local units where N u is not prime.

Known result: Grunwald–Wang theorem in prime exponent. -/
lemma grunwald [NumberField.IsTotallyComplex E] {p S} (hp : p.Prime) (hS : Set.Finite S)
    (ψ : _ →* _) (c : ψ.ker.IsOpen) (t : ∀ a, ψ a ^ p = 1) : ∃ χ, p • χ = 0 ∧ ∀ u x, u ∈ S ∨
    ¬u.q.Prime ∧ Valued.v x.1 = 1 → QZChar.abelianLift χ (artinMap Gal(Ω/E) (locIdele u x)) =
  ψ (locIdele u x) := by
  obtain ⟨_, T, f, _, -, g⟩ := Fact.mk hp, exists_sup_idelesUnitOff_eq_top hS
  let N := (@powMonoidHom (T.unit E) _ p).range
  choose r hr using IsAIC.exists_pow_eq (A := Ω) p
  choose v _ _ A H σ K F using fun q : {q : _ ⧸ N // ψ (principalIdele q.out) ≠ 1} ↦
    chebotarev (.sdiff Fact.out (isClosed_setOf_smul _ (· = _))) (Set.not_subset.1 fun h ↦
    ((pow_mem_range_pow_of_coprime (.of_dvd_left (by grw [finrank_fixedFieldOf, index_ker,
    card_subgroup_dvd_card, Nat.card_units]) (by simp [hp.one_le])) _).1
    ⟨Algebra.norm E (⟨_, (h ·.2)⟩ : fixedFieldOf (cycCharMod Ω p).ker), (map_pow ..).symm.trans
    ((congrArg _ (by bound)).trans (Algebra.norm_algebraMap q.1.out.1.1))⟩).elim
    fun z e ↦ q.2 ((Units.ofPow _ z hp.ne_zero e ^ p).ext e ▸ by simp [t])) f
  let R q := (powMonoidHom p).range.comap (ideleAt (v q))
  obtain ⟨_, θ, k, hB⟩ := N.finiteIndex_iff.2 (index_range_pow_eq
    (mod_cast @cokerKerIndex_eq_pow_finrank _ _ _ _ (SUnit.dirichlet_unit_theorem f).1)).1,
    exists_monoidHom_extend (d := by exact instDivisibleByQZInt) (idelesUnitOff T ⊓ iInf R).subtype
    (ψ.domRestrict _) principalIdele.range (by
    simp; rintro _ a b x ⟨⟩
    obtain ⟨⟨_, y, ⟨⟩⟩, e⟩ := QuotientGroup.mk_out_eq_mul N ⟨x, by aesop⟩
    exact by_contra fun _ ↦ (K ⟨_, e ▸ by simpa [t]⟩).2 ((H _).smul_root_eq_of_local_pow
      (congr($e.1 ∈ (R _).comap _).mpr (mul_mem (b ..) (by simp [R]))) (hr _) _ (F _).1.1 (K _).1))
  have ⟨μ, C, h⟩ := exists_comp_artinMap Gal(Ω/E) θ (.of_isOpen_ker _ ((_ ⊓ _ ⊓ iInf R).isOpen_mono
    (by simp_all [LE.le]) ((c.inter (isOpen_idelesUnitOff T)).and
    (coe_iInf.substr (isOpen_iInter_of_finite fun q ↦ (isOpen_of_forall_pow_mem hp.ne_zero
    (MonoidHom.mem_range.2 ⟨·, rfl⟩)).preimage_of_continuous))))) (k ⟨·, rfl⟩)
  use ⟨μ, C, μ.2⟩,
    Subtype.ext (funext (artinMap_surjective _ ⟦·⟧ |>.elim (congr($(h · _ ·) ^ p).trans
    (sup_le (c := (θ ^ p).ker) (by simp_all [LE.le]) (by simpa [t] using hB ⟨· ^ p, by simp [R,
    pow_mem ·]⟩) (g.ge ⟨⟩))))), fun w x _ ↦ .trans (by rcases _ : artinMap _ _; tauto) (hB ⟨locIdele
    w x, by simpa +contextual [← and_forall_ne w, R, show ∀ q, v q ≠ w by grind] using by tauto⟩)

variable [NumberField.IsCMField E] (χ : QZChar Gal(Ω/E))

/-- For a character χ of the absolute Galois group of a CM field, the character g ↦ χ(g) +
χ(g^c), g^c the conjugate of g by complex conjugation (`conjGal`). -/
noncomputable abbrev QZChar.symmetrise := χ + comap ⟨_, continuous_conjGal⟩ χ

/-- For a ℚ/ℤ-valued character χ of Gal(Ω/E), the character exp(2πi χ∘Art) of the finite ideles
of E. -/
noncomputable abbrev QZChar.ideleChar := QZ.expUnit.comp ((abelianLift χ).comp (artinMap _))

lemma QZChar.abelianLift_symmetrise a : abelianLift (symmetrise χ) (artinMap _ a) =
  abelianLift χ (artinMap _ a) * abelianLift χ (artinMap _ (star a)) := by
  rcases h : artinMap _ a; exact artinMap_star _ h ▸ rfl
