/- GID: D5/S1/Solenoid/Connectivity/CharacterCompletionDuality
   generality: I
   mirror-B: D5/B/S1/Solenoid/Connectivity/CharacterCompletionDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Profinite and solenoid completions recover their rational continuous character groups. -/

import D5.S1.Dynamics.ProfiniteCharacter
import D5.S1.Dynamics.SolenoidCharacter
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map

/- Search audit (2026-08-26):
   * The frozen profinite-character module gives finite-residue factorization,
     but no equivalence with the rational additive circle.
   * The frozen solenoid-character module already gives the rational-slope
     equivalence and is reused directly here.
   * Pinned Mathlib supplies the range equivalences used below, but no exact
     character classification for either repository carrier. -/

namespace D5.S1.Solenoid.Connectivity.CharacterCompletionDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Dynamics
open D5.S1.Dynamics.ProfiniteCharacter
open D5.S1.Dynamics.SolenoidCharacter

/-- The rational phase map into the unit additive circle. -/
noncomputable def rationalPhaseHom : ℚ →+ UnitAddCircle where
  toFun q := ((q : ℝ) : UnitAddCircle)
  map_zero' := by simp
  map_add' q r := by rw [Rat.cast_add, AddCircle.coe_add]

/-- The canonical embedding of rational phases modulo integers into the unit
additive circle. -/
noncomputable def rationalCircleEmbedding :
    AddCircle (1 : ℚ) →+ UnitAddCircle :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) rationalPhaseHom (by
    intro q hq
    rw [AddMonoidHom.mem_ker]
    rw [AddSubgroup.mem_zmultiples_iff] at hq
    rcases hq with ⟨z, rfl⟩
    simp [rationalPhaseHom])

@[simp] theorem rationalCircleEmbedding_coe (q : ℚ) :
    rationalCircleEmbedding (q : AddCircle (1 : ℚ)) =
      ((q : ℝ) : UnitAddCircle) := by
  rw [rationalCircleEmbedding, QuotientAddGroup.lift_mk']
  rfl

private theorem rationalCircleEmbedding_eq_zero_iff
    (q : AddCircle (1 : ℚ)) :
    rationalCircleEmbedding q = 0 ↔ q = 0 := by
  refine QuotientAddGroup.induction_on q ?_
  intro r
  rw [rationalCircleEmbedding_coe, AddCircle.coe_eq_zero_iff,
    AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Rat.cast_injective (α := ℝ) ?_⟩
    simpa using hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [Rat.cast_intCast] using congrArg (fun x : ℚ => (x : ℝ)) hz

private theorem rationalCircleEmbedding_injective :
    Function.Injective rationalCircleEmbedding := by
  rw [injective_iff_map_eq_zero]
  exact fun q => (rationalCircleEmbedding_eq_zero_iff q).mp

/-- Evaluation of a profinite-integer character at the dense integer
generator. -/
noncomputable def profiniteCharacterAtOne :
    (ProfiniteIntegers →ₜ+ UnitAddCircle) →+ UnitAddCircle where
  toFun chi := chi (ProfiniteIntegers.natEmbedding 1)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem natEmbedding_eq_nsmul_one (n : ℕ) :
    ProfiniteIntegers.natEmbedding n =
      n • ProfiniteIntegers.natEmbedding 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hadd :
          ProfiniteIntegers.natEmbedding (n + 1) =
            ProfiniteIntegers.natEmbedding n +
              ProfiniteIntegers.natEmbedding 1 := by
        apply Subtype.ext
        funext m
        change residueProjection m (ProfiniteIntegers.natEmbedding (n + 1)) =
          residueProjection m
            (ProfiniteIntegers.natEmbedding n +
              ProfiniteIntegers.natEmbedding 1)
        rw [map_add]
        change ((n + 1 : ℕ) : ZMod (m + 1)) =
          (n : ZMod (m + 1)) + (1 : ZMod (m + 1))
        norm_num
      calc
        ProfiniteIntegers.natEmbedding (Nat.succ n) =
            ProfiniteIntegers.natEmbedding n +
              ProfiniteIntegers.natEmbedding 1 := by
          simpa [Nat.succ_eq_add_one] using hadd
        _ = n • ProfiniteIntegers.natEmbedding 1 +
              ProfiniteIntegers.natEmbedding 1 := by rw [ih]
        _ = Nat.succ n • ProfiniteIntegers.natEmbedding 1 :=
          (succ_nsmul _ _).symm

private theorem profiniteCharacterAtOne_injective :
    Function.Injective profiniteCharacterAtOne := by
  intro chi psi h
  apply ContinuousAddMonoidHom.ext
  intro x
  have hdense := ProfiniteIntegers.denseRange_natEmbedding.equalizer
    chi.continuous_toFun psi.continuous_toFun
    (funext fun n => by
      dsimp [Function.comp_def]
      rw [natEmbedding_eq_nsmul_one, map_nsmul, map_nsmul]
      exact congrArg (n • ·) h)
  exact congrFun hdense x

private noncomputable def rationalResidueCharacter (q : ℚ) :
    ProfiniteIntegers →ₜ+ UnitAddCircle :=
  let m := q.den - 1
  let k : ZMod (m + 1) := q.num
  { toFun := fun x => ZMod.toAddCircle (k * residueProjection m x)
    map_zero' := by simp
    map_add' := by
      intro x y
      rw [map_add, mul_add, map_add]
    continuous_toFun :=
      (continuous_of_discreteTopology
        (f := fun z : ZMod (m + 1) => ZMod.toAddCircle (k * z))).comp
          (residueProjection m).continuous_toFun }

private theorem rationalResidueCharacter_at_one (q : ℚ) :
    profiniteCharacterAtOne (rationalResidueCharacter q) =
      rationalCircleEmbedding (q : AddCircle (1 : ℚ)) := by
  let m := q.den - 1
  have hm : m + 1 = q.den := Nat.sub_add_cancel q.den_pos
  change ZMod.toAddCircle
      ((q.num : ZMod (m + 1)) *
        residueProjection m (ProfiniteIntegers.natEmbedding 1)) = _
  rw [rationalCircleEmbedding_coe]
  change ZMod.toAddCircle ((q.num : ZMod (m + 1)) * 1) = _
  rw [mul_one, ZMod.toAddCircle_intCast]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  rw [Rat.cast_def]
  push_cast [hm]
  rfl

private theorem profinite_character_at_one_is_rational
    (chi : ProfiniteIntegers →ₜ+ UnitAddCircle) :
    ∃ q : AddCircle (1 : ℚ),
      rationalCircleEmbedding q = profiniteCharacterAtOne chi := by
  rcases continuous_character_factors_through_residue chi with ⟨m, k, hk⟩
  let q : ℚ := (k.val : ℚ) / (m + 1)
  refine ⟨(q : AddCircle (1 : ℚ)), ?_⟩
  rw [rationalCircleEmbedding_coe]
  change (((q : ℚ) : ℝ) : UnitAddCircle) =
    chi (ProfiniteIntegers.natEmbedding 1)
  rw [hk]
  change (((q : ℚ) : ℝ) : UnitAddCircle) =
    ZMod.toAddCircle (k * 1)
  rw [mul_one, ZMod.toAddCircle_apply]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  dsimp [q]
  norm_num
  rfl

private theorem profinite_character_phase_ranges_eq :
    profiniteCharacterAtOne.range = rationalCircleEmbedding.range := by
  ext phase
  constructor
  · rintro ⟨chi, rfl⟩
    rcases profinite_character_at_one_is_rational chi with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    refine QuotientAddGroup.induction_on q ?_
    intro r
    exact ⟨rationalResidueCharacter r,
      rationalResidueCharacter_at_one r⟩

/-- The canonical additive equivalence from continuous profinite-integer
characters to rational phases modulo integers. -/
noncomputable def profiniteCharacterEquivRationalCircle :
    (ProfiniteIntegers →ₜ+ UnitAddCircle) ≃+ AddCircle (1 : ℚ) :=
  (profiniteCharacterAtOne.ofInjective profiniteCharacterAtOne_injective).trans
    ((AddEquiv.addSubgroupCongr profinite_character_phase_ranges_eq).trans
      (rationalCircleEmbedding.ofInjective
        rationalCircleEmbedding_injective).symm)

@[simp] theorem profiniteCharacterEquivRationalCircle_apply
    (chi : ProfiniteIntegers →ₜ+ UnitAddCircle) :
    rationalCircleEmbedding (profiniteCharacterEquivRationalCircle chi) =
      profiniteCharacterAtOne chi := by
  rw [profiniteCharacterEquivRationalCircle]
  exact AddMonoidHom.apply_ofInjective_symm
    rationalCircleEmbedding_injective
    ((AddEquiv.addSubgroupCongr profinite_character_phase_ranges_eq)
      ((profiniteCharacterAtOne.ofInjective
        profiniteCharacterAtOne_injective) chi))

/-- The two completion carriers recover their rational continuous character
groups through the canonical profinite evaluation and solenoid slope maps. -/
theorem character_completion_duality :
    (∀ chi : ProfiniteIntegers →ₜ+ UnitAddCircle,
      rationalCircleEmbedding (profiniteCharacterEquivRationalCircle chi) =
        profiniteCharacterAtOne chi) ∧
    (∀ chi : Character,
      rationalCharacterHom (characterEquivRational chi) = chi) := by
  constructor
  · exact profiniteCharacterEquivRationalCircle_apply
  · intro chi
    exact (AddEquiv.ofBijective rationalCharacterHom
      continuous_solenoid_characters_are_rational).apply_symm_apply chi

noncomputable example := profiniteCharacterEquivRationalCircle
noncomputable example := characterEquivRational

#print axioms character_completion_duality

end D5.S1.Solenoid.Connectivity.CharacterCompletionDuality
