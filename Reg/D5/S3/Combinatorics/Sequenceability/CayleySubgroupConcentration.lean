import D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-! Exact-telescope audit of original-label cardinality in the proper stabilizer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

namespace Reg.D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration

open _root_.D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev Params := Σ K : Type u, Group K × Fintype K × Finset K

abbrev signature : Signature where
  Params := Params.{u}
  State p := by letI := p.2.1; exact Subgroup p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p L => by
    letI := p.2.1
    letI := p.2.2.1
    exact ((retained p.2.2.2 L).card : ℝ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [g : Group K] [f : Fintype K]
    (T : Finset K), T.Nonempty →
    ∀ (β : ℝ), 0 ≤ β → β ≤ (density T) ^ 2 / 1000 →
    ∀ (v : EuclideanSpace ℝ K), ‖v‖ = 1 →
    (∑ x : K, v x) = 0 →
    (1 - β) * (T.card : ℝ) ≤ (∑ t ∈ T, ∑ x : K, v x * v (x * t)) →
    ∃ L : Subgroup K, L ≠ ⊤ ∧
      (1 - 50 * β / (density T) ^ 2) * (T.card : ℝ) ≤
        R.readout () ⟨K, g, f, T⟩ L

private abbrev Bit := ULift.{u} (Multiplicative (ZMod 2))

private def signedBit : EuclideanSpace ℝ Bit.{u} :=
  WithLp.toLp 2 (fun g => if g.down = 1 then 1 else -1)

private theorem signedBit_mean : (∑ g : Bit.{u}, signedBit g) = 0 := by
  rw [Fintype.sum_equiv Equiv.ulift (fun g => signedBit g)
    (fun g : Multiplicative (ZMod 2) => if g = 1 then (1 : ℝ) else -1)
    (fun _ => rfl)]
  change (∑ g : Fin 2, if g = 0 then (1 : ℝ) else -1) = 0
  simp [Fin.sum_univ_two]

private theorem signedBit_ne : signedBit.{u} ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ Bit.{u} => v 1) h
  norm_num [signedBit] at this

private def unitBit : EuclideanSpace ℝ Bit.{u} :=
  ‖signedBit.{u}‖⁻¹ • signedBit.{u}

private theorem unitBit_norm : ‖unitBit.{u}‖ = 1 := by
  rw [unitBit, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr signedBit_ne.{u})

private theorem unitBit_mean : (∑ g : Bit.{u}, unitBit g) = 0 := by
  simp [unitBit, ← Finset.mul_sum, signedBit_mean]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hvsum : (∑ x : Bit.{u}, unitBit x * unitBit x) = 1 := by
    have := EuclideanSpace.real_norm_sq_eq unitBit.{u}
    rw [unitBit_norm] at this
    simpa [pow_two] using this.symm
  obtain ⟨L, _, hL⟩ := h Bit {1} (Finset.singleton_nonempty 1) 0 (by norm_num)
    (by positivity) unitBit unitBit_norm unitBit_mean (by simpa using hvsum.ge)
  norm_num [rejected, realize] at hL

def family : Registration arena.{u} (type_of% (@near_invariant_localization.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro K g f T hT β hβ0 hβ v hv hm hc
    exact near_invariant_localization T hT β hβ0 hβ v hv hm hc,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let p : Params.{u} := ⟨Bit, inferInstance, inferInstance, Finset.univ⟩
    refine ⟨p, ⊥, ⊤, ?_⟩
    have htop : Fintype.card (⊤ : Subgroup Bit.{u}) = 2 := by
      rw [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_eq_fintype_card]
      simp [Bit]
    intro he
    norm_num [actual, realize, p, retained, htop] at he

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@near_invariant_localization.{u}) (Realization signature.{u})
    (type_of% (@Subgroup.{u})) Unit where
  unitName := .str
    `D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration.near_invariant_localization
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Subgroup.{u})
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
end
