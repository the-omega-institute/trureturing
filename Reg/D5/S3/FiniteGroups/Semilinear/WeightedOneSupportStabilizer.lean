import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer
import Reg.Support.DependentFamily

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open WeightedSemilinear.OneSupport63
open scoped Classical
namespace Reg.D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer
noncomputable section

structure Scope where
  K : Type
  [fieldK : Field K]
  [finiteK : Fintype K]
  [algebraK : Algebra (ZMod 5) K]
attribute [instance] Scope.fieldK Scope.finiteK Scope.algebraK

private theorem primitive_exists :
    ∃ (p : Scope) (hL : Fintype.card p.K = 15625) (ζ : p.K), IsPrimitiveRoot ζ 15624 := by
  let L := GaloisField 5 6
  letI : Fintype L := Fintype.ofFinite L
  have hL : Fintype.card L = 15625 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 5 6 (by decide)
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  have hc : Nat.card Lˣ = 15624 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hL]
  have hp : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.iff_orderOf.mpr (hz.trans hc)
  exact ⟨⟨L⟩, hL, z, IsPrimitiveRoot.coe_units_iff.mpr hp⟩

namespace stabilizer_structure
abbrev signature : Signature where
  Params := Scope
  State p := Ambient p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ g => orderOf g) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {K : Type} [Field K] [Fintype K] [Algebra (ZMod 5) K]
    (hK : Fintype.card K = 15625) (ζ : K) (hζ : IsPrimitiveRoot ζ 15624),
    let z := primitiveUnit ζ hζ
    let hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
    alpha z ∈ stabilizer z ∧ tau z ∈ stabilizer z ∧ beta z ∈ stabilizer z ∧
    r.readout () ⟨K⟩ (alpha z) = 21 ∧ orderOf (tau z) = 9 ∧ orderOf (beta z) = 7 ∧
    tau z ^ 3 = alpha z ^ 7 ∧ alpha z ^ 7 ≠ 1 ∧
    tau z * beta z * (tau z)⁻¹ = beta z ^ 4 ∧
    Nat.card (stabilizer z) = 63 ∧
    IsCyclic (betaSubgroup z hz) ∧ Nat.card (betaSubgroup z hz) = 7 ∧
    IsCyclic (tauSubgroup z) ∧ Nat.card (tauSubgroup z) = 9 ∧
    (betaSubgroup z hz).Normal ∧
    (betaSubgroup z hz).IsComplement' (tauSubgroup z) ∧
    Nonempty ((betaSubgroup z hz) ⋊[internalAction hK z hz] (tauSubgroup z) ≃*
      stabilizer z) ∧
    internalAction hK z hz ⟨tauIn z, Subgroup.mem_zpowers _⟩
      ⟨betaIn z hz, Subgroup.mem_zpowers _⟩ =
        (⟨betaIn z hz, Subgroup.mem_zpowers _⟩ : betaSubgroup z hz) ^ 4
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hK, ζ, hζ⟩ := primitive_exists
  let K := p.K
  letI := p.fieldK
  letI := p.finiteK
  letI := p.algebraK
  have hbad := (h hK ζ hζ).2.2.2.1
  change (0 : ℕ) = 21 at hbad
  norm_num at hbad
def family : Registration arena (type_of% (@WeightedSemilinear.OneSupport63.stabilizer_structure)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.OneSupport63.stabilizer_structure, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨p, hK, ζ, hζ⟩ := primitive_exists
    let K := p.K
    letI := p.fieldK
    letI := p.finiteK
    letI := p.algebraK
    refine ⟨⟨K⟩, 1, alpha (primitiveUnit ζ hζ), ?_⟩
    have horder := (WeightedSemilinear.OneSupport63.stabilizer_structure hK ζ hζ).2.2.2.1
    change orderOf (1 : Ambient K) ≠ orderOf (alpha (primitiveUnit ζ hζ))
    rw [orderOf_one, horder]
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.OneSupport63.stabilizer_structure) (Realization signature) Unit Unit where
  unitName := `WeightedSemilinear.OneSupport63.stabilizer_structure.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer.stabilizer_structure.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","arg","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end stabilizer_structure

namespace galois_nonsplitting
abbrev signature : Signature where
  Params := Scope
  State p := Ambient p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Ambient p.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ g => g ^ 3) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {K : Type} [Field K] [Fintype K] [Algebra (ZMod 5) K]
    (hK : Fintype.card K = 15625) (ζ : K) (hζ : IsPrimitiveRoot ζ 15624),
    let z := primitiveUnit ζ hζ
    let hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
    (projection z).range = galoisSubgroup K ∧ Nat.card (galoisSubgroup K) = 3 ∧
    Nat.card (projection z).ker = 21 ∧
    (projection z).ker = Subgroup.zpowers (alphaIn z hz) ∧
    Function.Surjective (galoisProjection hK z hz) ∧
    (∀ g : stabilizer z, projection z g = frob K ^ 2 →
      r.readout () ⟨K⟩ g.val = SemidirectProduct.inl (z ^ 5208) ∧ g ^ 3 ≠ 1) ∧
    ¬ ∃ s : galoisSubgroup K →* stabilizer z,
      (galoisProjection hK z hz).comp s = MonoidHom.id _
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hK, ζ, hζ⟩ := primitive_exists
  let K := p.K
  letI := p.fieldK
  letI := p.finiteK
  letI := p.algebraK
  let z := primitiveUnit ζ hζ
  have hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hpos := WeightedSemilinear.OneSupport63.stabilizer_structure hK ζ hζ
  let g : stabilizer z := ⟨tau z, hpos.2.1⟩
  have hg : projection z g = frob K ^ 2 := rfl
  have hb := (h hK ζ hζ).2.2.2.2.2.1 g hg
  have hp := (WeightedSemilinear.OneSupport63.galois_nonsplitting hK ζ hζ).2.2.2.2.2.1 g hg
  have he : (g.val : Ambient K) ^ 3 = 1 := hp.1.trans hb.1.symm
  apply hp.2
  apply Subtype.ext
  exact he
def family : Registration arena (type_of% (@WeightedSemilinear.OneSupport63.galois_nonsplitting)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@WeightedSemilinear.OneSupport63.galois_nonsplitting, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨p, hK, ζ, hζ⟩ := primitive_exists
    let K := p.K
    letI := p.fieldK
    letI := p.finiteK
    letI := p.algebraK
    refine ⟨⟨K⟩, 1, tau (primitiveUnit ζ hζ), ?_⟩
    have hpos := WeightedSemilinear.OneSupport63.stabilizer_structure hK ζ hζ
    change (1 : Ambient K) ^ 3 ≠ tau (primitiveUnit ζ hζ) ^ 3
    rw [one_pow, hpos.2.2.2.2.2.2.1]
    exact Ne.symm hpos.2.2.2.2.2.2.2.1

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@WeightedSemilinear.OneSupport63.galois_nonsplitting) (Realization signature) Unit Unit where
  unitName := `WeightedSemilinear.OneSupport63.galois_nonsplitting.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer.galois_nonsplitting.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","arg","arg","arg","arg","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end galois_nonsplitting
end
end Reg.D5.S3.FiniteGroups.Semilinear.WeightedOneSupportStabilizer
