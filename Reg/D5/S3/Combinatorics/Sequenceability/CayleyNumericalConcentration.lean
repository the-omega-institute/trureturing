import D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-! Full-telescope dependent-family audit candidate for the full structural
result. Source-selection binding must be taken from the current compiled
expression after the caller hands off; no accepted binding is asserted here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration

open _root_.D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev Params := Σ G : Type u, Group G × Fintype G × Finset G

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
  realize signature (fun _ p H => by
    letI := p.2.1
    letI := p.2.2.1
    exact ((retained p.2.2.2 H).card : ℝ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀     (G : Type u) [g : Group G] [f : Fintype G]
    (S : Finset G), S.Nonempty →
    ∀ (ε : ℝ), 0 < ε → ε < (1 / 2 : ℝ) →
    ∃ H : Subgroup G,
      let T := retained S H
      let σ := density S
      let τ := density T
      let η := ε * σ ^ 2 / 1000
      (1 - ε) * (S.card : ℝ) ≤ R.readout () ⟨G, g, f, S⟩ H ∧
      σ ≤ τ ∧ NumericalGap T η ∧
      (∀ X Y : Finset H, Disjoint X Y → X ∪ Y = Finset.univ →
        η * τ * (X.card : ℝ) * (Y.card : ℝ) ≤ (directedCut T X Y : ℝ) ∧
        (ε * σ ^ 3 / 1000) * (X.card : ℝ) * (Y.card : ℝ) ≤
          η * τ * (X.card : ℝ) * (Y.card : ℝ) ∧
        directedCut T X Y = directedCut T Y X) ∧
      (∀ z : H → ℂ, (∑ x : H, z x) = 0 →
        (∑ x : H, ∑ t ∈ T, z (x * t)) = 0) ∧
      (∀ (lam : ℂ) (z : H → ℂ),
        (∑ x : H, z x) = 0 → z ≠ 0 →
        (∀ x : H, (∑ t ∈ T, z (x * t)) = lam * z x) →
        lam.re ≤ (1 - η) * (T.card : ℝ)) ∧
      (∀ a : G,
        Function.Bijective (leftCosetMap H a) ∧
        (∀ (h k : H) (s : G),
          (s ∈ S ∧ (leftCosetMap H a k : G) = (leftCosetMap H a h : G) * s) ↔
            ∃ t ∈ T, (t : G) = s ∧ k = h * t)) ∧
      ((H.index : ℝ) ≤ 1 / ((1 - ε) * σ) ∧
        1 / ((1 - ε) * σ) < 2 / σ ∧ (H.index : ℝ) < 2 / σ)

private abbrev Bit := ULift.{u} (Multiplicative (ZMod 2))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨H, hretain, _⟩ := h Bit {1} (Finset.singleton_nonempty 1)
    (1 / 4) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hretain

def family : Registration arena.{u} (type_of% (@exists_subgroup_concentration.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro G g f S hS ε hε hεhalf
    exact exists_subgroup_concentration S hS ε hε hεhalf,
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

/-- This is a concrete full-source candidate, with binding deliberately absent
until the exact current compiler expression is available. It is not a
`declared_validated` registration or evidence that issue 21342 is resolved. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_subgroup_concentration.{u}) (Realization signature.{u})
    (type_of% (@Subgroup.{u})) Unit where
  unitName := .str
    `D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration.exists_subgroup_concentration
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.CayleyNumericalConcentration
end

-- Temporary current-expression diagnostic; removed before delivery.
run_cmd do
  let info ← Lean.getConstInfo
    `D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration.exists_subgroup_concentration
  let rec walk (e : Lean.Expr) (path : List String) : Lean.Elab.Command.CommandElabM Unit := do
    if e.getAppFn.constName? == some ``Nat.cast then
      Lean.logInfo m!"FULL_CORE_CAST {repr path} {repr e}"
    match e with
    | .forallE _ d b _ | .lam _ d b _ => walk d (path ++ ["domain"]); walk b (path ++ ["body"])
    | .letE _ t v b _ => walk t (path ++ ["type"]); walk v (path ++ ["value"]); walk b (path ++ ["body"])
    | .app f a => walk f (path ++ ["fn"]); walk a (path ++ ["arg"])
    | .mdata _ b => walk b (path ++ ["body"])
    | .proj _ _ b => walk b (path ++ ["body"])
    | _ => pure ()
  walk info.type []
