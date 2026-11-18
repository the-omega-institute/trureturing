import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
import Reg.Support.DependentFamily

/-! The full polymorphic binomial limit as a convergence readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
universe u

abbrev signature : Signature where
  Params := Type u
  State α := α → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Filter α → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {l : Filter α} (y : α → ℝ) (n k : α → ℕ)
    {d r : ℝ}, Tendsto y l atTop → 0 < d → 0 < r → r < d →
    Tendsto (fun x => (n x : ℝ) / y x) l (𝓝 d) →
    Tendsto (fun x => (k x : ℝ) / y x) l (𝓝 r) →
    R.readout () α (fun x => log ((n x).choose (k x) : ℝ) / y x) l
      (𝓝 (d * binEntropy (r / d)))

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (d := 1) (r := 1/2) tendsto_bot (by norm_num) (by norm_num) (by norm_num)
    tendsto_bot tendsto_bot

def family : Registration arena.{u} (type_of% @log_choose_scaled.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_choose_scaled, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro he
    have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) :=
      Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_choose_scaled.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy.log_choose_scaled.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
