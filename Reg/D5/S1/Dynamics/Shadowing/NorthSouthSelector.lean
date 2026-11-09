import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Shadowing.NorthSouthSelector

/-! The full source telescope is retained. The observed state is the actual
selector output and its comparison point is the integer translate of Q(x).
A source-selection certificate is not asserted by the typed logical bridge. -/

noncomputable section
open Set Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open _root_.D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
open _root_.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector (LocalEquiconnection)

namespace Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector
universe u

abbrev outputSignature : Signature where
  Params := Σ X : Type u, X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization outputSignature.{u} :=
  realize outputSignature (fun _ p x => @decide (x = p.2) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization outputSignature.{u} :=
  realize outputSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := outputSignature.{u}
  Law A := ∀ {M : Type u} [MetricSpace M] [CompactSpace M] {f : M ≃ₜ M} {N S : M},
    Pointwise f N S → ∀ H : LocalEquiconnection M,
      ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ Q : CompactSelector.Space f δ → M,
        Continuous Q ∧
        (∀ p, Q (CompactSelector.trueOrbit f hδ.le p) = p) ∧
        ∀ (k : ℤ) (x : CompactSelector.Space f δ),
          A.readout () ⟨M, (f ^ k) (Q x)⟩ (Q (CompactSelector.shift f k x)) = true

abbrev Two := ULift.{u} (Fin 2)

instance : MetricSpace Two.{u} := Topology.IsEmbedding.comapMetricSpace
  (fun p : Two => (p.down.val : ℝ))
  ((continuous_of_discreteTopology : Continuous (fun p : Two => (p.down.val : ℝ))).isClosedEmbedding
    (by
      intro p q hpq
      apply ULift.ext
      apply Fin.ext
      have hh : (p.down.val : ℝ) = (q.down.val : ℝ) := hpq
      exact_mod_cast hh)).isEmbedding

def north : Two.{u} := ⟨0⟩
def south : Two.{u} := ⟨1⟩

def twoDynamics : Pointwise (Homeomorph.refl Two.{u}) north south where
  distinct := by
    intro hh
    have := congrArg (fun p : Two => p.down.val) hh
    norm_num [north, south] at this
  north_fixed := rfl
  south_fixed := rfl
  forward p hpN hpS := by
    rcases p with ⟨p⟩
    fin_cases p
    · exact (hpN rfl).elim
    · exact (hpS rfl).elim
  backward p hpN hpS := by
    rcases p with ⟨p⟩
    fin_cases p
    · exact (hpN rfl).elim
    · exact (hpS rfl).elim

def twoConnection : LocalEquiconnection Two.{u} where
  domain := {p | p.1 = p.2}
  isOpen_domain := isOpen_discrete _
  diagonal _ := rfl
  connect z := z.1.1.1
  continuous_connect := continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  left _ := rfl
  right p := p.2
  refl _ _ := rfl

theorem actual_law : arena.{u}.Law actual := by
  classical
  simpa only [arena, actual, realize, decide_eq_true_eq] using
    (@pointwise_north_south_selector.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  obtain ⟨δ, hδ, Q, hQ, hfix, heq⟩ := hh twoDynamics twoConnection
  exact Bool.false_ne_true (heq 0 (CompactSelector.trueOrbit _ hδ.le north))

def familyRegistration : Registration arena.{u} (type_of% (@pointwise_north_south_selector.{u})) where
  actual := actual
  bridge := by
    classical
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Two.{u}, north⟩, north, south, ?_⟩
    simp [actual, realize, north, south]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pointwise_north_south_selector.{u}) (Realization outputSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector.integerEquivariance
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize outputSignature.{u}
    (fun _ p x => @decide (x = p.2) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Shadowing.NorthSouthSelector
