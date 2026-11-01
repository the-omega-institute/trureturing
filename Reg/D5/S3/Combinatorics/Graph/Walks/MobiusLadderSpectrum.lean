import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
import Reg.Support.DependentFamily

set_option autoImplicit false
namespace Reg.D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
open _root_.CubicCirculant
open _root_.MatchingCliqueCycle (spectrum)
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Spectrum
abbrev signature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p k => decide (k ∈ spectrum (mobius p))) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ m k : ℕ,
    R.readout () m k = true ↔ m+2 ≤ 2*k ∧ k ≤ m+2 ∧ Odd k

private lemma source_law : arena.Law actual := by
  intro m k
  change decide (k ∈ spectrum (mobius m)) = true ↔ _
  rw [decide_eq_true_eq]
  exact mobius_spectrum m k
private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 1).mpr (by norm_num)
  exact Bool.false_ne_true hh

def registration : Registration arena (type_of% (@_root_.CubicCirculant.mobius_spectrum)) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨source_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨0,1,0,?_⟩
    have hy : 1 ∈ spectrum (mobius 0) :=
      (mobius_spectrum 0 1).mpr (by norm_num)
    have hn : 0 ∉ spectrum (mobius 0) := by
      rw [mobius_spectrum]
      norm_num
    change decide (1 ∈ spectrum (mobius 0)) ≠
      decide (0 ∈ spectrum (mobius 0))
    rw [decide_eq_true hy,decide_eq_false hn]
    decide

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.CubicCirculant.mobius_spectrum)
    (type_of% (realize signature (fun _ p k => decide (k ∈ spectrum (mobius p))) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `CubicCirculant.mobius_spectrum
    "Reg.D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum/Reg.D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum.Spectrum.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum.Spectrum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => decide (k ∈ spectrum (mobius p))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit,value := .bool false }] }
#print axioms registration
#print axioms contract
end Spectrum
end
end Reg.D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
