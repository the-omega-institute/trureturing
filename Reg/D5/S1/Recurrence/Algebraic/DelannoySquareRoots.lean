import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.DelannoySquareRoots
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots

open _root_.D5.S1.Recurrence.Algebraic.DelannoySquareRoots
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := List Step
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => (endpoint p).1 + (endpoint p).2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The entire source law is retained. The observation is the endpoint coordinate sum
in the path-enumeration equivalence, with its original row and path variables. -/
def arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ) (p : List Step), p ∈ paths n ↔ R.readout () n p = n) ∧
    squareDenominator * squareSeries = 1 - PowerSeries.X ∧
    (∀ n : ℕ, (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (1 - Real.sqrt 2) ≠ 0) ∧
    ∀ (u v y : ℂ), u ≠ 0 → v ≠ 0 → u + v + u * v = 1 → y * u * v = 1 →
      ∀ n : ℕ, y * (v - u) * (-1) ^ n *
        (squareRow n).eval₂ (Int.castRingHom ℂ) (-y) =
        (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u) / u ^ (n + 1) -
          (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-v) / v ^ (n + 1)

def family : Registration arena (type_of% source_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_correspondence, rejected, by
    intro h
    have h0 := (h.1 0 []).mp (by simp [paths])
    norm_num [rejected, realize] at h0⟩
  sensitivity := by
    have bad : ¬ arena.Law rejected := by
      intro h
      have h0 := (h.1 0 []).mp (by simp [paths])
      norm_num [rejected, realize] at h0
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(0 : ℕ), ([] : List Step), [Step.east], ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    source_correspondence (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.DelannoySquareRoots.source_correspondence
    "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots.family
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
    owner := `D5.S1.Recurrence.Algebraic.DelannoySquareRoots
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots
