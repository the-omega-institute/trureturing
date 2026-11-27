import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull
import Reg.Support.DependentFamily

/-! The absolute-sum threshold as a readout of the dilation. -/

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull

open _root_.OlairezQ62 _root_.OlairezWrapHull
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

noncomputable section

private abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ n k => (n : ℝ) * (k : ℝ)) (fun e => nomatch e)

private def negativeReadout : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (k : ℕ) (d : sumZero n),
    d ∈ (k : ℝ) • convexHull ℝ (signedPoints n) ↔
      ∃ t : ℝ, absoluteSum (fun i => d.val i + t) ≤ R.readout () n k

private theorem negativeReadout_fails : ¬ arena.Law negativeReadout := by
  intro law
  have h : (0 : sumZero 3) ∈ ((0 : ℕ) : ℝ) • convexHull ℝ (signedPoints 3) :=
    (scaled_wrap_hull_iff (n := 3) 0 0).2 ⟨0, by simp [absoluteSum]⟩
  obtain ⟨t, ht⟩ := (law (n := 3) 0 0).1 h
  change absoluteSum (fun i : ZMod 3 => (0 : sumZero 3).val i + t) ≤ -1 at ht
  have hn : 0 ≤ absoluteSum (fun i : ZMod 3 => (0 : sumZero 3).val i + t) :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

def family : Registration arena (type_of% (@_root_.OlairezWrapHull.scaled_wrap_hull_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_wrap_hull_iff, negativeReadout, negativeReadout_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨negativeReadout, ?_, rfl, negativeReadout_fails⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨3, 0, 1, ?_⟩
    change (3 : ℝ) * (↑(0 : ℕ) : ℝ) ≠ (3 : ℝ) * (↑(1 : ℕ) : ℝ)
    norm_num

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.OlairezWrapHull.scaled_wrap_hull_iff) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `OlairezWrapHull.scaled_wrap_hull_iff
      "Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull/Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => (n : ℝ) * (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{name := `Elab.async, value := .bool true},
    {name := `internal.cmdlineSnapshots, value := .bool true},
    {name := `linter.mathlibStandardSet, value := .bool true},
    {name := `maxSynthPendingDepth, value := .nat 3},
    {name := `pp.unicode.fun, value := .bool true},
    {name := `relaxedAutoImplicit, value := .bool false}] }

end

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull
