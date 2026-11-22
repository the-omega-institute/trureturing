import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62
import Reg.Support.DependentFamily

/-! Source-bound affine action readout. -/

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62

open _root_.OlairezQ62
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev signature : Signature where
  Params := Σ n : ℕ, Equiv.Perm (ZMod n)
  State := fun p => Coordinates p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Coordinates p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p x => act p.2 x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 3 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    paperLabel (0 : ZMod n) = n ∧
    (∀ i j : ZMod n,
      permutationMatrix (s1 n) i j =
        (if paperLabel j = paperColumn1 n (paperLabel i) then 1 else 0) ∧
      permutationMatrix (s2 n) i j =
        (if paperLabel j = paperColumn2 n (paperLabel i) then 1 else 0)) ∧
    (∀ (g : Equiv.Perm (ZMod n)) (x : Coordinates n),
      (permutationMatrix g).mulVec x = R.readout () ⟨n, g⟩ x) ∧
    (∀ x : Coordinates n, act 1 x = x) ∧
    (∀ (g h : Equiv.Perm (ZMod n)) (x : Coordinates n), act (g * h) x = act g (act h x)) ∧
    (s1 n * s1 n = 1 ∧ s2 n * s2 n = 1) ∧
    (∀ g : Equiv.Perm (ZMod n),
      g ∈ sourceGroup n ↔ (∃ a, g = shift a) ∨ (∃ a, g = reflection a)) ∧
    (∀ j : ZMod n,
      act ((s2 n * s1 n) ^ (j - 1).val) (rho n) = r j ∧
      act ((s2 n * s1 n) ^ (j - 1).val * (s2 n * s1 n * s2 n)) (rho n) = f j ∧
      (∀ i : ZMod n, r j i = (paperLabel (i + j - 1) : ℝ) ∧
        f j i = (n : ℝ) + 1 - r j i)) ∧
    (∀ j : ZMod n, act (s2 n * s1 n * s2 n) (r j) = f (2 - j)) ∧
    (fun i => rho n ((s2 n * s1 n) i)) ≠ r (2 : ZMod n) ∧
    (¬ ∃ a : ZMod n, ∀ j : ZMod n, act (reflection a) (r j) = f j) ∧
    orbit n = Set.range (r (n := n)) ∪ Set.range (f (n := n)) ∧
    (fun w : sumZero n => w.val) '' centeredQ n =
      (fun x : Coordinates n => x - center n) '' Q n ∧
    (∀ (x : sumZero n) (i : ZMod n), (delta n x).val i = x.val (i + 1) - x.val i) ∧
    (∀ j : ZMod n, delta n (rCentered j) = wrapPoint (1 - j) ∧
      delta n (fCentered j) = -wrapPoint (1 - j)) ∧
    delta n '' centeredQ n = convexHull ℝ (signedPoints n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let g : Equiv.Perm (ZMod 3) := 1
  let x : Coordinates 3 := fun _ => 1
  have he := (h 3 (by decide)).2.2.1 g x
  have ha := (source_coordinate_conjugacy 3 (by decide)).2.2.1 g x
  have hc := congrFun (ha.symm.trans he) 0
  change (1 : ℝ) = 0 at hc
  norm_num at hc

def family : Registration arena (type_of% (@_root_.OlairezQ62.source_coordinate_conjugacy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.OlairezQ62.source_coordinate_conjugacy, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨3, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro eq
    have h := congrFun eq 0
    norm_num [actual, realize, act] at h

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.OlairezQ62.source_coordinate_conjugacy) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `OlairezQ62.source_coordinate_conjugacy "Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62/Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => act p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body", "arg"]
      stateBinder := 3
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

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62
