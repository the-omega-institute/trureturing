import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability (T depth)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval (coordinates offset)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators symmDiff Pointwise
noncomputable section

def signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => depth t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

namespace Cube
def arena : Arena where
  signature := signature
  Law R :=
    ∀ (n : ℕ), 3 ≤ n →
    (positions (T n)).card = Nat.fib (n-2) ∧
    Function.Injective
      (fun A : {A : Finset Address // A ⊆ positions (T n)} => variant (T n) A.val) ∧
    (∀ (A : Finset Address), A ⊆ positions (T n) →
      wd (variant (T n) A) = wd (T n) ∧
      (variant (T n) A).length = Nat.fib (n+1) ∧
      R.readout () () (variant (T n) A) = (if A = ∅ then n else 0) ∧
      areaVector (Nat.fib (n+1)) (variant (T n) A) =
        areaVector (Nat.fib (n+1)) (T n) +
          ∑ p ∈ A, gapVector (Nat.fib (n+1)) (offset (T n) p) ∧
      (∑ i, areaVector (Nat.fib (n+1)) (variant (T n) A) i) =
        ((Nat.fib (n+1)).choose 2 : ℝ) ∧
      (coordinates (variant (T n) A)).length = Nat.fib (n+1)-1 ∧
      ∀ B ⊆ positions (T n),
        ‖areaVector (Nat.fib (n+1)) (variant (T n) A) -
          areaVector (Nat.fib (n+1)) (variant (T n) B)‖ ^ 2 = 2 * ((A ∆ B).card : ℝ)) ∧
    (∀ p, p ∈ positions (T n) ↔ subtree p (T n) = some defectB) ∧
    (∀ p ∈ positions (T n), offset (T n) p < Nat.fib (n+1)-1 ∧
      offset (T n) p+1 < Nat.fib (n+1)-1) ∧
    (∀ p ∈ positions (T n), ∀ q ∈ positions (T n), p ≠ q →
      offset (T n) p+3 ≤ offset (T n) q ∨ offset (T n) q+3 ≤ offset (T n) p) ∧
    convexHull ℝ (areaVertices (T n) : Set (EuclideanSpace ℝ (Fin ((T n).length-1)))) =
      {areaVector (T n).length (T n)} +
        parallelepiped (fun p : positions (T n) =>
          gapVector (T n).length (offset (T n) p.val)) ∧
    (affineSpan ℝ (convexHull ℝ (areaVertices (T n) :
      Set (EuclideanSpace ℝ (Fin ((T n).length-1)))))).direction = directionSpan (T n) ∧
    Orthonormal ℝ (unitDirection (T n)) ∧
    directionSpan (T n) = Submodule.span ℝ (Set.range (fun p : positions (T n) =>
      gapVector (T n).length (offset (T n) p.val))) ∧
    Module.finrank ℝ (directionSpan (T n)) = Nat.fib (n-2) ∧
    (∀ p : positions (T n), ‖gapVector (T n).length (offset (T n) p.val)‖ = Real.sqrt 2) ∧
    MeasureTheory.volume (intrinsicCube (T n)) =
      ENNReal.ofReal ((2:ℝ) ^ ((Nat.fib (n-2):ℝ)/2))

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.native_area_cube)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_area_cube, rejected, by
    intro h
    have he := ((h 3 (by decide)).2.2.1 ∅ (Finset.empty_subset _)).2.2.1
    change (0 : ℕ) = 3 at he
    norm_num at he⟩
  sensitivity := by
    unfold Sensitivity
    dsimp only [arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, by
        intro h
        have he := ((h 3 (by decide)).2.2.1 ∅ (Finset.empty_subset _)).2.2.1
        change (0 : ℕ) = 3 at he
        norm_num at he⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    unfold ObservationalDependence
    dsimp only [arena, signature]
    intro i
    refine ⟨(), variant (T 3) ∅, variant (T 3) (positions (T 3)), ?_⟩
    have h := normalized_cube_diameter.1 3 (by decide)
    change depth (variant (T 3) ∅) ≠ depth (variant (T 3) (positions (T 3)))
    rw [h.2.2.1,h.2.2.2.1]
    decide

def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.native_area_cube)
    (type_of% (realize signature (fun _ _ t => depth t) (fun e => nomatch e)))
    (Type) (Unit) := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.Cube.native_area_cube.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.Cube.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => depth t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end Cube

namespace Diameter
def arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 3 ≤ n →
      Metric.diam (normalizedAreaFamily n) =
        Real.sqrt (2 * (Nat.fib (n-2) : ℝ)) / ((Nat.fib (n+1)).choose 2 : ℝ) ∧
      (sourceFamily (T n)).card = 2 ^ Nat.fib (n-2) ∧
      R.readout () () (variant (T n) ∅) = n ∧ depth (variant (T n) (positions (T n))) = 0 ∧
      ‖((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ • areaVector (T n).length (variant (T n) ∅) -
        ((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ •
          areaVector (T n).length (variant (T n) (positions (T n)))‖ =
        Metric.diam (normalizedAreaFamily n)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => Metric.diam (normalizedAreaFamily n))
      (fun n => (Nat.fib (n+1) : ℝ) ^ (-(3/2 : ℝ))) ∧
    Filter.Tendsto (fun n => Metric.diam (normalizedAreaFamily n))
      Filter.atTop (nhds 0)

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.normalized_cube_diameter)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_cube_diameter, rejected, by
    intro h
    have he := (h.1 3 (by decide)).2.2.1
    change (0 : ℕ) = 3 at he
    norm_num at he⟩
  sensitivity := by
    unfold Sensitivity
    dsimp only [arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, by
        intro h
        have he := (h.1 3 (by decide)).2.2.1
        change (0 : ℕ) = 3 at he
        norm_num at he⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    unfold ObservationalDependence
    dsimp only [arena, signature]
    intro i
    refine ⟨(), variant (T 3) ∅, variant (T 3) (positions (T 3)), ?_⟩
    have h := normalized_cube_diameter.1 3 (by decide)
    change depth (variant (T 3) ∅) ≠ depth (variant (T 3) (positions (T 3)))
    rw [h.2.2.1,h.2.2.2.1]
    decide

def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.normalized_cube_diameter)
    (type_of% (realize signature (fun _ _ t => depth t) (fun e => nomatch e)))
    (Type) (Unit) := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.Diameter.normalized_cube_diameter.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.Diameter.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => depth t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end Diameter

end
namespace FillAt
def signature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => subtree p t) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (t : Source) (a : Address → Bool) (p : Address), p ∈ positions t →
    F.readout () p (fill t a) = some (if a p then defectD else defectB)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have eq := h defectB (fun _ => false) [] (by decide)
  change (none : Option Source) = some defectB at eq
  cases eq

def evidence : Registration arena (type_of% (@fill_at)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fill_at,bad,bad_law⟩
  sensitivity := by
    unfold Sensitivity
    dsimp only [arena,signature]
    constructor
    · intro i
      exact ⟨bad,fun j ne => (ne (Subsingleton.elim j i)).elim,rfl,bad_law⟩
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨[],.of true,.of false,?_⟩
    change some (FreeMagma.of true) ≠ some (FreeMagma.of false)
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fill_at) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.fill_at.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.FillAt.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => subtree p t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end FillAt
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
