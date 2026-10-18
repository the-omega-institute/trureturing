import Reg.Support.FibonacciOriginalSourceWitness.WeightedPaths
import Reg.Support.FibonacciOriginalSourceWitness.Source110
import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
import Reg.Support.DependentFamily

set_option autoImplicit false

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph

noncomputable section

/-- The full family includes zero memory and every real seed. -/
abbrev windowValueSignature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℤ → CuLetter, ℤ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev windowValueArena : Arena where
  signature := windowValueSignature
  Law R := ∀ (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ),
    R.readout () ⟨n, ω, i⟩ z = finitePast ω i n z

def windowValueEvidence : Registration windowValueArena
    (∀ (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ),
      memoryValue (memoryWindow n ω i) z = finitePast ω i n z) := {
  actual := realize windowValueSignature
    (fun _ p z => memoryValue (memoryWindow p.1 p.2.1 p.2.2) z)
    (fun e => nomatch e)
  bridge := Iff.rfl
  variation := by
    refine ⟨window_value,
      realize windowValueSignature (fun _ _ _ => 0) (fun e => nomatch e), ?_⟩
    intro h
    have hzero := h 0 (fun _ => CuLetter.c) 0 1
    norm_num [realize, finitePast] at hzero
  sensitivity := by
    constructor
    · intro i
      refine ⟨realize windowValueSignature (fun _ _ _ => 0) (fun e => nomatch e),
        ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · intro h
        have hzero := h 0 (fun _ => CuLetter.c) 0 1
        norm_num [realize, finitePast] at hzero
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, (fun _ => CuLetter.c), 0⟩, 0, 1, ?_⟩
    norm_num [realize, memoryValue]
}

def window_value_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_value)
      (type_of% (realize.{0,0,0,0,0} windowValueSignature
        (fun _ p z => memoryValue (memoryWindow p.1 p.2.1 p.2.2) z)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_value_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.windowValueEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨windowValueArena⟩
  objectArena := .source ⟨windowValueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowValueArena ⟨windowValueEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} windowValueSignature
    (fun _ p z => memoryValue (memoryWindow p.1 p.2.1 p.2.2) z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

/-- Finite memory vertices do not restrict the bilateral stream or time domain. -/
abbrev windowShiftSignature : Signature where
  Params := Σ _ : ℕ, ℤ → CuLetter
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MemoryVertex p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev windowShiftArena : Arena where
  signature := windowShiftSignature
  Law R := ∀ (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ),
    R.readout () ⟨n, ω⟩ i = memoryShift (memoryWindow n ω i) (ω i)

def windowShiftEvidence : Registration windowShiftArena
    (∀ (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ),
      memoryWindow n ω (i+1) = memoryShift (memoryWindow n ω i) (ω i)) := {
  actual := realize windowShiftSignature
    (fun _ p i => memoryWindow p.1 p.2 (i+1)) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := by
    refine ⟨window_shift,
      realize windowShiftSignature (fun _ _ _ _ => CuLetter.c) (fun e => nomatch e), ?_⟩
    intro h
    have hfirst := congrFun (h 1 (fun _ => CuLetter.u) 0) (0 : Fin 1)
    simp [realize, memoryShift] at hfirst
  sensitivity := by
    constructor
    · intro i
      refine ⟨realize windowShiftSignature (fun _ _ _ _ => CuLetter.c)
        (fun e => nomatch e), ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · intro h
        have hfirst := congrFun (h 1 (fun _ => CuLetter.u) 0) (0 : Fin 1)
        simp [realize, memoryShift] at hfirst
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, (fun j : ℤ => if j = 0 then CuLetter.c else CuLetter.u)⟩,
      0, 1, ?_⟩
    intro h
    have hfirst := congrFun h (0 : Fin 1)
    norm_num [realize, memoryWindow] at hfirst
}

def window_shift_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_shift)
      (type_of% (realize.{0,0,0,0,0} windowShiftSignature
        (fun _ p i => memoryWindow p.1 p.2 (i+1)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_shift_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.windowShiftEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨windowShiftArena⟩
  objectArena := .source ⟨windowShiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowShiftArena ⟨windowShiftEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} windowShiftSignature
    (fun _ p i => memoryWindow p.1 p.2 (i+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

/-- Arbitrary paths and the original shift premise remain in the whole Law.
The witnesses concern the whole family, not dependence in each memory fiber. -/
abbrev pathMemorySignature : Signature where
  Params := Σ n : ℕ, ℤ → MemoryVertex n
  State _ := ℤ → CuLetter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ → MemoryVertex p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev pathMemoryArena : Arena where
  signature := pathMemorySignature
  Law R := ∀ {n : ℕ} (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
    (shift : ∀ i, p (i+1) = memoryShift (p i) (ω i)),
    p = R.readout () ⟨n, p⟩ ω

def pathMemoryEvidence : Registration pathMemoryArena
    (∀ {n : ℕ} (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
      (shift : ∀ i, p (i+1) = memoryShift (p i) (ω i)),
      p = memoryWindow n ω) := {
  actual := realize pathMemorySignature
    (fun _ p ω => memoryWindow p.1 ω) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := by
    refine ⟨@path_memory_reconstruction,
      realize pathMemorySignature (fun _ _ _ _ _ => CuLetter.c) (fun e => nomatch e), ?_⟩
    intro h
    have hpath := @h 1 (fun _ _ => CuLetter.u) (fun _ => CuLetter.u) (by
      intro i
      funext k
      simp [memoryShift])
    have hfirst := congrFun (congrFun hpath (0 : ℤ)) (0 : Fin 1)
    simp [realize] at hfirst
  sensitivity := by
    constructor
    · intro i
      refine ⟨realize pathMemorySignature (fun _ _ _ _ _ => CuLetter.c)
        (fun e => nomatch e), ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · intro h
        have hpath := @h 1 (fun _ _ => CuLetter.u) (fun _ => CuLetter.u) (by
          intro j
          funext k
          simp [memoryShift])
        have hfirst := congrFun (congrFun hpath (0 : ℤ)) (0 : Fin 1)
        simp [realize] at hfirst
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ _ => CuLetter.c)⟩,
      (fun _ => CuLetter.c), (fun _ => CuLetter.u), ?_⟩
    intro h
    have hfirst := congrFun (congrFun h (0 : ℤ)) (0 : Fin 1)
    simp [realize, memoryWindow] at hfirst
}

def path_memory_reconstruction_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.path_memory_reconstruction)
      (type_of% (realize.{0,0,0,0,0} pathMemorySignature
        (fun _ p ω => memoryWindow p.1 ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.path_memory_reconstruction_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.pathMemoryEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pathMemoryArena⟩
  objectArena := .source ⟨pathMemoryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathMemoryArena ⟨pathMemoryEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} pathMemorySignature
    (fun _ p ω => memoryWindow p.1 ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal109
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℤ → CuLetter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℤ → CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ ω => ω) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ _ => CuLetter.u) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (positive : 0 < K) (memory : K ≤ n) (ω : ℤ → CuLetter),
    r.readout () () ω ∈ MemoryLanguage side n K d ↔
      ∃! p : ℤ → MemoryVertex n, BilateralGraphPath side K d p ω

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have member : (fun _ : ℤ => CuLetter.u) ∈ MemoryLanguage .lower 1 1 0 :=
    (original_memory_graph_correspondence .lower 1 1 0 (by decide) (by decide) _).mpr
      ⟨(fun _ _ => .u), all_u_path 1 .lower 1 0, by
        intro p hp
        exact path_memory_reconstruction p _ (fun i => (hp i).1)⟩
  have path := (h .lower 1 1 0 (by decide) (by decide) (fun _ => .c)).mp member
  have bad := (original_memory_graph_correspondence .lower 1 1 0 (by decide) (by decide) _).mpr path
  exact bad.1 0 (fun _ => rfl)

def evidence : Registration sourceArena (type_of% @original_memory_graph_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_memory_graph_correspondence, rejected, rejected_law⟩
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
    refine ⟨(), (fun _ => .u), (fun _ => .c), ?_⟩
    intro eq
    have bad := congrFun eq 0
    cases bad

def original_memory_graph_correspondence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.original_memory_graph_correspondence)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ ω => ω) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal109.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal109.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ ω => ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_graph_correspondence_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal109

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal111
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℤ → CuLetter
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ ω i => ω i) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => CuLetter.c) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ) (v : MemoryVertex n) (w : List CuLetter)
    (walk : RetainedWalk side K d v w), ∃ p ω, BilateralGraphPath side K d p ω ∧ p 0 = v ∧
      ∀ k : Fin w.length, r.readout () ω (k : ℕ) = w[k]

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have walk : RetainedWalk .lower 1 0 (fun _ : Fin 0 => CuLetter.u) [.u] := by
    refine ⟨all_u_live 0 .lower 1 0, ?_, ?_⟩
    · exact ⟨rfl, (by intro h; cases h.1), (by intro h; cases h.1)⟩
    · have eq : memoryShift (fun _ : Fin 0 => CuLetter.u) .u = (fun _ : Fin 0 => CuLetter.u) := by
        funext k; exact Fin.elim0 k
      rw [eq]
      exact all_u_live 0 .lower 1 0
  obtain ⟨p, ω, path, start, letters⟩ := h .lower 1 0 (fun _ : Fin 0 => .u) [.u] walk
  have bad := letters 0
  cases bad

def evidence : Registration sourceArena (type_of% @retained_walk_extension) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@retained_walk_extension, rejected, rejected_law⟩
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
    refine ⟨(fun j : ℤ => if j = 0 then .u else .c), 0, 1, ?_⟩
    simp [actual, realize]

def retained_walk_extension_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.retained_walk_extension)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ ω i => ω i) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal111.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal111.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ ω i => ω i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms retained_walk_extension_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal111

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal112
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ n : ℕ, ℤ → MemoryVertex n
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun q => MemoryVertex q.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ q i => q.2 i) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ q _ _ => CuLetter.c) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ) (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
    (path : BilateralGraphPath side K d p ω) (w : List CuLetter) (i : ℤ)
    (letters : ∀ k : Fin w.length, ω (i+(k : ℕ))=w[k]),
    RetainedWalk side K d (r.readout () ⟨n,p⟩ i) w

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have live := h .lower 0 0 (fun (_ : ℤ) (_ : Fin 1) => CuLetter.u) (fun _ => CuLetter.u)
    (all_u_path 1 .lower 0 0) [] 0 (by intro k; exact Fin.elim0 k)
  obtain ⟨p, ω, path, start⟩ := live
  have shift := congrFun (path (-1)).1 (0 : Fin 1)
  have atzero : p 0 0 = CuLetter.c := congrFun start 0
  have letter : ω (-1) = CuLetter.c := by simpa [memoryShift, atzero] using shift.symm
  apply (path (-1)).2.1
  refine ⟨letter, ?_⟩
  intro k hk
  omega

def evidence : Registration sourceArena (type_of% @bilateral_path_segment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilateral_path_segment, rejected, rejected_law⟩
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
    refine ⟨⟨1, (fun j : ℤ => fun _ : Fin 1 => if j = 0 then .u else .c)⟩, 0, 1, ?_⟩
    intro eq
    have bad := congrFun eq (0 : Fin 1)
    simpa [actual, realize] using bad

def bilateral_path_segment_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.bilateral_path_segment)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ q i => q.2 i) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal112.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal112.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ q i => q.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms bilateral_path_segment_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal112

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal113
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ n => 2^n) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (positive : 0 < K) (memory : K ≤ n) (T : ℕ),
    Finite (RetainedPathDictionary side n K d T) ∧
    factorCount (MemoryLanguage side n K d) T ≤ Nat.card (RetainedPathDictionary side n K d T) ∧
    Nat.card (RetainedPathDictionary side n K d T) ≤ r.readout () () n * factorCount (MemoryLanguage side n K d) T

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bound := h .lower 1 1 0 (by decide) (by decide) 0
  letI : Finite (RetainedPathDictionary .lower 1 1 0 0) := bound.1
  letI : Nonempty (RetainedPathDictionary .lower 1 1 0 0) := ⟨empty_retained⟩
  have positive := Nat.card_pos (α := RetainedPathDictionary .lower 1 1 0 0)
  have upper := bound.2.2
  change Nat.card (RetainedPathDictionary .lower 1 1 0 0) ≤ 0 * _ at upper
  simp only [Nat.zero_mul] at upper
  omega

def evidence : Registration sourceArena (type_of% @original_weighted_path_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_weighted_path_count, rejected, rejected_law⟩
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
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def original_weighted_path_count_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.original_weighted_path_count)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ n => 2^n) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal113.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal113.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ n => 2^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_weighted_path_count_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal113

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal107
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℤ → CuLetter
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => .u) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r₁ := ∀ (n r : ℕ) (positive : 0 < r) (bound : r ≤ n+1) (ω : ℤ → CuLetter) (i : ℤ), memoryRun (memoryWindow n ω i) (ω i) r ↔ ∀ k : Fin r, r₁.readout () ω (i-(k : ℕ)) = .c

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have left : memoryRun (memoryWindow 0 (fun _ => .c) 0) .c 1 := by
    constructor
    · rfl
    · intro k
      exact Fin.elim0 k
  have impossible := (h 0 1 (by omega) (by omega) (fun _ => .c) 0).mp left ⟨0, by omega⟩
  cases impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_run) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_run, rejected, rejected_law⟩
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
    refine ⟨(fun x => if x = 0 then .c else .u), 0, 1, ?_⟩
    simp [actual, realize]

def window_run_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.window_run)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal107.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal107.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms window_run_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal107

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal108
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℤ → CuLetter
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => .u) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (ω : ℤ → CuLetter), (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ)) = .c) ↔ (∀ i : ℤ, ¬ ∀ k : Fin (K+1), r.readout () ω (i-(k : ℕ)) = .c)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have right : ∀ i : ℤ, ¬ ∀ k : Fin (0+1), rejected.readout () (fun _ => .c) (i-(k : ℕ)) = .c := by
    intro i all
    have impossible := all ⟨0, by omega⟩
    cases impossible
  exact (h 0 (fun _ => .c)).mpr right 0 (fun _ => rfl)

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.forbidden_run_reversal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.forbidden_run_reversal, rejected, rejected_law⟩
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
    refine ⟨(fun x => if x = 0 then .c else .u), 0, 1, ?_⟩
    simp [actual, realize]

def forbidden_run_reversal_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.forbidden_run_reversal)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal108.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal108.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ ω x => ω x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms forbidden_run_reversal_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.ExactOriginal108

namespace Reg.Support.FibonacciOriginalSourceWitness.Source110
noncomputable section

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.prepend_bilateral_path)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ ν => ν 0) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source110.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source110.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ ν => ν 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source110

open Reg.Support.FibonacciOriginalSourceWitness.WeightedPaths in
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.original_weighted_adjacency_paths_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.original_weighted_adjacency_paths)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p choices => coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 choices) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.original_weighted_adjacency_paths_registration_unit, realizationName := `Reg.Support.FibonacciOriginalSourceWitness.WeightedPaths.evidence,
  realizationSource := none, generated := false, arena := .source ⟨sourceArena⟩,
  objectArena := .source ⟨sourceArena⟩, catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sourceArena ⟨evidence⟩, correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p choices => coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 choices) (fun e => nomatch e)), variation := .absent,
  sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph, definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
