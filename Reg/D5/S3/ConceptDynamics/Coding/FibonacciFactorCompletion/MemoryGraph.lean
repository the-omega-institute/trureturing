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

def windowValueArena : Arena where
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

def windowShiftArena : Arena where
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

def pathMemoryArena : Arena where
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
