import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open LeanInformationAudit

noncomputable section

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro first second; fin_cases first <;> fin_cases second <;> rfl
  even_diagonal := by intro axis; fin_cases axis <;> exact ⟨0, rfl⟩

abbrev Parameter :=
  Σ D : LatticeData, Σ g : Charge D ≃+ Charge D, Charge D →+ F₂

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    Parameter (fun p => Charge p.1) (fun p => Carrier p.1)

def actual : Realization signature :=
  realize signature
    (fun _ p a => corrected p.1 p.2.1 p.2.2
      (Finsupp.single a (1 : Oscillator p.1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) (a : Charge D),
    r.readout () ⟨D, g, chi⟩ a =
      ((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase D g a : ℂ) *
          complexSign (chi a)) •
        Finsupp.single (g a) (1 : Oscillator D)

theorem source_bridge :
    (type_of% (@corrected_ground_single)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h hyperbolic (AddEquiv.refl _) (by intro a b; rfl) 0 0
  have value := congrArg (fun v : Carrier hyperbolic => v 0) bad
  have hscalar :
      ((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase hyperbolic
          (AddEquiv.refl _) 0 : ℂ) *
        complexSign (0 : F₂)) ≠ 0 := by
    exact mul_ne_zero (Units.ne_zero _) (sign_nonzero _)
  apply hscalar
  simpa [rejected, realize, smul_eq_mul] using value.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨hyperbolic, AddEquiv.refl _, 0⟩, 0,
    unitCharge hyperbolic (0 : Fin 2), ?_⟩
  intro equality
  have hzero := corrected_ground_single hyperbolic (AddEquiv.refl _)
    (by intro a b; rfl) 0 0
  have hone := corrected_ground_single hyperbolic (AddEquiv.refl _)
    (by intro a b; rfl) 0 (unitCharge hyperbolic (0 : Fin 2))
  have equality' :
      corrected hyperbolic (AddEquiv.refl _) 0 (Finsupp.single 0 1) =
        corrected hyperbolic (AddEquiv.refl _) 0
          (Finsupp.single (unitCharge hyperbolic (0 : Fin 2)) 1) := by
    simpa [actual, realize] using equality
  rw [hzero, hone] at equality'
  have value := congrArg (fun v : Carrier hyperbolic => v 0) equality'
  have hunit :
      (0 : Charge hyperbolic) ≠ unitCharge hyperbolic (0 : Fin 2) := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num [unitCharge] at h0
  have hscalar :
      ((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase hyperbolic
          (AddEquiv.refl _) 0 : ℂ) *
        complexSign (0 : F₂)) ≠ 0 := by
    exact mul_ne_zero (Units.ne_zero _) (sign_nonzero _)
  have value' :
      ((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase hyperbolic
          (AddEquiv.refl _) 0 : ℂ) *
        complexSign (0 : F₂)) • (1 : Oscillator hyperbolic) = 0 := by
    calc
      ((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase hyperbolic
          (AddEquiv.refl _) 0 : ℂ) *
        complexSign (0 : F₂)) • (1 : Oscillator hyperbolic) =
          (Finsupp.single (unitCharge hyperbolic (0 : Fin 2))
            (((_root_.D5.S3.VertexAlgebra.Lattice.IsometryLift.phase hyperbolic
              (AddEquiv.refl _) (unitCharge hyperbolic (0 : Fin 2)) : ℂ) *
                complexSign (0 : F₂)) • (1 : Oscillator hyperbolic))) 0 := by
            simpa [hunit] using value
      _ = 0 := by simp [hunit]
  apply hscalar
  simpa [smul_eq_mul] using value'

def family : Registration arena (type_of% (@corrected_ground_single)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp corrected_ground_single, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

abbrev PowParameter :=
  Σ D : LatticeData,
    Σ g : Charge D ≃+ Charge D,
      Σ chi : Charge D →+ F₂, ℕ

abbrev powSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    PowParameter (fun p => Charge p.1) (fun p => Carrier p.1)

def powActual : Realization powSignature :=
  realize powSignature
    (fun _ p a =>
      (corrected p.1 p.2.1 p.2.2.1 ^ p.2.2.2)
        (Finsupp.single a (1 : Oscillator p.1)))
    (fun e => nomatch e)

def powRejected : Realization powSignature :=
  realize powSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev powArena : Arena where
  signature := powSignature
  Law r := ∀ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (chi : Charge D →+ F₂) (n : ℕ) (a : Charge D),
    r.readout () ⟨D, g, chi, n⟩ a =
      correctedGroundPhase D g chi n a •
        Finsupp.single (g^[n] a) (1 : Oscillator D)

theorem powSourceBridge :
    (type_of% (@corrected_ground_pow_single)) ↔ powArena.Law powActual := by
  constructor
  · intro h D g hg chi n a
    simpa [powActual, realize] using h D g hg chi n a
  · intro h D g hg chi n a
    simpa [powActual, realize] using h D g hg chi n a

private theorem powRejectedLaw : ¬ powArena.Law powRejected := by
  intro h
  have bad := h hyperbolic (AddEquiv.refl _) (by intro a b; rfl) 0 0 0
  have value := congrArg (fun v : Carrier hyperbolic => v 0) bad
  simpa [powRejected, realize, correctedGroundPhase] using value

private theorem powDependence : ObservationalDependence powSignature powActual := by
  intro _
  refine ⟨⟨hyperbolic, AddEquiv.refl _, 0, 0⟩, 0,
    unitCharge hyperbolic (0 : Fin 2), ?_⟩
  intro equality
  have value := congrArg (fun v : Carrier hyperbolic => v 0) equality
  have hunit :
      (0 : Charge hyperbolic) ≠ unitCharge hyperbolic (0 : Fin 2) := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num [unitCharge] at h0
  have one_eq_zero : (1 : ℂ) = 0 := by
    simpa [powActual, realize, hunit] using value
  exact one_ne_zero one_eq_zero

def powFamily : Registration powArena (type_of% (@corrected_ground_pow_single)) where
  actual := powActual
  bridge := powSourceBridge
  variation := ⟨powSourceBridge.mp corrected_ground_pow_single,
    powRejected, powRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    powArena.Law powActual powRejected powRejectedLaw
  dependence := powDependence

namespace ObservedGround

abbrev Statement : Prop := type_of% (@corrected_ground_single)

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => decide (s = true)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ s : Bool,
    (r.readout () () s = true) ↔ (if s then Statement else False)

private theorem bridge :
    (type_of% (@corrected_ground_single_observed)) ↔ arena.Law actual := by
  constructor
  · intro h s
    simpa [actual, realize] using h s
  · intro h s
    simpa [actual, realize] using h s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Statement := corrected_ground_single
  have hf : False := by
    simpa [rejected, realize] using (h true).mpr hs
  exact hf

def family : Registration arena (type_of% (@corrected_ground_single_observed)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp corrected_ground_single_observed, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), true, false, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@corrected_ground_single_observed)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.observedUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.ObservedGround.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ObservedGround

namespace ObservedPower

abbrev Statement : Prop := type_of% (@corrected_ground_pow_single)

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => decide (s = true)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ s : Bool,
    (r.readout () () s = true) ↔ (if s then Statement else False)

private theorem bridge :
    (type_of% (@corrected_ground_pow_single_observed)) ↔ arena.Law actual := by
  constructor
  · intro h s
    simpa [actual, realize] using h s
  · intro h s
    simpa [actual, realize] using h s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Statement := corrected_ground_pow_single
  have hf : False := by
    simpa [rejected, realize] using (h true).mpr hs
  exact hf

def family : Registration arena (type_of% (@corrected_ground_pow_single_observed)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp corrected_ground_pow_single_observed, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), true, false, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@corrected_ground_pow_single_observed)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.observedPowUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift.ObservedPower.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ObservedPower

end
end Reg.D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
