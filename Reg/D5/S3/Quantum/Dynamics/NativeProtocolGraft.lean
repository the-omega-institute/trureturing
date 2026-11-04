import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Dynamics.NativeProtocolGraft

noncomputable section
open scoped BigOperators Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
namespace Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (T : Tree Cut) (C : Path T → Fin 2 → Tree Stop)
    (program : ℕ) (event : (ℕ × Path T × Option (Fin 2) × Stop) → Basis → Bool) ,
    r.readout () () (projectedMass T C program event)
      (∑ p, ∑ q : Path (extension T C p), ∑ z,
        if event (program,p,readTag (label T p) (C p) q,label (extension T C p) q) z then
          Complex.normSq (((operator (extension T C p) q * operator T p).mulVec omega0) z)
        else 0) ∧
    maxCalls (graft T (extension T C)) =
      Finset.univ.sup (fun p => calls T p + maxCalls (extension T C p)) ∧
    (∀ p, CutLaw (label T p) (C p)) ∧
    (∀ (p : Path T) (q : Path (extension T C p)),
      operator (graft T (extension T C)) (attach T (extension T C) p q) =
        operator (extension T C p) q * operator T p ∧
      archive (graft T (extension T C)) (attach T (extension T C) p q) =
        archive T p ++ archive (extension T C p) q ∧
      calls (graft T (extension T C)) (attach T (extension T C) p q) =
        calls T p + calls (extension T C p) q ∧
      label (graft T (extension T C)) (attach T (extension T C) p q) =
        label (extension T C p) q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let T : Tree Cut := .leaf .active
  let C : Path T → Fin 2 → Tree Stop := fun _ _ => .leaf ⟨.normal,0⟩
  exact (h T C 0 (fun _ _ => false)).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at he
  have hf : (1 : ℝ) = 0 := Eq.mp he rfl
  norm_num at hf

def family : Registration arena (type_of% (@original_native_projection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_native_projection,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- The full source family has typed evidence. Source occurrence selection
remains unspecified; this does not assert accepted source reconstruction. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_native_projection) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Dynamics.NativeProtocolGraft.original_native_projection.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.NativeProtocolGraft
