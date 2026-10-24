import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical

set_option autoImplicit false
set_option Elab.async false

open Matrix Finset LeanInformationAudit
open scoped BigOperators ComplexOrder
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (5*n) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i)^2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ) (_hn : 5 ≤ n) (_hn' : n ≤ 18)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ),
    Antitone l → (∀ i, 0 ≤ l i) →
    APPT (diagonal (fun p => (l (e p) : ℂ))) →
    O.readout () n l ≤
      ((((5*n : ℕ) : ℝ)+8)/((((5*n : ℕ) : ℝ)+2)^2))*(∑ i,l i)^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e : (Fin 5 × Fin 5) ≃ Fin (5*5) := finProdFinEquiv
  have hz : APPT (diagonal (fun p => ((0 : Fin (5*5) → ℝ) (e p) : ℂ))) := by
    intro U
    have hzero :
        _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
          (0 : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ) = 0 := by
      ext p q
      rfl
    simpa [hzero, Pi.zero_apply] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ).PosSemidef)
  have hb := h 5 (by decide) (by decide) e 0
    (by intro i j hij; exact le_rfl) (fun _ => le_rfl) hz
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨5, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def family : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical.physical_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical.physical_upper,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Candidate for the original arbitrary-mass physical upper theorem. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical.physical_upper)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical.physical_upper.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => ∑ i, (l i)^2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- UNVALIDATED: actual elaborated occurrence/scope extraction remains required.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

-- actual_to_hyp's own multi-field source registration remains unpaid. This
-- physical_upper record does not stand in for that separate declaration.
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
