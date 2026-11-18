import D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound spectral observation of the actual history matrix. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open _root_.D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open _root_.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum

abbrev signature : Signature where
  Params := Σ _m : ℕ, Σ _n : ℕ, ℕ
  State p := Matrix (Fin (p.2.2+1) × Vtx (![p.1,p.2.1] : Fin 2 → ℕ))
    (Fin (p.2.2+1) × Vtx (![p.1,p.2.1] : Fin 2 → ℕ)) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => spectrum ℂ M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n a b K : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (_haK : a ≤ K) (_hbK : b ≤ K) (z : ℂ) (_hz : z ≠ 0),
    (z ∈ R.readout () ⟨m,n,K⟩ ((asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map
      (algebraMap ℝ ℂ)) ↔ z^(a+b+2) ∈ spectrum ℂ ((U*V).map (algebraMap ℝ ℂ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (m:=1) (n:=1) (a:=0) (b:=0) (K:=0) 1 1 (by omega) (by omega)
    1 (by norm_num)
  have hr : (1:ℂ)^(0+0+2) ∈ spectrum ℂ
      (((1 : Matrix (Fin 1) (Fin 1) ℝ)*1).map (algebraMap ℝ ℂ)) := by
    simp [Matrix.map_one,spectrum.one_eq]
  exact h.mpr hr

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  letI : Nonempty (Fin (0+1) × Vtx (![1,1] : Fin 2 → ℕ)) := ⟨(0,⟨0,(⟨0,by decide⟩ : Fin 1)⟩)⟩
  refine ⟨⟨1,1,0⟩,0,1,?_⟩
  change spectrum ℂ (0 : Matrix (Fin (0+1) × Vtx (![1,1] : Fin 2 → ℕ))
    (Fin (0+1) × Vtx (![1,1] : Fin 2 → ℕ)) ℂ) ≠ spectrum ℂ 1
  intro h
  have hz : (0:ℂ) ∈ spectrum ℂ (0 : Matrix (Fin (0+1) × Vtx (![1,1] : Fin 2 → ℕ))
    (Fin (0+1) × Vtx (![1,1] : Fin 2 → ℕ)) ℂ) :=
    (spectrum.zero_mem_iff ℂ).mpr not_isUnit_zero
  rw [h] at hz
  exact spectrum.zero_notMem ℂ isUnit_one hz

def family : Registration arena (type_of% (@nonzero_spectrum_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonzero_spectrum_iff,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonzero_spectrum_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage:=.evidence,objectStage:=.evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => spectrum ℂ M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
    definition := none
    coordinates := #[0,1,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
