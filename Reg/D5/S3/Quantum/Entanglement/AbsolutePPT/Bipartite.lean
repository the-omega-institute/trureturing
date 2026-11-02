import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of cyclic sector reconstruction and Fourier coordinates. -/

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev dimensions := Σ _n : ℕ, ℕ

/-- Translate a residue string by its sector origin. -/
abbrev pointSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature dimensions
    (fun p => ZMod p.2) (fun p => (Fin p.1 → ZMod p.2) → Fin p.1 → ZMod p.2)

def pointActual : Realization pointSignature :=
  realize pointSignature (fun _ _ t => sectorPoint t) (fun e => nomatch e)

def pointRejected : Realization pointSignature :=
  realize pointSignature (fun _ _ _ _ => 0) (fun e => nomatch e)

private theorem pointDependence : ObservationalDependence pointSignature pointActual := by
  intro i
  refine ⟨⟨1, 2⟩, 0, 1, ?_⟩
  intro h
  have hbad := congrFun (congrFun h 0) 0
  change (0 : ZMod 2) + 0 = 1 + 0 at hbad
  norm_num at hbad

namespace Coordinates

abbrev arena : Arena where
  signature := pointSignature
  Law R := ∀ {n d : ℕ} [NeZero n] (i : Fin n → ZMod d),
    sectorCoordinate i 0 = 0 ∧
      R.readout () ⟨n, d⟩ (i 0) (sectorCoordinate i) = i

private theorem rejected_law : ¬ arena.Law pointRejected := by
  intro h
  have hbad := (@h 1 2 inferInstance (fun _ => 1)).2
  have hh := congrFun hbad 0
  change (0 : ZMod 2) = 1 at hh
  norm_num at hh

def source : Registration arena (type_of% @sector_coordinates) where
  actual := pointActual
  bridge := Iff.rfl
  variation := ⟨@sector_coordinates, pointRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    pointActual pointRejected rejected_law
  dependence := pointDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sector_coordinates) (Realization pointSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.Coordinates.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pointSignature (fun _ _ t => sectorPoint t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end Coordinates

namespace Injective

abbrev arena : Arena where
  signature := pointSignature
  Law R := ∀ {n d : ℕ} [NeZero n] (r s : Fin n → ZMod d)
    (_hr : r 0 = 0) (_hs : s 0 = 0) (t u : ZMod d),
    R.readout () ⟨n, d⟩ t r = sectorPoint u s → t = u ∧ r = s

private theorem rejected_law : ¬ arena.Law pointRejected := by
  intro h
  have hbad := (@h 1 2 inferInstance 0 0 rfl rfl 1 0 rfl).1
  norm_num at hbad

def source : Registration arena (type_of% @sectorPoint_injective) where
  actual := pointActual
  bridge := Iff.rfl
  variation := ⟨@sectorPoint_injective, pointRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    pointActual pointRejected rejected_law
  dependence := pointDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sectorPoint_injective) (Realization pointSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.Injective.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pointSignature (fun _ _ t => sectorPoint t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end Injective

namespace AtPoint

/-- The normalized complex character amplitude, with the modulus retained. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ d z => (Real.sqrt d : ℂ)⁻¹ * z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n d : ℕ} [NeZero n] [NeZero d] (a t : ZMod d)
    (r : Fin n → ZMod d) (_hr : r 0 = 0),
    fourierVector a r (sectorPoint t r) = R.readout () d (ZMod.stdAddChar (a * t))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := @h 1 1 inferInstance inferInstance 0 0 0 rfl
  rw [fourier_at_point 0 0 0 rfl] at hbad
  norm_num [rejected, realize] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def source : Registration arena (type_of% @fourier_at_point) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fourier_at_point, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fourier_at_point) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.AtPoint.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ d z => (Real.sqrt d : ℂ)⁻¹ * z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end AtPoint

namespace OffSector

/-- Evaluate a Fourier vector at the selected residue string. -/
abbrev parameters := Σ n : ℕ, Σ d : ℕ, Fin n → ZMod d

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature parameters
    (fun p => (Fin p.1 → ZMod p.2.1) → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p f => f p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n d : ℕ} [NeZero n] [NeZero d] (a : ZMod d)
    (r i : Fin n → ZMod d) (_hi : i ≠ sectorPoint (i 0) r),
    R.readout () ⟨n, d, i⟩ (fourierVector a r) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : (0 : Fin 1 → ZMod 2) ≠ sectorPoint 0 (fun _ => 1) := by
    intro he
    have hh := congrFun he 0
    norm_num [sectorPoint] at hh
  have hbad := @h 1 2 inferInstance inferInstance 0 (fun _ => 1) 0 hi
  change (1 : ℂ) = 0 at hbad
  exact one_ne_zero hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 0⟩, 0, 1, ?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

def source : Registration arena (type_of% @fourier_off_sector) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fourier_off_sector, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fourier_off_sector) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.OffSector.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => f p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end OffSector

namespace Basis

/-- Complex conjugation of the first Fourier vector in the inner product. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature dimensions
    (fun p => (Fin p.1 → ZMod p.2) → ℂ) (fun p => (Fin p.1 → ZMod p.2) → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => star f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) [NeZero n] [NeZero d] (_hn : 2 ≤ n) (_hd : 2 ≤ d)
    (a c : ZMod d) (r s : Fin n → ZMod d) (_hr : r 0 = 0) (_hs : s 0 = 0),
    R.readout () ⟨n, d⟩ (fourierVector a r) ⬝ᵥ fourierVector c s =
      if a = c ∧ r = s then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 2 (by decide) (by decide) 0 0 0 0 rfl rfl
  change (0 : (Fin 2 → ZMod 2) → ℂ) ⬝ᵥ fourierVector 0 0 =
    if (0 : ZMod 2) = 0 ∧ (0 : Fin 2 → ZMod 2) = 0 then 1 else 0 at hbad
  simp only [zero_dotProduct, and_self, ↓reduceIte] at hbad
  exact zero_ne_one hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro h
  have hbad := congrFun h 0
  change star (0 : ℂ) = star (1 : ℂ) at hbad
  simp at hbad

def source : Registration arena (type_of% @sector_basis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sector_basis, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sector_basis) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.Basis.unit
  realizationName := ``source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => star f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end Basis

#print sector_coordinates
#print sectorPoint_injective
#print fourier_at_point
#print fourier_off_sector
#print sector_basis

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
