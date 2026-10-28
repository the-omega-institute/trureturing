import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.SourceMobius.Nilpotence
/-! Faithful dependent-family source registration for the original theorem telescope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.SourceMobius.Nilpotence
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.SourceMobius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, Charge D × ℕ) (fun t => Oscillator t.1) (fun t => Oscillator t.1)
def actual : Realization signature := realize signature
  (fun _ t p => ((sectorL1 t.1 t.2.1).toLinearMap ^ t.2.2) p) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ t p => ((sectorL1 t.1 t.2.1).toLinearMap ^ t.2.2) p + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    H * gramComplex D = 1 → gramComplex D * H = 1 → ∀ (a : Charge D) (p : Oscillator D) (n : ℕ),
      (sugawaraMode D H 1 ^ n) (Finsupp.single a p) = Finsupp.single a (R.readout () ⟨D,(a,n)⟩ p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) *
      gramComplex emptyLattice = 1 := Subsingleton.elim _ _
  have hf : gramComplex emptyLattice *
      (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) = 1 := Subsingleton.elim _ _
  have hh := congrArg (fun v : Carrier emptyLattice => v 0)
    (h emptyLattice 0 he hf 0 0 0)
  simpa [rejected, realize] using hh

set_option maxHeartbeats 2000000 in
def sourceProof : Registration arena (type_of% (@sugawara_pow_single)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sugawara_pow_single, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨emptyLattice,(0,0)⟩, (0 : Oscillator emptyLattice),
      (1 : Oscillator emptyLattice), ?_⟩
    change (0 : Oscillator emptyLattice) ≠ 1
    exact zero_ne_one

def sugawara_pow_single_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.VertexAlgebra.SourceMobius.sugawara_pow_single)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SourceMobius.Nilpotence.sugawara_pow_single
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceMobius.Nilpotence.sourceProof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t p => ((sectorL1 t.1 t.2.1).toLinearMap ^ t.2.2) p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceMobius.Nilpotence
    definition := none
    coordinates := #[0,4,6]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 5,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }

  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.SourceMobius.Nilpotence
