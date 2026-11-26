import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance
import Reg.Support.UniverseSingleReadout

/-! The actual Gram square root in the complete isometry-equivariance theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices
open EuclideanSublattices EuclideanHarderNarasimhan EuclideanHNEquivariance
open _root_.D5.S3.Combinatorics.Lattices.HarderNarasimhan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {E : Type u} [normed : NormedAddCommGroup E] [inner : InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
    (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
    [FiniteDimensional ℝ E] [DiscreteTopology L],
    let Λ := Sublattice L
    let e : Λ → Λ := sublatticeMap L T hT
    let D : SlopeData Λ := slopeData L
    let R : Λ → ℤ := D.rank
    let F : Λ → Λ → List Λ → Prop := D.Filtration
    let C : Λ → ℝ := fun A => covolume (integral L A)
    let G : Λ → ℝ := gramDet L
    let H : ℝ → Λ → List Λ → Λ := above L D
    (∀ A : Λ, R (e A) = R A ∧ C (e A) = V.readout () () (G A)) ∧
    (∀ (A B : Λ) (l : List Λ), F A B l ↔ F (e A) (e B) (l.map e)) ∧
    ∀ (A B : Λ) (l : List Λ), e A = A → e B = B → F A B l →
      l.map e = l ∧ (∀ K ∈ l, e K = K) ∧
      ∀ t : ℝ, e (H t A l) = H t A l

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  let T := LinearIsometryEquiv.refl ℝ E
  have hT : L.map (T.toLinearMap.restrictScalars ℤ) = L := by simp [L, T]
  have h := ((law L T hT).1 ⊥).2
  dsimp only at h
  rw [covolume_eq_gram _ (Module.Basis.empty _ : Module.Basis Empty ℤ _)] at h
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by change Real.sqrt 0 ≠ Real.sqrt 1; norm_num⟩

def family : Registration arena.{u} (type_of% @isometry_hn.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isometry_hn.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isometry_hn.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance.isometry_hn
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHNEquivariance
