import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
import Reg.Support.UniverseSingleReadout

/-! The Gram square-root readout in the integral basis formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.BasisFormula

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (M : Submodule ℤ E)
    (b : Module.Basis ι ℤ M),
    @covolume E _ _ M (Module.Free.of_basis b) (Module.Finite.of_basis b) =
      V.readout () () (Matrix.gram ℝ (fun i => (b i : E))).det

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let M : Submodule ℤ E := ⊥
  let b : Module.Basis (ULift.{v} Empty) ℤ M := Module.Basis.empty M
  have h := law M b
  rw [covolume_eq_gram M b] at h
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by change Real.sqrt 0 ≠ Real.sqrt 1; norm_num⟩

def family : Registration arena.{u,v} (type_of% @covolume_eq_gram.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@covolume_eq_gram.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@covolume_eq_gram.{u,v}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.covolume_eq_gram
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.BasisFormula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.BasisFormula

open _root_.D5.S3.Combinatorics.Lattices.EuclideanSublattices
open _root_.D5.S3.Combinatorics.Lattices

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Hn

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (A B : Sublattice L),
    V.readout () () (saturationIndex L A B) * covolume (integral L (A ⊓ B)) *
      covolume (integral L (A ⊔ B)) ≤
        covolume (integral L A) * covolume (integral L B) ∧
    ((∃! l, (slopeData L).Filtration A B l) ↔ A ≤ B) ∧
    ∀ e l, (slopeData L).Filtration A B (e :: l) →
      let D := slopeData L
      let q := HarderNarasimhan.lastLower A (e :: l)
      A ≤ q ∧ q < B ∧
        IsGreatest {s | ∃ x, A < x ∧ x ≤ B ∧ D.slope A x = s} (D.slope A e) ∧
        IsLeast {s | ∃ x, A ≤ x ∧ x < B ∧ D.slope x B = s} (D.slope q B) ∧
        D.muMax A B = D.slope A e ∧ D.muMin A B = D.slope q B ∧
        D.Destabilizer A B e ∧ D.slope q B ≤ D.slope A e ∧
        (D.Semistable A B ↔ l = []) ∧
        (D.muMin A B = D.muMax A B ↔ D.Semistable A B) ∧
        (l ≠ [] → D.slope q B < D.slope A e)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  let A : Sublattice L := ⊤
  have hm (M : Submodule ℤ E) : covolume M = 1 := by
    rw [covolume_eq_gram M (Module.Basis.empty M : Module.Basis Empty ℤ M)]
    simp
  have h := (law L A A).1
  simp only [rejected, realize] at h
  simp only [hm] at h
  norm_num at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena.{u} (type_of% @euclidean_hn.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@euclidean_hn.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@euclidean_hn.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.euclidean_hn
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Hn.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Hn

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Index

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M N : Submodule ℤ E) [DiscreteTopology N] (hMN : M ≤ N)
    (hspan : Submodule.span ℝ (M : Set E) = Submodule.span ℝ (N : Set E)),
    letI : DiscreteTopology M :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology N) hMN
    0 < M.toAddSubgroup.relIndex N.toAddSubgroup ∧
    covolume M =
      V.readout () () (M.toAddSubgroup.relIndex N.toAddSubgroup) * covolume N ∧
    (covolume M = covolume N ↔ M = N)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  have h := (law L L le_rfl rfl).2.1
  rw [covolume_eq_gram _ (Module.Basis.empty _ : Module.Basis Empty ℤ L)] at h
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena.{u} (type_of% @covolume_index.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@covolume_index.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@covolume_index.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.covolume_index
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Index.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Index
