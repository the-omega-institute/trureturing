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
open scoped InnerProductSpace
open Module Finset

universe u v w

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

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.SublatticeRank

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ m n => m = n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (M : Submodule ℤ L), T.readout () () (Module.finrank ℤ M)
      (Module.finrank ℝ (EuclideanSublattices.realSpan L M))
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  exact law L (⊥ : Submodule ℤ L)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hn : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

def family : Registration arena.{u} (type_of% @EuclideanSublattices.integral_rank_eq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EuclideanSublattices.integral_rank_eq.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanSublattices.integral_rank_eq.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanSublattices.integral_rank_eq
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.SublatticeRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m n => m = n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.SublatticeRank

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.IntegralRank

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ m n => m = n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [DiscreteTopology M],
    T.readout () () (Module.finrank ℤ M)
      (Module.finrank ℝ (EuclideanHarderNarasimhan.realSpan M))
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  exact law L
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hn : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

def family : Registration arena.{u} (type_of% @EuclideanHarderNarasimhan.integral_rank_eq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EuclideanHarderNarasimhan.integral_rank_eq.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanHarderNarasimhan.integral_rank_eq.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.integral_rank_eq
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.IntegralRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m n => m = n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.IntegralRank

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Positive

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [DiscreteTopology M],
    T.readout () () 0 (covolume M)
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  exact law (⊥ : Submodule ℤ (EuclideanSpace ℝ (ULift.{u} Empty)))
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hp : (0 : ℝ) < 1 := by norm_num
  have hn : ¬ (1 : ℝ) < 1 := lt_irrefl 1
  exact hn (Eq.mp (congrFun h 1) hp)

def family : Registration arena.{u} (type_of% @EuclideanHarderNarasimhan.covolume_pos.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EuclideanHarderNarasimhan.covolume_pos.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanHarderNarasimhan.covolume_pos.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.covolume_pos
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Positive

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Contained

abbrev Params := Σ E : Type u, NormedAddCommGroup E
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{u}
    (fun p => letI := p.2; Submodule ℤ p.1)
    (fun p => letI := p.2; Submodule ℤ p.1 → Prop)
def actual : Realization signature.{u} :=
  realize signature (fun _ p M N => letI := p.2; M ≤ N) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (A : Sublattice L),
    T.readout () ⟨E, inferInstance⟩ (integral L A) L
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  exact law L (⊤ : Sublattice L)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let x := EuclideanSpace.basisFun (ULift.{u} Unit) ℝ (ULift.up ())
  refine ⟨⟨E, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have hle : (⊤ : Submodule ℤ E) ≤ ⊥ := Eq.mp (congrFun h ⊥) le_rfl
  have hm : x ∈ (⊥ : Submodule ℤ E) := hle (by trivial)
  have hz : x = 0 := hm
  have hn := (EuclideanSpace.basisFun (ULift.{u} Unit) ℝ).norm_eq_one (ULift.up ())
  change ‖x‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

def family : Registration arena.{u} (type_of% @EuclideanHarderNarasimhan.integral_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EuclideanHarderNarasimhan.integral_le.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanHarderNarasimhan.integral_le.{u}) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.integral_le
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Contained.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p M N => letI := p.2; M ≤ N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Contained

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Saturated

abbrev Params := Σ E : Type u, NormedAddCommGroup E
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{u}
    (fun p => letI := p.2; Submodule ℤ p.1) (fun p => p.1 → Prop)
def actual : Realization signature.{u} :=
  realize signature (fun _ p M x => letI := p.2; x ∈ M) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (A : Sublattice L) (x : E) (_hxL : x ∈ L)
    (_hx : x ∈ EuclideanHarderNarasimhan.realSpan (integral L A)),
    T.readout () ⟨E, inferInstance⟩ (integral L A) x
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  exact law L (⊤ : Sublattice L) 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let x := EuclideanSpace.basisFun (ULift.{u} Unit) ℝ (ULift.up ())
  refine ⟨⟨E, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have hm : x ∈ (⊥ : Submodule ℤ E) := Eq.mpr (congrFun h x) (by trivial)
  have hz : x = 0 := hm
  have hn := (EuclideanSpace.basisFun (ULift.{u} Unit) ℝ).norm_eq_one (ULift.up ())
  change ‖x‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

def family : Registration arena.{u}
    (type_of% @EuclideanHarderNarasimhan.integral_saturated.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@EuclideanHarderNarasimhan.integral_saturated.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanHarderNarasimhan.integral_saturated.{u}) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.integral_saturated
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Saturated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p M x => letI := p.2; x ∈ M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Saturated

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Gram

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type w)
    (fun κ => Matrix κ κ ℝ) (fun κ => Matrix κ κ ℝ → Prop)
def actual : Realization signature.{w} :=
  realize signature (fun _ _ M N => M = N) (fun e => nomatch e)
def rejected : Realization signature.{w} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{w}
  Law T := ∀ {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type v} {κ : Type w} [Fintype ι] (v : ι → E) (M : Matrix ι κ ℝ),
    T.readout () κ (Matrix.gram ℝ (fun j => ∑ i, M i j • v i))
      (M.transpose * Matrix.gram ℝ v * M)
private theorem rejected_fails : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let v : ULift.{v} Empty → E := fun j => nomatch j.down
  let M : Matrix (ULift.{v} Empty) (ULift.{w} Empty) ℝ := fun j => nomatch j.down
  exact law v M
private theorem dependence : ObservationalDependence signature.{w} actual := by
  intro _
  refine ⟨ULift.{w} Unit, 0, (fun _ _ => 1), ?_⟩
  intro h
  have hn : (fun _ _ => (1 : ℝ)) = (0 : Matrix (ULift.{w} Unit) (ULift.{w} Unit) ℝ) :=
    Eq.mp (congrFun h 0) rfl
  have he := congrArg (fun M => M (ULift.up ()) (ULift.up ())) hn
  norm_num at he

def family : Registration arena.{u,v,w}
    (type_of% @EuclideanHarderNarasimhan.gram_linear_combination.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@EuclideanHarderNarasimhan.gram_linear_combination.{u,v,w}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v,w}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@EuclideanHarderNarasimhan.gram_linear_combination.{u,v,w})
    (Realization signature.{w}) Unit Unit where
  unitName := .str
    `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.gram_linear_combination
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Gram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{w} (fun _ _ M N => M = N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan.Gram
