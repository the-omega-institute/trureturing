import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCyclicContinuation
import Reg.Support.SingleDependentReadout
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
/-! Source-equivalent readouts with explicit variation and observational dependence. -/

open _root_.D5.S3.CharacterSums.DirichletCyclicContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter MeasureTheory
open scoped Topology BigOperators
open _root_.D5.S3.CharacterSums.DirichletCyclicLaplace
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.CharacterSums.DirichletCyclicContinuation

namespace Transform
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 0, fun y => Complex.exp ((-1 : ℂ) * y), ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℂ)) ≠ ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num : (-1 : ℂ).re < 0)]
  norm_num
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), r ≤ orderOf χ →
    ∀ {s : ℂ}, 1 < s.re →
    V.readout () () (fun u : ℝ => Complex.exp (-s * u) *
      (gl1CyclicFamily (r := r) χ (Real.exp u) : ℂ)) = continuation (r := r) χ s
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h (1 : DirichletCharacter ℂ 1) le_rfl (s := 2) (by norm_num)
  change (∫ u : ℝ in Ioi 0, Complex.exp (-(2 : ℂ) * u) *
    (gl1CyclicFamily (r := orderOf (1 : DirichletCharacter ℂ 1))
      (1 : DirichletCharacter ℂ 1) (Real.exp u) : ℂ)) + 1 = _ at bad
  rw [← continuation_half_plane_laplace (1 : DirichletCharacter ℂ 1)
    le_rfl (by norm_num : 1 < (2 : ℂ).re)] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @continuation_half_plane_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuation_half_plane_laplace, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuation_half_plane_laplace) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.continuation_half_plane_laplace
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.Transform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transform

namespace Poles
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), r ≤ orderOf χ →
    (∀ z : ℂ, 0 < z.re → z ∉ actualZeros (r := r) χ →
      AnalyticAt ℂ (continuation (r := r) χ) z) ∧
    (∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ actualZeros (r := r) χ) ∧
    (∀ z : ℂ, V.readout () () (actualZeros (r := r) χ) z →
      let c : ℝ := ∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z
      0 < c ∧ (-1 / (z * (z - 1))) * (c : ℂ) ≠ 0 ∧
        (∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
          continuation (r := r) χ =ᶠ[𝓝[≠] z]
            fun w => ((-1 / (z * (z - 1))) * (c : ℂ)) / (w - z) + R w) ∧
        meromorphicOrderAt (continuation (r := r) χ) z = -1)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := ((h (1 : DirichletCharacter ℂ 1) le_rfl).2.2 0 True.intro).2.1
  simpa using bad

def family : Registration arena (type_of% @continuation_actual_poles) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuation_actual_poles, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuation_actual_poles) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.continuation_actual_poles
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.Poles.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Poles

namespace Left
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), r ≤ orderOf χ →
    ∀ {z : ℂ}, V.readout () () (actualZeros (r := r) χ) z → z.re < 1
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h (1 : DirichletCharacter ℂ 1) le_rfl (z := 2) True.intro
  norm_num at bad

def family : Registration arena (type_of% @actualZeros_re_lt_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actualZeros_re_lt_one, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualZeros_re_lt_one) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.actualZeros_re_lt_one
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.Left.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Left

namespace RealResidue
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), r ≤ orderOf χ →
    ∀ {z : ℂ}, V.readout () () (actualZeros (r := r) χ) z → z.im = 0 →
    let c : ℝ := ∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z
    0 < (((-1 / (z * (z - 1))) * (c : ℂ))).re ∧
      (((-1 / (z * (z - 1))) * (c : ℂ))).im = 0
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := (h (1 : DirichletCharacter ℂ 1) le_rfl (z := 0) True.intro rfl).1
  simpa using bad

def family : Registration arena (type_of% @actual_real_residue_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_real_residue_pos, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_real_residue_pos) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.actual_real_residue_pos
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.RealResidue.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RealResidue

namespace ZetaMember
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ}, 0 < z.re → riemannZeta z = 0 →
    V.readout () () (actualZeros (r := r) χ) z
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hρ := zetaZeroData_isNontrivial 0
  exact @h 1 1 inferInstance 1 (zetaZeroData.zero 0) hρ.2.1 hρ.1

def family : Registration arena (type_of% @zeta_zero_mem_actualZeros) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zeta_zero_mem_actualZeros, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zeta_zero_mem_actualZeros) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.zeta_zero_mem_actualZeros
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.ZetaMember.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZetaMember

namespace CharacterMember
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) ∈ (∅ : Set ℂ)) = ((0 : ℂ) ∈ Set.univ) at he
  simpa using he
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ}, 0 < z.re → ∀ j : Fin (r - 1),
    (χ ^ (j.1 + 1)).LFunction z = 0 → V.readout () () (actualZeros (r := r) χ) z
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hρ := zetaZeroData_isNontrivial 0
  apply @h 1 2 inferInstance 1 (zetaZeroData.zero 0) hρ.2.1 0
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    (show riemannZeta (zetaZeroData.zero 0) = 0 from hρ.1)

def family : Registration arena (type_of% @member_zero_mem_actualZeros) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@member_zero_mem_actualZeros, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@member_zero_mem_actualZeros) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicContinuation.member_zero_mem_actualZeros
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicContinuation.CharacterMember.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z z => z ∈ Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicContinuation
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CharacterMember

end Reg.D5.S3.CharacterSums.DirichletCyclicContinuation
