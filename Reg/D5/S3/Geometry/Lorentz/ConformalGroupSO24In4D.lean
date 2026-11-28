import Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Inversion
import Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Twistor

/-! Source registrations for the generators of the conformal algebra. -/

open _root_.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.OmegaMath.OrthogonalMatrixGenerators (generator)
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open Matrix
open scoped Matrix

namespace Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private theorem generator_changes : L 0 0 ≠ L 0 1 := by
  intro h
  have he := congrArg (fun X : RMat6 => X 0 1) h
  norm_num [L, generator, metricSign24, Matrix.single_apply] at he

namespace Antisymmetry

abbrev sig : Signature := signature (Fin 6) (fun _ => Fin 6) (fun _ => RMat6)

def actual : Realization sig :=
  realize sig (fun _ a b => L a b) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ a b : Fin 6,
    (L a b)ᵀ * eta24 + eta24 * R.readout () a b = 0

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := congrArg (fun X : RMat6 => X 0 0) (h 0 0)
  change (((L 0 0)ᵀ * eta24 + eta24 * 1) : RMat6) 0 0 = 0 at h0
  norm_num [L, generator, eta24, metricSign24, OmegaMath.OrthogonalMatrixGenerators.metric] at h0

def family : Registration arena (type_of% @so24_antisym_metric) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨so24_antisym_metric, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    exact ⟨0, 0, 1, generator_changes⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so24_antisym_metric) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.so24_antisym_metric.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Antisymmetry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ a b => L a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Antisymmetry

namespace Bracket

abbrev sig : Signature := signature (Fin 6) (fun _ => Fin 6) (fun _ => RMat6)

def actual : Realization sig :=
  realize sig (fun _ a b => L a b) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ a b c d : Fin 6,
    R.readout () a b * L c d - L c d * L a b =
      eta24 b c • L a d - eta24 a c • L b d -
        eta24 b d • L a c + eta24 a d • L b c

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := h 0 0 0 1
  change (1 : RMat6) * L 0 1 - L 0 1 * L 0 0 =
    eta24 0 0 • L 0 1 - eta24 0 0 • L 0 1 -
      eta24 0 1 • L 0 0 + eta24 0 1 • L 0 0 at h0
  have hz : L 0 0 = 0 := by simp [L, generator]
  simp only [hz, one_mul, mul_zero, sub_zero, sub_self, smul_zero, zero_add] at h0
  exact generator_changes (hz.trans h0.symm)

def family : Registration arena (type_of% @so24_commutator_universal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨so24_commutator_universal, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    exact ⟨0, 0, 1, generator_changes⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so24_commutator_universal) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.so24_commutator_universal.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Bracket.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ a b => L a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path :=
        #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bracket

namespace Expansion

abbrev sig : Signature := signature (Unit) (fun _ => RMat6) (fun _ => RMat6)

def actual : Realization sig :=
  realize sig (fun _ _ X => X) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ X : RMat6, X ∈ so24Subspace →
    (∑ p : ConformalPair, (X p.val.1 p.val.2 * metricSign24 p.val.2) • so24Basis p) =
      R.readout () () X

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := h 0 so24Subspace.zero_mem
  change (∑ p : ConformalPair, (0 * metricSign24 p.val.2) • so24Basis p) = 1 at h0
  simp at h0

def family : Registration arena (type_of% @so24_expansion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨so24_expansion, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 0, 1, zero_ne_one⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so24_expansion) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.so24_expansion.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Expansion

namespace Independence

abbrev sig : Signature := signature (Unit) (fun _ => ConformalPair) (fun _ => RMat6)

def actual : Realization sig :=
  realize sig (fun _ _ p => so24Basis p) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := LinearIndependent ℝ (R.readout () ())

private theorem rejected : ¬ arena.Law erased := by
  intro h
  let p : ConformalPair := ⟨(0, 1), by decide⟩
  have hn := h.ne_zero p
  change (0 : RMat6) ≠ 0 at hn
  exact hn rfl

def family : Registration arena (type_of% @so24_basis15_linearIndependent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨so24_basis15_linearIndependent, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    let p : ConformalPair := ⟨(0, 1), by decide⟩
    let q : ConformalPair := ⟨(0, 2), by decide⟩
    refine ⟨(), p, q, ?_⟩
    intro h
    have he := congrArg (fun X : RMat6 => X 0 1) h
    change L 0 1 0 1 = L 0 2 0 1 at he
    norm_num [L, generator, metricSign24, Matrix.single_apply] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so24_basis15_linearIndependent) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.so24_basis15_linearIndependent.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Independence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ p => so24Basis p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Independence

namespace Dimension

abbrev sig : Signature := signature (Unit) (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ a b => a = b) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := R.readout () () (Module.finrank ℝ so24Subspace) 15

private theorem rejected : ¬ arena.Law erased := by
  exact id

def family : Registration arena (type_of% @so24_subspace_finrank_15) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨so24_subspace_finrank_15, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so24_subspace_finrank_15) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.so24_subspace_finrank_15.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Dimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dimension

namespace Dilatation

abbrev sig : Signature := signature (Unit) (fun _ => Fin 4) (fun _ => RMat6)

def actual : Realization sig :=
  realize sig (fun _ _ μ => translationGen μ) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ μ ν ρ : Fin 4,
    bracket (translationGen μ) (translationGen ν) = 0 ∧
    bracket (specialGen μ) (specialGen ν) = 0 ∧
    bracket dilatation (LorentzGen μ ν) = 0 ∧
    bracket dilatation (translationGen μ) = R.readout () () μ ∧
    bracket dilatation (specialGen μ) = -specialGen μ ∧
    bracket (specialGen μ) (translationGen ν) = (2 : ℝ) •
      (LorentzGen μ ν - eta24 μ.castSucc.castSucc ν.castSucc.castSucc • dilatation) ∧
    bracket (LorentzGen μ ν) (translationGen ρ) =
      eta24 ν.castSucc.castSucc ρ.castSucc.castSucc • translationGen μ -
      eta24 μ.castSucc.castSucc ρ.castSucc.castSucc • translationGen ν ∧
    bracket (LorentzGen μ ν) (specialGen ρ) =
      eta24 ν.castSucc.castSucc ρ.castSucc.castSucc • specialGen μ -
      eta24 μ.castSucc.castSucc ρ.castSucc.castSucc • specialGen ν

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := (h 0 0 0).2.2.2.1
  rw [(conformal_algebra_commutators 0 0 0).2.2.2.1] at h0
  have he := congrArg (fun X : RMat6 => X 0 5) h0
  change translationGen 0 0 5 = 0 at he
  norm_num [translationGen, L, generator, metricSign24, Matrix.single_apply] at he

def family : Registration arena (type_of% @conformal_algebra_commutators) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conformal_algebra_commutators, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrArg (fun X : RMat6 => X 0 5) h
    change translationGen 0 0 5 = translationGen 1 0 5 at he
    norm_num [translationGen, L, generator, metricSign24, Matrix.single_apply] at he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conformal_algebra_commutators) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.conformal_algebra_commutators.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.Dilatation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ μ => translationGen μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dilatation

end

end Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
