import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Source-bound dependent-family audits of the literal finite approximants. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
open LeanInformationAudit

namespace Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants

private theorem block_dependence : e 1 (1 / 4) ≠ e 1 (3 / 4) := by
  norm_num [e, Set.indicator]

private theorem error_dependence :
    (1 - F 1 (1 / 4)) ^ 2 ≠ (1 - F 1 (3 / 4)) ^ 2 := by
  have hm : m 1 = 1 := by simp [m, muQ]
  have hs : S 1 = 1 := by simp [S, hm]
  have hf (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : F 1 u = 1 - e 1 u := by
    simp only [F, Finset.sum_range_one, zero_add]
    rw [h_step (by norm_num : 1 ≤ (1 : ℕ)) hu]
    norm_num [hm, hs]
  rw [hf (1 / 4) (by constructor <;> norm_num),
    hf (3 / 4) (by constructor <;> norm_num)]
  norm_num [e, Set.indicator]

namespace Floor

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n u => floorMoebiusSum n u) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {u : ℝ}, 0 < n → u ∈ Ioo 0 1 → R.readout () n u = indicatorThreshold n u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (u := 1 / 4) (by norm_num) (by norm_num)
  norm_num [rejected, realize, indicatorThreshold] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1 / 4, 3 / 4, ?_⟩
  change floorMoebiusSum 2 (1 / 4) ≠ floorMoebiusSum 2 (3 / 4)
  rw [floor_moebius_bridge (by norm_num) (by norm_num),
    floor_moebius_bridge (by norm_num) (by norm_num)]
  norm_num [indicatorThreshold]

def family : Registration arena (type_of% (@floor_moebius_bridge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@floor_moebius_bridge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@floor_moebius_bridge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.floor_moebius_bridge.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Floor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n u => floorMoebiusSum n u) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Floor

namespace Step

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n u => H (n + 1) u - H n u) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {u : ℝ}, 1 ≤ n → u ∈ Ioo 0 1 → R.readout () n u = (m n : ℝ) - e n u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (u := 1 / 4) (by norm_num) (by norm_num)
  norm_num [rejected, realize, m, muQ, e, Set.indicator] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1 / 4, 3 / 4, ?_⟩
  change H 2 (1 / 4) - H 1 (1 / 4) ≠ H 2 (3 / 4) - H 1 (3 / 4)
  rw [h_step (by norm_num) (by norm_num), h_step (by norm_num) (by norm_num)]
  norm_num [m, muQ, e, Set.indicator]

def family : Registration arena (type_of% (@h_step)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@h_step, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@h_step) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.h_step.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Step.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n u => H (n + 1) u - H n u) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Step

namespace Block

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n u => (e n u) ^ 2) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 1 ≤ n → (∫ u in Ioo (0 : ℝ) 1, R.readout () n u) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1 / 4, 3 / 4, ?_⟩
  norm_num [actual, realize, e, Set.indicator]

def family : Registration arena (type_of% (@block_integral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@block_integral, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@block_integral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.block_integral.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Block.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n u => (e n u) ^ 2) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Block

namespace Orthogonality

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p u => e p.1 u) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ p u => e p.2 u) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → m ≠ n → (∫ u in Ioo (0 : ℝ) 1, R.readout () ⟨m,n⟩ u * e n u) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (m := 1) (n := 2) (by norm_num) (by norm_num) (by norm_num)
  change (∫ u in Ioo (0 : ℝ) 1, e 2 u * e 2 u) = 0 at hh
  simp_rw [← pow_two] at hh
  rw [block_integral (by norm_num : 1 ≤ (2 : ℕ))] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,2⟩, 1 / 4, 3 / 4, ?_⟩
  exact block_dependence

def family : Registration arena (type_of% (@block_orthogonality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@block_orthogonality, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@block_orthogonality) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.block_orthogonality.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Orthogonality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => e p.1 u) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Orthogonality

namespace Energy

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => (S N : ℝ)) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 1 ≤ N → 0 < R.readout () () N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (N := 1) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, S, m, muQ, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

def family : Registration arena (type_of% (@s_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@s_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@s_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.s_pos.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => (S N : ℝ)) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Energy

namespace Integrability

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ N u => (1 - F N u) ^ 2) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ u => u ^ (-1 : ℝ)) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 1 ≤ N → IntegrableOn (fun u : ℝ => R.readout () N u) (Ioo (0 : ℝ) 1) volume

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (N := 1) (by norm_num)
  change IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) volume at hh
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1 / 4, 3 / 4, ?_⟩
  exact error_dependence

def family : Registration arena (type_of% (@error_sq_integrable)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@error_sq_integrable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@error_sq_integrable) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.error_sq_integrable.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Integrability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N u => (1 - F N u) ^ 2) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Integrability

namespace Error

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ N u => (1 - F N u) ^ 2) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun z => nomatch z)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, 1 ≤ N → (∫ u in Ioo (0 : ℝ) 1, R.readout () N u) = (1 : ℝ) / (S N : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (N := 1) (by norm_num)
  norm_num [rejected, realize, S, m, muQ] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1 / 4, 3 / 4, ?_⟩
  exact error_dependence

def family : Registration arena (type_of% (@finite_error)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_error, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_error) (Realization signature) Unit Unit where
  unitName := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.finite_error.audit
  realizationName := `Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants.Error.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N u => (1 - F N u) ^ 2) (fun z => nomatch z))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Error

end Reg.D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
