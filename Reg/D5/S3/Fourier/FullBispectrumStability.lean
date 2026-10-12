import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.FullBispectrumStability
import Reg.Support.DependentFamily
import Mathlib.Tactic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.FullBispectrumStability
open LeanInformationAudit Finset
open scoped BigOperators ComplexConjugate

noncomputable section
namespace Reg.D5.S3.Fourier.FullBispectrumStability

abbrev Parameters := Σ N : ℕ, ZMod N → ℂ

abbrev signature : Signature where
  Params := Parameters
  State p := ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The observed signal value at the original summation variable. -/
def actual : Realization signature :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (m ε : ℝ),
    0 < m → 0 ≤ ε → ε ≤ m ^ 3 / 4 →
    ZMod.dft f 0 = ZMod.dft g 0 →
    (∀ k, m ≤ ‖ZMod.dft f k‖) →
    (∀ k l, ‖ZMod.dft g k * ZMod.dft g l * conj (ZMod.dft g (k + l)) -
      ZMod.dft f k * ZMod.dft f l * conj (ZMod.dft f (k + l))‖ ≤ ε) →
    ∃ t : ZMod N,
      (∑ x, ‖R.readout () ⟨N, g⟩ x - f (x - t)‖ ^ 2) ≤ (2 * ε / m ^ 2) ^ 2 ∧
      (∀ k, ‖ZMod.dft g k - ZMod.stdAddChar (-(k * t)) * ZMod.dft f k‖ ≤
        2 * ε / m ^ 2) ∧
      (∀ s : ZMod N, (∑ x, ‖g x - f (x - s)‖ ^ 2) ≤
        (2 * ε / m ^ 2) ^ 2 → s = t)

/-- Deleting the signal readout fails on the calibrated order-one signal. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ZMod 1 → ℂ := fun _ => 1
  have hf (k : ZMod 1) : ZMod.dft f k = 1 := by
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [ZMod.dft_apply_zero]
    simp [f]
  obtain ⟨t, ht, _⟩ := h f f 1 0 (by norm_num) (by norm_num) (by norm_num)
    rfl (by intro k; rw [hf]; norm_num) (by intro k l; simp)
  norm_num [rejected, realize, f, ZMod.card] at ht

/-- A fixed nonconstant signal gives different observations at two states. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  let g : ZMod 2 → ℂ := fun x => if x = 0 then 1 else 0
  refine ⟨⟨2, g⟩, 0, 1, ?_⟩
  norm_num [actual, realize, g]

def registration : Registration arena (type_of% (@full_bispectrum_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_bispectrum_stability, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@full_bispectrum_stability)
      (type_of% (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Fourier.FullBispectrumStability.full_bispectrum_stability.information_unit,
  realizationName := `Reg.D5.S3.Fourier.FullBispectrumStability.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.FullBispectrumStability,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn",
        "arg", "arg", "body", "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 13,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration


namespace cyclic_parsevalAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (f : ZMod N → ℂ),
    R.readout () () (∑ x, ‖f x‖ ^ 2) (𝔼 k, ‖ZMod.dft f k‖ ^ 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ : ZMod 1 => 0)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congr_fun h 0
  have hf : (1 : ℝ) = 0 := Eq.mp he rfl
  norm_num at hf

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Fourier.FullBispectrumStability.cyclic_parseval)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.FullBispectrumStability.cyclic_parseval,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Fourier.FullBispectrumStability.cyclic_parseval)
    (type_of% (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.FullBispectrumStability.cyclic_parseval.information_unit,
  realizationName := `Reg.D5.S3.Fourier.FullBispectrumStability.cyclic_parsevalAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.FullBispectrumStability,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end cyclic_parsevalAudit

namespace dft_translationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (t k : ZMod N),
    R.readout () () (ZMod.dft (fun x => f (x - t)) k)
      (ZMod.stdAddChar (-(k * t)) * ZMod.dft f k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (fun _ : ZMod 1 => 0) 0 0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congr_fun h 0
  have hf : (1 : ℂ) = 0 := Eq.mp he rfl
  norm_num at hf

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Fourier.FullBispectrumStability.dft_translation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.FullBispectrumStability.dft_translation,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Fourier.FullBispectrumStability.dft_translation)
    (type_of% (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.FullBispectrumStability.dft_translation.information_unit,
  realizationName := `Reg.D5.S3.Fourier.FullBispectrumStability.dft_translationAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.FullBispectrumStability,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end dft_translationAudit

namespace unit_mul_conjAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (z : ℂ), ‖z‖ = 1 → R.readout () () (z * conj z) 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by norm_num)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congr_fun h 0
  have hf : (1 : ℂ) = 0 := Eq.mp he rfl
  norm_num at hf

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Fourier.FullBispectrumStability.unit_mul_conj)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.FullBispectrumStability.unit_mul_conj,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Fourier.FullBispectrumStability.unit_mul_conj)
    (type_of% (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.FullBispectrumStability.unit_mul_conj.information_unit,
  realizationName := `Reg.D5.S3.Fourier.FullBispectrumStability.unit_mul_conjAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.FullBispectrumStability,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end unit_mul_conjAudit

end Reg.D5.S3.Fourier.FullBispectrumStability
