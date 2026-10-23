import D5.S1.Recurrence.OEISA400644
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.OEISA400644
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.OEISA400644
noncomputable section

private abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev natActual (f : ℕ → ℕ) : Realization natSignature :=
  realize natSignature (fun _ _ n => f n) (fun e => nomatch e)

private abbrev natArena (law : (ℕ → ℕ) → Prop) : Arena where
  signature := natSignature
  Law r := law (r.readout () ())

private def natEvidence (f bad : ℕ → ℕ) (law : (ℕ → ℕ) → Prop)
    (good : law f) (rejected : ¬ law bad) (dependence : ∃ x y, f x ≠ f y) :
    Registration (natArena law) (law f) where
  actual := natActual f
  bridge := Iff.rfl
  variation := ⟨good,natActual bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natActual bad,?_,rfl,rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨x,y,h⟩ := dependence
    exact ⟨(),x,y,h⟩

private theorem a_dependence : ∃ x y, a x ≠ a y := ⟨0,2,by simp [a]⟩
private theorem round_dependence : ∃ x y, sourceRound x ≠ sourceRound y :=
  ⟨0,1,by norm_num [sourceRound]⟩
private theorem sqrt_dependence : ∃ x y, Nat.sqrt x ≠ Nat.sqrt y := ⟨0,1,by norm_num⟩

private def sqrt_bracket_law (f : ℕ → ℕ) : Prop := ∀ s, f s*f s ≤ s ∧ s < (f s+1)*(f s+1)
private theorem sqrt_bracket_bad : ¬ sqrt_bracket_law (fun _ => 0) := by
  intro h
  have hh := (h 1).2
  norm_num at hh

def sqrt_bracket_evidence : Registration (natArena sqrt_bracket_law) (sqrt_bracket_law Nat.sqrt) :=
  natEvidence Nat.sqrt (fun _ => 0) sqrt_bracket_law sqrt_bracket sqrt_bracket_bad sqrt_dependence

noncomputable def sqrt_bracket_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.sqrt_bracket)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.sqrt_bracket_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.sqrt_bracket_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena sqrt_bracket_law⟩
  objectArena := .source ⟨natArena sqrt_bracket_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena sqrt_bracket_law) ⟨sqrt_bracket_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => Nat.sqrt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def sourceRound_spec_law (f : ℕ → ℕ) : Prop := ∀ s, let r := Nat.sqrt s; r*r ≤ s ∧ s < (r+1)*(r+1) ∧ (f s=r ∨ f s=r+1)
private theorem sourceRound_spec_bad : ¬ sourceRound_spec_law (fun _ => 2) := by
  intro h
  have hh := h 0
  norm_num at hh

def sourceRound_spec_evidence : Registration (natArena sourceRound_spec_law) (sourceRound_spec_law sourceRound) :=
  natEvidence sourceRound (fun _ => 2) sourceRound_spec_law sourceRound_spec sourceRound_spec_bad round_dependence

noncomputable def sourceRound_spec_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.sourceRound_spec)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_spec_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_spec_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena sourceRound_spec_law⟩
  objectArena := .source ⟨natArena sourceRound_spec_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena sourceRound_spec_law) ⟨sourceRound_spec_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => sourceRound n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def sourceRound_ge_sqrt_law (f : ℕ → ℕ) : Prop := ∀ s, Nat.sqrt s ≤ f s
private theorem sourceRound_ge_sqrt_bad : ¬ sourceRound_ge_sqrt_law (fun _ => 0) := by
  intro h
  have hh := h 1
  norm_num at hh

def sourceRound_ge_sqrt_evidence : Registration (natArena sourceRound_ge_sqrt_law) (sourceRound_ge_sqrt_law sourceRound) :=
  natEvidence sourceRound (fun _ => 0) sourceRound_ge_sqrt_law sourceRound_ge_sqrt sourceRound_ge_sqrt_bad round_dependence

noncomputable def sourceRound_ge_sqrt_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.sourceRound_ge_sqrt)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_ge_sqrt_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_ge_sqrt_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena sourceRound_ge_sqrt_law⟩
  objectArena := .source ⟨natArena sourceRound_ge_sqrt_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena sourceRound_ge_sqrt_law) ⟨sourceRound_ge_sqrt_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => sourceRound n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def sourceRound_real_error_law (f : ℕ → ℕ) : Prop := ∀ s : ℕ, |Real.sqrt (s : ℝ)-(f s : ℝ)| < (1 : ℝ)/2
private theorem sourceRound_real_error_bad : ¬ sourceRound_real_error_law (fun _ => 0) := by
  intro h
  have hh := h 1
  norm_num at hh

def sourceRound_real_error_evidence : Registration (natArena sourceRound_real_error_law) (sourceRound_real_error_law sourceRound) :=
  natEvidence sourceRound (fun _ => 0) sourceRound_real_error_law sourceRound_real_error sourceRound_real_error_bad round_dependence

noncomputable def sourceRound_real_error_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.sourceRound_real_error)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_real_error_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.sourceRound_real_error_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena sourceRound_real_error_law⟩
  objectArena := .source ⟨natArena sourceRound_real_error_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena sourceRound_real_error_law) ⟨sourceRound_real_error_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => sourceRound n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_recurrence_law (f : ℕ → ℕ) : Prop := ∀ n, f (n+3)=sourceRound (f (n+2)^2+f (n+1)^2+f n^2)
private theorem a_recurrence_bad : ¬ a_recurrence_law (fun _ => 1) := by
  intro h
  have hh := h 0
  norm_num [sourceRound] at hh

def a_recurrence_evidence : Registration (natArena a_recurrence_law) (a_recurrence_law a) :=
  natEvidence a (fun _ => 1) a_recurrence_law a_recurrence a_recurrence_bad a_dependence

noncomputable def a_recurrence_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_recurrence)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_recurrence_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_recurrence_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_recurrence_law⟩
  objectArena := .source ⟨natArena a_recurrence_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_recurrence_law) ⟨a_recurrence_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_mono_law (f : ℕ → ℕ) : Prop := ∀ n, f n ≤ f (n+1)
private theorem a_mono_bad : ¬ a_mono_law (fun n => if n=0 then 1 else 0) := by
  intro h
  have hh := h 0
  norm_num at hh

def a_mono_evidence : Registration (natArena a_mono_law) (a_mono_law a) :=
  natEvidence a (fun n => if n=0 then 1 else 0) a_mono_law a_mono a_mono_bad a_dependence

noncomputable def a_mono_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_mono)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_mono_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_mono_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_mono_law⟩
  objectArena := .source ⟨natArena a_mono_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_mono_law) ⟨a_mono_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_pos_law (f : ℕ → ℕ) : Prop := ∀ n, 1 ≤ f (n+2)
private theorem a_pos_bad : ¬ a_pos_law (fun _ => 0) := by
  intro h
  have hh := h 0
  norm_num at hh

def a_pos_evidence : Registration (natArena a_pos_law) (a_pos_law a) :=
  natEvidence a (fun _ => 0) a_pos_law a_pos a_pos_bad a_dependence

noncomputable def a_pos_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_pos)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_pos_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_pos_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_pos_law⟩
  objectArena := .source ⟨natArena a_pos_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_pos_law) ⟨a_pos_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_unique_law (f : ℕ → ℕ) : Prop := ∀ {b : ℕ → ℕ}, b 0=0 → b 1=0 → b 2=1 → (∀ n, b (n+3)=sourceRound (b (n+2)^2+b (n+1)^2+b n^2)) → ∀ n, b n=f n
private theorem a_unique_bad : ¬ a_unique_law (fun _ => 0) := by
  intro h
  have hh := h a_zero a_one a_two a_recurrence 2
  norm_num [a] at hh

def a_unique_evidence : Registration (natArena a_unique_law) (a_unique_law a) :=
  natEvidence a (fun _ => 0) a_unique_law a_unique a_unique_bad a_dependence

noncomputable def a_unique_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_unique)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_unique_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_unique_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_unique_law⟩
  objectArena := .source ⟨natArena a_unique_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_unique_law) ⟨a_unique_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_zero_law (f : ℕ → ℕ) : Prop := f 0=0
private theorem a_zero_bad : ¬ a_zero_law (fun _ => 1) := by
  intro h
  have hh := h
  norm_num [a_zero_law] at hh

def a_zero_evidence : Registration (natArena a_zero_law) (a_zero_law a) :=
  natEvidence a (fun _ => 1) a_zero_law a_zero a_zero_bad a_dependence

noncomputable def a_zero_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_zero)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_zero_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_zero_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_zero_law⟩
  objectArena := .source ⟨natArena a_zero_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_zero_law) ⟨a_zero_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_one_law (f : ℕ → ℕ) : Prop := f 1=0
private theorem a_one_bad : ¬ a_one_law (fun _ => 1) := by
  intro h
  have hh := h
  norm_num [a_one_law] at hh

def a_one_evidence : Registration (natArena a_one_law) (a_one_law a) :=
  natEvidence a (fun _ => 1) a_one_law a_one a_one_bad a_dependence

noncomputable def a_one_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_one)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_one_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_one_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_one_law⟩
  objectArena := .source ⟨natArena a_one_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_one_law) ⟨a_one_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def a_two_law (f : ℕ → ℕ) : Prop := f 2=1
private theorem a_two_bad : ¬ a_two_law (fun _ => 0) := by
  intro h
  have hh := h
  norm_num [a_two_law] at hh

def a_two_evidence : Registration (natArena a_two_law) (a_two_law a) :=
  natEvidence a (fun _ => 0) a_two_law a_two a_two_bad a_dependence

noncomputable def a_two_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.a_two)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.a_two_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.a_two_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena a_two_law⟩
  objectArena := .source ⟨natArena a_two_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena a_two_law) ⟨a_two_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev realSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev realActual (f : ℝ → ℝ) : Realization realSignature :=
  realize realSignature (fun _ _ x => f x) (fun e => nomatch e)

private abbrev realArena (law : (ℝ → ℝ) → Prop) : Arena where
  signature := realSignature
  Law r := law (r.readout () ())

private def realEvidence (law : (ℝ → ℝ) → Prop)
    (good : law id) (rejected : ¬ law (fun _ => 0)) :
    Registration (realArena law) (law id) where
  actual := realActual id
  bridge := Iff.rfl
  variation := ⟨good,realActual (fun _ => 0),rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨realActual (fun _ => 0),?_,rfl,rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(),0,1,by norm_num [realActual,realize]⟩

private def rho_pos_law (f : ℝ → ℝ) : Prop := 0 < f rho
private theorem rho_pos_bad : ¬ rho_pos_law (fun _ => 0) := by
  norm_num [rho_pos_law]

def rho_pos_evidence : Registration (realArena rho_pos_law) (rho_pos_law id) :=
  realEvidence rho_pos_law rho_pos rho_pos_bad

noncomputable def rho_pos_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.rho_pos)
    (Realization realSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.rho_pos_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.rho_pos_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨realArena rho_pos_law⟩
  objectArena := .source ⟨realArena rho_pos_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (realArena rho_pos_law) ⟨rho_pos_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def rho_sextic_law (f : ℝ → ℝ) : Prop := (f rho)^6-(f rho)^4-(f rho)^2-1=0
private theorem rho_sextic_bad : ¬ rho_sextic_law (fun _ => 0) := by
  norm_num [rho_sextic_law]

def rho_sextic_evidence : Registration (realArena rho_sextic_law) (rho_sextic_law id) :=
  realEvidence rho_sextic_law rho_sextic rho_sextic_bad

noncomputable def rho_sextic_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.rho_sextic)
    (Realization realSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.rho_sextic_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.rho_sextic_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨realArena rho_sextic_law⟩
  objectArena := .source ⟨realArena rho_sextic_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (realArena rho_sextic_law) ⟨rho_sextic_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def positive_sextic_root_eq_rho_law (f : ℝ → ℝ) : Prop := ∀ {x : ℝ}, 0<x → x^6-x^4-x^2-1=0 → f x=rho
private theorem positive_sextic_root_eq_rho_bad : ¬ positive_sextic_root_eq_rho_law (fun _ => 0) := by
  intro h
  have hh := h rho_pos rho_sextic
  have hp := rho_pos
  change 0=rho at hh
  linarith

def positive_sextic_root_eq_rho_evidence : Registration (realArena positive_sextic_root_eq_rho_law) (positive_sextic_root_eq_rho_law id) :=
  realEvidence positive_sextic_root_eq_rho_law @positive_sextic_root_eq_rho positive_sextic_root_eq_rho_bad

noncomputable def positive_sextic_root_eq_rho_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.positive_sextic_root_eq_rho)
    (Realization realSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.positive_sextic_root_eq_rho_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.positive_sextic_root_eq_rho_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨realArena positive_sextic_root_eq_rho_law⟩
  objectArena := .source ⟨realArena positive_sextic_root_eq_rho_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (realArena positive_sextic_root_eq_rho_law) ⟨positive_sextic_root_eq_rho_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def rho_is_largest_positive_root_law (f : ℝ → ℝ) : Prop := 0<f rho ∧ (f rho)^6-(f rho)^4-(f rho)^2-1=0 ∧ ∀ x : ℝ, 0<x → x^6-x^4-x^2-1=0 → x≤f rho
private theorem rho_is_largest_positive_root_bad : ¬ rho_is_largest_positive_root_law (fun _ => 0) := by
  intro h
  have hh := h.1
  change (0 : ℝ)<0 at hh
  exact (lt_irrefl 0) hh

def rho_is_largest_positive_root_evidence : Registration (realArena rho_is_largest_positive_root_law) (rho_is_largest_positive_root_law id) :=
  realEvidence rho_is_largest_positive_root_law rho_is_largest_positive_root rho_is_largest_positive_root_bad

noncomputable def rho_is_largest_positive_root_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.rho_is_largest_positive_root)
    (Realization realSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.rho_is_largest_positive_root_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.rho_is_largest_positive_root_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨realArena rho_is_largest_positive_root_law⟩
  objectArena := .source ⟨realArena rho_is_largest_positive_root_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (realArena rho_is_largest_positive_root_law) ⟨rho_is_largest_positive_root_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

private def result_law (f : ℕ → ℕ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧
    (∀ x : ℝ, 0 < x → x^6-x^4-x^2-1 = 0 → x ≤ ρ) ∧
    Filter.Tendsto (fun n : ℕ => (f (n+3) : ℝ) / f (n+2)) Filter.atTop (nhds ρ) ∧
    ρ^6-ρ^4-ρ^2-1 = 0 ∧ sourceSpec sourceA ∧
    (∀ n : ℕ, 3 ≤ n → 0 < sourceA n) ∧
    (∀ g : ℕ → ℕ, sourceSpec g →
      (∀ n : ℕ, 1 ≤ n → g n = sourceA n) ∧
      Filter.Tendsto (fun n : ℕ => (g (n+4) : ℝ) / g (n+3)) Filter.atTop (nhds ρ))

private theorem result_bad : ¬ result_law (fun _ => 0) := by
  rintro ⟨r,hpos,hroot,hlim,hrest⟩
  have hl : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds r) := by
    simpa using hlim
  have hz : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have heq := tendsto_nhds_unique hz hl
  linarith

def result_evidence : Registration (natArena result_law) (result_law a) :=
  natEvidence a (fun _ => 0) result_law result result_bad a_dependence

noncomputable def result_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.OEISA400644.result)
    (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.OEISA400644.result_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400644.result_evidence
  realizationSource := none
  generated := false
  arena := .source ⟨natArena result_law⟩
  objectArena := .source ⟨natArena result_law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (natArena result_law) ⟨result_evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.OEISA400644
