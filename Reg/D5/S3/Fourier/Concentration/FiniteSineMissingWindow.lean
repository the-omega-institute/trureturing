import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.Concentration.FiniteSineMissingWindow

/-! The selected observations are the signed grid score and the sine score in each window law. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
open LeanInformationAudit Finset Set
open scoped NNReal

noncomputable section

universe u v p s

abbrev oneRole (P : Type p) (State : P → Type s) : Signature where
  Params := P
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

theorem sensitivity {P : Type p} {State : P → Type s}
    (law : Realization (oneRole P State) → Prop)
    (actual rejected : Realization (oneRole P State)) (h : ¬ law rejected) :
    Sensitivity ⟨oneRole P State, law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, h⟩
    · intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

abbrev gridSignature : Signature :=
  oneRole (Σ J : Type u, Σ _ : Finset J, J → Bool) (fun q => q.1 → ℝ)

def gridActual : Realization gridSignature.{u} :=
  realize gridSignature (fun _ q c => signedScore q.2.1 c q.2.2) (fun e => nomatch e)

def gridRejected : Realization gridSignature.{u} :=
  realize gridSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev gridArena : Arena where
  signature := gridSignature.{u}
  Law readout := ∀ {J : Type u} {K : Type v} [Finite J] [Fintype K]
    (s : Finset J) (w : J → ℝ≥0) (c : K → J → ℝ)
    (_ : ∀ k j, j ∈ s → |c k j| ≤ w j) {δ : ℝ} (_ : 0 < δ),
    ((∑ j ∈ s, (w j : ℝ) ^ 2) = 0 ∨
      (Fintype.card K : ℝ) * Real.exp (-δ ^ 2 / (2 * ∑ j ∈ s, (w j : ℝ) ^ 2)) < 1) →
    ∃ b : J → Bool, ∀ k, readout.readout () ⟨J, s, b⟩ (c k) < δ

private theorem grid_rejected : ¬ gridArena.{u,v}.Law gridRejected := by
  intro law
  obtain ⟨b, hb⟩ := law (K := ULift.{v} Unit) (∅ : Finset (ULift.{u} Unit))
    0 (fun _ => 0) (by simp) (δ := 1) zero_lt_one (Or.inl (by simp))
  simpa [gridRejected, realize] using hb ⟨()⟩

private theorem grid_dependence : ObservationalDependence gridSignature.{u} gridActual := by
  intro i
  let j : ULift.{u} Unit := ⟨()⟩
  refine ⟨⟨ULift.{u} Unit, {j}, fun _ => true⟩, fun _ => 0, fun _ => 1, ?_⟩
  simp [gridActual, realize, signedScore]

def gridEvidence : Registration gridArena.{u,v} (type_of% @exists_signs_on_grid.{u,v}) where
  actual := gridActual
  bridge := Iff.rfl
  variation := ⟨@exists_signs_on_grid.{u,v}, gridRejected, grid_rejected⟩
  sensitivity := sensitivity gridArena.Law gridActual gridRejected grid_rejected
  dependence := grid_dependence

def gridRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_signs_on_grid.{u,v}) (Realization gridSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.gridUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.gridEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gridArena.{u,v}⟩
  objectArena := .source ⟨gridArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gridArena.{u,v} ⟨gridEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gridSignature (fun _ q c => signedScore q.2.1 c q.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteSineMissingWindow
    definition := none
    coordinates := #[0, 4, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg"]
      functionOperand := false
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev windowSignature : Signature :=
  oneRole (Σ J : Type u, Σ _ : Fintype J, Σ _ : J → ℝ, Σ _ : J → ℝ≥0, J → ℝ)
    (fun _ => ℝ)

def windowActual : Realization windowSignature.{u} :=
  realize windowSignature
    (fun _ q t => @sineScore q.1 q.2.1 q.2.2.1 q.2.2.2.2 q.2.2.2.1 t)
    (fun e => nomatch e)

def windowRejected : Realization windowSignature.{u} :=
  realize windowSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev windowArena : Arena where
  signature := windowSignature.{u}
  Law readout := ∀ {J : Type u} [i : Fintype J] [DecidableEq J]
    (head : Finset J) (f θ : J → ℝ) (w : J → ℝ≥0) {R h δ : ℝ}
    (_ : 0 < h) (_ : 0 < δ),
    ((∑ j ∈ headᶜ, (w j : ℝ) ^ 2) = 0 ∨
      ((⌊R / h⌋₊ : ℝ) + 1) *
        Real.exp (-δ ^ 2 / (2 * ∑ j ∈ headᶜ, (w j : ℝ) ^ 2)) < 1) →
    ∃ φ : J → ℝ, (∀ j ∈ head, φ j = θ j) ∧ (∀ j ∈ headᶜ, φ j = 0 ∨ φ j = Real.pi) ∧
      ∀ t ∈ Icc (0 : ℝ) R, readout.readout () ⟨J, i, f, w, φ⟩ t <
        (∑ j ∈ head, (w j : ℝ)) + δ + h * ∑ j ∈ headᶜ, (w j : ℝ) * |f j|

private theorem window_rejected : ¬ windowArena.{u}.Law windowRejected := by
  intro law
  obtain ⟨φ, _, _, hs⟩ := law (∅ : Finset (ULift.{u} Unit)) 0 0 0
    (R := 1) (h := 1) (δ := 1) zero_lt_one zero_lt_one (Or.inl (by simp))
  have h := hs 0 (by simp)
  simp [windowRejected, realize] at h

private theorem window_dependence :
    ObservationalDependence windowSignature.{u} windowActual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1, 1, 0⟩, 0, Real.pi / 2, ?_⟩
  simp [windowActual, realize, sineScore, Real.sin_pi_div_two]

def windowEvidence :
    Registration windowArena.{u} (type_of% @exists_phases_on_closed_window.{u}) where
  actual := windowActual
  bridge := Iff.rfl
  variation := ⟨@exists_phases_on_closed_window.{u}, windowRejected, window_rejected⟩
  sensitivity := sensitivity windowArena.Law windowActual windowRejected window_rejected
  dependence := window_dependence

def windowRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_phases_on_closed_window.{u}) (Realization windowSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.windowUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.windowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena.{u}⟩
  objectArena := .source ⟨windowArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena.{u} ⟨windowEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize windowSignature
    (fun _ q t => @sineScore q.1 q.2.1 q.2.2.1 q.2.2.2.2 q.2.2.2.1 t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteSineMissingWindow
    definition := none
    coordinates := #[0, 4, 6, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev orbitSignature : Signature :=
  oneRole (Σ J : Type u, Σ _ : Fintype J, Σ _ : J → ℝ, J → ℝ≥0) (fun _ => ℝ)

def orbitActual : Realization orbitSignature.{u} :=
  realize orbitSignature (fun _ q t => @sineScore q.1 q.2.1 q.2.2.1 0 q.2.2.2 t)
    (fun e => nomatch e)

def orbitRejected : Realization orbitSignature.{u} :=
  realize orbitSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev orbitArena : Arena where
  signature := orbitSignature.{u}
  Law readout := ∀ {J : Type u} [i : Fintype J] [DecidableEq J]
    (head : Finset J) (f : J → ℝ) (w : J → ℝ≥0) (_ : LinearIndependent ℚ f)
    {R h δ B : ℝ} (_ : 0 < h) (_ : 0 < δ),
    ((∑ j ∈ headᶜ, (w j : ℝ) ^ 2) = 0 ∨
      ((⌊R / h⌋₊ : ℝ) + 1) *
        Real.exp (-δ ^ 2 / (2 * ∑ j ∈ headᶜ, (w j : ℝ) ^ 2)) < 1) →
    ((∑ j ∈ head, (w j : ℝ)) + δ + h * ∑ j ∈ headᶜ, (w j : ℝ) * |f j| < B) →
    ∀ A : ℝ, ∃ a > A, ∀ t ∈ Icc a (a + R), readout.readout () ⟨J, i, f, w⟩ t < B

private theorem orbit_rejected : ¬ orbitArena.{u}.Law orbitRejected := by
  intro law
  let J := ULift.{u} Empty
  let f : J → ℝ := 0
  have hli : LinearIndependent ℚ f := linearIndependent_empty_type
  obtain ⟨a, _, hs⟩ := law (∅ : Finset J) f 0 hli
    (R := 1) (h := 1) (δ := 1 / 2) (B := 1)
    zero_lt_one (by norm_num) (Or.inl (by simp)) (by simp [f]; norm_num) 0
  have h := hs a ⟨le_rfl, by linarith⟩
  simp [orbitRejected, realize] at h

private theorem orbit_dependence : ObservationalDependence orbitSignature.{u} orbitActual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1, 1⟩, 0, Real.pi / 2, ?_⟩
  simp [orbitActual, realize, sineScore, Real.sin_pi_div_two]

def orbitEvidence :
    Registration orbitArena.{u} (type_of% @exists_arbitrarily_late_missing_window.{u}) where
  actual := orbitActual
  bridge := Iff.rfl
  variation := ⟨@exists_arbitrarily_late_missing_window.{u}, orbitRejected, orbit_rejected⟩
  sensitivity := sensitivity orbitArena.Law orbitActual orbitRejected orbit_rejected
  dependence := orbit_dependence

def orbitRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_arbitrarily_late_missing_window.{u}) (Realization orbitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.orbitUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow.orbitEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨orbitArena.{u}⟩
  objectArena := .source ⟨orbitArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source orbitArena.{u} ⟨orbitEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orbitSignature
    (fun _ q t => @sineScore q.1 q.2.1 q.2.2.1 0 q.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteSineMissingWindow
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body",
        "fn", "arg"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms gridRegistration
#print axioms windowRegistration
#print axioms orbitRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
