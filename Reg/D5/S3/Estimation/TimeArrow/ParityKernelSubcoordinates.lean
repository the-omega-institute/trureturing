import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Reg.Support.ParityKernelRegistrationTemplates
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
  let owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
  let lawRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `lawArena
    theoremName := owner ++ `subcoordinateLaw_eq
    statementIdentity := "sha256:7c157665ce037dde96ecbbb8d69e0cf53810af5a7416ca1930a9ff88e929a20a"
    registrationModuleName := root }
  let mixRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `mixArena
    theoremName := owner ++ `parityKernel_mul_eq_uniform
    statementIdentity := "sha256:a1bea434e651834066312346de701d9d1671a6d3cc94b390ec9db163a7c119a4"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[lawRow, mixRow], source := #[lawRow, mixRow],
    companionPrefix := some root }

/-! ### The coordinate-record law -/

def lawActual : Realization subcoordinateRecordSignature :=
  realize subcoordinateRecordSignature
    (fun _ p w => (subcoordinateLaw p.2.1 p.2.2.1 p.2.2.2 w : ℝ)) (fun e => nomatch e)

def lawRejected : Realization subcoordinateRecordSignature :=
  realize subcoordinateRecordSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def lawArena : Arena where
  signature := subcoordinateRecordSignature
  Law R := ∀ {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d)) (_hS : S ≠ Finset.univ) (T : ℕ)
    (w : Fin (T + 1) → Fin d → ℤˣ),
    R.readout () ⟨d, a, S, T⟩ w = ((1 / 2 ^ S.card : ℝ)) ^ (T + 1)

/-- With every coordinate observed, the record law is the full path law of the recorded path. -/
theorem subcoordinateLaw_univ {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (T : ℕ)
    (w : Fin (T + 1) → Fin d → ℤˣ) :
    subcoordinateLaw a Finset.univ T w =
      (1 / 2 ^ d : ℝ) * ∏ t : Fin T, parityKernel a (w t.castSucc) (w t.succ) := by
  unfold subcoordinateLaw
  rw [Finset.sum_eq_single w]
  · simp
  · intro x _ hx
    obtain ⟨t, ht⟩ : ∃ t, x t ≠ w t := by
      by_contra h
      exact hx (funext fun t => by_contra fun ht => h ⟨t, ht⟩)
    have hzero : (if ∀ j ∈ (Finset.univ : Finset (Fin d)), x t j = w t j then (1 : ℝ) else 0) = 0 :=
      if_neg fun h => ht (funext fun j => h j (Finset.mem_univ j))
    rw [Finset.prod_eq_zero (Finset.mem_univ t) hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

def onePath : Fin 2 → Fin 1 → ℤˣ := fun _ _ => 1

def flipPath : Fin 2 → Fin 1 → ℤˣ := fun t _ => if t = 0 then 1 else -1

theorem parity_one : parity (fun _ : Fin 1 => (1 : ℤˣ)) = 1 := by simp [parity]

theorem parity_neg_one : parity (fun _ : Fin 1 => (-1 : ℤˣ)) = -1 := by simp [parity]

theorem lawActual_onePath :
    lawActual.readout () ⟨1, fun _ => 1 / 2, Finset.univ, 1⟩ onePath = (3 / 8 : ℝ) := by
  show subcoordinateLaw (d := 1) (fun _ => (1 / 2 : ℝ)) Finset.univ 1 onePath = (3 / 8 : ℝ)
  rw [subcoordinateLaw_univ]
  have h1 : onePath (Fin.succ 0) = fun _ => 1 := rfl
  simp only [parityKernel, Fin.prod_univ_one, h1, parity_one]
  norm_num

theorem lawActual_flipPath :
    lawActual.readout () ⟨1, fun _ => 1 / 2, Finset.univ, 1⟩ flipPath = (1 / 8 : ℝ) := by
  show subcoordinateLaw (d := 1) (fun _ => (1 / 2 : ℝ)) Finset.univ 1 flipPath = (1 / 8 : ℝ)
  rw [subcoordinateLaw_univ]
  have h0 : flipPath (Fin.castSucc 0) = fun _ => 1 := by funext j; simp [flipPath]
  have h1 : flipPath (Fin.succ 0) = fun _ => -1 := by funext j; simp [flipPath]
  simp only [Fin.prod_univ_one, parityKernel, h0, h1, parity_neg_one]
  norm_num

theorem lawRejected_law : ¬ lawArena.Law lawRejected := by
  intro h
  have hs : (∅ : Finset (Fin 1)) ≠ Finset.univ := by
    intro he
    have : (0 : Fin 1) ∈ (∅ : Finset (Fin 1)) := he ▸ Finset.mem_univ _
    simp at this
  have := h (d := 1) (fun _ => 0) ∅ hs 0 (fun _ _ => 1)
  change (0 : ℝ) = _ at this
  norm_num at this

theorem law_sensitivity : Sensitivity lawArena lawActual := by
  constructor
  · intro i
    refine ⟨lawRejected, ?_, rfl, lawRejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem law_dependence : ObservationalDependence subcoordinateRecordSignature lawActual := by
  intro i
  refine ⟨⟨1, fun _ => 1 / 2, Finset.univ, 1⟩, onePath, flipPath, ?_⟩
  cases i
  rw [lawActual_onePath, lawActual_flipPath]
  intro h
  have h' : (3 / 8 : ℝ) = 1 / 8 := h
  norm_num at h'

def lawRegistration : Registration lawArena (lawArena.Law lawActual) where
  actual := lawActual
  bridge := Iff.rfl
  variation := ⟨fun a S hS T w => subcoordinateLaw_eq a S hS T w, lawRejected, lawRejected_law⟩
  sensitivity := law_sensitivity
  dependence := law_dependence

register_information_theorem subcoordinateLaw_eq in lawArena
  readout via (realize subcoordinateRecordSignature
    (fun _ p w => (subcoordinateLaw p.2.1 p.2.2.1 p.2.2.2 w : ℝ)) (fun e => nomatch e))
  realizes lawRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

/-! ### The two-step product -/

def mixActual : Realization twoStepKernelSignature :=
  realize twoStepKernelSignature
    (fun _ p z => (∑ y, parityKernel p.2.1 p.2.2.2 y * parityKernel p.2.2.1 y z : ℝ))
    (fun e => nomatch e)

def mixRejected : Realization twoStepKernelSignature :=
  realize twoStepKernelSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def mixArena : Arena where
  signature := twoStepKernelSignature
  Law R := ∀ {d : ℕ} (_hd : 1 ≤ d) (a b : (Fin d → ℤˣ) → ℝ) (_hb : ∑ y, b y = 0)
    (_hχb : ∑ y, parity y * b y = 0) (x z : Fin d → ℤˣ),
    R.readout () ⟨d, a, b, x⟩ z = (1 / 2 ^ d : ℝ)

theorem mixActual_value (z : Fin 1 → ℤˣ) :
    mixActual.readout () ⟨1, fun _ => 0, fun _ => 1, fun _ => 1⟩ z = ((1 + parity z) / 2 : ℝ) := by
  change ∑ y, parityKernel _ _ y * parityKernel _ y z = _
  simp only [parityKernel, zero_mul, add_zero, one_mul, pow_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_units_int, nsmul_eq_mul]
  norm_num
  ring

theorem mixRejected_law : ¬ mixArena.Law mixRejected := by
  intro h
  have := h (d := 1) le_rfl (fun _ => 0) (fun _ => 0) (by simp) (by simp) (fun _ => 1) (fun _ => 1)
  change (0 : ℝ) = _ at this
  norm_num at this

theorem mix_sensitivity : Sensitivity mixArena mixActual := by
  constructor
  · intro i
    refine ⟨mixRejected, ?_, rfl, mixRejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem mix_dependence : ObservationalDependence twoStepKernelSignature mixActual := by
  intro i
  refine ⟨⟨1, fun _ => 0, fun _ => 1, fun _ => 1⟩, fun _ => 1, fun _ => -1, ?_⟩
  cases i
  rw [mixActual_value, mixActual_value]
  intro h
  have h' : ((1 + parity (fun _ : Fin 1 => (1 : ℤˣ))) / 2 : ℝ) =
      (1 + parity (fun _ : Fin 1 => (-1 : ℤˣ))) / 2 := h
  rw [parity_one, parity_neg_one] at h'
  norm_num at h'

def mixRegistration : Registration mixArena (mixArena.Law mixActual) where
  actual := mixActual
  bridge := Iff.rfl
  variation := ⟨fun hd a b hb hχb x z => parityKernel_mul_eq_uniform hd a b hb hχb x z,
    mixRejected, mixRejected_law⟩
  sensitivity := mix_sensitivity
  dependence := mix_dependence

register_information_theorem parityKernel_mul_eq_uniform in mixArena
  readout via (realize twoStepKernelSignature
    (fun _ p z => (∑ y, parityKernel p.2.1 p.2.2.2 y * parityKernel p.2.2.1 y z : ℝ))
    (fun e => nomatch e))
  realizes mixRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
    coordinates := #[0, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms lawRejected_law
#print axioms law_sensitivity
#print axioms law_dependence
#print axioms mixRejected_law
#print axioms mix_sensitivity
#print axioms mix_dependence

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
