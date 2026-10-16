import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction (K1 K2)
open LeanInformationAudit Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin (n + 10) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev statement : Prop := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n →
  SpectralBound (n + 1 + a) → SpectralBound (n + 1)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n a : ℕ), 1 ≤ a → SpectralBound n → SpectralBound (n + 1 + a) →
    ∀ l : Fin (n + 10) → ℝ, Antitone l → (∀ i, 0 ≤ l i) →
      (∑ i, l i) = 1 → (K1 (boundaryValues (n + 1) l)).PosSemidef →
      (K2 (boundaryValues (n + 1) l)).PosSemidef →
      O.readout () n l ≤ purityBound (n + 10)

private theorem endpoint18 : SpectralBound 9 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 9 l = QutritSpectralReduction.boundaryValues 3 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN6PurityBound.certificate_bound l ho (hn 17) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem endpoint21 : SpectralBound 12 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 12 l = QutritSpectralReduction.boundaryValues 4 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex, QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN7PurityBound.certificate_bound l ho (hn 20) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem flat_psd (k : Bool) :
    ((if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ)))).PosSemidef := by
  have heq : (if k then K1 else K2) (boundaryValues 10 (fun _ => (1 / 19 : ℝ))) =
      (2 / 19 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [K1, K2, boundaryValues, Matrix.smul_apply, Matrix.one_apply]
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hle := h 9 2 (by decide) endpoint18 endpoint21 (fun _ => (1 / 19 : ℝ))
    (fun _ _ _ => le_rfl) (fun _ => by norm_num) (by simp)
    (by simpa using flat_psd true) (by simpa using flat_psd false)
  norm_num [rejected, realize, purityBound] at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena statement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨spectral_bound_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- The omitted source selector leaves the structural reconstruction obligation open. -/
def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer)
    (Realization signature) (Type 0) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.spectral_bound_transfer.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration

namespace SharedObserver

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ × ℕ)
    (fun x => Fin (x.1 + x.2.1 + x.2.2 + 1) → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (p q n a : ℕ) (C : (Fin (p + q) → ℝ) → Prop) (kappa : ℝ),
    PositiveScaleInvariant C → 1 ≤ a → 10 ≤ p + q + n + 1 →
    1 < ((p + q + n + 1 : ℕ) : ℝ) - kappa →
    0 ≤ (10 - kappa) * ((p + q + n + 1 : ℕ) : ℝ) ^ 2 +
      (6 - 15 * kappa) * ((p + q + n + 1 : ℕ) : ℝ) - 20 * kappa - 16 →
    (∀ (l : Fin (p + q + n + 1) → ℝ), Antitone l →
      (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
      C (observerValues p q (p + q + n + 1) (by omega) l) →
      (((p + q + n + 1 : ℕ) : ℝ) - kappa) * l ⟨p + n, by omega⟩ ≤ 1) →
    ObserverBound p q C (p + q + n) →
    ObserverBound p q C (p + q + n + 1 + a) →
    ∀ (h : p + q ≤ p + q + n + 1) (l : Fin (p + q + n + 1) → ℝ),
      Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
      C (observerValues p q (p + q + n + 1) h l) →
      O.readout () ⟨p, q, n⟩ l ≤ purityBound (p + q + n + 1)

private def FlatBoundary (b : Fin 2 → ℝ) : Prop := b 0 = b 1

private theorem flat_scaling : PositiveScaleInvariant FlatBoundary := by
  intro b s hs
  change (b 0 / s = b 1 / s) ↔ b 0 = b 1
  constructor
  · intro h
    have hh := congrArg (fun x : ℝ => x * s) h
    simpa [hs.ne'] using hh
  · intro h; rw [h]

private theorem flat_all (N : ℕ) (hN : 2 ≤ N) (l : Fin N → ℝ) (ho : Antitone l)
    (hc : FlatBoundary (observerValues 1 1 N hN l)) :
    ∀ i, l i = l ⟨0, by omega⟩ := by
  have hends : l ⟨0, by omega⟩ = l ⟨N - 1, by omega⟩ := by
    change l (observerIndex 1 1 N hN 0) = l (observerIndex 1 1 N hN 1) at hc
    convert hc using 1 <;> congr 1 <;> apply Fin.ext <;> norm_num [observerIndex] <;> omega
  intro i
  have h0 := ho (show (⟨0, by omega⟩ : Fin N) ≤ i by change 0 ≤ i.val; omega)
  have hlast := ho (show i ≤ (⟨N - 1, by omega⟩ : Fin N) by
    change i.val ≤ N - 1; omega)
  linarith

private theorem flat_bound (N : ℕ) (hN : 2 ≤ N) : ObserverBound 1 1 FlatBoundary N := by
  intro h l ho hn ht hc
  have hall := flat_all N hN l ho hc
  have hs : (N : ℝ) * l ⟨0, by omega⟩ = 1 := by simpa [hall] using ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : l ⟨0, by omega⟩ = 1 / (N : ℝ) :=
    (eq_div_iff hN0.ne').mpr (by linarith)
  simp_rw [hall, hl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold purityBound
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < (N : ℝ) + 2 by positivity))).mpr
  field_simp [hN0.ne']
  nlinarith [show (2 : ℝ) ≤ N by exact_mod_cast hN]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcap : ∀ l : Fin (1 + 1 + 7 + 1) → ℝ, Antitone l →
      (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
      FlatBoundary (observerValues 1 1 (1 + 1 + 7 + 1) (by decide) l) →
      (((1 + 1 + 7 + 1 : ℕ) : ℝ) - 0) * l ⟨1 + 7, by decide⟩ ≤ 1 := by
    intro l ho hn ht hc
    have hall := flat_all 10 (by decide) l ho hc
    have hs : (10 : ℝ) * l 0 = 1 := by simpa [hall] using ht
    simpa [hall] using hs.le
  have hh := h 1 1 7 1 FlatBoundary 0 flat_scaling (by decide) (by decide)
    (by norm_num) (by norm_num) hcap (flat_bound 9 (by decide))
    (flat_bound 11 (by decide)) (by decide) (fun _ => (1 / 10 : ℝ))
    (fun _ _ _ => le_rfl) (fun _ => by norm_num) (by simp)
    (by rfl)
  norm_num [rejected, realize, purityBound] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def familyRegistration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨observer_bound_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := actual_dependence

/-- The full parameter telescope is modeled; raw source selection remains absent. -/
def registration : Contract.Registration
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.observer_bound_transfer)
    (Realization signature) (Type 0) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.observer_bound_transfer.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer.SharedObserver.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ l => ∑ i, (l i) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration

end SharedObserver

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
