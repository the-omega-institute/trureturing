import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
import Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for SIC k-Fidelity Achievable Regions -/

namespace Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion

open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.FiniteDimensional
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open _root_.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
open _root_.Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ZeroRegion

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n : ℕ), 1 ≤ n →
    ∀ (ρ : Fin n → Fin 4 → QubitMatrix), (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
      achievableRegion n 0 ρ =
        convexHull ℝ ({(1, 1), ((3 : ℝ)⁻¹ ^ O.readout () () n, 0), ((3 : ℝ)⁻¹, 0)} :
          Set (ℝ × ℝ)) ∧
      (2 ≤ n → ∀ p : ℝ × ℝ, p ∈ achievableRegion n 0 ρ ↔ 0 ≤ p.2 ∧
        1 - (3 / 2 : ℝ) * (1 - p.1) ≤ p.2 ∧
        p.2 ≤ (p.1 - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n)) ∧
      (n = 1 → ∀ p : ℝ × ℝ, p ∈ achievableRegion n 0 ρ ↔
        p.2 = 1 - (3 / 2 : ℝ) * (1 - p.1) ∧ (3 : ℝ)⁻¹ ≤ p.1 ∧ p.1 ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        let q : PauliLabel n → ℝ :=
          fun γ => if γ = 0 then t else if γ = (fun _ => 3) then 1 - t else 0
        (pauliChannel q).IsCompletelyPositive ∧ (pauliChannel q).IsTracePreserving ∧
          (realKFidelity ρ 0 (pauliChannel q), realProcessFidelity (pauliChannel q)) =
            (t + (1 - t) * (3 : ℝ)⁻¹ ^ n, t)) ∧
      (∀ β : PauliLabel n, hammingWeight β = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        let q : PauliLabel n → ℝ :=
          fun γ => if γ = 0 then t else if γ = β then 1 - t else 0
        (pauliChannel q).IsCompletelyPositive ∧ (pauliChannel q).IsTracePreserving ∧
          (realKFidelity ρ 0 (pauliChannel q), realProcessFidelity (pauliChannel q)) =
            (t + (1 - t) * (3 : ℝ)⁻¹, t)) ∧
      (2 ≤ n → ∀ x : ℝ, (3 : ℝ)⁻¹ ^ n ≤ x → x ≤ 1 →
        IsGreatest {y : ℝ | (x, y) ∈ achievableRegion n 0 ρ}
          ((x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n)) ∧
        (x < 1 → (x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n) < x) ∧
        x - (x - (3 : ℝ)⁻¹ ^ n) / (1 - (3 : ℝ)⁻¹ ^ n) =
          (1 - x) * (3 : ℝ)⁻¹ ^ n / (1 - (3 : ℝ)⁻¹ ^ n) ∧
        IsLeast {y : ℝ | (x, y) ∈ achievableRegion n 0 ρ}
          (max 0 (1 - (3 / 2 : ℝ) * (1 - x))))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmem : ((3 : ℝ)⁻¹ ^ 2, (0 : ℝ)) ∈ achievableRegion 2 0 (canonicalSICFamily 2) := by
    rw [(achievableRegion_zero_characterization 2 (by decide) (canonicalSICFamily 2)
      (canonicalSICFamily_isQubitSICProjector 2)).2.1 (by decide)]
    norm_num
  have hr := (h 2 (by decide) (canonicalSICFamily 2)
    (canonicalSICFamily_isQubitSICProjector 2)).1
  dsimp [rejected, realize] at hr
  rw [hr] at hmem
  have hsub : convexHull ℝ ({(1, 1), ((3 : ℝ)⁻¹ ^ 1, 0), ((3 : ℝ)⁻¹, 0)} : Set (ℝ × ℝ)) ⊆
      {p : ℝ × ℝ | (3 : ℝ)⁻¹ ≤ p.1} :=
    convexHull_min (by rintro p (rfl | rfl | rfl) <;> dsimp <;> norm_num)
      (fun x hx y hy a b ha hb hab => by dsimp at hx hy ⊢; nlinarith)
  have hbad : (3 : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ ^ 2 := hsub hmem
  norm_num at hbad

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 1, 2, by decide⟩

def evidence : Registration arena
    (type_of% (@achievableRegion_zero_characterization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@achievableRegion_zero_characterization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@achievableRegion_zero_characterization)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.ZeroRegion.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.ZeroRegion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg", "fn", "arg",
        "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ZeroRegion

namespace HighRegion

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix),
    (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
    (1 ≤ k ∧ k + 1 ≤ n →
      (0 < tailCoeff k (optWeight n k) ∧ tailCoeff k (optWeight n k) < 1) ∧
      (∀ w ∈ Finset.Icc 1 n, tailCoeff k w ≤ tailCoeff k (optWeight n k)) ∧
      (Finset.Icc 1 n).filter (fun w => tailCoeff k w = tailCoeff k (optWeight n k)) =
        (@ite _ (Even k ∧ 3 * k / 2 + 1 ≤ n) (Classical.propDecidable _)
          {3 * k / 2, 3 * k / 2 + 1} {optWeight n k}) ∧
      achievableRegion n k ρ =
        convexHull ℝ ({(1, 1), (0, 0), (extremalAbscissa n (O.readout () () k), 0)} :
          Set (ℝ × ℝ)) ∧
      (Odd k → ∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ ↔
        0 ≤ p.2 ∧ p.1 ≤ p.2 ∧
        p.2 ≤ (p.1 - extremalAbscissa n k) / (1 - extremalAbscissa n k)) ∧
      (Even k → ∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ ↔
        0 ≤ p.2 ∧ (p.1 - extremalAbscissa n k) / (1 - extremalAbscissa n k) ≤ p.2 ∧
        p.2 ≤ p.1) ∧
      (∀ p : ℝ × ℝ, p ∈ achievableRegion n k ρ → 0 ≤ p.2 ∧ p.2 ≤ 1) ∧
      (MatrixMap.IsCompletelyPositive (LinearMap.id : QubitMap n) ∧
        MatrixMap.IsTracePreserving (LinearMap.id : QubitMap n) ∧
        (realKFidelity ρ k (LinearMap.id : QubitMap n),
          realProcessFidelity (LinearMap.id : QubitMap n)) = (1, 1)) ∧
      (∀ β : PauliLabel n, hammingWeight β = 1 →
        (pauliChannel (fun γ => if γ = β then 1 else 0)).IsCompletelyPositive ∧
        (pauliChannel (fun γ => if γ = β then 1 else 0)).IsTracePreserving ∧
        (realKFidelity ρ k (pauliChannel (fun γ => if γ = β then 1 else 0)),
          realProcessFidelity (pauliChannel (fun γ => if γ = β then 1 else 0))) = (0, 0)) ∧
      (∃ β : PauliLabel n, hammingWeight β = optWeight n k) ∧
      (∀ β : PauliLabel n, hammingWeight β = optWeight n k →
        (pauliChannel (fun γ => if γ = β then 1 else 0)).IsCompletelyPositive ∧
        (pauliChannel (fun γ => if γ = β then 1 else 0)).IsTracePreserving ∧
        (realKFidelity ρ k (pauliChannel (fun γ => if γ = β then 1 else 0)),
          realProcessFidelity (pauliChannel (fun γ => if γ = β then 1 else 0))) =
            (extremalAbscissa n k, 0))) ∧
    (1 ≤ n ∧ n ≤ k →
      achievableRegion n k ρ = convexHull ℝ ({(0, 0), (1, 1)} : Set (ℝ × ℝ)) ∧
      achievableRegion n k ρ = {p : ℝ × ℝ | p.1 = p.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1})

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he21 : extremalAbscissa 2 1 = -(9 : ℝ)⁻¹ := by
    unfold extremalAbscissa tailCoeff optWeight; norm_num
  have he22 : extremalAbscissa 2 2 = 0 := by
    unfold extremalAbscissa tailCoeff optWeight; norm_num
  have hmem : (extremalAbscissa 2 1, (0 : ℝ)) ∈
      achievableRegion 2 1 (canonicalSICFamily 2) := by
    rw [((achievableRegion_intermediate_and_high_characterization 2 1 (canonicalSICFamily 2)
      (canonicalSICFamily_isQubitSICProjector 2)).1 ⟨by omega, by omega⟩).2.2.2.2.1
      ⟨0, rfl⟩]
    rw [he21]; norm_num
  have hr := ((h 2 1 (canonicalSICFamily 2)
    (canonicalSICFamily_isQubitSICProjector 2)).1 ⟨by omega, by omega⟩).2.2.2.1
  rw [hr] at hmem
  have hsub : convexHull ℝ ({(1, 1), (0, 0), (extremalAbscissa 2 2, 0)} : Set (ℝ × ℝ)) ⊆
      {p : ℝ × ℝ | 0 ≤ p.1} :=
    convexHull_min (by rintro p (rfl | rfl | rfl) <;> dsimp <;> norm_num [he22])
      (fun x hx y hy a b ha hb hab => by dsimp at hx hy ⊢; nlinarith)
  have hbad : 0 ≤ extremalAbscissa 2 1 := hsub (by simpa [rejected, realize] using hmem)
  rw [he21] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 1, 2, by decide⟩

def evidence : Registration arena
    (type_of% (@achievableRegion_intermediate_and_high_characterization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@achievableRegion_intermediate_and_high_characterization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@achievableRegion_intermediate_and_high_characterization)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.HighRegion.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.HighRegion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "arg", "arg", "arg", "fn",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HighRegion

namespace NonIdent

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => QubitMap n) (fun _ => ℝ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ Λ₂ => realProcessFidelity Λ₂) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n k : ℕ), 2 ≤ n → k + 1 ≤ n →
    ∀ (ρ : Fin n → Fin 4 → QubitMatrix), (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
      ∃ Λ₁ Λ₂ : QubitMap n,
        Λ₁.IsCompletelyPositive ∧ Λ₁.IsTracePreserving ∧
        Λ₂.IsCompletelyPositive ∧ Λ₂.IsTracePreserving ∧
        realKFidelity ρ k Λ₁ = realKFidelity ρ k Λ₂ ∧
        realProcessFidelity Λ₁ = 0 ∧
        0 < O.readout () n Λ₂ ∧
        realProcessFidelity Λ₁ ≠ realProcessFidelity Λ₂

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, Λ₂, _, _, _, _, _, _, hpos, _⟩ :=
    h 2 0 (by decide) (by decide) (canonicalSICFamily 2)
      (canonicalSICFamily_isQubitSICProjector 2)
  simp [rejected, realize] at hpos

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  obtain ⟨Λ₁, Λ₂, _, _, _, _, _, _, _, hne⟩ :=
    kFidelity_non_identifiability_of_processFidelity 2 0 (by decide) (by decide)
      (canonicalSICFamily 2) (canonicalSICFamily_isQubitSICProjector 2)
  exact ⟨2, Λ₁, Λ₂, by simpa [actual, realize] using hne⟩

def evidence : Registration arena
    (type_of% (@kFidelity_non_identifiability_of_processFidelity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kFidelity_non_identifiability_of_processFidelity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@kFidelity_non_identifiability_of_processFidelity)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ Λ₂ => realProcessFidelity Λ₂)
        (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.NonIdent.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion.NonIdent.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ Λ₂ => realProcessFidelity Λ₂)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NonIdent

end

end Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityAchievableRegion
