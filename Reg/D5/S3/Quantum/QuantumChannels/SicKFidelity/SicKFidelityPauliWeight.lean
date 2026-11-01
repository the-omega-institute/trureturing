import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
import Reg.Support.SingleDependentReadout
/-! # Escape Registration for SIC k-Fidelity and Pauli-Weight Geometry -/
namespace Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.FiniteDimensional _root_.D5.S3.Quantum.PureState.PureStateHandshake
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf Finset Matrix Complex
open _root_.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
def sicR : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
theorem sicR_sq : sicR ^ 2 = (3 : ℂ)⁻¹ := by
  dsimp [sicR]
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
def sicSign1 : Fin 4 → ℂ := fun a => match a with | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -1
def sicSign2 : Fin 4 → ℂ := fun a => match a with | 0 => 1 | 1 => -1 | 2 => 1 | 3 => -1
def sicSign3 : Fin 4 → ℂ := fun a => match a with | 0 => 1 | 1 => -1 | 2 => -1 | 3 => 1
def canonicalQubitSIC (a : Fin 4) : QubitMatrix :=
  (2 : ℂ)⁻¹ • ((1 : QubitMatrix) + sicR •
    (sicSign1 a • pauli1 1 + sicSign2 a • pauli1 2 + sicSign3 a • pauli1 3))
theorem canonicalQubitSIC_isQubitSICProjector : IsQubitSICProjector canonicalQubitSIC := by
  refine ⟨fun a => ⟨?_, ?_, ?_⟩, fun a b hab => ?_⟩
  · ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp [canonicalQubitSIC, sicR, sicSign1, sicSign2, sicSign3, pauli1, qubitX, qubitZ,
        Matrix.conjTranspose_apply] <;> ring
  · ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp [canonicalQubitSIC, sicSign1, sicSign2, sicSign3, pauli1, qubitX, qubitZ,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq, sicR_sq] <;> ring
  · fin_cases a <;>
      simp [canonicalQubitSIC, sicSign1, sicSign2, sicSign3, pauli1, qubitX, qubitZ,
        Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring
  · fin_cases a <;> fin_cases b <;> (try exact (hab rfl).elim) <;>
      simp [canonicalQubitSIC, sicSign1, sicSign2, sicSign3, pauli1, qubitX, qubitZ,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq, sicR_sq] <;> norm_num
def canonicalSICFamily (n : ℕ) : Fin n → Fin 4 → QubitMatrix := fun _ => canonicalQubitSIC
theorem canonicalSICFamily_isQubitSICProjector (n : ℕ) (i : Fin n) :
    IsQubitSICProjector (canonicalSICFamily n i) :=
  canonicalQubitSIC_isQubitSICProjector
def pauliZ1Weight : PauliLabel 1 → ℝ := fun β => if β = (fun _ => 3) then 1 else 0
def pauliZ1 : QubitMap 1 := pauliChannel pauliZ1Weight
theorem pauliZ1_zero_ne : (0 : PauliLabel 1) ≠ (fun _ => 3) := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0
theorem pauliZ1_props :
    pauliZ1.IsCompletelyPositive ∧ pauliZ1.IsTracePreserving ∧
    pauliTwirlWeight pauliZ1 0 = 0 ∧ pauliWeightSum pauliZ1 0 = 0 ∧
    processFidelity pauliZ1 = 0 ∧ realProcessFidelity pauliZ1 = 0 ∧
    kFidelity (canonicalSICFamily 1) 0 pauliZ1 = (3 : ℂ)⁻¹ ∧
    realKFidelity (canonicalSICFamily 1) 0 pauliZ1 = (3 : ℝ)⁻¹ := by
  have hch := pauli_process_matrix_and_fidelity_characterization 1
  have hpc := hch.2.2.2.2 pauliZ1Weight
  have hCP : pauliZ1.IsCompletelyPositive :=
    hpc.2.1 fun β => by dsimp [pauliZ1Weight]; split_ifs <;> norm_num
  have hTP : pauliZ1.IsTracePreserving :=
    hpc.2.2 (by simp [pauliZ1Weight])
  have htw (β : PauliLabel 1) : pauliTwirlWeight pauliZ1 β = (pauliZ1Weight β : ℂ) := by
    simpa [pauliTwirlWeight, pauliZ1] using hpc.1 β β
  have htw0 : pauliTwirlWeight pauliZ1 0 = 0 := by
    rw [htw 0]; simp [pauliZ1Weight, pauliZ1_zero_ne]
  have hws0 : pauliWeightSum pauliZ1 0 = 0 := (hch.2.1 pauliZ1).2.1.trans htw0
  have hpf0 : processFidelity pauliZ1 = 0 := (hch.2.1 pauliZ1).1.trans htw0
  have hrpf0 : realProcessFidelity pauliZ1 = 0 := by simp [realProcessFidelity, hpf0]
  have hkf : kFidelity (canonicalSICFamily 1) 0 pauliZ1 = (3 : ℂ)⁻¹ := by
    rw [(kFidelity_eq_pauliWeight_alternating_sum 1 0 (canonicalSICFamily 1)
      (canonicalSICFamily_isQubitSICProjector 1) pauliZ1).2.2.1]
    simp_rw [htw]
    rw [Fintype.sum_eq_single (fun _ : Fin 1 => (3 : Fin 4)) fun β hβ => by
      simp [pauliZ1Weight, hβ]]
    have hhw : hammingWeight (fun _ : Fin 1 => (3 : Fin 4)) = 1 := by decide
    simp [pauliZ1Weight, hhw]
  have hrkf : realKFidelity (canonicalSICFamily 1) 0 pauliZ1 = (3 : ℝ)⁻¹ := by
    simp [realKFidelity, hkf]
  exact ⟨hCP, hTP, htw0, hws0, hpf0, hrpf0, hkf, hrkf⟩
namespace ProcessMatrix
abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n : ℕ),
    (∀ (Λ : QubitMap n),
      (∀ X, Λ X = ∑ β : PauliLabel n, ∑ γ : PauliLabel n,
        processMatrix Λ β γ • (pauliN n β * X * pauliN n γ)) ∧
      (∀ c : PauliLabel n → PauliLabel n → ℂ,
        (∀ X, Λ X = ∑ β : PauliLabel n, ∑ γ : PauliLabel n,
          c β γ • (pauliN n β * X * pauliN n γ)) →
          ∀ β γ, c β γ = processMatrix Λ β γ)) ∧
    (∀ (Λ : QubitMap n),
      processFidelity Λ = pauliTwirlWeight Λ 0 ∧
      pauliWeightSum Λ 0 = pauliTwirlWeight Λ 0 ∧
      ∑ w ∈ Finset.range (O.readout () () n + 1), pauliWeightSum Λ w =
        ∑ β : PauliLabel n, pauliTwirlWeight Λ β) ∧
    (∀ (Λ : QubitMap n),
      (Λ.IsTracePreserving ↔ ∑ β : PauliLabel n, ∑ γ : PauliLabel n,
        processMatrix Λ β γ • (pauliN n γ * pauliN n β) = 1) ∧
      (Λ.IsTracePreserving → ∑ β : PauliLabel n, pauliTwirlWeight Λ β = 1 ∧
        ∑ w ∈ Finset.range (n + 1), pauliWeightSum Λ w = 1)) ∧
    (∀ (Λ : QubitMap n), Λ.IsCompletelyPositive →
      (∀ β : PauliLabel n,
        (pauliTwirlWeight Λ β).im = 0 ∧ 0 ≤ (pauliTwirlWeight Λ β).re) ∧
      (∀ w : ℕ, ((realWeightSum Λ w : ℝ) : ℂ) = pauliWeightSum Λ w ∧
        0 ≤ realWeightSum Λ w) ∧
      ((realProcessFidelity Λ : ℝ) : ℂ) = processFidelity Λ) ∧
    (∀ (q : PauliLabel n → ℝ),
      (∀ β γ : PauliLabel n, processMatrix (pauliChannel q) β γ =
        if β = γ then (q β : ℂ) else 0) ∧
      ((∀ β : PauliLabel n, 0 ≤ q β) → (pauliChannel q).IsCompletelyPositive) ∧
      (∑ β : PauliLabel n, q β = 1 → (pauliChannel q).IsTracePreserving))
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hTP, _, hws0, _⟩ := pauliZ1_props
  have hr := ((h 1).2.1 pauliZ1).2.2
  have hsum1 := (((pauli_process_matrix_and_fidelity_characterization 1).2.2.1 pauliZ1).2 hTP).1
  simp [rejected, realize, hws0, hsum1] at hr
theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩
def evidence : Registration arena
    (type_of% (@pauli_process_matrix_and_fidelity_characterization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pauli_process_matrix_and_fidelity_characterization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@pauli_process_matrix_and_fidelity_characterization)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.ProcessMatrix.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.ProcessMatrix.evidence
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
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ProcessMatrix
namespace ProjectorIff
abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 4 → QubitMatrix) (fun _ => Fin 4 → QubitMatrix)
def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ ρ => ρ) (fun e => nomatch e)
def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law O := ∀ (ρ : Fin 4 → QubitMatrix),
    IsQubitSICProjector (O.readout () () ρ) ↔
      ∃ ψ : Fin 4 → Fin 2 → ℂ, IsUnitVectorQubitSIC ψ ∧
        ∀ a : Fin 4, ρ a = rankOneDensity (ψ a)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hrhs := (isQubitSICProjector_iff_exists_unitVectorQubitSIC canonicalQubitSIC).mp
    canonicalQubitSIC_isQubitSICProjector
  have h0 : IsQubitSICProjector 0 := by
    simpa [rejected, realize] using (h canonicalQubitSIC).mpr hrhs
  have htr := (h0.1 0).2.2
  simp at htr
theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  refine ⟨(), 0, canonicalQubitSIC, fun h => ?_⟩
  dsimp [actual, realize] at h
  have htr := congrArg (fun f : Fin 4 → QubitMatrix => Matrix.trace (f 0)) h
  rw [Pi.zero_apply, Matrix.trace_zero, (canonicalQubitSIC_isQubitSICProjector.1 0).2.2] at htr
  exact zero_ne_one htr
def evidence : Registration arena
    (type_of% (@isQubitSICProjector_iff_exists_unitVectorQubitSIC)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isQubitSICProjector_iff_exists_unitVectorQubitSIC, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@isQubitSICProjector_iff_exists_unitVectorQubitSIC)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ ρ => ρ) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.ProjectorIff.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.ProjectorIff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ ρ => ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ProjectorIff
namespace SicTraces
abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n : ℕ),
    (sicOverlapB * (1 - sicMatrixA) = 1 ∧ (1 - sicMatrixA) * sicOverlapB = 1) ∧
    (∀ a : Fin 4,
      (sicOverlapB * (1 - Matrix.of (fun i j : Fin 4 =>
        (1 - if i = j then (5 : ℂ) else 0) / 4))) a a = 7 / 4) ∧
    (∀ a b : PauliLabel n,
      (∏ i : Fin n, (1 - sicMatrixA) (a i) (b i)) =
        ∑ T : Finset (Fin n), (-1 : ℂ) ^ T.card * sicSubsetKernel n T a b ∧
      (∏ i : Fin n, (1 - sicMatrixA) (a i) (b i)) =
        (-1 : ℂ) ^ (Finset.univ.filter (fun i : Fin n => a i ≠ b i)).card *
          (5 : ℂ) ^ (O.readout () () n -
            (Finset.univ.filter (fun i : Fin n => a i ≠ b i)).card) /
          (4 : ℂ) ^ n) ∧
    (∀ ρ₀ : Fin 4 → QubitMatrix, IsQubitSICProjector ρ₀ →
      (∀ x₁ x₂ y₁ y₂ : Fin 2, ∑ a : Fin 4, ρ₀ a x₁ y₁ * ρ₀ a x₂ y₂ =
        (2 / 3 : ℂ) * ((if x₁ = y₁ ∧ x₂ = y₂ then 1 else 0) +
          (if x₁ = y₂ ∧ x₂ = y₁ then 1 else 0))) ∧
      ∑ a : Fin 4, ρ₀ a = (2 : ℂ) • (1 : QubitMatrix) ∧
      (∀ X Y : QubitMatrix, ∑ a : Fin 4, Matrix.trace (ρ₀ a * X) * Matrix.trace (ρ₀ a * Y) =
        (2 / 3 : ℂ) * (Matrix.trace (X * Y) + Matrix.trace X * Matrix.trace Y)) ∧
      (∀ β γ : Fin 4, sicE ρ₀ β γ =
        if β = γ then (if β = 0 then 1 else (3 : ℂ)⁻¹) else 0) ∧
      (∀ β γ : Fin 4, sicAlpha ρ₀ β γ =
        if β = γ then (if β = 0 then 0 else (3 : ℂ)⁻¹) else 0)) ∧
    (∀ (ρ : Fin n → Fin 4 → QubitMatrix) (T : Finset (Fin n)) (β γ : PauliLabel n),
      ((4 : ℂ) ^ n)⁻¹ * ∑ a : PauliLabel n, ∑ b : PauliLabel n, sicSubsetKernel n T a b *
        Matrix.trace (productSIC ρ b * pauliN n β * productSIC ρ a * pauliN n γ) =
        ∏ i : Fin n, if i ∈ T then sicAlpha (ρ i) (β i) (γ i) else sicE (ρ i) (β i) (γ i)) ∧
    (∀ (ρ : Fin n → Fin 4 → QubitMatrix), (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
      ∀ (k : ℕ) (Λ : QubitMap n),
        kFidelity ρ k Λ = ∑ β : PauliLabel n, pauliTwirlWeight Λ β *
          ∑ T ∈ @Finset.filter _ (fun T : Finset (Fin n) => T.card ≤ k)
            (Classical.decPred _) Finset.univ,
            (-1 : ℂ) ^ T.card * (∏ i ∈ T, sicAlpha (ρ i) (β i) (β i)) *
              (∏ i ∈ Tᶜ, sicE (ρ i) (β i) (β i)) ∧
        kFidelity ρ k Λ = kFidelity ρ k (complexPauliTwirl Λ)) ∧
    (∀ (ρ₁ ρ₂ : Fin n → Fin 4 → QubitMatrix),
      (∀ i : Fin n, IsQubitSICProjector (ρ₁ i)) →
      (∀ i : Fin n, IsQubitSICProjector (ρ₂ i)) →
      ∀ (k : ℕ) (Λ : QubitMap n), kFidelity ρ₁ k Λ = kFidelity ρ₂ k Λ)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := ((h 1).2.2.1 0 0).2
  have hgood := ((qubit_sic_matrices_and_per_qubit_traces 1).2.2.1 0 0).2
  have heq := hgood.symm.trans hbad
  simp [rejected, realize] at heq
  norm_num at heq
theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩
def evidence : Registration arena
    (type_of% (@qubit_sic_matrices_and_per_qubit_traces)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qubit_sic_matrices_and_per_qubit_traces, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@qubit_sic_matrices_and_per_qubit_traces)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.SicTraces.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.SicTraces.evidence
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
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "fn", "arg", "body", "body", "arg", "arg", "fn", "arg",
        "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SicTraces
namespace AlternatingSum
abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix),
    (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
    ∀ (Λ : QubitMap n),
      kFidelity ρ k Λ = pauliWeightSum Λ 0 + (-1 : ℂ) ^ k *
        ∑ w ∈ Finset.Icc 1 (O.readout () () n),
          ((3 : ℂ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℂ)) * pauliWeightSum Λ w ∧
      (n ≤ k → kFidelity ρ k Λ = processFidelity Λ) ∧
      kFidelity ρ 0 Λ =
        ∑ β : PauliLabel n, (3 : ℂ)⁻¹ ^ hammingWeight β * pauliTwirlWeight Λ β ∧
      (Λ.IsCompletelyPositive →
        ((realKFidelity ρ k Λ : ℝ) : ℂ) = kFidelity ρ k Λ ∧
        realKFidelity ρ k Λ = realWeightSum Λ 0 + (-1 : ℝ) ^ k *
          ∑ w ∈ Finset.Icc 1 n,
            ((3 : ℝ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, hws0, _, _, hkf, _⟩ := pauliZ1_props
  have hr := (h 1 0 (canonicalSICFamily 1) (canonicalSICFamily_isQubitSICProjector 1) pauliZ1).1
  simp [rejected, realize, hws0, hkf] at hr
theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩
def evidence : Registration arena
    (type_of% (@kFidelity_eq_pauliWeight_alternating_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kFidelity_eq_pauliWeight_alternating_sum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@kFidelity_eq_pauliWeight_alternating_sum)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.AlternatingSum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.AlternatingSum.evidence
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
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg", "fn",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AlternatingSum
namespace TruncationBound
abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)
def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := sig
  Law O := ∀ (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix),
    (∀ i : Fin n, IsQubitSICProjector (ρ i)) →
    ∀ (Λ : QubitMap n), Λ.IsCompletelyPositive →
      (-1 : ℝ) ^ k * (realKFidelity ρ k Λ - realProcessFidelity Λ) =
        ∑ w ∈ Finset.Icc (k + 1) (O.readout () () n),
          ((3 : ℝ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w ∧
      0 ≤ ∑ w ∈ Finset.Icc (k + 1) n,
        ((3 : ℝ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w ∧
      (Odd k → realKFidelity ρ k Λ ≤ realProcessFidelity Λ) ∧
      (Even k → realProcessFidelity Λ ≤ realKFidelity ρ k Λ) ∧
      (∀ i j : ℕ, Odd j → Even i → realKFidelity ρ j Λ ≤ realKFidelity ρ i Λ) ∧
      ((realKFidelity ρ k Λ = realProcessFidelity Λ ↔
          ∀ w ∈ Finset.Icc (k + 1) n, realWeightSum Λ w = 0) ∧
        (realKFidelity ρ k Λ = realProcessFidelity Λ ↔
          ∀ β : PauliLabel n, k < hammingWeight β → realTwirlWeight Λ β = 0))
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hCP, _, _, _, _, hrpf0, _, hrkf⟩ := pauliZ1_props
  have hr := (h 1 0 (canonicalSICFamily 1)
    (canonicalSICFamily_isQubitSICProjector 1) pauliZ1 hCP).1
  simp [rejected, realize, hrpf0, hrkf] at hr
theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩
def evidence : Registration arena
    (type_of% (@cp_kFidelity_alternating_truncation_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cp_kFidelity_alternating_truncation_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cp_kFidelity_alternating_truncation_bound)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.TruncationBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight.TruncationBound.evidence
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
    owner := `D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TruncationBound
end
end Reg.D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
