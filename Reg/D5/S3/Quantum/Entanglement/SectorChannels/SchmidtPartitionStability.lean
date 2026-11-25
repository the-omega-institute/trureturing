import D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Registration for the exact finite Schmidt partition readout. -/

set_option autoImplicit false

open scoped BigOperators
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
open _root_.D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
open RTMajorizationRound RoundingEnvelope RTPartitionEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => (m : ℕ) → (ℕ → ℝ) → (Fin (m + 1) → ℝ) → ℝ)

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => readPartition n) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    let observed := R.readout () () n
    ∀ (m : ℕ) (s : ℕ → ℝ) (w : Fin (m + 1) → ℝ),
    let D := observed m s w
    ∀ (tag : ℕ → Fin (m + 1)) (l : ℕ → ℝ) (eta E : ℝ),
      E ≤ 2 →
      preSum (fun i => (s i)^2) n = 1 →
      preSum (fun i => (l i)^2) n = 1 - eta →
      (∀ k ≤ n, preSum l k ≤ preSum s k) →
      (∀ i < n, 0 ≤ l i) →
      (∀ i j, i ≤ j → j < n → l j ≤ l i) →
      (∑ a : Fin (m + 1), w a = 1) →
      (1 - E / 2 ≤ ∑ a : Fin (m + 1), min (w a) (grouped n tag l a)) →
      (D ≤ 4 / 3 → lower D ≤ E) ∧ (4 / 3 ≤ D → D - 2 / 3 ≤ E) ∧
      (E ≤ 2 / 3 → D ≤ curve E) ∧
      ∀ T : ℝ, 2 ≤ T → 2 / T ≤ D → 2 / (T * (T + 1)) < E

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 (fun _ => 1) (fun _ => 1)
    (fun _ => 0) (fun _ => 1) 0 0 (by norm_num)
    (by norm_num [preSum]) (by norm_num [preSum])
    (by intros; exact le_rfl) (by intros; norm_num) (by intros; exact le_rfl)
    (by norm_num)
    (by
      change (1 : ℝ) - 0 / 2 ≤
        ∑ a : Fin 1, min 1 (grouped 1 (fun _ => 0) (fun _ => 1) a)
      rw [Fin.sum_univ_one]
      norm_num [grouped, preSum])
  have hf := hh.2.2.1 (by norm_num)
  change (2 : ℝ) ≤ curve 0 at hf
  norm_num [curve] at hf

private theorem singleton_readout (n : ℕ) :
    readPartition n 0 (fun _ => 1) (fun _ => 1) = |(1 : ℝ) - n| := by
  unfold readPartition partitionDistance
  have h (f : Fin n → Fin 1) :
      partitionError n (fun _ => 1) (fun _ => 1) f = |(1 : ℝ) - n| := by
    unfold partitionError
    simp only [Fin.sum_univ_one]
    have hf : ∀ i : Fin n, f i = 0 := fun i => Subsingleton.elim _ _
    simp [hf]
  apply le_antisymm
  · have hle := Finset.inf'_le
      (partitionError n (fun _ => 1) (fun _ : Fin 1 => 1))
      (Finset.mem_univ (fun _ : Fin n => (0 : Fin 1)))
    rw [h] at hle
    exact hle
  · apply Finset.le_inf'
    intro f _
    rw [h]

private theorem actual_dependence : actual.readout () () 0 ≠ actual.readout () () 1 := by
  intro h
  have he := congrFun (congrFun (congrFun h 0) (fun _ => 1)) (fun _ => 1)
  change readPartition 0 0 (fun _ => 1) (fun _ => 1) =
    readPartition 1 0 (fun _ => 1) (fun _ => 1) at he
  rw [singleton_readout,singleton_readout] at he
  norm_num at he

noncomputable def family : Registration arena (type_of% @sorted_partition_inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sorted_partition_inverse,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, actual_dependence⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@sorted_partition_inverse) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability.sorted_partition_inverse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
      owner := `D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
      definition := none
      coordinates := #[]
      readouts := #[{
        path := #["body","value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.SchmidtPartitionStability
