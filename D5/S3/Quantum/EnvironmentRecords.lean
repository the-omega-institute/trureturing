/- GID: D5/S3/Quantum/EnvironmentRecords
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive finite record decoherence and its selected fixed algebra. -/

import D5.S3.Quantum.PointerBasis

namespace D5.S3.Quantum.EnvironmentRecords

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open scoped BigOperators

/-- A two-component environment record vector for each system address. -/
abbrev EnvironmentRecord := Fin 2 -> Fin 2 -> ℂ

/-- The density matrix of a qubit together with its two-component environment. -/
abbrev JointQubitEnvironmentMatrix :=
  Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The Gram overlap between the environment records written by two addresses. -/
def recordOverlap (record : EnvironmentRecord) (i j : Fin 2) : ℂ :=
  ∑ a, record i a * star (record j a)

/-- The joint state after the address-controlled environment record interaction. -/
def controlledRecordJointState (record : EnvironmentRecord) (rho : QubitMatrix) :
    JointQubitEnvironmentMatrix :=
  fun ia jb => record ia.1 ia.2 * star (record jb.1 jb.2) * rho ia.1 jb.1

/-- Trace a two-component environment out of a joint density matrix. -/
def traceEnvironment (joint : JointQubitEnvironmentMatrix) : QubitMatrix :=
  fun i j => ∑ a, joint (i, a) (j, a)

/-- The system channel selected directly by an environment record rule. -/
def recordChannel (record : EnvironmentRecord) (rho : QubitMatrix) : QubitMatrix :=
  fun i j => recordOverlap record i j * rho i j

/-- Tracing the environment of any controlled record gives its record channel. -/
theorem trace_environment_controlled_record_eq_record_channel
    (record : EnvironmentRecord) (rho : QubitMatrix) :
    traceEnvironment (controlledRecordJointState record rho) = recordChannel record rho := by
  ext i j
  change (∑ a, record i a * star (record j a) * rho i j) =
    recordOverlap record i j * rho i j
  rw [← Finset.sum_mul]
  rfl

/-- A controlled environment record with constant off-diagonal overlap induces
the repository's phase-damping channel after tracing out the environment. -/
theorem trace_environment_controlled_record_eq_phase_damping
    (record : EnvironmentRecord) (c : DampingCoefficient) (rho : QubitMatrix)
    (hGram : ∀ i j, recordOverlap record i j =
      if i = j then 1 else ((c : ℝ) : ℂ)) :
    traceEnvironment (controlledRecordJointState record rho) = phaseDamping c rho := by
  rw [trace_environment_controlled_record_eq_record_channel]
  ext i j
  change recordOverlap record i j * rho i j = _
  rw [hGram]
  by_cases h : i = j <;> simp [phaseDamping, h]

/-- The fixed algebra of a record channel contains exactly the matrix entries
between environment records with unit overlap. -/
theorem record_channel_fixed_iff_selected_blocks
    (record : EnvironmentRecord) (rho : QubitMatrix) :
    recordChannel record rho = rho ↔
      ∀ i j, recordOverlap record i j ≠ 1 -> rho i j = 0 := by
  constructor
  · intro hFixed i j hOverlap
    have hEntry := congrFun (congrFun hFixed i) j
    have hProduct : (recordOverlap record i j - 1) * rho i j = 0 := by
      calc
        (recordOverlap record i j - 1) * rho i j =
            recordOverlap record i j * rho i j - rho i j := by ring
        _ = 0 := sub_eq_zero.mpr hEntry
    exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr hOverlap)
  · intro hSelected
    funext i j
    by_cases hOverlap : recordOverlap record i j = 1
    · simp [recordChannel, hOverlap]
    · simp [recordChannel, hSelected i j hOverlap]

end D5.S3.Quantum.EnvironmentRecords
