import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexOrder InnerProductSpace ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy

abbrev K := EuclideanSpace ℂ (ULift.{u} Unit)

def oneState : Reference K :=
  ⟨TraceClass.ofOperator 1 (isTraceClass_of_finiteDimensional 1), zero_le_one, le_rfl⟩

theorem one_trace : (trace oneState.1.1 (TraceClass.isTraceClass_coe oneState.1)).re = 1 := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  rw [trace_eq_of_hilbertBasis _ b, ← trace_eq_sum_inner_hilbertBasis_of_finiteDimensional]
  change (LinearMap.trace ℂ K LinearMap.id).re = 1
  simp [K]

theorem one_entropy : spectralEntropy oneState = 0 := by
  let d := nativeResolution oneState
  have hv (i : d.index) : d.values i = 1 := by
    have he := congrArg (fun x : K => (⟪d.basis i, x⟫_ℂ).re) (d.eigen i)
    change (⟪d.basis i, d.basis i⟫_ℂ).re =
      (⟪d.basis i, (d.values i : ℂ) • d.basis i⟫_ℂ).re at he
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, d.basis.orthonormal.1 i] at he
    simpa using he.symm
  change (∑' i, ENNReal.ofReal (-d.values i * Real.log (d.values i))) = 0
  simp_rw [hv, Real.log_one, mul_zero, ENNReal.ofReal_zero, tsum_zero]

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ z => z + 1) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1),
    R.readout ⟨()⟩ () (spectralEntropy rho + ENNReal.ofReal (‖rho.1 - sigma.1‖ ^ 2 / 4)) ≤
      spectralEnergy sigma rho.1

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ rho sigma hr hs
  exact spectralEntropy_add_traceNorm_sq_le_energy rho sigma hr hs

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState oneState one_trace one_trace
  simpa [rejected, realize, spectralEnergy_self, one_entropy] using hh

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.spectralEntropy_add_traceNorm_sq_le_energy.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration


namespace Diagonal
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ z => z + 1) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Reference H) (d : SpectralResolution T) (v : H),
    HasSum (fun i => d.values i * ‖⟪v, d.basis i⟫_ℂ‖ ^ 2)
      (R.readout ⟨()⟩ () (⟪v, T.1.1 v⟫_ℂ).re)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.resolution_diagonal.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h oneState (nativeResolution oneState) 0).tsum_eq
  simpa [rejected, realize] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.resolution_diagonal.{u})) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.resolution_diagonal.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.Diagonal.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.Diagonal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Diagonal

namespace ResolutionEntropy
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ z => z + 1) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Reference H) (d : SpectralResolution T),
    (∑' i, ENNReal.ofReal (-d.values i * Real.log (d.values i))) = (R.readout ⟨()⟩ () (spectralEntropy T))

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.resolution_entropy.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState (nativeResolution oneState)
  rw [resolution_entropy, one_entropy] at hh
  simpa [rejected, realize, one_entropy] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.resolution_entropy.{u})) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.resolution_entropy.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.ResolutionEntropy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.ResolutionEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end ResolutionEntropy

namespace CrossEnergy
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ z => z + 1) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho sigma : Reference H)
    (d : SpectralResolution rho) (e : SpectralResolution sigma),
    (∑' i, ∑' j, (ENNReal.ofReal (d.values i) * singularLog (e.values j)) *
      ENNReal.ofReal (‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2)) =
        (R.readout ⟨()⟩ () (spectralEnergy sigma rho.1))

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.resolution_cross_energy.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState oneState (nativeResolution oneState) (nativeResolution oneState)
  rw [resolution_cross_energy, spectralEnergy_self, one_entropy] at hh
  simpa [rejected, realize, spectralEnergy_self, one_entropy] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.resolution_cross_energy.{u})) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.resolution_cross_energy.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.CrossEnergy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy.CrossEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end CrossEnergy
end Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
