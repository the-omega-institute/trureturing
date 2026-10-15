import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy
import Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy

open scoped ComplexOrder InnerProductSpace ENNReal
open QuantumLogEnergy
open Filter Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy (oneState one_trace one_entropy K)
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy

namespace Operators
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
    (rho sigma : Reference H) (n : ℕ),
    let eps : ℝ := ((n : ℝ) + 1)⁻¹
    let Lr := CFC.log (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) eps)
    let Ls := CFC.log (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) eps)
    IsStrictlyPositive (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) eps) ∧
    IsStrictlyPositive (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) eps) ∧
    (∀ x, ‖Lr x‖ ≤ ‖Lr‖ * ‖x‖) ∧ (∀ x, ‖Ls x‖ ≤ ‖Ls‖ * ‖x‖) ∧
    IsTraceClass ((Lr - Ls) * rho.1.1) ∧ IsTraceClass (rho.1.1 * (Lr - Ls)) ∧
    (R.readout ⟨()⟩ () (traceLogGrid rho sigma n)) =
      (trace (rho.1.1 * (Lr - Ls))
        (by simpa using (isTraceClass_mul_mul (A := 1) (B := Lr - Ls)
          (TraceClass.isTraceClass_coe rho.1)))).re ∧
    (R.readout ⟨()⟩ () (traceLogGrid rho sigma n)) = regularizedEnergy eps sigma.1.1 rho.1 -
      regularizedEnergy eps rho.1.1 rho.1

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.traceLogGrid_operators.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h oneState oneState 0).2.2.2.2.2.2.2
  have hz : traceLogGrid oneState.{u} oneState 0 = 0 := by
    simpa using (traceLogGrid_operators oneState oneState 0).2.2.2.2.2.2.2
  simpa [rejected, realize, hz] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.traceLogGrid_operators.{u})) where
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
    (@QuantumLogEnergy.traceLogGrid_operators.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Operators.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Operators.family
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
end Operators

namespace Characterization
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
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞),
    (R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS)) =
      spectralEnergy sigma rho.1 - spectralEntropy rho

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.finiteEntropyRelativeEntropy_eq_energy_tsub.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState oneState one_trace one_trace (by rw [one_entropy]; exact ENNReal.zero_ne_top)
  simpa [rejected, realize, finiteEntropyRelativeEntropy_eq_energy_tsub,
    spectralEnergy_self, one_entropy] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.finiteEntropyRelativeEntropy_eq_energy_tsub.{u})) where
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
    (@QuantumLogEnergy.finiteEntropyRelativeEntropy_eq_energy_tsub.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Characterization.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Characterization.family
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
end Characterization

namespace Branches
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
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞),
    (∀ hE : spectralEnergy sigma rho.1 ≠ ∞,
      (R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS)) =
        ENNReal.ofReal ((spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal) ∧
      ((R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS))).toReal =
        (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal ∧
      ‖rho.1 - sigma.1‖ ^ 2 / 4 ≤
        ((R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS))).toReal) ∧
    (spectralEnergy sigma rho.1 = ∞ → (R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS)) = ∞) ∧
    (¬ sigma.1.1.ker ≤ rho.1.1.ker → (R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS)) = ∞)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.finiteEntropyRelativeEntropy_branches.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := ((h oneState oneState one_trace one_trace
    (by rw [one_entropy]; exact ENNReal.zero_ne_top)).1
      (by rw [spectralEnergy_self, one_entropy]; exact ENNReal.zero_ne_top)).1
  simpa [rejected, realize, finiteEntropyRelativeEntropy_eq_energy_tsub,
    spectralEnergy_self, one_entropy] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.finiteEntropyRelativeEntropy_branches.{u})) where
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
    (@QuantumLogEnergy.finiteEntropyRelativeEntropy_branches.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Branches.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Branches.family
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
end Branches

namespace Spectral
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
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) (hE : spectralEnergy sigma rho.1 ≠ ∞)
    (d : SpectralResolution rho) (e : SpectralResolution sigma),
    let f := fun p : d.index × e.index => d.values p.1 *
      ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2 *
        (Real.log (d.values p.1) - Real.log (e.values p.2))
    Summable (fun p => |f p|) ∧
      (∑' p, f p) = (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal ∧
      (∑' i, ∑' j, f (i,j)) = ∑' p, f p ∧
      (R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS)) = ENNReal.ofReal (∑' p, f p) ∧
      ((R.readout ⟨()⟩ () (finiteEntropyRelativeEntropy rho sigma hr hs hS))).toReal = ∑' p, f p ∧
      (∀ i j, e.values j = 0 → d.values i * ‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2 = 0)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.finiteEntropyRelativeEntropy_spectral.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState oneState one_trace one_trace
    (by rw [one_entropy]; exact ENNReal.zero_ne_top)
    (by rw [spectralEnergy_self, one_entropy]; exact ENNReal.zero_ne_top)
    (nativeResolution oneState) (nativeResolution oneState)
  have hz := hh.2.1
  have he := hh.2.2.2.1
  rw [hz] at he
  simpa [rejected, realize, finiteEntropyRelativeEntropy_eq_energy_tsub,
    spectralEnergy_self, one_entropy] using he

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.finiteEntropyRelativeEntropy_spectral.{u})) where
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
    (@QuantumLogEnergy.finiteEntropyRelativeEntropy_spectral.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Spectral.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.Spectral.family
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
end Spectral



namespace ClosedFamily
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

def theoremLaw (Q : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A),
    let R : A → Reference H := fun r =>
      ⟨r.1, hp r.1 r.2, density_le_one r.1 (hp r.1 r.2) (ht r.1 r.2)⟩
    IsCompact A ∧ ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ (sigma : Reference H)
        (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1),
      sigma.1 ∈ A ∧
      (∀ r : A, (Q.readout ⟨()⟩ () (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2))) ≠ ∞ ∧
        ((Q.readout ⟨()⟩ () (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)))).toReal ≤
          realEntropy gamma + Real.log 2 ∧
        ‖r.1 - sigma.1‖ ^ 2 / 4 ≤
          ((Q.readout ⟨()⟩ () (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)))).toReal) ∧
      Continuous (fun r : A =>
        (Q.readout ⟨()⟩ () (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)))) ∧
      Continuous (fun r : A =>
        ((Q.readout ⟨()⟩ () (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)))).toReal)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.closedConvex_finiteEntropy_commonReference.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Set (TraceClass K) := {oneState.1}
  have hp : ∀ r ∈ A, 0 ≤ r.1 := by intro r hr; rw [Set.mem_singleton_iff.mp hr]; exact oneState.2.1
  have ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1 := by
    intro r hr; rw [Set.mem_singleton_iff.mp hr]; exact one_trace
  have hf : ∀ (r) (hr : r ∈ A), spectralEntropy
      (⟨r, hp r hr, density_le_one r (hp r hr) (ht r hr)⟩ : Reference K) ≠ ∞ := by
    intro r hr
    have he : (⟨r, hp r hr, density_le_one r (hp r hr) (ht r hr)⟩ : Reference K) = oneState :=
      Subtype.ext (Set.mem_singleton_iff.mp hr)
    rw [he, one_entropy]
    exact ENNReal.zero_ne_top
  obtain ⟨_, gamma, hg, _, sigma, hs, hsmem, hb, _, _⟩ := h
    (Set.singleton_nonempty _) isClosed_singleton (convex_singleton _) hp ht hf
    (continuousOn_singleton _ _)
  have hg' : gamma = oneState.1 := Set.mem_singleton_iff.mp hg
  have hs' : sigma = oneState := Subtype.ext (Set.mem_singleton_iff.mp hsmem)
  have hh := (hb (⟨oneState.1, rfl⟩ : A)).2.1
  have hr' : (⟨oneState.1, hp oneState.1 rfl,
      density_le_one oneState.1 (hp oneState.1 rfl) (ht oneState.1 rfl)⟩ : Reference K) =
      oneState := Subtype.ext rfl
  dsimp only at hh
  simp only [rejected, realize] at hh
  simp only [hr', hs', hg', finiteEntropyRelativeEntropy_eq_energy_tsub,
    spectralEnergy_self, one_entropy, tsub_self, zero_add, ENNReal.toReal_one,
    realEntropy_reference, ENNReal.toReal_zero] at hh
  have hl : Real.log 2 < 1 := by
    have hl := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  linarith

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.closedConvex_finiteEntropy_commonReference.{u})) where
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
    (@QuantumLogEnergy.closedConvex_finiteEntropy_commonReference.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.ClosedFamily.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy.ClosedFamily.family
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
end ClosedFamily
end Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy
