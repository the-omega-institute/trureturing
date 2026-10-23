import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity
import Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy

open scoped ComplexOrder ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy (oneState one_trace one_entropy K)
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity

namespace Weighted
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
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1),
    R.readout ⟨()⟩ () (ENNReal.ofReal a * spectralEntropy rho +
      ENNReal.ofReal b * spectralEntropy sigma +
      ENNReal.ofReal (a*b*‖rho.1-sigma.1‖^2/4)) ≤
      spectralEntropy (mixture rho sigma hr hs a b ha hb hab)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ rho sigma hr hs a b ha hb hab
  exact spectralEntropy_mixture rho sigma hr hs a b ha hb hab

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState oneState one_trace one_trace 1 0 zero_le_one le_rfl (by norm_num)
  have hm : mixture oneState oneState one_trace one_trace 1 0 zero_le_one le_rfl
      (by norm_num) = oneState := by
    apply Subtype.ext
    simp [mixture]
  rw [hm] at hh
  simpa [rejected, realize, one_entropy] using hh

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
    (@QuantumLogEnergy.spectralEntropy_mixture.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.Weighted.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.Weighted.family
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
#print axioms registration

end Weighted

namespace Strong
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
    {A : Set (TraceClass H)} (hA : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (h : rho ∈ A), spectralEntropy
      (⟨rho, hp rho h, density_le_one rho (hp rho h) (ht rho h)⟩ : Reference H) ≠ ∞),
    Convex ℝ A ∧ ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → ∀ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a+b=1 →
      R.readout ⟨()⟩ () (a • realEntropy x + b • realEntropy y +
        a*b*((1/2 : ℝ)/2*‖x-y‖^2)) ≤ realEntropy (a • x+b • y)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ A hA hp ht hf
  exact strongConcaveOn_realEntropy hA hp ht hf

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Set (TraceClass K) := {oneState.1}
  have hp : ∀ rho ∈ A, 0 ≤ rho.1 := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact oneState.2.1
  have ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact one_trace
  have hf : ∀ (rho) (hr : rho ∈ A), spectralEntropy
      (⟨rho, hp rho hr, density_le_one rho (hp rho hr) (ht rho hr)⟩ : Reference K) ≠ ∞ := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    change spectralEntropy oneState ≠ ∞
    rw [one_entropy]
    exact ENNReal.zero_ne_top
  have hh0 := (h (A := A) (convex_singleton _) hp ht hf).2
  have hh := hh0
    (show oneState.1 ∈ A from Set.mem_singleton _) (show oneState.1 ∈ A from Set.mem_singleton _)
    (a := 1) (b := 0) zero_le_one le_rfl (by norm_num)
  have he : realEntropy (oneState.{u}).1 = 0 := by
    simp [realEntropy, oneState.2, one_entropy]
  norm_num [rejected, realize, he] at hh

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
    (@QuantumLogEnergy.strongConcaveOn_realEntropy.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.Strong.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.Strong.family
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
#print axioms registration

end Strong


namespace RealEntropy
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
    (rho : Reference H),
    (R.readout ⟨()⟩ () (realEntropy rho.1)) = (spectralEntropy rho).toReal

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  exact @QuantumLogEnergy.realEntropy_reference.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h oneState
  simpa [rejected, realize, realEntropy_reference, one_entropy] using hh

def family : Registration arena.{u} (type_of% (@QuantumLogEnergy.realEntropy_reference.{u})) where
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
    (@QuantumLogEnergy.realEntropy_reference.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.RealEntropy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity.RealEntropy.family
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
end RealEntropy
end Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity
