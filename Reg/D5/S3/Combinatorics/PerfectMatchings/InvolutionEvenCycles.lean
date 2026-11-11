import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles
import Reg.Support.DependentFamily

/-! Dependent-family evidence for the rooted interlacing and reconstruction laws. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles

open _root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles
open _root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open _root_.D5.S3.Zeros.Convolution.PerfectMatchingCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Equiv

universe u
noncomputable section

abbrev signature : Signature where
  Params := Σ X : Type u, Fintype X × LinearOrder X
  State p := FixedPointFreeInvolution p.1 × FixedPointFreeInvolution p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI := p.2.1
    letI := p.2.2
    exact {q : Perm p.1 // (∀ x, q x ≠ x) ∧
      ∀ c ∈ q.cycleFactorsFinset, Even c.support.card}
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p st => by letI := p.2.1; letI := p.2.2; exact forward st)
  (fun e => nomatch e)

def swapped : Realization signature.{u} := realize signature
  (fun _ p st => by letI := p.2.1; letI := p.2.2; exact forward (st.2,st.1))
  (fun e => nomatch e)

private def s : FixedPointFreeInvolution (ULift.{u} (Fin 4)) :=
  ⟨swap ⟨0⟩ ⟨1⟩ * swap ⟨2⟩ ⟨3⟩, by
    constructor <;> (rintro ⟨x⟩; fin_cases x <;> decide)⟩

private def t : FixedPointFreeInvolution (ULift.{u} (Fin 4)) :=
  ⟨swap ⟨0⟩ ⟨3⟩ * swap ⟨1⟩ ⟨2⟩, by
    constructor <;> (rintro ⟨x⟩; fin_cases x <;> decide)⟩

private theorem ordered_ne : (t.{u},s.{u}) ≠ (s,t) := by decide

private theorem forward_ne : forward (t.{u},s.{u}) ≠ forward (s,t) := by
  intro h
  apply ordered_ne
  have he := congrArg recover h
  simpa only [(rooted_interlacing t s).1, (rooted_interlacing s t).1] using he

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 4), inferInstance, inferInstance⟩, (t,s), (s,t), ?_⟩
  exact forward_ne

namespace Interlacing

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X] [LinearOrder X]
      (s t : FixedPointFreeInvolution X),
    recover (R.readout () ⟨X, inferInstance, inferInstance⟩ (s,t)) = (s,t) ∧
    (∀ x y, (interlace s t).SameCycle x y ↔ Connected s.val t.val x y) ∧
    (∀ x, Connected s.val t.val x (componentRoot s t x) ∧
      ∀ y, Connected s.val t.val x y → componentRoot s t x ≤ y) ∧
    (∀ m, (∀ y, Connected s.val t.val m y → m ≤ y) → ∀ k : ℕ,
      (interlace s t ^ (2*k)) m = ((t.val*s.val)^k) m ∧
      (interlace s t ^ (2*k+1)) m = s.val (((t.val*s.val)^k) m)) ∧
    (∀ x, interlace s t x = (if firstPhase s t x then s.val x else t.val x) ∧
      (interlace s t)⁻¹ x = (if firstPhase s t x then t.val x else s.val x) ∧
      (cyclePhase (interlace s t) x ↔ firstPhase s t x))

private theorem swapped_invalid : ¬ arena.{u}.Law swapped := by
  intro h
  have hh := (h s.{u} t.{u}).1
  change recover (forward (t,s)) = (s,t) at hh
  rw [(rooted_interlacing t s).1] at hh
  exact ordered_ne hh

def registration : Registration arena.{u} (type_of% (@rooted_interlacing.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rooted_interlacing, swapped, swapped_invalid⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨swapped, ?_, rfl, swapped_invalid⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rooted_interlacing.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles.rooted_interlacing.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles.Interlacing.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p st => by letI := p.2.1; letI := p.2.2; exact forward st)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interlacing

namespace Reconstruction

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [Fintype X] [LinearOrder X]
      (q : {q : Perm X // (∀ x, q x ≠ x) ∧
        ∀ c ∈ q.cycleFactorsFinset, Even c.support.card}),
    R.readout () ⟨X, inferInstance, inferInstance⟩ (recover q) = q ∧ ∀ x,
      (recover q).1.val x = (if cyclePhase q.val x then q.val x else q.val⁻¹ x) ∧
      (recover q).2.val x = (if cyclePhase q.val x then q.val⁻¹ x else q.val x)

private theorem swapped_invalid : ¬ arena.{u}.Law swapped := by
  intro h
  have hh := (h (forward (s.{u},t.{u}))).1
  change forward ((recover (forward (s,t))).2, (recover (forward (s,t))).1) =
    forward (s,t) at hh
  rw [(rooted_interlacing s t).1] at hh
  exact forward_ne hh

def registration : Registration arena.{u} (type_of% (@rooted_reconstruction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rooted_reconstruction, swapped, swapped_invalid⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨swapped, ?_, rfl, swapped_invalid⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rooted_reconstruction.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles.rooted_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles.Reconstruction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p st => by letI := p.2.1; letI := p.2.2; exact forward st)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reconstruction

#print axioms Interlacing.registration
#print axioms Reconstruction.registration

end

end Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles
