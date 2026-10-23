import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.PresburgerPatternGrowth
import Reg.Support.DependentFamily
import Mathlib.Tactic.Linarith

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Classical
open PresburgerPatternGrowth
open scoped BigOperators

namespace Reg.D5.S0.Computability.PresburgerPatternGrowth
noncomputable section
set_option autoImplicit false

namespace mem_traces
abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I × (I → Bool)
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @decide (p.2.2.2 ∈ @traces p.1 p.2.1 p.2.2.1 f) (Classical.propDecidable _))
  (fun e => nomatch e)
def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w} (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I] (f : X → I → Bool) (p : I → Bool),
    R.readout () ⟨X, I, inferInstance, p⟩ f = true ↔ ∃ x, f x = p

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  intro h
  have hh := (h (X := ULift.{u} Unit) (I := ULift.{w} Unit) (fun _ _ => false) (fun _ => false)).mpr ⟨⟨()⟩, rfl⟩
  exact Bool.noConfusion hh

def registration.{u,w} : Registration arena.{u,w}
    (∀ {X : Type u} {I : Type w} [Fintype I] (f : X → I → Bool) (p : I → Bool),
      p ∈ traces f ↔ ∃ x, f x = p) where
  actual := actual.{u,w}
  bridge := by simp [arena, actual, realize]
  variation := ⟨by intro X I _ f p; simpa [actual, realize] using (PresburgerPatternGrowth.mem_traces f p), rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, ULift.{w} Unit, inferInstance, fun _ => false⟩,
      (fun _ _ => false), (fun _ _ => true), ?_⟩
    simp [actual, realize, PresburgerPatternGrowth.mem_traces]
    intro h
    have hi := congrFun h ⟨()⟩
    exact Bool.noConfusion hi

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.mem_traces.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @decide (p.2.2.2 ∈ @traces p.1 p.2.1 p.2.2.1 f) (Classical.propDecidable _)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.mem_traces.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.mem_traces.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @decide (p.2.2.2 ∈ @traces p.1 p.2.1 p.2.2.1 f) (Classical.propDecidable _)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := true
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end mem_traces

namespace trace_card_factor

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w,v} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I] {K : Type v} [Fintype K]
    (f : X → I → Bool) (code : X → K) (decode : K → I → Bool)
    (_h : ∀ x, f x = decode (code x)),
    R.readout () ⟨X, I, inferInstance⟩ f ≤ Fintype.card K

theorem rejected_law.{u,w,v} : ¬ arena.{u,w,v}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit) (K := ULift.{v} Unit)
    (fun _ _ => false) (fun _ => ⟨()⟩) (fun _ _ => false) (fun _ => rfl)
  norm_num [rejected, realize] at hh

def registration.{u,w,v} : Registration arena.{u,w,v} (arena.{u,w,v}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_factor, rejected.{u,w}, rejected_law.{u,w,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w,v}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w,v} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_factor.{u,w,v}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_factor.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_factor.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w,v}⟩,
  objectArena := .source ⟨arena.{u,w,v}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w,v} ⟨registration.{u,w,v}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_factor

namespace trace_card_threshold

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I] (A : X → Int) (B : I → Int),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => decide (A x ≤ B i)) ≤ Fintype.card I + 1

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit) (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize] at hh

def registration.{u,w} : Registration arena.{u,w} (arena.{u,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_threshold, rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_threshold.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_threshold.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_threshold.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_threshold

namespace trace_card_dvd

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I]
    (d : Nat) (_hd : 0 < d) (A : X → Int) (B : I → Int),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => decide ((d : Int) ∣ A x + B i)) ≤ d

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit) 1 (by decide) (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize] at hh

def registration.{u,w} : Registration arena.{u,w} (arena.{u,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_dvd, rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_dvd.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_dvd.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_dvd.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_dvd

namespace trace_card_ndvd

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I]
    (d : Nat) (_hd : 0 < d) (A : X → Int) (B : I → Int),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => decide (¬ (d : Int) ∣ A x + B i)) ≤ d

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit) 1 (by decide) (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize] at hh

def registration.{u,w} : Registration arena.{u,w} (arena.{u,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_ndvd, rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_ndvd.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_ndvd.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_ndvd.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_ndvd

namespace trace_card_unary

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I] (op : Bool → Bool) (f : X → I → Bool),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => op (f x i)) ≤ (traces f).card

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit) id (fun _ _ => false)
  have hc : (traces (fun (_ : ULift.{u} Unit) (_ : ULift.{w} Unit) => false)).card ≤ 1 :=
    PresburgerPatternGrowth.trace_card_factor (X := ULift.{u} Unit) (I := ULift.{w} Unit) _ (fun _ : ULift.{u} Unit => ()) (fun _ _ => false) (fun _ => rfl)
  change 100 ≤ _ at hh
  exact (by omega : ¬ (100 : Nat) ≤ 1) (hh.trans hc)

def registration.{u,w} : Registration arena.{u,w} (arena.{u,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_unary, rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_unary.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_unary.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_unary.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_unary

namespace trace_card_binary

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {I : Type w} [Fintype I]
    (op : Bool → Bool → Bool) (f g : X → I → Bool),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => op (f x i) (g x i)) ≤ (traces f).card * (traces g).card

theorem rejected_law.{u,w} : ¬ arena.{u,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := h (X := ULift.{u} Unit) (I := ULift.{w} Unit)
    (fun a _ => a) (fun _ _ => false) (fun _ _ => false)
  have hc : (traces (fun (_ : ULift.{u} Unit) (_ : ULift.{w} Unit) => false)).card ≤ 1 :=
    PresburgerPatternGrowth.trace_card_factor (X := ULift.{u} Unit) (I := ULift.{w} Unit) _ (fun _ : ULift.{u} Unit => ()) (fun _ _ => false) (fun _ => rfl)
  change 100 ≤ _ at hh
  exact (by omega : ¬ (100 : Nat) ≤ 1) (hh.trans (Nat.mul_le_mul hc hc))

def registration.{u,w} : Registration arena.{u,w} (arena.{u,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.trace_card_binary, rejected.{u,w}, rejected_law.{u,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.trace_card_binary.{u,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.trace_card_binary.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.trace_card_binary.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,w}⟩,
  objectArena := .source ⟨arena.{u,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,w} ⟨registration.{u,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end trace_card_binary

namespace polynomial_trace_bound

abbrev signature.{u,w} : Signature where
  Params := Σ X : Type u, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w} : Realization signature.{u,w} := realize signature.{u,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,v,w} : Arena where
  signature := signature.{u,w}
  Law R := ∀ {X : Type u} {Y : Type v} {f : X → Y → Bool} {C s : Nat}
    (_h : Growth f C s),
    0 < C ∧ ∀ {I : Type w} [Fintype I] (sample : I → Y),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => f x (sample i)) ≤ C * (Fintype.card I + 1) ^ s

theorem rejected_law.{u,v,w} : ¬ arena.{u,v,w}.Law rejected.{u,w} := by
  classical
  intro h
  have hh := (h (X := ULift.{u} Unit) (Y := ULift.{v} Unit) (Growth.constant false)).2
    (I := ULift.{w} Unit) (fun _ => ⟨()⟩)
  norm_num [rejected, realize] at hh

def registration.{u,v,w} : Registration arena.{u,v,w} (arena.{u,v,w}.Law actual.{u,w}) where
  actual := actual.{u,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerPatternGrowth.polynomial_trace_bound, rejected.{u,w}, rejected_law.{u,v,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w}, ?_, ?_, rejected_law.{u,v,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{u} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{u} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,v,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerPatternGrowth.polynomial_trace_bound.{u,v,w}) (type_of% (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerPatternGrowth.polynomial_trace_bound.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerPatternGrowth.polynomial_trace_bound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w}⟩,
  objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w} ⟨registration.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerPatternGrowth
    definition := none
    coordinates := #[0, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end polynomial_trace_bound

end
end Reg.D5.S0.Computability.PresburgerPatternGrowth
