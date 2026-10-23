import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.PresburgerFiniteFamilies
import Reg.Support.DependentFamily
import Mathlib.Tactic.Linarith

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Classical
open PresburgerPatternGrowth
open PresburgerFiniteFamilies
open scoped BigOperators

namespace Reg.D5.S0.Computability.PresburgerFiniteFamilies
noncomputable section
set_option autoImplicit false

namespace trace_card_dependent_product

abbrev signature.{v,z} : Signature where
  Params := Σ X : Type v, Σ I : Type z, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{v,z} : Realization signature.{v,z} := realize signature.{v,z}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{v,z} : Realization signature.{v,z} := realize signature.{v,z}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,v,w,z} : Arena where
  signature := signature.{v,z}
  Law R := ∀ {T : Type u} [Fintype T] {X : Type v} {Y : T → Type w} {I : Type z} [Fintype I]
    (f : (t : T) → X → Y t → Bool) (sample : I → Sigma Y),
    R.readout () ⟨X, I, inferInstance⟩ (fun x i => f (sample i).1 x (sample i).2) ≤
      ∏ t, (traces (fun x (i : {i : I // (sample i).1 = t}) =>
        f t x (cast (congrArg Y i.2) (sample i.1).2))).card

theorem rejected_law.{u,v,w,z} : ¬ arena.{u,v,w,z}.Law rejected.{v,z} := by
  classical
  intro h
  have hh := h (T := ULift.{u} Unit) (X := ULift.{v} Unit)
    (Y := fun _ => ULift.{w} Unit) (I := ULift.{z} Empty)
    (fun _ _ _ => false) (fun i => nomatch i.down)
  change 100 ≤ _ at hh
  refine (by omega : ¬ (100 : Nat) ≤ 1) (hh.trans ?_)
  calc
    _ ≤ ∏ _t : ULift.{u} Unit, (1 : Nat) := by
      apply Finset.prod_le_prod'
      intro t ht
      exact (Finset.card_le_univ _).trans_eq (by simp)
    _ = 1 := by simp

def registration.{u,v,w,z} : Registration arena.{u,v,w,z} (arena.{u,v,w,z}.Law actual.{v,z}) where
  actual := actual.{v,z}
  bridge := Iff.rfl
  variation := ⟨PresburgerFiniteFamilies.trace_card_dependent_product, rejected.{v,z}, rejected_law.{u,v,w,z}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{v,z}, ?_, ?_, rejected_law.{u,v,w,z}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} Bool, ULift.{z} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{v} Bool) (_ : ULift.{z} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{v} Bool) (_ : ULift.{z} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{v} Bool) (_ : ULift.{z} Unit) => false)).card ≠
      (traces (fun (b : ULift.{v} Bool) (_ : ULift.{z} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,v,w,z} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerFiniteFamilies.trace_card_dependent_product.{u,v,w,z}) (type_of% (realize signature.{v,z} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerFiniteFamilies.trace_card_dependent_product.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerFiniteFamilies.trace_card_dependent_product.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w,z}⟩,
  objectArena := .source ⟨arena.{u,v,w,z}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w,z} ⟨registration.{u,v,w,z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{v,z} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerFiniteFamilies
    definition := none
    coordinates := #[2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
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
end trace_card_dependent_product

namespace trace_card_chart_sum

abbrev signature.{u,v,w} : Signature where
  Params := Σ X : Type max u v, Σ I : Type w, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,v,w} : Realization signature.{u,v,w} := realize signature.{u,v,w}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,v,w} : Realization signature.{u,v,w} := realize signature.{u,v,w}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,v,w} : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {K : Type u} [Fintype K] {X : K → Type v} {I : Type w} [Fintype I]
    (f : (k : K) → X k → I → Bool),
    R.readout () ⟨Sigma X, I, inferInstance⟩ (fun x i => f x.1 x.2 i) ≤
      ∑ k, (traces (f k)).card

theorem rejected_law.{u,v,w} : ¬ arena.{u,v,w}.Law rejected.{u,v,w} := by
  classical
  intro h
  have hh := h (K := ULift.{u} Unit) (X := fun _ => ULift.{v} Unit) (I := ULift.{w} Unit)
    (fun _ _ _ => false)
  have hc : (traces (fun (_ : ULift.{v} Unit) (_ : ULift.{w} Unit) => false)).card ≤ 1 :=
    PresburgerPatternGrowth.trace_card_factor _ (fun _ => ()) (fun _ _ => false) (fun _ => rfl)
  change 100 ≤ _ at hh
  have hb : (100 : Nat) ≤ 1 := hh.trans (by simpa using hc)
  omega

def registration.{u,v,w} : Registration arena.{u,v,w} (arena.{u,v,w}.Law actual.{u,v,w}) where
  actual := actual.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨PresburgerFiniteFamilies.trace_card_chart_sum, rejected.{u,v,w}, rejected_law.{u,v,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,v,w}, ?_, ?_, rejected_law.{u,v,w}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{max u v} Bool, ULift.{w} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{max u v} Bool) (_ : ULift.{w} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{max u v} Bool) (_ : ULift.{w} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{max u v} Bool) (_ : ULift.{w} Unit) => false)).card ≠
      (traces (fun (b : ULift.{max u v} Bool) (_ : ULift.{w} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,v,w} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerFiniteFamilies.trace_card_chart_sum.{u,v,w}) (type_of% (realize signature.{u,v,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerFiniteFamilies.trace_card_chart_sum.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerFiniteFamilies.trace_card_chart_sum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w}⟩,
  objectArena := .source ⟨arena.{u,v,w}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w} ⟨registration.{u,v,w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,v,w} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerFiniteFamilies
    definition := none
    coordinates := #[0, 2, 3],
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
end trace_card_chart_sum

namespace finite_family_polynomial_bound

abbrev signature.{u,w,r} : Signature where
  Params := Σ X : Type max u w, Σ I : Type r, Fintype I
  State p := p.1 → p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,w,r} : Realization signature.{u,w,r} := realize signature.{u,w,r}
  (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)

def rejected.{u,w,r} : Realization signature.{u,w,r} := realize signature.{u,w,r}
  (fun _ _ _ => 100) (fun e => nomatch e)

abbrev arena.{u,v,w,z,r} : Arena where
  signature := signature.{u,w,r}
  Law R := ∀ {K : Type u} {T : Type v} [Fintype K] [Fintype T] {X : K → Type w} {Y : T → Type z}
    (f : (k : K) → (t : T) → X k → Y t → Bool)
    (C s : K → T → Nat) (_h : ∀ k t, Growth (f k t) (C k t) (s k t)),
    0 < (∑ k, ∏ t, C k t) + 1 ∧
    ∀ {I : Type r} [Fintype I] (sample : I → Sigma Y),
    R.readout () ⟨Sigma X, I, inferInstance⟩ (fun x i => joint f x (sample i)) ≤
      ((∑ k, ∏ t, C k t) + 1) * (Fintype.card I + 1) ^ (∑ k, ∑ t, s k t)

theorem rejected_law.{u,v,w,z,r} : ¬ arena.{u,v,w,z,r}.Law rejected.{u,w,r} := by
  classical
  intro h
  have hh := (h (K := ULift.{u} Unit) (T := ULift.{v} Unit)
    (X := fun _ => ULift.{w} Unit) (Y := fun _ => ULift.{z} Unit)
    (fun _ _ _ _ => false) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => Growth.constant false)).2
    (I := ULift.{r} Unit) (fun _ => ⟨⟨()⟩, ⟨()⟩⟩)
  norm_num [rejected, realize] at hh

def registration.{u,v,w,z,r} : Registration arena.{u,v,w,z,r} (arena.{u,v,w,z,r}.Law actual.{u,w,r}) where
  actual := actual.{u,w,r}
  bridge := Iff.rfl
  variation := ⟨PresburgerFiniteFamilies.finite_family_polynomial_bound, rejected.{u,w,r}, rejected_law.{u,v,w,z,r}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,w,r}, ?_, ?_, rejected_law.{u,v,w,z,r}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{max u w} Bool, ULift.{r} Unit, inferInstance⟩,
      (fun _ _ => false), (fun b _ => b.down), ?_⟩
    have hc : traces (fun (_ : ULift.{max u w} Bool) (_ : ULift.{r} Unit) => false) =
        {fun _ => false} := by
      ext p
      simp only [mem_traces, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx⟩; exact hx.symm
      · intro hp; exact ⟨⟨false⟩, hp.symm⟩
    have hv : traces (fun (b : ULift.{max u w} Bool) (_ : ULift.{r} Unit) => b.down) =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro p
      exact (mem_traces _ _).mpr ⟨⟨p ⟨()⟩⟩, by funext j; congr 1⟩
    change (traces (fun (_ : ULift.{max u w} Bool) (_ : ULift.{r} Unit) => false)).card ≠
      (traces (fun (b : ULift.{max u w} Bool) (_ : ULift.{r} Unit) => b.down)).card
    rw [hc, hv]
    simp

noncomputable def registration_1.{u,v,w,z,r} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerFiniteFamilies.finite_family_polynomial_bound.{u,v,w,z,r}) (type_of% (realize signature.{u,w,r} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerFiniteFamilies.finite_family_polynomial_bound.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerFiniteFamilies.finite_family_polynomial_bound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w,z,r}⟩,
  objectArena := .source ⟨arena.{u,v,w,z,r}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w,z,r} ⟨registration.{u,v,w,z,r}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u,w,r} (fun _ p f => @Finset.card _ (@traces p.1 p.2.1 p.2.2 f)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerFiniteFamilies
    definition := none
    coordinates := #[0, 4, 10],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
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
end finite_family_polynomial_bound

namespace finite_exponential_domination
abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ C s : Nat, ∃ n : Nat, C * (n + 1) ^ s < R.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := h 0 0
  exact Nat.not_lt_zero _ hn

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨PresburgerFiniteFamilies.finite_exponential_domination, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PresburgerFiniteFamilies.finite_exponential_domination) (type_of% (realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e))) Unit Unit := {
  unitName := `PresburgerFiniteFamilies.finite_exponential_domination.__information_unit,
  realizationName := `Reg.D5.S0.Computability.PresburgerFiniteFamilies.finite_exponential_domination.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.PresburgerFiniteFamilies
    definition := none
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end finite_exponential_domination

end
end Reg.D5.S0.Computability.PresburgerFiniteFamilies
