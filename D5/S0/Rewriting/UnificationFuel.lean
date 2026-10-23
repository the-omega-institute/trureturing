/- GID: D5/S0/Rewriting/UnificationFuel
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact bounded simulation of the native unifier's recursive calls. -/

/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
The bounded evaluator follows the licensed unifier in NativeTermUnification.
-/

import D5.S0.Rewriting.NativeTermUnification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Lambda.UnificationFuel
open Strata.Util

abbrev Result := Except UnifyError Subst

/-- Erase the proof fields while retaining the complete native error or substitution. -/
def erase {cs : Constraints} {S : SubstInfo}
    (r : Except UnifyError (ValidSubstRelation cs S)) : Result :=
  r.map (fun s => s.newS.subst)

mutual
/-- Fuel bounds recursive call depth. Exhaustion is distinct from unification failure. -/
def one : Nat → Constraint → Subst → Option Result
  | 0, _, _ => none
  | fuel + 1, c, S =>
    let (t1,t2) := c
    if t1 == t2 then some (.ok S) else
    match t1,t2 with
    | .ftvar id, orig | orig, .ftvar id =>
        let ty := LMonoTy.subst S orig
        if .ftvar id == ty then some (.ok S)
        else if id ∈ ty.freeVars then some (.error (.FailedOccursCheck id ty c))
        else match S.find? id with
          | some sty => one fuel (sty,ty) S
          | none => some (.ok ((Subst.apply (HMap.single id ty) S).insert id ty))
    | .bitvec n, .bitvec m =>
        if n == m then some (.ok []) else some (.error (.ImpossibleToUnify c))
    | .tcons name args, .tcons name' args' =>
        if name == name' && args.length == args'.length then
          core fuel (args.zip args') S
        else some (.error (.ImpossibleToUnify c))
    | .bitvec _, .tcons _ _ | .tcons _ _, .bitvec _ =>
        some (.error (.ImpossibleToUnify c))
/-- Equations remain in their original order; errors retain their original equation. -/
def core : Nat → Constraints → Subst → Option Result
  | 0, _, _ => none
  | fuel + 1, [], S => some (.ok S)
  | fuel + 1, c :: rest, S =>
      match one fuel c S with
      | none => none
      | some (.error e) => some (.error (e.addOriginalConstraint c))
      | some (.ok S') => core fuel rest S'
end

private def OneExact (c : Constraint) (S : SubstInfo) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → one fuel c S.subst = some (erase (c.unifyOne S))

private def CoreExact (cs : Constraints) (S : SubstInfo) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → core fuel cs S.subst = some (erase (cs.unifyCore S))

set_option maxHeartbeats 2000000 in
private theorem exact_mutual :
    (∀ c S, OneExact c S) ∧ (∀ cs S, CoreExact cs S) := by
  apply Constraint.unifyOne.mutual_induct
    (motive1 := OneExact) (motive2 := CoreExact)
  · intro S t1 t2 hEq hSub
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hEq]
  · intro S id orig hne lty h1 h2 heq
    dsimp only [lty] at *
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne, heq]
  · intro S id orig hne lty h1 h2 hneq hoc
    dsimp only [lty] at *
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne, hneq, hoc]
  · intro S id orig hne lty h1 h2 hneq hnoc sty hfind ih
    dsimp only [lty] at *
    obtain ⟨b, hb⟩ := ih
    refine ⟨b + 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp only [one, erase, hne, Bool.false_eq_true, dite_false, dite_true, ite_false, ite_true, hneq, hnoc, hfind]
      rw [hb fuel (by omega)]
      split
      · rename_i sty' hs
        rw [hfind] at hs
        cases hs
        cases Constraint.unifyOne (sty, lty) S <;> rfl
      · rename_i hn
        rw [hfind] at hn
        contradiction
  · intro S id orig hne lty h1 h2 hneq hnoc hfind hwf happ new_subst h' newS hs1 hs2
    dsimp only [lty] at *
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp only [one, erase, hne, Bool.false_eq_true, dite_false, dite_true, ite_false, ite_true, hneq, hnoc, hfind]
      split
      · rename_i sty hs
        rw [hfind] at hs
        contradiction
      · rfl
  · intro S orig id hne hcontra lty h1 h2 heq
    dsimp only [lty] at *
    cases orig <;> try exact False.elim (hcontra _ hne rfl HEq.rfl)
    all_goals
      refine ⟨1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraint.unifyOne.eq_def]
        simp [one, erase, Except.map, hne, heq]
  · intro S orig id hne hcontra lty h1 h2 hneq hoc
    dsimp only [lty] at *
    cases orig <;> try exact False.elim (hcontra _ hne rfl HEq.rfl)
    all_goals
      refine ⟨1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraint.unifyOne.eq_def]
        simp [one, erase, Except.map, hne, hneq, hoc]
  · intro S orig id hne hcontra lty h1 h2 hneq hnoc sty hfind ih
    dsimp only [lty] at *
    cases orig <;> try exact False.elim (hcontra _ hne rfl HEq.rfl)
    all_goals
      obtain ⟨b, hb⟩ := ih
      refine ⟨b + 1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraint.unifyOne.eq_def]
        simp only [one, erase, hne, Bool.false_eq_true, dite_false, dite_true, ite_false, ite_true, hneq, hnoc, hfind]
        rw [hb fuel (by omega)]
        split
        · rename_i sty' hs
          rw [hfind] at hs
          cases hs
          cases Constraint.unifyOne (sty, lty) S <;> rfl
        · rename_i hn
          rw [hfind] at hn
          contradiction
  · intro S orig id hne hcontra lty h1 h2 hneq hnoc hfind hwf happ new_subst h' newS hs1 hs2
    dsimp only [lty] at *
    cases orig <;> try exact False.elim (hcontra _ hne rfl HEq.rfl)
    all_goals
      refine ⟨1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraint.unifyOne.eq_def]
        simp only [one, erase, hne, Bool.false_eq_true, dite_false, dite_true, ite_false, ite_true, hneq, hnoc, hfind]
        split
        · rename_i sty hs
          rw [hfind] at hs
          contradiction
        · rfl
  · intro S n1 n2 hne heq
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne, heq]
  · intro S n1 n2 hne hneq
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne, hneq]
  · intro S name1 args1 name2 args2 hne heq new_constraints ih
    obtain ⟨b, hb⟩ := ih
    refine ⟨b + 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp only [one, erase, hne, Bool.false_eq_true, dite_false, dite_true, ite_false, ite_true, heq]
      rw [hb fuel (by omega)]
      cases ccall : Constraints.unifyCore (args1.zip args2) S <;>
        simp +instances [erase, ccall, Except.map, Bind.bind, Except.bind]
  · intro S name1 args1 name2 args2 hne hneq
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne, hneq]
  · intro S size name args hne
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne]
  · intro S name args size hne
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraint.unifyOne.eq_def]
      simp [one, erase, Except.map, hne]
  · intro S
    refine ⟨1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Constraints.unifyCore.eq_def]
      simp [core, erase, Except.map]
  · intro S c rest ihOne ihCore
    obtain ⟨b1, hb1⟩ := ihOne
    cases hcall : c.unifyOne S with
    | error e =>
      refine ⟨b1 + 1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraints.unifyCore.eq_def]
        simp [core, hb1 fuel (by omega), erase, hcall, Except.map, Except.mapError,
          Bind.bind, Except.bind]
    | ok rel =>
      obtain ⟨b2, hb2⟩ := ihCore rel
      refine ⟨max b1 b2 + 1, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [Constraints.unifyCore.eq_def]
        simp [core, hb1 fuel (by omega), erase, hcall, Except.map, Except.mapError,
          Bind.bind, Except.bind, hb2 fuel (by omega)]
        cases Constraints.unifyCore rest rel.newS <;> rfl
/-- Every well-formed substitution and finite equation list has a finite exact
    fuel simulation, including both failure and success with the original keys. -/
private theorem finite_exact_run (cs : Constraints) (S : SubstInfo) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      core fuel cs S.subst = some ((cs.unify S).map SubstInfo.subst) := by
  obtain ⟨bound,h⟩ := exact_mutual.2 cs S
  refine ⟨bound, ?_⟩
  intro fuel hf
  have he := h fuel hf
  cases hcore : cs.unifyCore S <;> simpa [erase, Constraints.unify, Except.bind, Except.map, Bind.bind, hcore] using he

private theorem fuel_monotone (fuel : Nat) :
    (∀ (c : Constraint) (S : Subst) (r : Result), one fuel c S = some r →
      ∀ more, fuel ≤ more → one more c S = some r) ∧
    (∀ (cs : Constraints) (S : Subst) (r : Result), core fuel cs S = some r →
      ∀ more, fuel ≤ more → core more cs S = some r) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp_all only [one, core, reduceCtorEq]
  | succ fuel ih =>
    constructor
    · intro c S r h more hm
      cases more with
      | zero => omega
      | succ more =>
        rcases c with ⟨t1,t2⟩
        cases t1 <;> cases t2 <;> simp only [one] at h ⊢
        all_goals
          repeat first
            | split at h <;> try simp_all only [if_pos, if_neg, ite_false, ite_true, reduceCtorEq]
            | exact h
            | exact ih.1 _ _ _ h more (by omega)
            | exact ih.2 _ _ _ h more (by omega)
    · intro cs S r h more hm
      cases more with
      | zero => omega
      | succ more =>
        cases cs with
        | nil => simpa only [core] using h
        | cons c rest =>
          simp only [core] at h ⊢
          cases ho : one fuel c S with
          | none => simp only [ho, reduceCtorEq] at h
          | some out =>
            have ho' := ih.1 c S out ho more (by omega)
            rw [ho']
            cases out with
            | error e => simpa only [ho] using h
            | ok S' =>
              simp only [ho] at h
              exact ih.2 rest S' r h more (by omega)

/-- Search consumes the finite evaluator; unification failure is a finished result. -/
def run (cs : Constraints) (S : SubstInfo) : Result :=
  let h : ∃ fuel, (core fuel cs S.subst).isSome := by
    obtain ⟨b, hb⟩ := finite_exact_run cs S
    exact ⟨b, by rw [hb b (Nat.le_refl b)]; rfl⟩
  (core (Nat.find h) cs S.subst).getD (.ok S.subst)

/-- Bounded executions stabilize to the exact native result, every finished
execution is already exact, and the assembled terminating search returns it. -/
theorem exact_fuel_simulation (cs : Constraints) (S : SubstInfo) :
    (∃ bound, ∀ fuel, bound ≤ fuel →
      core fuel cs S.subst = some ((cs.unify S).map SubstInfo.subst)) ∧
    (∀ fuel r, core fuel cs S.subst = some r →
      r = (cs.unify S).map SubstInfo.subst) ∧
    run cs S = (cs.unify S).map SubstInfo.subst := by
  have hb := finite_exact_run cs S
  have hs : ∀ fuel r, core fuel cs S.subst = some r →
      r = (cs.unify S).map SubstInfo.subst := by
    intro fuel r hr
    obtain ⟨b, hb⟩ := hb
    have hm := (fuel_monotone fuel).2 cs S.subst r hr (max b fuel) (by omega)
    rw [hb (max b fuel) (by omega)] at hm
    exact (Option.some.inj hm).symm
  refine ⟨hb, hs, ?_⟩
  let h : ∃ fuel, (core fuel cs S.subst).isSome := by
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, by rw [hb b (Nat.le_refl b)]; rfl⟩
  change (core (Nat.find h) cs S.subst).getD (.ok S.subst) = _
  cases he : core (Nat.find h) cs S.subst with
  | none => simpa [he] using Nat.find_spec h
  | some r => simpa only [Option.getD_some] using hs _ r he

end Lambda.UnificationFuel
