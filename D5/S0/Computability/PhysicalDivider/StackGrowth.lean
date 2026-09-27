/- GID: D5/S0/Computability/PhysicalDivider/StackGrowth
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stack occupancy growth under the actual stack-machine transition. -/

/-
Source: szymtor/RAM-TM, commit 6fe5a3d94f6c2da46cc2c5ab98cd36997b130737.
Authors: Szymon Toruńczyk and Codex 5.6 (upstream manifest).
Apache-2.0; full license, source mapping and retirement condition:
Library/Computability/ramtm2026divider.md.
Original declaration names and proof derivations are retained. Import routing,
definitional unfolding and local inlining adapt the source to the current pin.
These symbolic program and word laws contain no certified finite instance,
bounded enumeration, certificate checker or conditional numerical reduction.
-/

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax51Proofs.RamToTM

open Turing TM2

-- Source: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:7-14.
def stmtPushCount {K Λ σ : Type} {Γ : K → Type} :
    TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => stmtPushCount q + 1
  | .peek _ _ q => stmtPushCount q
  | .pop _ _ q => stmtPushCount q
  | .load _ q => stmtPushCount q
  | .branch _ q₁ q₂ => max (stmtPushCount q₁) (stmtPushCount q₂)
  | .goto _ | .halt => 0

-- Source: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:16-48.
theorem stepAux_stack_length_le {K Λ σ : Type} {Γ : K → Type}
    [DecidableEq K] (q : TM2.Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) (stack : K) :
    ((TM2.stepAux q state tapes).stk stack).length ≤
      (tapes stack).length + stmtPushCount q := by
  induction q generalizing state tapes with
  | push k f q ih =>
      simp only [TM2.stepAux, stmtPushCount]
      have h := ih state (Function.update tapes k (f state :: tapes k))
      by_cases hk : stack = k
      · subst k
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [hk] at h
        exact h.trans (by omega)
  | peek k f q ih =>
      simpa [stmtPushCount] using ih (f state (tapes k).head?) tapes
  | pop k f q ih =>
      simp only [TM2.stepAux, stmtPushCount]
      have h := ih (f state (tapes k).head?)
        (Function.update tapes k (tapes k).tail)
      by_cases hk : stack = k
      · subst k
        simp at h
        exact h.trans (by simp)
      · simpa [hk] using h
  | load f q ih => simpa [stmtPushCount] using ih (f state) tapes
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, stmtPushCount]
      cases h : f state
      · exact (ih₂ state tapes).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · exact (ih₁ state tapes).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [stmtPushCount]
  | halt => simp [stmtPushCount]

-- Source: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:50-52.
def programPushBound {K Λ σ : Type} {Γ : K → Type}
    [Fintype Λ] (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  ∑ label : Λ, stmtPushCount (program label)

-- Source: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:79-112.
theorem iterate_stack_length_le {K Λ σ : Type} {Γ : K → Type}
    [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (program : Λ → TM2.Stmt Γ Λ σ) (n : Nat)
    (c d : TM2.Cfg Γ Λ σ)
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (stack : K) :
    (d.stk stack).length ≤
      (c.stk stack).length + n * programPushBound program := by
  -- Original proof: proofs/Lax51Proofs/RamToTM/StatementEmbedding.lean:120.
  have iterate_optionBind_none {α : Type} (f : α → Option α) (n : ℕ) :
      ((fun o : Option α => o.bind f)^[n]) none = none := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply]
        exact ih
  -- Original proof: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:63.
  have step_stack_length_le {K Λ σ : Type} {Γ : K → Type}
      [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
      (program : Λ → TM2.Stmt Γ Λ σ) (c d : TM2.Cfg Γ Λ σ)
      (hstep : TM2.step program c = some d) (stack : K) :
      (d.stk stack).length ≤
        (c.stk stack).length + programPushBound program := by
    -- Original proof: proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:54.
    have stmtPushCount_le_programPushBound {K Λ σ : Type} {Γ : K → Type}
        [Fintype Λ] [DecidableEq Λ]
        (program : Λ → TM2.Stmt Γ Λ σ) (label : Λ) :
        stmtPushCount (program label) ≤ programPushBound program := by
      unfold programPushBound
      exact Finset.single_le_sum
        (f := fun label => stmtPushCount (program label))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)
    rcases c with ⟨label, state, tapes⟩
    cases label with
    | none => simp [TM2.step] at hstep
    | some label =>
        simp only [TM2.step, Option.some.injEq] at hstep
        subst d
        exact (stepAux_stack_length_le (program label) state tapes stack).trans
          (Nat.add_le_add_left
            (stmtPushCount_le_programPushBound program label) _)
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
      subst d
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs : TM2.step program c with
      | none =>
          simp only [hs, Option.bind_none] at hrun
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs, Option.bind_some] at hrun
          have hfirst := step_stack_length_le program c c' hs stack
          have hrest := ih c' hrun
          calc
            (d.stk stack).length
                ≤ (c'.stk stack).length + n * programPushBound program := hrest
            _ ≤ ((c.stk stack).length + programPushBound program) +
                n * programPushBound program :=
              Nat.add_le_add_right hfirst _
            _ = (c.stk stack).length + Nat.succ n * programPushBound program := by
              simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]

end Lax51Proofs.RamToTM
