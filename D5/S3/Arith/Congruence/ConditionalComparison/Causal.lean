/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Causal
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Reverse causal gate comparison. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Causal.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Supermodular
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Reverse causal gate comparison

An adapted finite process is represented from left to right by exact rational
kernels.  The comparison theorem is proved from the final coordinate
backwards.  All coordinates use one ambient finite alphabet; smaller residual
alphabets are embedded by assigning zero mass to unused symbols.
-/

namespace Erdos7

section LabelSelection

variable {Q : ℕ}

/-- Retain labels that are either unconstrained or request a symbol in `J`. -/
noncomputable def selectBySet (A : Finset ℕ) (req : ℕ → Option (Fin Q))
    (J : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter fun l ↦ match req l with
      | none => True
      | some y => (y : ℕ) ∈ J

/-- Retain labels compatible with one realized symbol. -/
noncomputable def selectAt (A : Finset ℕ) (req : ℕ → Option (Fin Q))
    (y : Fin Q) : Finset ℕ :=
  selectBySet A req {(y : ℕ)}

/-- Labels that do not constrain the current coordinate. -/
noncomputable def unconstrained (A : Finset ℕ) (req : ℕ → Option (Fin Q)) : Finset ℕ :=
  selectBySet A req ∅

theorem selectBySet_mono (A : Finset ℕ) (req : ℕ → Option (Fin Q))
    {J K : Finset ℕ} (hJK : J ⊆ K) :
    selectBySet A req J ⊆ selectBySet A req K := by
  classical
  intro l hl
  simp only [selectBySet, Finset.mem_filter] at hl ⊢
  rcases hl with ⟨hlA, hl⟩
  refine ⟨hlA, ?_⟩
  cases hreq : req l with
  | none => simp [hreq]
  | some y =>
      simp only [hreq] at hl ⊢
      exact hJK hl

theorem selectBySet_left_mono (req : ℕ → Option (Fin Q)) (J : Finset ℕ)
    {A B : Finset ℕ} (hAB : A ⊆ B) :
    selectBySet A req J ⊆ selectBySet B req J := by
  classical
  intro l hl
  simp only [selectBySet, Finset.mem_filter] at hl ⊢
  exact ⟨hAB hl.1, hl.2⟩

@[simp] theorem selectBySet_inter (A : Finset ℕ) (req : ℕ → Option (Fin Q))
    (J K : Finset ℕ) :
    selectBySet A req (J ∩ K) = selectBySet A req J ∩ selectBySet A req K := by
  classical
  ext l
  by_cases hl : l ∈ A <;> simp [selectBySet, hl]
  cases req l <;> simp

@[simp] theorem selectBySet_union (A : Finset ℕ) (req : ℕ → Option (Fin Q))
    (J K : Finset ℕ) :
    selectBySet A req (J ∪ K) = selectBySet A req J ∪ selectBySet A req K := by
  classical
  ext l
  by_cases hl : l ∈ A <;> simp [selectBySet, hl]
  cases req l <;> simp <;> tauto

@[simp] theorem selectBySet_empty (A : Finset ℕ) (req : ℕ → Option (Fin Q)) :
    selectBySet A req ∅ = unconstrained A req := rfl

@[simp] theorem selectBySet_range (A : Finset ℕ) (req : ℕ → Option (Fin Q)) :
    selectBySet A req (Finset.range Q) = A := by
  classical
  ext l
  by_cases hl : l ∈ A <;> simp [selectBySet, hl]
  cases hreq : req l <;> simp [hreq]

/-- Pull a set functional back along the symbol-bundle map. -/
noncomputable def bundled (F : Finset ℕ → ℚ) (A : Finset ℕ)
    (req : ℕ → Option (Fin Q)) (J : Finset ℕ) : ℚ :=
  F (selectBySet A req J)

theorem bundled_increasing {F : Finset ℕ → ℚ} (hF : Increasing F)
    (A : Finset ℕ) (req : ℕ → Option (Fin Q)) :
    Increasing (bundled F A req) := by
  intro J K hJK
  exact hF (selectBySet_mono A req hJK)

theorem bundled_supermodular {F : Finset ℕ → ℚ} (hF : Supermodular F)
    (A : Finset ℕ) (req : ℕ → Option (Fin Q)) :
    Supermodular (bundled F A req) := by
  intro J K
  simpa [bundled] using hF (selectBySet A req J) (selectBySet A req K)

/-- One reverse-elimination step: mutually exclusive symbols become one gate. -/
theorem one_step_common_gate
    (μ : FiniteLaw (Fin Q)) (r : ℚ)
    (hcap : ∀ y, μ.weight y ≤ r)
    {F : Finset ℕ → ℚ} (hSup : Supermodular F) (hInc : Increasing F)
    (A : Finset ℕ) (req : ℕ → Option (Fin Q)) :
    μ.expect (fun y ↦ F (selectAt A req y)) ≤
      (1 - r) * F (unconstrained A req) + r * F A := by
  let activeSymbol : Fin Q → Finset ℕ := fun y ↦ {(y : ℕ)}
  have hactive : ∀ y, activeSymbol y ⊆ Finset.range Q := by
    intro y i hi
    simp only [activeSymbol, Finset.mem_singleton] at hi
    simpa [hi] using y.isLt
  have hmarg : ∀ i < Q, μ.prob (fun y ↦ i ∈ activeSymbol y) ≤ r := by
    intro i hi
    let y : Fin Q := ⟨i, hi⟩
    calc
      μ.prob (fun z ↦ i ∈ activeSymbol z)
          = μ.prob (fun z ↦ z = y) := by
              apply μ.prob_congr
              intro z
              simp [activeSymbol, y, Fin.ext_iff, eq_comm]
      _ = μ.weight y := μ.prob_singleton y
      _ ≤ r := hcap y
  have h := common_gate_bound μ
    (bundled_supermodular hSup A req)
    (bundled_increasing hInc A req)
    Q activeSymbol hactive r hmarg
  simpa [activeSymbol, bundled, selectAt] using h

end LabelSelection

section Continuation

variable {Q : ℕ}

/-- The continuation functional after replacing one coordinate by a gate. -/
noncomputable def continuation (req : ℕ → Option (Fin Q)) (r : ℚ)
    (F : Finset ℕ → ℚ) (A : Finset ℕ) : ℚ :=
  (1 - r) * F (unconstrained A req) + r * F A

@[simp] theorem unconstrained_inter (req : ℕ → Option (Fin Q))
    (A B : Finset ℕ) :
    unconstrained (A ∩ B) req = unconstrained A req ∩ unconstrained B req := by
  classical
  ext l
  by_cases hlA : l ∈ A <;> by_cases hlB : l ∈ B <;>
    simp [unconstrained, selectBySet, hlA, hlB]

@[simp] theorem unconstrained_union (req : ℕ → Option (Fin Q))
    (A B : Finset ℕ) :
    unconstrained (A ∪ B) req = unconstrained A req ∪ unconstrained B req := by
  classical
  ext l
  by_cases hlA : l ∈ A <;> by_cases hlB : l ∈ B <;>
    simp [unconstrained, selectBySet, hlA, hlB]

theorem continuation_increasing
    {F : Finset ℕ → ℚ} (hF : Increasing F)
    (req : ℕ → Option (Fin Q)) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Increasing (continuation req r F) := by
  intro A B hAB
  have hu : unconstrained A req ⊆ unconstrained B req := by
    exact selectBySet_left_mono req ∅ hAB
  have h1 := mul_le_mul_of_nonneg_left (hF hu) (by linarith : 0 ≤ 1 - r)
  have h2 := mul_le_mul_of_nonneg_left (hF hAB) hr0
  unfold continuation
  linarith

theorem continuation_supermodular
    {F : Finset ℕ → ℚ} (hF : Supermodular F)
    (req : ℕ → Option (Fin Q)) {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Supermodular (continuation req r F) := by
  intro A B
  have hu := hF (unconstrained A req) (unconstrained B req)
  have ha := hF A B
  rw [← unconstrained_inter, ← unconstrained_union] at hu
  have h1 := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ 1 - r)
  have h2 := mul_le_mul_of_nonneg_left ha hr0
  unfold continuation
  linarith

end Continuation

section CausalProcess

/-- A length-`n` path in one finite ambient alphabet. -/
abbrev CausalPath (Q n : ℕ) := Fin n → Fin Q

/--
An exact finite adapted process, stored as its preceding process followed by a
history-dependent final kernel.  Each kernel carries its atom cap.
-/
inductive CausalLaw (Q : ℕ) : ℕ → Type
  | nil : CausalLaw Q 0
  | snoc {n : ℕ}
      (prior : CausalLaw Q n)
      (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
      (kernel : CausalPath Q n → FiniteLaw (Fin Q))
      (atomCap : ∀ x y, (kernel x).weight y ≤ r) :
      CausalLaw Q (n + 1)

namespace CausalLaw

variable {Q : ℕ}

/-- Exact expectation of a path functional. -/
def expect : {n : ℕ} → CausalLaw Q n → (CausalPath Q n → ℚ) → ℚ
  | 0, .nil, f => f (fun i ↦ Fin.elim0 i)
  | _ + 1, .snoc prior _ _ _ kernel _, f =>
      prior.expect fun x ↦ (kernel x).expect fun y ↦ f (Fin.snoc x y)

theorem expect_mono {n : ℕ} (P : CausalLaw Q n)
    {f g : CausalPath Q n → ℚ} (hfg : ∀ x, f x ≤ g x) :
    P.expect f ≤ P.expect g := by
  induction P with
  | nil => exact hfg _
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      apply ih
      intro x
      apply (kernel x).expect_mono
      intro y
      exact hfg (Fin.snoc x y)

theorem expect_congr {n : ℕ} (P : CausalLaw Q n)
    {f g : CausalPath Q n → ℚ} (hfg : ∀ x, f x = g x) :
    P.expect f = P.expect g := by
  apply le_antisymm
  · exact P.expect_mono fun x ↦ (hfg x).le
  · exact P.expect_mono fun x ↦ (hfg x).ge

/-- Remove the final coordinate from a family of label requirements. -/
def reqInit {n : ℕ} (req : ℕ → Fin (n + 1) → Option (Fin Q)) :
    ℕ → Fin n → Option (Fin Q) :=
  fun l i ↦ req l i.castSucc

/-- The final-coordinate requirement of every label. -/
def reqLast {n : ℕ} (req : ℕ → Fin (n + 1) → Option (Fin Q)) :
    ℕ → Option (Fin Q) :=
  fun l ↦ req l (Fin.last n)

/-- Labels in `A` whose every coordinate requirement is satisfied. -/
noncomputable def activeWithin {n : ℕ} (A : Finset ℕ)
    (req : ℕ → Fin n → Option (Fin Q)) (z : CausalPath Q n) : Finset ℕ :=
  A.filter fun l ↦ ∀ i, req l i = none ∨ req l i = some (z i)

@[simp] theorem activeWithin_zero (A : Finset ℕ)
    (req : ℕ → Fin 0 → Option (Fin Q)) (z : CausalPath Q 0) :
    activeWithin A req z = A := by
  ext l
  simp [activeWithin]

@[simp] theorem activeWithin_snoc {n : ℕ} (A : Finset ℕ)
    (req : ℕ → Fin (n + 1) → Option (Fin Q))
    (x : CausalPath Q n) (y : Fin Q) :
    activeWithin A req (Fin.snoc x y) =
      selectAt (activeWithin A (reqInit req) x) (reqLast req) y := by
  ext l
  simp only [activeWithin, selectAt, selectBySet, Finset.mem_filter]
  dsimp only [reqInit, reqLast]
  rw [Fin.forall_fin_succ']
  cases hlast : req l (Fin.last n) with
  | none => simp
  | some y' => simp [Fin.ext_iff, and_assoc]

/-- The fully gated comparison value obtained by reverse elimination. -/
noncomputable def gateValue : {n : ℕ} → CausalLaw Q n → Finset ℕ →
    (ℕ → Fin n → Option (Fin Q)) → (Finset ℕ → ℚ) → ℚ
  | 0, .nil, A, _, F => F A
  | _ + 1, .snoc prior r _ _ _ _, A, req, F =>
      prior.gateValue A (reqInit req) (continuation (reqLast req) r F)

/-- Reverse causal gate domination for an arbitrary increasing supermodular functional. -/
theorem causal_gate_bound {n : ℕ} (P : CausalLaw Q n)
    (A : Finset ℕ) (req : ℕ → Fin n → Option (Fin Q))
    (F : Finset ℕ → ℚ) (hSup : Supermodular F) (hInc : Increasing F) :
    P.expect (fun z ↦ F (activeWithin A req z)) ≤
      P.gateValue A req F := by
  induction P generalizing A F with
  | nil => simp [expect, gateValue]
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      simp only [expect, gateValue]
      calc
        prior.expect (fun x ↦
            (kernel x).expect fun y ↦ F (activeWithin A req (Fin.snoc x y)))
          ≤ prior.expect (fun x ↦
              continuation (reqLast req) r F
                (activeWithin A (reqInit req) x)) := by
              apply prior.expect_mono
              intro x
              simpa [activeWithin_snoc, continuation] using
                (one_step_common_gate (kernel x) r (atomCap x)
                  hSup hInc (activeWithin A (reqInit req) x) (reqLast req))
        _ ≤ prior.gateValue A (reqInit req)
              (continuation (reqLast req) r F) := by
              exact ih A (reqInit req) (continuation (reqLast req) r F)
                (continuation_supermodular hSup (reqLast req) hr0 hr1)
                (continuation_increasing hInc (reqLast req) hr0 hr1)

end CausalLaw
end CausalProcess

end Erdos7
