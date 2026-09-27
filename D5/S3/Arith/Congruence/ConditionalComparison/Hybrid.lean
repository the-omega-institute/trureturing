/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Hybrid
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Hybrid initial-variable / causal comparison. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Hybrid.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Causal
import Mathlib.Tactic

/-!
# Hybrid initial-variable / causal comparison

The ternary residual leaf is sampled first and need not be a product of
digits.  Every later digit is an adapted finite kernel.  This module keeps
that distinction in the types and proves the exact hybrid comparison used in
the paper: eliminate the adapted coordinates backwards, then apply the
unconditional prefix caps to the initial variable.
-/

namespace Erdos7

universe u

/-- A state consisting of an arbitrary initial sample and `n` later symbols. -/
abbrev BasedPath (Ω : Type*) (Q n : ℕ) := Ω × CausalPath Q n

/--
An adapted finite process over an arbitrary finite initial probability space.
The atom cap attached to each later kernel may depend on the coordinate but
not on the realized history.
-/
inductive BasedCausalLaw (Ω : Type u) [Fintype Ω] (Q : ℕ) : ℕ → Type (u + 1)
  | base (μ : FiniteLaw Ω) : BasedCausalLaw Ω Q 0
  | snoc {n : ℕ}
      (prior : BasedCausalLaw Ω Q n)
      (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
      (kernel : BasedPath Ω Q n → FiniteLaw (Fin Q))
      (atomCap : ∀ x y, (kernel x).weight y ≤ r) :
      BasedCausalLaw Ω Q (n + 1)

namespace BasedCausalLaw

variable {Ω : Type u} [Fintype Ω] {Q : ℕ}

/-- The initial law carried unchanged through the adapted process. -/
def initialLaw : {n : ℕ} → BasedCausalLaw Ω Q n → FiniteLaw Ω
  | 0, .base μ => μ
  | _ + 1, .snoc prior _ _ _ _ _ => prior.initialLaw

/-- Exact expectation of a functional of the complete based path. -/
def expect : {n : ℕ} → BasedCausalLaw Ω Q n → (BasedPath Ω Q n → ℚ) → ℚ
  | 0, .base μ, f => μ.expect fun ω ↦ f (ω, fun i ↦ Fin.elim0 i)
  | _ + 1, .snoc prior _ _ _ kernel _, f =>
      prior.expect fun x ↦ (kernel x).expect fun y ↦
        f (x.1, Fin.snoc x.2 y)

@[simp] theorem expect_const {n : ℕ} (P : BasedCausalLaw Ω Q n) (c : ℚ) :
    P.expect (fun _ ↦ c) = c := by
  induction P with
  | base μ => simp [expect]
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      simp only [expect]
      simp_rw [FiniteLaw.expect_const]
      exact ih

theorem expect_add {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (f g : BasedPath Ω Q n → ℚ) :
    P.expect (fun x ↦ f x + g x) = P.expect f + P.expect g := by
  induction P with
  | base μ => exact μ.expect_add _ _
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      simp only [expect]
      simp_rw [FiniteLaw.expect_add]
      exact ih _ _

theorem expect_smul {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (c : ℚ) (f : BasedPath Ω Q n → ℚ) :
    P.expect (fun x ↦ c * f x) = c * P.expect f := by
  induction P with
  | base μ => exact μ.expect_smul _ _
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      simp only [expect]
      simp_rw [FiniteLaw.expect_smul]
      exact ih _

theorem expect_mono {n : ℕ} (P : BasedCausalLaw Ω Q n)
    {f g : BasedPath Ω Q n → ℚ} (hfg : ∀ x, f x ≤ g x) :
    P.expect f ≤ P.expect g := by
  induction P with
  | base μ => exact μ.expect_mono fun ω ↦ hfg _
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      apply ih
      intro x
      apply (kernel x).expect_mono
      intro y
      exact hfg _

theorem expect_congr {n : ℕ} (P : BasedCausalLaw Ω Q n)
    {f g : BasedPath Ω Q n → ℚ} (hfg : ∀ x, f x = g x) :
    P.expect f = P.expect g := by
  apply le_antisymm
  · exact P.expect_mono fun x ↦ (hfg x).le
  · exact P.expect_mono fun x ↦ (hfg x).ge

/-- Later requirements filter the labels selected by the initial sample. -/
noncomputable def active (initial : Ω → Finset ℕ) {n : ℕ}
    (req : ℕ → Fin n → Option (Fin Q)) (x : BasedPath Ω Q n) : Finset ℕ :=
  CausalLaw.activeWithin (initial x.1) req x.2

@[simp] theorem active_zero (initial : Ω → Finset ℕ)
    (req : ℕ → Fin 0 → Option (Fin Q)) (x : BasedPath Ω Q 0) :
    active initial req x = initial x.1 := by
  simp [active]

@[simp] theorem active_snoc (initial : Ω → Finset ℕ) {n : ℕ}
    (req : ℕ → Fin (n + 1) → Option (Fin Q))
    (x : BasedPath Ω Q n) (y : Fin Q) :
    active initial req (x.1, Fin.snoc x.2 y) =
      selectAt (active initial (CausalLaw.reqInit req) x)
        (CausalLaw.reqLast req) y := by
  simpa [active] using
    (CausalLaw.activeWithin_snoc (initial x.1) req x.2 y)

/-- The set functional left after all later coordinates have become gates. -/
noncomputable def gateFunctional : {n : ℕ} → BasedCausalLaw Ω Q n →
    (ℕ → Fin n → Option (Fin Q)) → (Finset ℕ → ℚ) → Finset ℕ → ℚ
  | 0, .base _, _, F => F
  | _ + 1, .snoc prior r _ _ _ _, req, F =>
      prior.gateFunctional (CausalLaw.reqInit req)
        (continuation (CausalLaw.reqLast req) r F)

theorem gateFunctional_increasing {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (req : ℕ → Fin n → Option (Fin Q)) {F : Finset ℕ → ℚ}
    (hF : Increasing F) : Increasing (P.gateFunctional req F) := by
  induction P generalizing F with
  | base μ => exact hF
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      exact ih (CausalLaw.reqInit req)
        (continuation_increasing hF (CausalLaw.reqLast req) hr0 hr1)

theorem gateFunctional_supermodular {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (req : ℕ → Fin n → Option (Fin Q)) {F : Finset ℕ → ℚ}
    (hF : Supermodular F) : Supermodular (P.gateFunctional req F) := by
  induction P generalizing F with
  | base μ => exact hF
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      exact ih (CausalLaw.reqInit req)
        (continuation_supermodular hF (CausalLaw.reqLast req) hr0 hr1)

/-- Expectation in the independent-gate upper model. -/
noncomputable def gateValue {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (initial : Ω → Finset ℕ) (req : ℕ → Fin n → Option (Fin Q))
    (F : Finset ℕ → ℚ) : ℚ :=
  P.initialLaw.expect fun ω ↦ P.gateFunctional req F (initial ω)

/-- Reverse causal domination while retaining an arbitrary initial law. -/
theorem causal_gate_bound {n : ℕ} (P : BasedCausalLaw Ω Q n)
    (initial : Ω → Finset ℕ) (req : ℕ → Fin n → Option (Fin Q))
    (F : Finset ℕ → ℚ) (hSup : Supermodular F) (hInc : Increasing F) :
    P.expect (fun x ↦ F (active initial req x)) ≤
      P.gateValue initial req F := by
  induction P generalizing F with
  | base μ => simp [expect, gateValue, initialLaw, gateFunctional, active]
  | snoc prior r hr0 hr1 kernel atomCap ih =>
      simp only [expect, gateValue, initialLaw, gateFunctional]
      calc
        prior.expect (fun x ↦ (kernel x).expect fun y ↦
            F (active initial req (x.1, Fin.snoc x.2 y)))
          ≤ prior.expect (fun x ↦
              continuation (CausalLaw.reqLast req) r F
                (active initial (CausalLaw.reqInit req) x)) := by
              apply prior.expect_mono
              intro x
              simpa [continuation] using
                (one_step_common_gate (kernel x) r (atomCap x)
                  hSup hInc (active initial (CausalLaw.reqInit req) x)
                  (CausalLaw.reqLast req))
        _ ≤ prior.gateValue initial (CausalLaw.reqInit req)
              (continuation (CausalLaw.reqLast req) r F) := by
              exact ih (CausalLaw.reqInit req)
                (continuation (CausalLaw.reqLast req) r F)
                (continuation_supermodular hSup (CausalLaw.reqLast req) hr0 hr1)
                (continuation_increasing hInc (CausalLaw.reqLast req) hr0 hr1)

/--
Hybrid comparison in linearized form.  The later adapted symbols are removed
first.  The only assumptions on the initial selectors are their unconditional
marginal caps; no conditional ternary digit estimate appears.
-/
theorem hybrid_prefix_causal_bound {n L : ℕ}
    (P : BasedCausalLaw Ω Q n)
    (initial : Ω → Finset ℕ) (hinitial : ∀ ω, initial ω ⊆ Finset.range L)
    (req : ℕ → Fin n → Option (Fin Q))
    (F : Finset ℕ → ℚ) (hSup : Supermodular F) (hInc : Increasing F)
    (ρ : ℕ → ℚ)
    (hmarg : ∀ l < L,
      P.initialLaw.prob (fun ω ↦ l ∈ initial ω) ≤ ρ l) :
    P.expect (fun x ↦ F (active initial req x)) ≤
      P.gateFunctional req F ∅ +
        ∑ l ∈ Finset.range L, ρ l * prefixMarginal (P.gateFunctional req F) l := by
  calc
    P.expect (fun x ↦ F (active initial req x))
        ≤ P.gateValue initial req F :=
          P.causal_gate_bound initial req F hSup hInc
    _ ≤ P.gateFunctional req F ∅ +
          ∑ l ∈ Finset.range L,
            ρ l * prefixMarginal (P.gateFunctional req F) l := by
          exact bernoulli_rearrangement P.initialLaw
            (P.gateFunctional_supermodular req hSup)
            (P.gateFunctional_increasing req hInc)
            L initial hinitial ρ hmarg

end BasedCausalLaw
end Erdos7
