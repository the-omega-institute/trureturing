/- GID: D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.claim; result=D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result; claim=D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.claim
   digest: Four-party no-signalling boxes have q <= 1/4 in the relaxed Hardy test of 1507.07327. -/

/-
proof_shape: result: bind-only (at four parties with two outcomes, for each fixed party j:
  instantiation of no-signalling equalities, the three Hardy conditions, nonnegativity and
  normalization, closed by linear arithmetic, i.e. a linear dual certificate for 4 q ≤ 1)
escape_witness: null
admission_basis: open-problem-resolution (issue #12033; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.RelaxedHardyNoSignallingOptimum

/-- `P` is a no-signalling box of `N` parties with `d` outcomes each: for every input string
`s` (`false` is the input `u`, `true` the input `v`), `P s` is a probability distribution on the
outcome strings `Fin N → Fin d`, and for every party `p` the marginal of the other parties does
not depend on the input of `p`. -/
def IsNSBox (N d : ℕ) (P : (Fin N → Bool) → (Fin N → Fin d) → ℝ) : Prop :=
  (∀ s x, 0 ≤ P s x) ∧ (∀ s, ∑ x, P s x = 1) ∧
  ∀ (p : Fin N) (s s' : Fin N → Bool), (∀ k, k ≠ p → s k = s' k) →
    ∀ x : Fin N → Fin d, ∑ a, P s (Function.update x p a) = ∑ a, P s' (Function.update x p a)

/-- The relaxed Hardy conditions `(relH)` of arXiv:1507.07327 with success probability `q`.
The outcome value `0` is the paper's outcome `1` and the value `d - 1` is its outcome `d`:
`P(1…1 | u…u) = q > 0`; with `v` at `r` only, every outcome string with value other than
`d - 1` at `r` and `0` elsewhere has probability `0`; and for one fixed party `j` and every
`i ≠ j`, with `v` at `i` and `j`, the string with `d - 1` at `i` and `j` and `0` elsewhere has
probability `0`. -/
def RelaxedHardy (N d : ℕ) (P : (Fin N → Bool) → (Fin N → Fin d) → ℝ) (q : ℝ) : Prop :=
  0 < q ∧
  (∀ x : Fin N → Fin d, (∀ k, (x k : ℕ) = 0) → P (fun _ => false) x = q) ∧
  (∀ (r : Fin N) (x : Fin N → Fin d), (∀ k, k ≠ r → (x k : ℕ) = 0) → (x r : ℕ) ≠ d - 1 →
    P (fun k => decide (k = r)) x = 0) ∧
  ∃ j : Fin N, ∀ i : Fin N, i ≠ j → ∀ x : Fin N → Fin d, (x i : ℕ) = d - 1 → (x j : ℕ) = d - 1 →
    (∀ k, k ≠ i → k ≠ j → (x k : ℕ) = 0) → P (fun k => decide (k = i ∨ k = j)) x = 0

/-- A consequence of the conjecture of Bhattacharya, Roy, Mukherjee and Rahaman
(arXiv:1507.07327) that the optimal success probability of the relaxed Hardy test under
no-signalling is `1/3` for any number of parties and any dimension: for every `N ≥ 3` and every
common number `d ≥ 2` of outcomes, no-signalling boxes satisfying `(relH)` reach success
probabilities arbitrarily close to `1/3`. -/
def claim : Prop :=
  ∀ N d : ℕ, 3 ≤ N → 2 ≤ d → ∀ ε : ℝ, 0 < ε →
    ∃ (P : (Fin N → Bool) → (Fin N → Fin d) → ℝ) (q : ℝ),
      IsNSBox N d P ∧ RelaxedHardy N d P q ∧ 1 / 3 - ε < q

/-- The conjecture fails for four parties with two outcomes: every no-signalling box satisfying
`(relH)` has `4 q ≤ 1`, so no success probability exceeds `1/4 = 1/3 - 1/12`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨P, q, ⟨hnn, hnorm, hns⟩, ⟨hq, h1, h2, j, h3⟩, hlt⟩ :=
    h 4 2 (by norm_num) le_rfl (1 / 12) (by norm_num)
  have ns' : ∀ (p : Fin 4) (s s' : Fin 4 → Bool) (x y₀ y₁ : Fin 4 → Fin 2),
      (∀ k, k ≠ p → s k = s' k) → Function.update x p 0 = y₀ → Function.update x p 1 = y₁ →
        P s y₀ + P s y₁ = P s' y₀ + P s' y₁ := by
    intro p s s' x y₀ y₁ hs h₀ h₁
    have h := hns p s s' hs x
    rwa [Fin.sum_univ_two, Fin.sum_univ_two, h₀, h₁] at h
  have norm4 : ∀ a b c e : Fin 4 → Fin 2,
      a ∉ ({b, c, e} : Finset (Fin 4 → Fin 2)) ∧ b ∉ ({c, e} : Finset (Fin 4 → Fin 2)) ∧ c ≠ e →
        P (fun _ => false) a + P (fun _ => false) b + P (fun _ => false) c +
          P (fun _ => false) e ≤ 1 := by
    intro a b c e h
    obtain ⟨ha, hb, hc⟩ := h
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({a, b, c, e} : Finset (Fin 4 → Fin 2)))
      (fun x _ _ => hnn (fun _ => false) x) (f := P (fun _ => false))
    rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_pair hc, hnorm] at hsub
    linarith
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl | rfl
  · -- the fixed party is 0
    have g1 := h1 ![0,0,0,0] (by decide)
    have n1 := ns' 0 (fun _ => false) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have g2_0 := h2 0 ![0,0,0,0] (by decide) (by decide)
    have n2 := ns' 1 (fun _ => false) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have g2_1 := h2 1 ![0,0,0,0] (by decide) (by decide)
    have n3 := ns' 2 (fun _ => false) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have g2_2 := h2 2 ![0,0,0,0] (by decide) (by decide)
    have n4 := ns' 3 (fun _ => false) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have g2_3 := h2 3 ![0,0,0,0] (by decide) (by decide)
    have n5 := ns' 0 (fun k => decide (k = 1 ∨ k = 0)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have n6 := ns' 1 (fun k => decide (k = 1 ∨ k = 0)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have n7 := ns' 1 (fun k => decide (k = 1 ∨ k = 0)) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have n8 := ns' 0 (fun k => decide (k = 0)) (fun _ => false)
      ![0,1,0,0] ![0,1,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have g3_1 := h3 1 (by decide) ![1,1,0,0] (by decide) (by decide) (by decide)
    have p1_1 := hnn (fun k => decide (k = 1)) ![1,1,0,0]
    have p2_1 := hnn (fun k => decide (k = 0)) ![1,1,0,0]
    have p3_1 := hnn (fun k => decide (k = 1 ∨ k = 0)) ![0,0,0,0]
    have n9 := ns' 0 (fun k => decide (k = 2 ∨ k = 0)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have n10 := ns' 2 (fun k => decide (k = 2 ∨ k = 0)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have n11 := ns' 2 (fun k => decide (k = 2 ∨ k = 0)) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have n12 := ns' 0 (fun k => decide (k = 0)) (fun _ => false)
      ![0,0,1,0] ![0,0,1,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have g3_2 := h3 2 (by decide) ![1,0,1,0] (by decide) (by decide) (by decide)
    have p1_2 := hnn (fun k => decide (k = 2)) ![1,0,1,0]
    have p2_2 := hnn (fun k => decide (k = 0)) ![1,0,1,0]
    have p3_2 := hnn (fun k => decide (k = 2 ∨ k = 0)) ![0,0,0,0]
    have n13 := ns' 0 (fun k => decide (k = 3 ∨ k = 0)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![1,0,0,1] (by decide) (by decide) (by decide)
    have n14 := ns' 3 (fun k => decide (k = 3 ∨ k = 0)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,0,0,1] (by decide) (by decide) (by decide)
    have n15 := ns' 3 (fun k => decide (k = 3 ∨ k = 0)) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have n16 := ns' 0 (fun k => decide (k = 0)) (fun _ => false)
      ![0,0,0,1] ![0,0,0,1] ![1,0,0,1] (by decide) (by decide) (by decide)
    have g3_3 := h3 3 (by decide) ![1,0,0,1] (by decide) (by decide) (by decide)
    have p1_3 := hnn (fun k => decide (k = 3)) ![1,0,0,1]
    have p2_3 := hnn (fun k => decide (k = 0)) ![1,0,0,1]
    have p3_3 := hnn (fun k => decide (k = 3 ∨ k = 0)) ![0,0,0,0]
    have n17 := ns' 0 (fun k => decide (k = 0)) (fun _ => false)
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have hsum := norm4 ![0,0,0,0] ![1,1,0,0] ![1,0,1,0] ![1,0,0,1] (by decide)
    linarith
  · -- the fixed party is 1
    have g1 := h1 ![0,0,0,0] (by decide)
    have n18 := ns' 0 (fun _ => false) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have g2_0 := h2 0 ![0,0,0,0] (by decide) (by decide)
    have n19 := ns' 1 (fun _ => false) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have g2_1 := h2 1 ![0,0,0,0] (by decide) (by decide)
    have n20 := ns' 2 (fun _ => false) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have g2_2 := h2 2 ![0,0,0,0] (by decide) (by decide)
    have n21 := ns' 3 (fun _ => false) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have g2_3 := h2 3 ![0,0,0,0] (by decide) (by decide)
    have n22 := ns' 1 (fun k => decide (k = 0 ∨ k = 1)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have n23 := ns' 0 (fun k => decide (k = 0 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have n24 := ns' 0 (fun k => decide (k = 0 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have n25 := ns' 1 (fun k => decide (k = 1)) (fun _ => false)
      ![1,0,0,0] ![1,0,0,0] ![1,1,0,0] (by decide) (by decide) (by decide)
    have g3_0 := h3 0 (by decide) ![1,1,0,0] (by decide) (by decide) (by decide)
    have p1_0 := hnn (fun k => decide (k = 0)) ![1,1,0,0]
    have p2_0 := hnn (fun k => decide (k = 1)) ![1,1,0,0]
    have p3_0 := hnn (fun k => decide (k = 0 ∨ k = 1)) ![0,0,0,0]
    have n26 := ns' 1 (fun k => decide (k = 2 ∨ k = 1)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have n27 := ns' 2 (fun k => decide (k = 2 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have n28 := ns' 2 (fun k => decide (k = 2 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have n29 := ns' 1 (fun k => decide (k = 1)) (fun _ => false)
      ![0,0,1,0] ![0,0,1,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have g3_2 := h3 2 (by decide) ![0,1,1,0] (by decide) (by decide) (by decide)
    have p1_2 := hnn (fun k => decide (k = 2)) ![0,1,1,0]
    have p2_2 := hnn (fun k => decide (k = 1)) ![0,1,1,0]
    have p3_2 := hnn (fun k => decide (k = 2 ∨ k = 1)) ![0,0,0,0]
    have n30 := ns' 1 (fun k => decide (k = 3 ∨ k = 1)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![0,1,0,1] (by decide) (by decide) (by decide)
    have n31 := ns' 3 (fun k => decide (k = 3 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![0,1,0,1] (by decide) (by decide) (by decide)
    have n32 := ns' 3 (fun k => decide (k = 3 ∨ k = 1)) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have n33 := ns' 1 (fun k => decide (k = 1)) (fun _ => false)
      ![0,0,0,1] ![0,0,0,1] ![0,1,0,1] (by decide) (by decide) (by decide)
    have g3_3 := h3 3 (by decide) ![0,1,0,1] (by decide) (by decide) (by decide)
    have p1_3 := hnn (fun k => decide (k = 3)) ![0,1,0,1]
    have p2_3 := hnn (fun k => decide (k = 1)) ![0,1,0,1]
    have p3_3 := hnn (fun k => decide (k = 3 ∨ k = 1)) ![0,0,0,0]
    have n34 := ns' 1 (fun k => decide (k = 1)) (fun _ => false)
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have hsum := norm4 ![0,0,0,0] ![1,1,0,0] ![0,1,1,0] ![0,1,0,1] (by decide)
    linarith
  · -- the fixed party is 2
    have g1 := h1 ![0,0,0,0] (by decide)
    have n35 := ns' 0 (fun _ => false) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have g2_0 := h2 0 ![0,0,0,0] (by decide) (by decide)
    have n36 := ns' 1 (fun _ => false) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have g2_1 := h2 1 ![0,0,0,0] (by decide) (by decide)
    have n37 := ns' 2 (fun _ => false) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have g2_2 := h2 2 ![0,0,0,0] (by decide) (by decide)
    have n38 := ns' 3 (fun _ => false) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have g2_3 := h2 3 ![0,0,0,0] (by decide) (by decide)
    have n39 := ns' 2 (fun k => decide (k = 0 ∨ k = 2)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have n40 := ns' 0 (fun k => decide (k = 0 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have n41 := ns' 0 (fun k => decide (k = 0 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have n42 := ns' 2 (fun k => decide (k = 2)) (fun _ => false)
      ![1,0,0,0] ![1,0,0,0] ![1,0,1,0] (by decide) (by decide) (by decide)
    have g3_0 := h3 0 (by decide) ![1,0,1,0] (by decide) (by decide) (by decide)
    have p1_0 := hnn (fun k => decide (k = 0)) ![1,0,1,0]
    have p2_0 := hnn (fun k => decide (k = 2)) ![1,0,1,0]
    have p3_0 := hnn (fun k => decide (k = 0 ∨ k = 2)) ![0,0,0,0]
    have n43 := ns' 2 (fun k => decide (k = 1 ∨ k = 2)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have n44 := ns' 1 (fun k => decide (k = 1 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have n45 := ns' 1 (fun k => decide (k = 1 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have n46 := ns' 2 (fun k => decide (k = 2)) (fun _ => false)
      ![0,1,0,0] ![0,1,0,0] ![0,1,1,0] (by decide) (by decide) (by decide)
    have g3_1 := h3 1 (by decide) ![0,1,1,0] (by decide) (by decide) (by decide)
    have p1_1 := hnn (fun k => decide (k = 1)) ![0,1,1,0]
    have p2_1 := hnn (fun k => decide (k = 2)) ![0,1,1,0]
    have p3_1 := hnn (fun k => decide (k = 1 ∨ k = 2)) ![0,0,0,0]
    have n47 := ns' 2 (fun k => decide (k = 3 ∨ k = 2)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![0,0,1,1] (by decide) (by decide) (by decide)
    have n48 := ns' 3 (fun k => decide (k = 3 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![0,0,1,1] (by decide) (by decide) (by decide)
    have n49 := ns' 3 (fun k => decide (k = 3 ∨ k = 2)) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have n50 := ns' 2 (fun k => decide (k = 2)) (fun _ => false)
      ![0,0,0,1] ![0,0,0,1] ![0,0,1,1] (by decide) (by decide) (by decide)
    have g3_3 := h3 3 (by decide) ![0,0,1,1] (by decide) (by decide) (by decide)
    have p1_3 := hnn (fun k => decide (k = 3)) ![0,0,1,1]
    have p2_3 := hnn (fun k => decide (k = 2)) ![0,0,1,1]
    have p3_3 := hnn (fun k => decide (k = 3 ∨ k = 2)) ![0,0,0,0]
    have n51 := ns' 2 (fun k => decide (k = 2)) (fun _ => false)
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have hsum := norm4 ![0,0,0,0] ![1,0,1,0] ![0,1,1,0] ![0,0,1,1] (by decide)
    linarith
  · -- the fixed party is 3
    have g1 := h1 ![0,0,0,0] (by decide)
    have n52 := ns' 0 (fun _ => false) (fun k => decide (k = 0))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have g2_0 := h2 0 ![0,0,0,0] (by decide) (by decide)
    have n53 := ns' 1 (fun _ => false) (fun k => decide (k = 1))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have g2_1 := h2 1 ![0,0,0,0] (by decide) (by decide)
    have n54 := ns' 2 (fun _ => false) (fun k => decide (k = 2))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have g2_2 := h2 2 ![0,0,0,0] (by decide) (by decide)
    have n55 := ns' 3 (fun _ => false) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have g2_3 := h2 3 ![0,0,0,0] (by decide) (by decide)
    have n56 := ns' 3 (fun k => decide (k = 0 ∨ k = 3)) (fun k => decide (k = 0))
      ![1,0,0,0] ![1,0,0,0] ![1,0,0,1] (by decide) (by decide) (by decide)
    have n57 := ns' 0 (fun k => decide (k = 0 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![1,0,0,1] (by decide) (by decide) (by decide)
    have n58 := ns' 0 (fun k => decide (k = 0 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![1,0,0,0] (by decide) (by decide) (by decide)
    have n59 := ns' 3 (fun k => decide (k = 3)) (fun _ => false)
      ![1,0,0,0] ![1,0,0,0] ![1,0,0,1] (by decide) (by decide) (by decide)
    have g3_0 := h3 0 (by decide) ![1,0,0,1] (by decide) (by decide) (by decide)
    have p1_0 := hnn (fun k => decide (k = 0)) ![1,0,0,1]
    have p2_0 := hnn (fun k => decide (k = 3)) ![1,0,0,1]
    have p3_0 := hnn (fun k => decide (k = 0 ∨ k = 3)) ![0,0,0,0]
    have n60 := ns' 3 (fun k => decide (k = 1 ∨ k = 3)) (fun k => decide (k = 1))
      ![0,1,0,0] ![0,1,0,0] ![0,1,0,1] (by decide) (by decide) (by decide)
    have n61 := ns' 1 (fun k => decide (k = 1 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![0,1,0,1] (by decide) (by decide) (by decide)
    have n62 := ns' 1 (fun k => decide (k = 1 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,1,0,0] (by decide) (by decide) (by decide)
    have n63 := ns' 3 (fun k => decide (k = 3)) (fun _ => false)
      ![0,1,0,0] ![0,1,0,0] ![0,1,0,1] (by decide) (by decide) (by decide)
    have g3_1 := h3 1 (by decide) ![0,1,0,1] (by decide) (by decide) (by decide)
    have p1_1 := hnn (fun k => decide (k = 1)) ![0,1,0,1]
    have p2_1 := hnn (fun k => decide (k = 3)) ![0,1,0,1]
    have p3_1 := hnn (fun k => decide (k = 1 ∨ k = 3)) ![0,0,0,0]
    have n64 := ns' 3 (fun k => decide (k = 2 ∨ k = 3)) (fun k => decide (k = 2))
      ![0,0,1,0] ![0,0,1,0] ![0,0,1,1] (by decide) (by decide) (by decide)
    have n65 := ns' 2 (fun k => decide (k = 2 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,1] ![0,0,0,1] ![0,0,1,1] (by decide) (by decide) (by decide)
    have n66 := ns' 2 (fun k => decide (k = 2 ∨ k = 3)) (fun k => decide (k = 3))
      ![0,0,0,0] ![0,0,0,0] ![0,0,1,0] (by decide) (by decide) (by decide)
    have n67 := ns' 3 (fun k => decide (k = 3)) (fun _ => false)
      ![0,0,1,0] ![0,0,1,0] ![0,0,1,1] (by decide) (by decide) (by decide)
    have g3_2 := h3 2 (by decide) ![0,0,1,1] (by decide) (by decide) (by decide)
    have p1_2 := hnn (fun k => decide (k = 2)) ![0,0,1,1]
    have p2_2 := hnn (fun k => decide (k = 3)) ![0,0,1,1]
    have p3_2 := hnn (fun k => decide (k = 2 ∨ k = 3)) ![0,0,0,0]
    have n68 := ns' 3 (fun k => decide (k = 3)) (fun _ => false)
      ![0,0,0,0] ![0,0,0,0] ![0,0,0,1] (by decide) (by decide) (by decide)
    have hsum := norm4 ![0,0,0,0] ![1,0,0,1] ![0,1,0,1] ![0,0,1,1] (by decide)
    linarith

end D5.S3.Quantum.Entanglement.RelaxedHardyNoSignallingOptimum
