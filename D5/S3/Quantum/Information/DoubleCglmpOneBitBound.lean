/- GID: D5/S3/Quantum/Information/DoubleCglmpOneBitBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/DoubleCglmpOneBitBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Double CGLMP_d has one-bit bound 12; its truncations have local bounds 7 and 4. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the order
  cycle `cyc` with the rectangle lemmas `rect1` and `rect2`, the kernel-checked rectangle counts
  `bound_*` combined over the message colourings in `detAB` and `detBA`, and the
  derandomisation `derandPoint` integrated over the hidden variable in `derand`
admission_basis: open-problem-resolution (issue #11276)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.DoubleCglmpOneBitBound

/-!
I. Márton, E. Bene, P. Diviánszky and T. Vértesi, *Beating one bit of communication with and
without quantum pseudo-telepathy*, arXiv:2308.10771 (npj Quantum Inf. 10, 79 (2024)), play two
copies of the game `CGLMP_d = P(A₀ ≥ B₀) + P(A₀ ≤ B₁) + P(A₁ < B₀) + P(A₁ ≥ B₁)` in parallel. They
conjecture that the one-bit bound of `CGLMP_d^{⊗2}` is 12 for every `d ≥ 2`, and give the
conjectured local bounds 7 and 4 of two truncations. All three hold.

In one copy the four winning conditions on a rectangle of inputs cannot all hold, since they would
give `α_U ≤ β_Z ≤ α_V < β_W ≤ α_U`; so every rectangle on which Bob answers alike loses a cell.
A kernel-checked count shows that, for every message, at least four cells are lost (two in the
truncations). For fixed hidden variable the value is linear in each response, so best outputs do
not decrease it, and integrating gives the bounds; point strategies attain them.
-/

open MeasureTheory

/-- Inputs of the double game: the input bits `(x, x')` of the two copies. -/
abbrev Inp := Fin 2 × Fin 2

/-- One copy of `CGLMP_d` is won on inputs `(x, y)` and outputs `(a, b)` when
`(0,0): a ≥ b`, `(0,1): a ≤ b`, `(1,0): a < b`, `(1,1): a ≥ b`. -/
abbrev copyWins {d : ℕ} (x y : Fin 2) (a b : Fin d) : Prop :=
  (x = 0 ∧ y = 0 ∧ b ≤ a) ∨ (x = 0 ∧ y = 1 ∧ a ≤ b) ∨ (x = 1 ∧ y = 0 ∧ a < b) ∨
    (x = 1 ∧ y = 1 ∧ b ≤ a)

/-- The double game is won when both copies are won. -/
abbrev wins {d : ℕ} (X Y : Inp) (A B : Fin d × Fin d) : Prop :=
  copyWins X.1 Y.1 A.1 B.1 ∧ copyWins X.2 Y.2 A.2 B.2

/-- The Bell expression `CGLMP_d^{⊗2}` restricted to the inputs `XS × YS`, on a behaviour `P`:
the total probability of winning. -/
def bell {d : ℕ} (XS YS : Finset Inp) (P : Inp → Inp → Fin d × Fin d → Fin d × Fin d → ℝ) : ℝ :=
  ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B, if wins X Y A B then P X Y A B else 0

/-- A conditional distribution of an output given the hidden variable, measurable in it. -/
def IsResponse {d : ℕ} (r : ℝ → Fin d × Fin d → ℝ) : Prop :=
  (∀ A, Measurable fun t => r t A) ∧ (∀ t A, 0 ≤ r t A) ∧ ∀ t, ∑ A, r t A = 1

/-- Eq. (P_LHV): a local hidden-variable behaviour. -/
def IsLocal (d : ℕ) (P : Inp → Inp → Fin d × Fin d → Fin d × Fin d → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∃ pA pB : Inp → ℝ → Fin d × Fin d → ℝ,
    (∀ X, IsResponse (pA X)) ∧ (∀ Y, IsResponse (pB Y)) ∧
      ∀ X Y A B, P X Y A B = ∫ t, pA X t A * pB Y t B ∂μ

/-- Eq. (P_LHV1bit): local hidden variables with one bit `l(X, λ)` sent from Alice to Bob. -/
def IsOneBitAB (d : ℕ) (P : Inp → Inp → Fin d × Fin d → Fin d × Fin d → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∃ (pA : Inp → ℝ → Fin d × Fin d → ℝ)
    (l : Inp → ℝ → Bool) (pB : Inp → Bool → ℝ → Fin d × Fin d → ℝ),
    (∀ X, IsResponse (pA X)) ∧ (∀ X, Measurable (l X)) ∧ (∀ Y m, IsResponse (pB Y m)) ∧
      ∀ X Y A B, P X Y A B = ∫ t, pA X t A * pB Y (l X t) t B ∂μ

/-- The same with one bit `l(Y, λ)` sent from Bob to Alice. -/
def IsOneBitBA (d : ℕ) (P : Inp → Inp → Fin d × Fin d → Fin d × Fin d → ℝ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∃ (pA : Inp → Bool → ℝ → Fin d × Fin d → ℝ)
    (l : Inp → ℝ → Bool) (pB : Inp → ℝ → Fin d × Fin d → ℝ),
    (∀ X m, IsResponse (pA X m)) ∧ (∀ Y, Measurable (l Y)) ∧ (∀ Y, IsResponse (pB Y)) ∧
      ∀ X Y A B, P X Y A B = ∫ t, pA X (l Y t) t A * pB Y t B ∂μ

/-- The inputs `{00, 01, 11}` of the truncated games. -/
def symInputs : Finset Inp := {(0, 0), (0, 1), (1, 1)}

/-- Bob's inputs `{00, 11}` of the asymmetric truncated game. -/
def asymInputs : Finset Inp := {(0, 0), (1, 1)}

/-- The conjecture `L1bit(CGLMP_d^{⊗2}) = 12` (both directions) and the conjectured local bounds
`L([CGLMP_d^{⊗2}]_s) = 7` and `L([CGLMP_d^{⊗2}]_a) = 4`, for every `d ≥ 2`. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    IsGreatest {v | ∃ P, IsOneBitAB d P ∧ bell Finset.univ Finset.univ P = v} 12 ∧
    IsGreatest {v | ∃ P, IsOneBitBA d P ∧ bell Finset.univ Finset.univ P = v} 12 ∧
    IsGreatest {v | ∃ P, IsLocal d P ∧ bell symInputs symInputs P = v} 7 ∧
    IsGreatest {v | ∃ P, IsLocal d P ∧ bell symInputs asymInputs P = v} 4

/-- Wins of a deterministic strategy in row `X`. -/
private def rowSum {d : ℕ} (α β : Inp → Fin d × Fin d) (X : Inp) : ℕ :=
  ∑ Y, if decide (wins X Y (α X) (β Y)) then 1 else 0

/-- Wins of a deterministic strategy in column `Y`. -/
private def colSum {d : ℕ} (α β : Inp → Fin d × Fin d) (Y : Inp) : ℕ :=
  ∑ X, if decide (wins X Y (α X) (β Y)) then 1 else 0

set_option maxHeartbeats 1600000 in
-- The kernel-checked counts and the colouring case splits share this one declaration.
theorem result : claim := by
  intro d hd
  have cyc : ∀ a a' b b' : Fin d,
      ¬ (copyWins 0 0 a b ∧ copyWins 0 1 a b' ∧ copyWins 1 0 a' b ∧ copyWins 1 1 a' b') := by
    intro a a' b b' h
    simp only [copyWins] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [true_and, Fin.isValue, zero_ne_one, false_and, and_false, and_self, or_self,
      or_false, one_ne_zero, false_or] at h1 h2 h3 h4
    exact lt_irrefl a (lt_of_le_of_lt (h2.trans h4) (h3.trans_le h1))
  have rect1 : ∀ (α β : Inp → Fin d × Fin d) (U V W Z : Inp), U.1 = 0 → V.1 = 1 → W.1 = 0 →
      Z.1 = 1 → (decide (wins U W (α U) (β W)) && decide (wins U Z (α U) (β Z)) &&
        decide (wins V W (α V) (β W)) && decide (wins V Z (α V) (β Z))) = false := by
    intro α β U V W Z hU hV hW hZ
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    simp only [wins, hU, hV, hW, hZ] at h1 h2 h3 h4
    exact cyc _ _ _ _ ⟨h1.1, h2.1, h3.1, h4.1⟩
  have rect2 : ∀ (α β : Inp → Fin d × Fin d) (U V W Z : Inp), U.2 = 0 → V.2 = 1 → W.2 = 0 →
      Z.2 = 1 → (decide (wins U W (α U) (β W)) && decide (wins U Z (α U) (β Z)) &&
        decide (wins V W (α V) (β W)) && decide (wins V Z (α V) (β Z))) = false := by
    intro α β U V W Z hU hV hW hZ
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    simp only [wins, hU, hV, hW, hZ] at h1 h2 h3 h4
    exact cyc _ _ _ _ ⟨h1.2, h2.2, h3.2, h4.2⟩
  -- kernel-checked counts of won cells under the rectangle constraints
  have bound_row0001 : ∀ w0000 w0001 w0010 w0011 w0100 w0101 w0110 w0111 : Bool,
      (!(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0011 && w0100 && w0111) &&
        !(w0010 && w0001 && w0110 && w0101) && !(w0010 && w0011 && w0110 && w0111)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w0110 then 1 else 0) + (if w0111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row0010 : ∀ w0000 w0001 w0010 w0011 w1000 w1001 w1010 w1011 : Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0000 && w0011 && w1000 && w1011) &&
        !(w0001 && w0010 && w1001 && w1010) && !(w0001 && w0011 && w1001 && w1011)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w1000 then 1 else 0) + (if w1001 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1011 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row0011 : ∀ w0000 w0001 w0010 w0011 w1100 w1101 w1110 w1111 : Bool,
      (!(w0000 && w0010 && w1100 && w1110) && !(w0000 && w0011 && w1100 && w1111) &&
        !(w0001 && w0010 && w1101 && w1110) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0000 && w0001 && w1100 && w1101) && !(w0010 && w0001 && w1110 && w1101) &&
        !(w0010 && w0011 && w1110 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w1100 then 1 else 0) + (if w1101 then 1 else 0)) +
        ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row0110 : ∀ w0100 w0101 w0110 w0111 w1000 w1001 w1010 w1011 : Bool,
      (!(w0100 && w0110 && w1000 && w1010) && !(w0100 && w0111 && w1000 && w1011) &&
        !(w0101 && w0110 && w1001 && w1010) && !(w0101 && w0111 && w1001 && w1011) &&
        !(w1000 && w1001 && w0100 && w0101) && !(w1000 && w1011 && w0100 && w0111) &&
        !(w1010 && w1001 && w0110 && w0101) && !(w1010 && w1011 && w0110 && w0111)) = true →
      (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w0110 then 1 else 0) +
        (if w0111 then 1 else 0))) + (((if w1000 then 1 else 0) + (if w1001 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1011 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row0111 : ∀ w0100 w0101 w0110 w0111 w1100 w1101 w1110 w1111 : Bool,
      (!(w0100 && w0110 && w1100 && w1110) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0101 && w0110 && w1101 && w1110) && !(w0101 && w0111 && w1101 && w1111)) = true →
      (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w0110 then 1 else 0) +
        (if w0111 then 1 else 0))) + (((if w1100 then 1 else 0) + (if w1101 then 1 else 0)) +
        ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row1011 : ∀ w1000 w1001 w1010 w1011 w1100 w1101 w1110 w1111 : Bool,
      (!(w1000 && w1001 && w1100 && w1101) && !(w1000 && w1011 && w1100 && w1111) &&
        !(w1010 && w1001 && w1110 && w1101) && !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w1000 then 1 else 0) + (if w1001 then 1 else 0)) + ((if w1010 then 1 else 0) +
        (if w1011 then 1 else 0))) + (((if w1100 then 1 else 0) + (if w1101 then 1 else 0)) +
        ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_row000110 : ∀ w0000 w0001 w0010 w0011 w0100 w0101 w0110 w0111 w1000 w1001 w1010 w1011 :
      Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0000 && w0011 && w1000 && w1011) &&
        !(w0001 && w0010 && w1001 && w1010) && !(w0001 && w0011 && w1001 && w1011) &&
        !(w0100 && w0110 && w1000 && w1010) && !(w0100 && w0111 && w1000 && w1011) &&
        !(w0101 && w0110 && w1001 && w1010) && !(w0101 && w0111 && w1001 && w1011) &&
        !(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0011 && w0100 && w0111) &&
        !(w0010 && w0001 && w0110 && w0101) && !(w0010 && w0011 && w0110 && w0111) &&
        !(w1000 && w1001 && w0100 && w0101) && !(w1000 && w1011 && w0100 && w0111) &&
        !(w1010 && w1001 && w0110 && w0101) && !(w1010 && w1011 && w0110 && w0111)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w0110 then 1 else 0) + (if w0111 then 1 else 0))) + (((if w1000 then 1 else 0) +
        (if w1001 then 1 else 0)) + ((if w1010 then 1 else 0) + (if w1011 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_row000111 : ∀ w0000 w0001 w0010 w0011 w0100 w0101 w0110 w0111 w1100 w1101 w1110 w1111 :
      Bool,
      (!(w0000 && w0010 && w1100 && w1110) && !(w0000 && w0011 && w1100 && w1111) &&
        !(w0001 && w0010 && w1101 && w1110) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0100 && w0110 && w1100 && w1110) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0101 && w0110 && w1101 && w1110) && !(w0101 && w0111 && w1101 && w1111) &&
        !(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0011 && w0100 && w0111) &&
        !(w0010 && w0001 && w0110 && w0101) && !(w0010 && w0011 && w0110 && w0111) &&
        !(w0000 && w0001 && w1100 && w1101) && !(w0010 && w0001 && w1110 && w1101) &&
        !(w0010 && w0011 && w1110 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w0110 then 1 else 0) + (if w0111 then 1 else 0))) + (((if w1100 then 1 else 0) +
        (if w1101 then 1 else 0)) + ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_row001011 : ∀ w0000 w0001 w0010 w0011 w1000 w1001 w1010 w1011 w1100 w1101 w1110 w1111 :
      Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0000 && w0011 && w1000 && w1011) &&
        !(w0001 && w0010 && w1001 && w1010) && !(w0001 && w0011 && w1001 && w1011) &&
        !(w0000 && w0010 && w1100 && w1110) && !(w0000 && w0011 && w1100 && w1111) &&
        !(w0001 && w0010 && w1101 && w1110) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0000 && w0001 && w1100 && w1101) && !(w0010 && w0001 && w1110 && w1101) &&
        !(w0010 && w0011 && w1110 && w1111) && !(w1000 && w1001 && w1100 && w1101) &&
        !(w1000 && w1011 && w1100 && w1111) && !(w1010 && w1001 && w1110 && w1101) &&
        !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0001 then 1 else 0)) + ((if w0010 then 1 else 0) +
        (if w0011 then 1 else 0))) + (((if w1000 then 1 else 0) + (if w1001 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1011 then 1 else 0))) + (((if w1100 then 1 else 0) +
        (if w1101 then 1 else 0)) + ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_row011011 : ∀ w0100 w0101 w0110 w0111 w1000 w1001 w1010 w1011 w1100 w1101 w1110 w1111 :
      Bool,
      (!(w0100 && w0110 && w1000 && w1010) && !(w0100 && w0111 && w1000 && w1011) &&
        !(w0101 && w0110 && w1001 && w1010) && !(w0101 && w0111 && w1001 && w1011) &&
        !(w0100 && w0110 && w1100 && w1110) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0101 && w0110 && w1101 && w1110) && !(w0101 && w0111 && w1101 && w1111) &&
        !(w1000 && w1001 && w0100 && w0101) && !(w1000 && w1011 && w0100 && w0111) &&
        !(w1010 && w1001 && w0110 && w0101) && !(w1010 && w1011 && w0110 && w0111) &&
        !(w1000 && w1001 && w1100 && w1101) && !(w1000 && w1011 && w1100 && w1111) &&
        !(w1010 && w1001 && w1110 && w1101) && !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w0100 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w0110 then 1 else 0) +
        (if w0111 then 1 else 0))) + (((if w1000 then 1 else 0) + (if w1001 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1011 then 1 else 0))) + (((if w1100 then 1 else 0) +
        (if w1101 then 1 else 0)) + ((if w1110 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_col0001 : ∀ w0000 w0100 w1000 w1100 w0001 w0101 w1001 w1101 : Bool,
      (!(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0001 && w1100 && w1101) &&
        !(w1000 && w1001 && w0100 && w0101) && !(w1000 && w1001 && w1100 && w1101)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w1001 then 1 else 0) + (if w1101 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col0010 : ∀ w0000 w0100 w1000 w1100 w0010 w0110 w1010 w1110 : Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0000 && w0010 && w1100 && w1110) &&
        !(w0100 && w0110 && w1000 && w1010) && !(w0100 && w0110 && w1100 && w1110)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0010 then 1 else 0) + (if w0110 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1110 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col0011 : ∀ w0000 w0100 w1000 w1100 w0011 w0111 w1011 w1111 : Bool,
      (!(w0000 && w0011 && w1000 && w1011) && !(w0000 && w0011 && w1100 && w1111) &&
        !(w0100 && w0111 && w1000 && w1011) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0000 && w0011 && w0100 && w0111) && !(w1000 && w1011 && w0100 && w0111) &&
        !(w1000 && w1011 && w1100 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0011 then 1 else 0) + (if w0111 then 1 else 0)) +
        ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col0110 : ∀ w0001 w0101 w1001 w1101 w0010 w0110 w1010 w1110 : Bool,
      (!(w0001 && w0010 && w1001 && w1010) && !(w0001 && w0010 && w1101 && w1110) &&
        !(w0101 && w0110 && w1001 && w1010) && !(w0101 && w0110 && w1101 && w1110) &&
        !(w0010 && w0001 && w0110 && w0101) && !(w0010 && w0001 && w1110 && w1101) &&
        !(w1010 && w1001 && w0110 && w0101) && !(w1010 && w1001 && w1110 && w1101)) = true →
      (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w1001 then 1 else 0) +
        (if w1101 then 1 else 0))) + (((if w0010 then 1 else 0) + (if w0110 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1110 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col0111 : ∀ w0001 w0101 w1001 w1101 w0011 w0111 w1011 w1111 : Bool,
      (!(w0001 && w0011 && w1001 && w1011) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0101 && w0111 && w1001 && w1011) && !(w0101 && w0111 && w1101 && w1111)) = true →
      (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w1001 then 1 else 0) +
        (if w1101 then 1 else 0))) + (((if w0011 then 1 else 0) + (if w0111 then 1 else 0)) +
        ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col1011 : ∀ w0010 w0110 w1010 w1110 w0011 w0111 w1011 w1111 : Bool,
      (!(w0010 && w0011 && w0110 && w0111) && !(w0010 && w0011 && w1110 && w1111) &&
        !(w1010 && w1011 && w0110 && w0111) && !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w0010 then 1 else 0) + (if w0110 then 1 else 0)) + ((if w1010 then 1 else 0) +
        (if w1110 then 1 else 0))) + (((if w0011 then 1 else 0) + (if w0111 then 1 else 0)) +
        ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 6 := by
    decide +kernel
  have bound_col000110 : ∀ w0000 w0100 w1000 w1100 w0001 w0101 w1001 w1101 w0010 w0110 w1010 w1110 :
      Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0001 && w0010 && w1001 && w1010) &&
        !(w0000 && w0010 && w1100 && w1110) && !(w0001 && w0010 && w1101 && w1110) &&
        !(w0100 && w0110 && w1000 && w1010) && !(w0101 && w0110 && w1001 && w1010) &&
        !(w0100 && w0110 && w1100 && w1110) && !(w0101 && w0110 && w1101 && w1110) &&
        !(w0000 && w0001 && w0100 && w0101) && !(w0010 && w0001 && w0110 && w0101) &&
        !(w0000 && w0001 && w1100 && w1101) && !(w0010 && w0001 && w1110 && w1101) &&
        !(w1000 && w1001 && w0100 && w0101) && !(w1010 && w1001 && w0110 && w0101) &&
        !(w1000 && w1001 && w1100 && w1101) && !(w1010 && w1001 && w1110 && w1101)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w1001 then 1 else 0) + (if w1101 then 1 else 0))) + (((if w0010 then 1 else 0) +
        (if w0110 then 1 else 0)) + ((if w1010 then 1 else 0) + (if w1110 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_col000111 : ∀ w0000 w0100 w1000 w1100 w0001 w0101 w1001 w1101 w0011 w0111 w1011 w1111 :
      Bool,
      (!(w0000 && w0011 && w1000 && w1011) && !(w0001 && w0011 && w1001 && w1011) &&
        !(w0000 && w0011 && w1100 && w1111) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0100 && w0111 && w1000 && w1011) && !(w0101 && w0111 && w1001 && w1011) &&
        !(w0100 && w0111 && w1100 && w1111) && !(w0101 && w0111 && w1101 && w1111) &&
        !(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0011 && w0100 && w0111) &&
        !(w0000 && w0001 && w1100 && w1101) && !(w1000 && w1001 && w0100 && w0101) &&
        !(w1000 && w1011 && w0100 && w0111) && !(w1000 && w1001 && w1100 && w1101) &&
        !(w1000 && w1011 && w1100 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) +
        ((if w1001 then 1 else 0) + (if w1101 then 1 else 0))) + (((if w0011 then 1 else 0) +
        (if w0111 then 1 else 0)) + ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_col001011 : ∀ w0000 w0100 w1000 w1100 w0010 w0110 w1010 w1110 w0011 w0111 w1011 w1111 :
      Bool,
      (!(w0000 && w0010 && w1000 && w1010) && !(w0000 && w0011 && w1000 && w1011) &&
        !(w0000 && w0010 && w1100 && w1110) && !(w0000 && w0011 && w1100 && w1111) &&
        !(w0100 && w0110 && w1000 && w1010) && !(w0100 && w0111 && w1000 && w1011) &&
        !(w0100 && w0110 && w1100 && w1110) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0000 && w0011 && w0100 && w0111) && !(w0010 && w0011 && w0110 && w0111) &&
        !(w0010 && w0011 && w1110 && w1111) && !(w1000 && w1011 && w0100 && w0111) &&
        !(w1010 && w1011 && w0110 && w0111) && !(w1000 && w1011 && w1100 && w1111) &&
        !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w0000 then 1 else 0) + (if w0100 then 1 else 0)) + ((if w1000 then 1 else 0) +
        (if w1100 then 1 else 0))) + (((if w0010 then 1 else 0) + (if w0110 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1110 then 1 else 0))) + (((if w0011 then 1 else 0) +
        (if w0111 then 1 else 0)) + ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_col011011 : ∀ w0001 w0101 w1001 w1101 w0010 w0110 w1010 w1110 w0011 w0111 w1011 w1111 :
      Bool,
      (!(w0001 && w0010 && w1001 && w1010) && !(w0001 && w0011 && w1001 && w1011) &&
        !(w0001 && w0010 && w1101 && w1110) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0101 && w0110 && w1001 && w1010) && !(w0101 && w0111 && w1001 && w1011) &&
        !(w0101 && w0110 && w1101 && w1110) && !(w0101 && w0111 && w1101 && w1111) &&
        !(w0010 && w0001 && w0110 && w0101) && !(w0010 && w0011 && w0110 && w0111) &&
        !(w0010 && w0001 && w1110 && w1101) && !(w0010 && w0011 && w1110 && w1111) &&
        !(w1010 && w1001 && w0110 && w0101) && !(w1010 && w1011 && w0110 && w0111) &&
        !(w1010 && w1001 && w1110 && w1101) && !(w1010 && w1011 && w1110 && w1111)) = true →
      (((if w0001 then 1 else 0) + (if w0101 then 1 else 0)) + ((if w1001 then 1 else 0) +
        (if w1101 then 1 else 0))) + (((if w0010 then 1 else 0) + (if w0110 then 1 else 0)) +
        ((if w1010 then 1 else 0) + (if w1110 then 1 else 0))) + (((if w0011 then 1 else 0) +
        (if w0111 then 1 else 0)) + ((if w1011 then 1 else 0) + (if w1111 then 1 else 0))) ≤ 8 := by
    decide +kernel
  have bound_symsym : ∀ w0000 w0001 w0011 w0100 w0101 w0111 w1100 w1101 w1111 : Bool,
      (!(w0000 && w0011 && w1100 && w1111) && !(w0001 && w0011 && w1101 && w1111) &&
        !(w0100 && w0111 && w1100 && w1111) && !(w0101 && w0111 && w1101 && w1111) &&
        !(w0000 && w0001 && w0100 && w0101) && !(w0000 && w0011 && w0100 && w0111) &&
        !(w0000 && w0001 && w1100 && w1101)) = true →
      (((if w0000 then 1 else 0) + ((if w0001 then 1 else 0) + (if w0011 then 1 else 0))) +
        (((if w0100 then 1 else 0) + ((if w0101 then 1 else 0) + (if w0111 then 1 else 0))) +
        ((if w1100 then 1 else 0) + ((if w1101 then 1 else 0) +
        (if w1111 then 1 else 0))))) ≤ 7 := by
    decide +kernel
  have bound_symasym : ∀ w0000 w0011 w0100 w0111 w1100 w1111 : Bool,
      (!(w0000 && w0011 && w1100 && w1111) && !(w0100 && w0111 && w1100 && w1111) &&
        !(w0000 && w0011 && w0100 && w0111)) = true →
      (((if w0000 then 1 else 0) + (if w0011 then 1 else 0)) + (((if w0100 then 1 else 0) +
        (if w0111 then 1 else 0)) + ((if w1100 then 1 else 0) +
        (if w1111 then 1 else 0)))) ≤ 4 := by
    decide +kernel
  have hrow4 : ∀ (α β : Inp → Fin d × Fin d) (X : Inp), rowSum α β X ≤ 4 := by
    intro α β X
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    split_ifs <;> omega
  have hcol4 : ∀ (α β : Inp → Fin d × Fin d) (Y : Inp), colSum α β Y ≤ 4 := by
    intro α β Y
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    split_ifs <;> omega
  have h_row0001 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (0, 1) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row0001 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect2 α β, Bool.not_false, Bool.and_self])
  have h_row0010 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (1, 0) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row0010 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, Bool.not_false, Bool.and_self])
  have h_row0011 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row0011 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_row0110 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 1) + rowSum α β (1, 0) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row0110 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_row0111 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 1) + rowSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row0111 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, Bool.not_false, Bool.and_self])
  have h_row1011 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (1, 0) + rowSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row1011 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect2 α β, Bool.not_false, Bool.and_self])
  have h_row000110 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (0, 1) + rowSum α β (1, 0) ≤ 8 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row000110 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_row000111 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (0, 1) + rowSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row000111 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_row001011 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 0) + rowSum α β (1, 0) + rowSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row001011 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_row011011 : ∀ α β : Inp → Fin d × Fin d,
      rowSum α β (0, 1) + rowSum α β (1, 0) + rowSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [rowSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_row011011 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col0001 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (0, 1) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col0001 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect2 α β, Bool.not_false, Bool.and_self])
  have h_col0010 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (1, 0) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col0010 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, Bool.not_false, Bool.and_self])
  have h_col0011 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col0011 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col0110 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 1) + colSum α β (1, 0) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col0110 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col0111 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 1) + colSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col0111 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, Bool.not_false, Bool.and_self])
  have h_col1011 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (1, 0) + colSum α β (1, 1) ≤ 6 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col1011 _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect2 α β, Bool.not_false, Bool.and_self])
  have h_col000110 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (0, 1) + colSum α β (1, 0) ≤ 8 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col000110 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col000111 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (0, 1) + colSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col000111 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col001011 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 0) + colSum α β (1, 0) + colSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col001011 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have h_col011011 : ∀ α β : Inp → Fin d × Fin d,
      colSum α β (0, 1) + colSum α β (1, 0) + colSum α β (1, 1) ≤ 8 := by
    intro α β
    simp only [colSum, Fintype.sum_prod_type, Fin.sum_univ_two]
    exact bound_col011011 _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have detAB : ∀ (α : Inp → Fin d × Fin d) (β : Inp → Bool → Fin d × Fin d) (m : Inp → Bool),
      (∑ X, ∑ Y, if decide (wins X Y (α X) (β Y (m X))) then 1 else 0 : ℕ) ≤ 12 := by
    intro α β m
    change ∑ X, rowSum α (fun Y => β Y (m X)) X ≤ 12
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    have := hrow4 α (fun Y => β Y true) (0, 0)
    have := hrow4 α (fun Y => β Y true) (0, 1)
    have := hrow4 α (fun Y => β Y true) (1, 0)
    have := hrow4 α (fun Y => β Y true) (1, 1)
    have := h_row0001 α (fun Y => β Y true)
    have := h_row0010 α (fun Y => β Y true)
    have := h_row0011 α (fun Y => β Y true)
    have := h_row0110 α (fun Y => β Y true)
    have := h_row0111 α (fun Y => β Y true)
    have := h_row1011 α (fun Y => β Y true)
    have := h_row000110 α (fun Y => β Y true)
    have := h_row000111 α (fun Y => β Y true)
    have := h_row001011 α (fun Y => β Y true)
    have := h_row011011 α (fun Y => β Y true)
    have := hrow4 α (fun Y => β Y false) (0, 0)
    have := hrow4 α (fun Y => β Y false) (0, 1)
    have := hrow4 α (fun Y => β Y false) (1, 0)
    have := hrow4 α (fun Y => β Y false) (1, 1)
    have := h_row0001 α (fun Y => β Y false)
    have := h_row0010 α (fun Y => β Y false)
    have := h_row0011 α (fun Y => β Y false)
    have := h_row0110 α (fun Y => β Y false)
    have := h_row0111 α (fun Y => β Y false)
    have := h_row1011 α (fun Y => β Y false)
    have := h_row000110 α (fun Y => β Y false)
    have := h_row000111 α (fun Y => β Y false)
    have := h_row001011 α (fun Y => β Y false)
    have := h_row011011 α (fun Y => β Y false)
    cases m (0, 0) <;> cases m (0, 1) <;> cases m (1, 0) <;> cases m (1, 1) <;> omega
  have detBA : ∀ (α : Inp → Bool → Fin d × Fin d) (β : Inp → Fin d × Fin d) (m : Inp → Bool),
      (∑ X, ∑ Y, if decide (wins X Y (α X (m Y)) (β Y)) then 1 else 0 : ℕ) ≤ 12 := by
    intro α β m
    rw [Finset.sum_comm]
    change ∑ Y, colSum (fun X => α X (m Y)) β Y ≤ 12
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    have := hcol4 (fun X => α X true) β (0, 0)
    have := hcol4 (fun X => α X true) β (0, 1)
    have := hcol4 (fun X => α X true) β (1, 0)
    have := hcol4 (fun X => α X true) β (1, 1)
    have := h_col0001 (fun X => α X true) β
    have := h_col0010 (fun X => α X true) β
    have := h_col0011 (fun X => α X true) β
    have := h_col0110 (fun X => α X true) β
    have := h_col0111 (fun X => α X true) β
    have := h_col1011 (fun X => α X true) β
    have := h_col000110 (fun X => α X true) β
    have := h_col000111 (fun X => α X true) β
    have := h_col001011 (fun X => α X true) β
    have := h_col011011 (fun X => α X true) β
    have := hcol4 (fun X => α X false) β (0, 0)
    have := hcol4 (fun X => α X false) β (0, 1)
    have := hcol4 (fun X => α X false) β (1, 0)
    have := hcol4 (fun X => α X false) β (1, 1)
    have := h_col0001 (fun X => α X false) β
    have := h_col0010 (fun X => α X false) β
    have := h_col0011 (fun X => α X false) β
    have := h_col0110 (fun X => α X false) β
    have := h_col0111 (fun X => α X false) β
    have := h_col1011 (fun X => α X false) β
    have := h_col000110 (fun X => α X false) β
    have := h_col000111 (fun X => α X false) β
    have := h_col001011 (fun X => α X false) β
    have := h_col011011 (fun X => α X false) β
    cases m (0, 0) <;> cases m (0, 1) <;> cases m (1, 0) <;> cases m (1, 1) <;> omega
  have detS : ∀ α β : Inp → Fin d × Fin d,
      (∑ X ∈ symInputs, ∑ Y ∈ symInputs, if decide (wins X Y (α X) (β Y)) then 1 else 0 : ℕ)
        ≤ 7 := by
    intro α β
    simp (disch := decide) only [symInputs, Finset.sum_insert, Finset.sum_singleton]
    exact bound_symsym _ _ _ _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  have detA : ∀ α β : Inp → Fin d × Fin d,
      (∑ X ∈ symInputs, ∑ Y ∈ asymInputs, if decide (wins X Y (α X) (β Y)) then 1 else 0 : ℕ)
        ≤ 4 := by
    intro α β
    simp (disch := decide) only [symInputs, asymInputs, Finset.sum_insert, Finset.sum_singleton]
    exact bound_symasym _ _ _ _ _ _ (by
      simp (disch := decide) only [rect1 α β, rect2 α β, Bool.not_false, Bool.and_self])
  -- a response distribution can be replaced by a best output
  have hne : Nonempty (Fin d × Fin d) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hbest : ∀ p g : Fin d × Fin d → ℝ, (∀ A, 0 ≤ p A) → ∑ A, p A = 1 →
      ∃ A₀, ∑ A, p A * g A ≤ g A₀ := by
    intro p g hp hs
    obtain ⟨A₀, -, hA₀⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
    refine ⟨A₀, ?_⟩
    calc ∑ A, p A * g A ≤ ∑ A, p A * g A₀ :=
          Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hA₀ A (Finset.mem_univ A)) (hp A)
      _ = g A₀ := by rw [← Finset.sum_mul, hs, one_mul]
  have hle1 : ∀ r : ℝ → Fin d × Fin d → ℝ, IsResponse r → ∀ t A, r t A ≤ 1 := by
    intro r hr t A
    rw [← hr.2.2 t]
    exact Finset.single_le_sum (fun B _ => hr.2.1 t B) (Finset.mem_univ A)
  -- derandomisation at a fixed hidden value, for any Boolean winning relation
  have derandPoint : ∀ (r : Inp → Inp → Fin d × Fin d → Fin d × Fin d → Bool) (XS YS : Finset Inp)
      (pA : Inp → Fin d × Fin d → ℝ) (m : Inp → Bool) (pB : Inp → Bool → Fin d × Fin d → ℝ)
      (K : ℝ), (∀ X A, 0 ≤ pA X A) → (∀ X, ∑ A, pA X A = 1) → (∀ Y b B, 0 ≤ pB Y b B) →
      (∀ Y b, ∑ B, pB Y b B = 1) →
      (∀ (α : Inp → Fin d × Fin d) (β : Inp → Bool → Fin d × Fin d),
        ∑ X ∈ XS, ∑ Y ∈ YS, (if r X Y (α X) (β Y (m X)) then (1 : ℝ) else 0) ≤ K) →
      ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B, (if r X Y A B then pA X A * pB Y (m X) B else 0) ≤ K := by
    intro r XS YS pA m pB K hpA hsA hpB hsB hK
    -- Alice's best outputs
    have h1 : ∀ X, ∃ A₀, ∑ A, pA X A * (∑ Y ∈ YS, ∑ B, if r X Y A B then pB Y (m X) B else 0) ≤
        ∑ Y ∈ YS, ∑ B, if r X Y A₀ B then pB Y (m X) B else 0 :=
      fun X => hbest (pA X) _ (hpA X) (hsA X)
    choose α hα using h1
    -- split the Alice inputs by the message they send
    have split : ∀ G : Inp → Bool → ℝ,
        ∑ X ∈ XS, G X (m X) = ∑ b : Bool, ∑ X ∈ XS.filter (fun X => m X = b), G X b := by
      intro G
      rw [Fintype.sum_bool, ← Finset.sum_filter_add_sum_filter_not XS (fun X => m X = true)]
      congr 1
      · exact Finset.sum_congr rfl fun X hX => by rw [(Finset.mem_filter.mp hX).2]
      · rw [show XS.filter (fun X => ¬ m X = true) = XS.filter (fun X => m X = false) from
          Finset.filter_congr fun X _ => by simp]
        exact Finset.sum_congr rfl fun X hX => by rw [(Finset.mem_filter.mp hX).2]
    -- Bob's best outputs, for each message
    have h2 : ∀ Y b, ∃ B₀, ∑ B, pB Y b B *
        (∑ X ∈ XS.filter (fun X => m X = b), if r X Y (α X) B then (1 : ℝ) else 0) ≤
        ∑ X ∈ XS.filter (fun X => m X = b), if r X Y (α X) B₀ then (1 : ℝ) else 0 :=
      fun Y b => hbest (pB Y b) _ (hpB Y b) (hsB Y b)
    choose β hβ using h2
    calc ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B, (if r X Y A B then pA X A * pB Y (m X) B else 0)
        = ∑ X ∈ XS, ∑ A, pA X A * (∑ Y ∈ YS, ∑ B, if r X Y A B then pB Y (m X) B else 0) := by
          refine Finset.sum_congr rfl fun X _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun Y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ X ∈ XS, ∑ Y ∈ YS, ∑ B, (if r X Y (α X) B then pB Y (m X) B else 0) :=
          Finset.sum_le_sum fun X _ => hα X
      _ = ∑ Y ∈ YS, ∑ b : Bool, ∑ X ∈ XS.filter (fun X => m X = b), ∑ B,
            (if r X Y (α X) B then pB Y b B else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun Y _ =>
            split fun X b => ∑ B, if r X Y (α X) B then pB Y b B else 0
      _ = ∑ Y ∈ YS, ∑ b : Bool, ∑ B, pB Y b B *
            (∑ X ∈ XS.filter (fun X => m X = b), if r X Y (α X) B then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun X _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ Y ∈ YS, ∑ b : Bool, ∑ X ∈ XS.filter (fun X => m X = b),
            (if r X Y (α X) (β Y b) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun b _ => hβ Y b
      _ = ∑ X ∈ XS, ∑ Y ∈ YS, (if r X Y (α X) (β Y (m X)) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm (s := XS)]
          exact Finset.sum_congr rfl fun Y _ =>
            (split fun X b => if r X Y (α X) (β Y b) then (1 : ℝ) else 0).symm
      _ ≤ K := hK α β
  -- integrating over the hidden variable
  have derand : ∀ (r : Inp → Inp → Fin d × Fin d → Fin d × Fin d → Bool) (XS YS : Finset Inp)
      (μ : Measure ℝ), IsProbabilityMeasure μ → ∀ (pA : Inp → ℝ → Fin d × Fin d → ℝ)
      (l : Inp → ℝ → Bool) (pB : Inp → Bool → ℝ → Fin d × Fin d → ℝ) (K : ℝ),
      (∀ X, IsResponse (pA X)) → (∀ X, Measurable (l X)) → (∀ Y b, IsResponse (pB Y b)) →
      (∀ t (α : Inp → Fin d × Fin d) (β : Inp → Bool → Fin d × Fin d),
        ∑ X ∈ XS, ∑ Y ∈ YS, (if r X Y (α X) (β Y (l X t)) then (1 : ℝ) else 0) ≤ K) →
      ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B,
        (if r X Y A B then ∫ t, pA X t A * pB Y (l X t) t B ∂μ else 0) ≤ K := by
    intro r XS YS μ hμ pA l pB K hA hl hB hK
    have hint : ∀ X Y A B, Integrable
        (fun t => if r X Y A B then pA X t A * pB Y (l X t) t B else 0) μ := by
      intro X Y A B
      have hm : Measurable fun t => pB Y (l X t) t B := by
        have e : (fun t => pB Y (l X t) t B) =
            fun t => if l X t = true then pB Y true t B else pB Y false t B := by
          funext t
          cases l X t <;> rfl
        rw [e]
        exact Measurable.ite ((hl X) (measurableSet_singleton true)) ((hB Y true).1 B)
          ((hB Y false).1 B)
      have hbd : ∀ t, ‖pA X t A * pB Y (l X t) t B‖ ≤ 1 := by
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ((hA X).2.1 t A) ((hB Y _).2.1 t B))]
        calc pA X t A * pB Y (l X t) t B ≤ 1 * 1 :=
              mul_le_mul (hle1 _ (hA X) t A) (hle1 _ (hB Y _) t B) ((hB Y _).2.1 t B) zero_le_one
          _ = 1 := one_mul 1
      split_ifs
      · exact Integrable.of_bound ((((hA X).1 A).mul hm).aestronglyMeasurable) 1
          (Filter.Eventually.of_forall hbd)
      · exact integrable_zero _ _ _
    have hsum : ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B,
        (if r X Y A B then ∫ t, pA X t A * pB Y (l X t) t B ∂μ else 0) =
        ∫ t, ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B,
          (if r X Y A B then pA X t A * pB Y (l X t) t B else 0) ∂μ := by
      rw [integral_finsetSum _ fun X _ => integrable_finsetSum _ fun Y _ =>
        integrable_finsetSum _ fun A _ => integrable_finsetSum _ fun B _ => hint X Y A B]
      refine Finset.sum_congr rfl fun X _ => ?_
      rw [integral_finsetSum _ fun Y _ => integrable_finsetSum _ fun A _ =>
        integrable_finsetSum _ fun B _ => hint X Y A B]
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [integral_finsetSum _ fun A _ => integrable_finsetSum _ fun B _ => hint X Y A B]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [integral_finsetSum _ fun B _ => hint X Y A B]
      refine Finset.sum_congr rfl fun B _ => ?_
      split_ifs <;> simp
    have hpt : ∀ t, ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B,
        (if r X Y A B then pA X t A * pB Y (l X t) t B else 0) ≤ K := fun t =>
      derandPoint r XS YS (fun X A => pA X t A) (fun X => l X t) (fun Y b B => pB Y b t B) K
        (fun X A => (hA X).2.1 t A) (fun X => (hA X).2.2 t) (fun Y b B => (hB Y b).2.1 t B)
        (fun Y b => (hB Y b).2.2 t) (fun α β => hK t α β)
    rw [hsum]
    calc ∫ t, ∑ X ∈ XS, ∑ Y ∈ YS, ∑ A, ∑ B,
          (if r X Y A B then pA X t A * pB Y (l X t) t B else 0) ∂μ ≤ ∫ _, K ∂μ :=
          integral_mono (integrable_finsetSum _ fun X _ => integrable_finsetSum _ fun Y _ =>
            integrable_finsetSum _ fun A _ => integrable_finsetSum _ fun B _ => hint X Y A B)
            (integrable_const K) hpt
      _ = K := by simp
  -- the deterministic counts as real numbers
  have castAB : ∀ (α : Inp → Fin d × Fin d) (β : Inp → Bool → Fin d × Fin d) (m : Inp → Bool),
      ∑ X, ∑ Y, (if decide (wins X Y (α X) (β Y (m X))) then (1 : ℝ) else 0) ≤ 12 := by
    intro α β m
    exact_mod_cast detAB α β m
  have castBA : ∀ (α : Inp → Bool → Fin d × Fin d) (β : Inp → Fin d × Fin d) (m : Inp → Bool),
      ∑ X, ∑ Y, (if decide (wins X Y (α X (m Y)) (β Y)) then (1 : ℝ) else 0) ≤ 12 := by
    intro α β m
    exact_mod_cast detBA α β m
  have castS : ∀ α β : Inp → Fin d × Fin d,
      ∑ X ∈ symInputs, ∑ Y ∈ symInputs, (if decide (wins X Y (α X) (β Y)) then (1 : ℝ) else 0)
        ≤ 7 := by
    intro α β
    exact_mod_cast detS α β
  have castA : ∀ α β : Inp → Fin d × Fin d,
      ∑ X ∈ symInputs, ∑ Y ∈ asymInputs, (if decide (wins X Y (α X) (β Y)) then (1 : ℝ) else 0)
        ≤ 4 := by
    intro α β
    exact_mod_cast detA α β
  -- upper bounds for the three classes
  have upAB : ∀ P, IsOneBitAB d P → bell Finset.univ Finset.univ P ≤ 12 := by
    rintro P ⟨μ, hμ, pA, l, pB, hA, hl, hB, hP⟩
    have := derand (fun X Y A B => decide (wins X Y A B)) Finset.univ Finset.univ μ hμ pA l pB 12
      hA hl hB fun t α β => castAB α β fun X => l X t
    simpa only [bell, hP, decide_eq_true_eq] using this
  have upBA : ∀ P, IsOneBitBA d P → bell Finset.univ Finset.univ P ≤ 12 := by
    rintro P ⟨μ, hμ, pA, l, pB, hA, hl, hB, hP⟩
    have := derand (fun Y X B A => decide (wins X Y A B)) Finset.univ Finset.univ μ hμ pB l pA 12
      hB hl hA fun t β α => by
        rw [Finset.sum_comm]
        exact castBA α β fun Y => l Y t
    simp only [bell, hP]
    rw [Finset.sum_comm]
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun X _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun A _ => ?_
    simp only [decide_eq_true_eq, mul_comm]
  have upLocal : ∀ (XS YS : Finset Inp) (K : ℝ),
      (∀ α β : Inp → Fin d × Fin d,
        ∑ X ∈ XS, ∑ Y ∈ YS, (if decide (wins X Y (α X) (β Y)) then (1 : ℝ) else 0) ≤ K) →
      ∀ P, IsLocal d P → bell XS YS P ≤ K := by
    rintro XS YS K hK P ⟨μ, hμ, pA, pB, hA, hB, hP⟩
    have := derand (fun X Y A B => decide (wins X Y A B)) XS YS μ hμ pA (fun _ _ => false)
      (fun Y _ => pB Y) K hA (fun _ => measurable_const) (fun Y _ => hB Y)
      fun _ α β => hK α fun Y => β Y false
    simpa only [bell, hP, decide_eq_true_eq] using this
  -- deterministic strategies with outputs in {0, 1}, embedded in Fin d
  let emb : Fin 2 × Fin 2 → Fin d × Fin d := fun A => (Fin.castLE hd A.1, Fin.castLE hd A.2)
  have hemb : ∀ X Y (A B : Fin 2 × Fin 2), wins X Y (emb A) (emb B) ↔ wins X Y A B := by
    intro X Y A B
    simp only [emb, wins, copyWins, Fin.le_def, Fin.lt_def, Fin.val_castLE]
  have point : ∀ (a₀ : Fin d × Fin d), IsResponse (d := d) fun _ A => if A = a₀ then 1 else 0 :=
    fun a₀ => ⟨fun _ => measurable_const, fun _ A => by
      change (0 : ℝ) ≤ if A = a₀ then 1 else 0
      split_ifs <;> norm_num, fun _ => by simp⟩
  have collapse : ∀ X Y (a₀ b₀ : Fin d × Fin d),
      (∑ A, ∑ B, if wins X Y A B then
        ∫ _ : ℝ, (if A = a₀ then (1 : ℝ) else 0) * (if B = b₀ then 1 else 0) ∂Measure.dirac 0
        else 0) = if wins X Y a₀ b₀ then 1 else 0 := by
    intro X Y a₀ b₀
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [Finset.sum_eq_single a₀ (fun A _ hA => by simp [hA]) (by simp)]
    rw [Finset.sum_eq_single b₀ (fun B _ hB => by simp [hB]) (by simp)]
    simp
  -- deterministic models: a point mass and point responses
  have achAB : ∀ (α : Inp → Fin 2 × Fin 2) (m : Inp → Bool) (β : Inp → Bool → Fin 2 × Fin 2),
      ∃ P, IsOneBitAB d P ∧ bell Finset.univ Finset.univ P =
        ∑ X, ∑ Y, if wins X Y (α X) (β Y (m X)) then (1 : ℝ) else 0 := by
    intro α m β
    refine ⟨fun X Y A B => ∫ _ : ℝ, (if A = emb (α X) then (1 : ℝ) else 0) *
        (if B = emb (β Y (m X)) then 1 else 0) ∂Measure.dirac 0,
      ⟨Measure.dirac 0, inferInstance, fun X _ A => if A = emb (α X) then 1 else 0,
        fun X _ => m X, fun Y b _ B => if B = emb (β Y b) then 1 else 0, fun X => point _,
        fun _ => measurable_const, fun Y b => point _, fun X Y A B => rfl⟩, ?_⟩
    simp only [bell, collapse, hemb]
  have achBA : ∀ (α : Inp → Bool → Fin 2 × Fin 2) (m : Inp → Bool) (β : Inp → Fin 2 × Fin 2),
      ∃ P, IsOneBitBA d P ∧ bell Finset.univ Finset.univ P =
        ∑ X, ∑ Y, if wins X Y (α X (m Y)) (β Y) then (1 : ℝ) else 0 := by
    intro α m β
    refine ⟨fun X Y A B => ∫ _ : ℝ, (if A = emb (α X (m Y)) then (1 : ℝ) else 0) *
        (if B = emb (β Y) then 1 else 0) ∂Measure.dirac 0,
      ⟨Measure.dirac 0, inferInstance, fun X b _ A => if A = emb (α X b) then 1 else 0,
        fun Y _ => m Y, fun Y _ B => if B = emb (β Y) then 1 else 0, fun X b => point _,
        fun _ => measurable_const, fun Y => point _, fun X Y A B => rfl⟩, ?_⟩
    simp only [bell, collapse, hemb]
  have achLocal : ∀ (XS YS : Finset Inp) (α β : Inp → Fin 2 × Fin 2),
      ∃ P, IsLocal d P ∧ bell XS YS P =
        ∑ X ∈ XS, ∑ Y ∈ YS, if wins X Y (α X) (β Y) then (1 : ℝ) else 0 := by
    intro XS YS α β
    refine ⟨fun X Y A B => ∫ _ : ℝ, (if A = emb (α X) then (1 : ℝ) else 0) *
        (if B = emb (β Y) then 1 else 0) ∂Measure.dirac 0,
      ⟨Measure.dirac 0, inferInstance, fun X _ A => if A = emb (α X) then 1 else 0,
        fun Y _ B => if B = emb (β Y) then 1 else 0, fun X => point _, fun Y => point _,
        fun X Y A B => rfl⟩, ?_⟩
    simp only [bell, collapse, hemb]
  -- the four statements
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨P, hP, hv⟩ := achAB (fun _ => (0, 0)) (fun X => decide (X ≠ (0, 0)))
      (fun Y b => if b then (if Y = (0, 0) then (0, 1) else if Y = (0, 1) then (1, 0)
        else if Y = (1, 0) then (0, 1) else (0, 0)) else (0, 0))
    refine ⟨P, hP, hv.trans ?_⟩
    exact_mod_cast (by decide : (∑ X : Inp, ∑ Y : Inp, if wins X Y ((0, 0) : Fin 2 × Fin 2)
      ((fun (Y : Inp) (b : Bool) => if b then (if Y = (0, 0) then ((0, 1) : Fin 2 × Fin 2)
        else if Y = (0, 1) then (1, 0) else if Y = (1, 0) then (0, 1) else (0, 0))
        else (0, 0)) Y (decide (X ≠ (0, 0)))) then 1 else 0 : ℕ) = 12)
  · rintro v ⟨P, hP, rfl⟩
    exact upAB P hP
  · obtain ⟨P, hP, hv⟩ := achBA (fun X b => if b then (0, 0) else (if X = (0, 0) then (0, 1)
        else if X = (0, 1) then (1, 0) else if X = (1, 0) then (0, 1) else (0, 0)))
      (fun Y => decide (Y = (1, 1)))
      (fun Y => if Y = (0, 0) then (1, 1) else if Y = (0, 1) then (1, 0)
        else if Y = (1, 0) then (0, 1) else (0, 0))
    refine ⟨P, hP, hv.trans ?_⟩
    exact_mod_cast (by decide : (∑ X : Inp, ∑ Y : Inp, if wins X Y
      ((fun (X : Inp) (b : Bool) => if b then ((0, 0) : Fin 2 × Fin 2) else
        (if X = (0, 0) then (0, 1) else if X = (0, 1) then (1, 0) else if X = (1, 0) then (0, 1)
        else (0, 0))) X (decide (Y = (1, 1))))
      ((fun (Y : Inp) => if Y = (0, 0) then ((1, 1) : Fin 2 × Fin 2) else if Y = (0, 1) then (1, 0)
        else if Y = (1, 0) then (0, 1) else (0, 0)) Y) then 1 else 0 : ℕ) = 12)
  · rintro v ⟨P, hP, rfl⟩
    exact upBA P hP
  · obtain ⟨P, hP, hv⟩ := achLocal symInputs symInputs
      (fun X => if X = (0, 0) then (1, 0) else if X = (0, 1) then (1, 0) else (0, 0))
      (fun Y => if Y = (0, 0) then (1, 1) else if Y = (0, 1) then (1, 0)
        else if Y = (1, 1) then (1, 0) else (0, 0))
    refine ⟨P, hP, hv.trans ?_⟩
    exact_mod_cast (by decide : (∑ X ∈ symInputs, ∑ Y ∈ symInputs, if wins X Y
      ((fun (X : Inp) => if X = (0, 0) then ((1, 0) : Fin 2 × Fin 2) else if X = (0, 1) then (1, 0)
        else (0, 0)) X)
      ((fun (Y : Inp) => if Y = (0, 0) then ((1, 1) : Fin 2 × Fin 2) else if Y = (0, 1) then (1, 0)
        else if Y = (1, 1) then (1, 0) else (0, 0)) Y) then 1 else 0 : ℕ) = 7)
  · rintro v ⟨P, hP, rfl⟩
    exact upLocal _ _ _ castS P hP
  · obtain ⟨P, hP, hv⟩ := achLocal symInputs asymInputs (fun _ => (0, 0)) (fun _ => (0, 0))
    refine ⟨P, hP, hv.trans ?_⟩
    exact_mod_cast (by decide : (∑ X ∈ symInputs, ∑ Y ∈ asymInputs,
      if wins X Y ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2) then 1 else 0 : ℕ) = 4)
  · rintro v ⟨P, hP, rfl⟩
    exact upLocal _ _ _ castA P hP

end D5.S3.Quantum.Information.DoubleCglmpOneBitBound
