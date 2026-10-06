/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The n = 3 genuine four-party multi-entropy collapse for pure qubit stabilizer states. -/

import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse

open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

/-- Translation in the coordinate assigned to `c`; the last party acts as the identity. -/
def shift (n q : ℕ) (c : Fin q) (r : Fin (q - 1) → ZMod n) :
    Fin (q - 1) → ZMod n :=
  fun i => if (i : ℕ) = (c : ℕ) then r i + 1 else r i

/-- The replica contraction on `(ℤ/n)^(q-1)`, with the last party unshifted. -/
def Z (n q : ℕ) [NeZero n] {N : ℕ} (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) : ℂ :=
  ∑ x : (Fin (q - 1) → ZMod n) → Fin N → Fin 2,
    ∏ r : Fin (q - 1) → ZMod n,
      star (ψ (x r)) * ψ (fun u => x (shift n q (col u) r) u)

/-- The normalized replica multi-entropy, using the real part of the complex quotient. -/
def S (n q : ℕ) [NeZero n] {N : ℕ} (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  1 / (1 - (n : ℝ)) * (1 / (n : ℝ) ^ (q - 2)) *
    Real.log ((Z n q col ψ / (Z 1 q col ψ) ^ (n ^ (q - 1))).re)

/-- The Rényi tripartite information: four singleton cuts minus three pair cuts. -/
def I3 (n : ℕ) [NeZero n] {N : ℕ} (party : Fin N → Fin 4)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  S n 2 ((![(0 : Fin 2), 0, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- ABC:D
    S n 2 ((![(0 : Fin 2), 0, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ABD:C
    S n 2 ((![(0 : Fin 2), 1, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ACD:B
    S n 2 ((![(1 : Fin 2), 0, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ - -- BCD:A
    (S n 2 ((![(0 : Fin 2), 0, 1, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- AB:CD
      S n 2 ((![(0 : Fin 2), 1, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- AC:BD
      S n 2 ((![(0 : Fin 2), 1, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ) -- AD:BC

/-- The genuine four-party multi-entropy with convention parameter `a`. -/
def GM4 (n : ℕ) [NeZero n] (a : ℝ) {N : ℕ} (party : Fin N → Fin 4)
    (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  S n 4 party ψ - 1 / 3 *
    (S n 3 ((![(0 : Fin 3), 0, 1, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- AB:C:D
      S n 3 ((![(0 : Fin 3), 1, 0, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- AC:B:D
      S n 3 ((![(0 : Fin 3), 1, 2, 0] : Fin 4 → Fin 3) ∘ party) ψ + -- AD:B:C
      S n 3 ((![(1 : Fin 3), 0, 0, 2] : Fin 4 → Fin 3) ∘ party) ψ + -- BC:A:D
      S n 3 ((![(1 : Fin 3), 0, 2, 0] : Fin 4 → Fin 3) ∘ party) ψ + -- BD:A:C
      S n 3 ((![(1 : Fin 3), 2, 0, 0] : Fin 4 → Fin 3) ∘ party) ψ) + -- CD:A:B
    1 / 3 *
      (S n 2 ((![(0 : Fin 2), 0, 0, 1] : Fin 4 → Fin 2) ∘ party) ψ + -- ABC:D
        S n 2 ((![(0 : Fin 2), 0, 1, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ABD:C
        S n 2 ((![(0 : Fin 2), 1, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ + -- ACD:B
        S n 2 ((![(1 : Fin 2), 0, 0, 0] : Fin 4 → Fin 2) ∘ party) ψ) - -- BCD:A
    a * I3 n party ψ

/-- Positivity of all n = 3 replica contractions and the four-party collapse. -/
def claim : Prop :=
  ∀ (N : ℕ) (party : Fin N → Fin 4) (ψ : (Fin N → Fin 2) → ℂ),
    StabilizedBy pauliSet ψ → (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 →
      (∀ (q : ℕ) (col : Fin N → Fin q),
        0 < (Z 3 q col ψ).re ∧ (Z 3 q col ψ).im = 0) ∧
      ∀ a : ℝ, GM4 3 a party ψ = -(a - 1 / 9) * I3 3 party ψ

theorem result : claim := by sorry

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
