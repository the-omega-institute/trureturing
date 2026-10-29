/- GID: D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim; result=D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result; claim=D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim
   digest: A completely symmetric three-qutrit density matrix is entangled. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled

open Matrix
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word occupation)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open scoped BigOperators ComplexOrder

/-- Invariance under all permutations of the ket and bra index positions. -/
def IsCompletelySymmetric {d : ℕ} (ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin d ⊕ Fin d)) (i j : Word (Fin 3) d),
    ρ (fun k => Sum.elim i j (π (Sum.inl k)))
      (fun k => Sum.elim i j (π (Sum.inr k))) = ρ i j

/-- Coordinates of the tensor product of the local vectors. -/
def productVector {d : ℕ} (v : Fin d → Fin 3 → ℂ) : Word (Fin 3) d → ℂ :=
  fun w => ∏ k, v k (w k)

/-- A finite convex combination of projectors onto unit pure product vectors. -/
def IsFullySeparable {d : ℕ} (ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ) : Prop :=
  ∃ (n : ℕ) (wt : Fin n → ℝ) (v : Fin n → Fin d → Fin 3 → ℂ),
    (∀ i, 0 < wt i) ∧ (∑ i, wt i) = 1 ∧
    (∀ i k, ∑ j, Complex.normSq (v i k j) = 1) ∧
    ρ = ∑ i, (wt i : ℂ) • vecMulVec (productVector (v i)) (star (productVector (v i)))

/-- Every completely symmetric state of at least three qutrits is fully separable. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ,
    IsDensity ρ → IsCompletelySymmetric ρ → IsFullySeparable ρ

private def counts (w : Word (Fin 3) 3) : Fin 3 → ℕ :=
  fun j => (occupation w).count j

private def moment (q : Fin 3 → ℕ) : ℝ :=
  if q = ![6, 0, 0] ∨ q = ![0, 6, 0] then 132
  else if q = ![0, 0, 6] then 3
  else if q = ![4, 2, 0] ∨ q = ![2, 4, 0] ∨ q = ![2, 2, 2] then 4
  else if q = ![4, 0, 2] ∨ q = ![0, 4, 2] then 20
  else if q = ![2, 0, 4] ∨ q = ![0, 2, 4] then 6
  else 0

private def state : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ :=
  fun a b => ((moment (fun j => counts a j + counts b j) / 471 : ℝ) : ℂ)

private def gramVector (k : Fin 7) (w : Word (Fin 3) 3) : ℂ :=
  ![if counts w = ![3, 0, 0] ∨ counts w = ![1, 2, 0] ∨ counts w = ![1, 0, 2]
      then 1 else 0,
    if counts w = ![3, 0, 0] then 8 else if counts w = ![1, 0, 2] then 1 else 0,
    if counts w = ![0, 3, 0] ∨ counts w = ![2, 1, 0] ∨ counts w = ![0, 1, 2]
      then 1 else 0,
    if counts w = ![0, 3, 0] then 8 else if counts w = ![0, 1, 2] then 1 else 0,
    if counts w = ![0, 0, 3] then 1
      else if counts w = ![2, 0, 1] ∨ counts w = ![0, 2, 1] then 2 else 0,
    if counts w = ![2, 0, 1] then 1 else if counts w = ![0, 2, 1] then -1 else 0,
    if counts w = ![1, 1, 1] then 1 else 0] k

private def gramWeight (k : Fin 7) : ℝ := ![4, 2, 4, 2, 3, 8, 4] k / 471

private def witness (w : Word (Fin 3) 3) : ℝ :=
  if counts w = ![2, 1, 0] ∨ counts w = ![1, 2, 0] then 1 / 3
  else if counts w = ![0, 0, 3] then 1
  else if counts w = ![1, 1, 1] then -1 / 2
  else 0

private theorem state_cs : IsCompletelySymmetric state := by
  sorry

private theorem gram_factor : state =
    ∑ k : Fin 7, (gramWeight k : ℂ) • vecMulVec (gramVector k) (star (gramVector k)) := by
  sorry

private theorem state_psd : state.PosSemidef := by
  rw [gram_factor]
  sorry

private theorem state_trace : trace state = 1 := by
  sorry

private theorem decomposition_support (n : ℕ) (wt : Fin n → ℝ)
    (ψ : Fin n → Word (Fin 3) 3 → ℂ) (hwt : ∀ i, 0 < wt i)
    (he : state = ∑ i, (wt i : ℂ) • vecMulVec (ψ i) (star (ψ i))) :
    ∀ i a b, counts a = counts b → ψ i a = ψ i b := by
  sorry

private theorem symmetric_product_power (v : Fin 3 → Fin 3 → ℂ)
    (hs : ∀ a b, counts a = counts b → productVector v a = productVector v b) :
    ∃ (c : ℂ) (x : Fin 3 → ℂ),
      ∀ w, productVector v w = c * ∏ k : Fin 3, x (w k) := by
  sorry

private theorem motzkin_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a ^ 2 * b + a * b ^ 2 + c ^ 3 - 3 * a * b * c := by
  sorry

private theorem power_witness_nonneg (c : ℂ) (x : Fin 3 → ℂ) :
    0 ≤ ∑ w : Word (Fin 3) 3,
      witness w * Complex.normSq (c * ∏ k : Fin 3, x (w k)) := by
  sorry

private theorem symmetric_product_witness_nonneg (v : Fin 3 → Fin 3 → ℂ)
    (hs : ∀ a b, counts a = counts b → productVector v a = productVector v b) :
    0 ≤ ∑ w : Word (Fin 3) 3, witness w * Complex.normSq (productVector v w) := by
  obtain ⟨c, x, hx⟩ := symmetric_product_power v hs
  simp_rw [hx]
  exact power_witness_nonneg c x

private theorem state_witness_value :
    (∑ w : Word (Fin 3) 3, witness w * (state w w).re) = -1 / 471 := by
  sorry

private theorem state_entangled : ¬ IsFullySeparable state := by
  intro h
  obtain ⟨n, wt, v, hwt, _, _, he⟩ := h
  have hs := decomposition_support n wt (fun i => productVector (v i)) hwt he
  have hp (i : Fin n) := symmetric_product_witness_nonneg (v i) (hs i)
  have hn : 0 ≤ ∑ w : Word (Fin 3) 3, witness w * (state w w).re := by
    sorry
  rw [state_witness_value] at hn
  norm_num at hn

/-- A completely symmetric three-qutrit state refutes the universal claim. -/
theorem result : ¬ claim := by
  intro h
  exact state_entangled (h 3 (by decide) state ⟨state_psd, state_trace⟩ state_cs)

end D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled
