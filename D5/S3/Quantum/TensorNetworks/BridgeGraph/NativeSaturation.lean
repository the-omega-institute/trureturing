/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact native width-three identity column Gram at the three-halves dimension threshold. -/

import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-! A coordinate routing realizes all rectangular native saturation dimensions. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation

private def leftSlices (a b : ℕ) : Fin 3 → Matrix (Fin a) (Fin b) ℂ :=
  ![fun i j => if i.val = j.val then 1 else 0,
    fun i j => if a ≤ j.val ∧ i.val = 2 * (j.val - a) then 1 else 0,
    fun i j => if a ≤ j.val ∧ i.val = 2 * (j.val - a) + 1 then 1 else 0]

private def rightSlices (q : ℕ) : Fin 3 → Matrix (Fin (3 * q)) (Fin (2 * q)) ℂ :=
  ![fun i j => if i.val = j.val then 1 else 0,
    fun i j => if j.val < q ∧ i.val = 2 * q + j.val then 1 else 0,
    fun i j => if q ≤ j.val ∧ i.val = q + j.val then 1 else 0]

private def route {a b q : ℕ} (h : 2 * b ≤ 3 * a)
    (x : Fin b × Fin (2 * q)) : Fin a × Fin (3 * q) :=
  if hj : x.1.val < a then
    (⟨x.1.val, hj⟩, ⟨x.2.val, by omega⟩)
  else if hk : x.2.val < q then
    (⟨2 * (x.1.val - a), by have := x.1.isLt; omega⟩,
      ⟨2 * q + x.2.val, by omega⟩)
  else
    (⟨2 * (x.1.val - a) + 1, by have := x.1.isLt; omega⟩,
      ⟨q + x.2.val, by have := x.2.isLt; omega⟩)

private theorem route_injective {a b q : ℕ} (h : 2 * b ≤ 3 * a) :
    Function.Injective (route (q := q) h) := by
  intro x y he
  have hr := congrArg (fun z : Fin a × Fin (3 * q) => z.1.val) he
  have hc := congrArg (fun z : Fin a × Fin (3 * q) => z.2.val) he
  dsimp [route] at hr hc
  split_ifs at hr hc <;> simp only at hr hc <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

private theorem tensor_route {a b q : ℕ} (h : 2 * b ≤ 3 * a) :
    (∑ r, kronecker (leftSlices a b r) (rightSlices q r)) =
      D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix
        (⟨route h, route_injective h⟩ : (Fin b × Fin (2 * q)) ↪
          (Fin a × Fin (3 * q))) := by
  ext i j
  rcases i with ⟨i, l⟩
  rcases j with ⟨j, k⟩
  rw [Fin.sum_univ_three]
  change
    (if i.val = j.val then (1 : ℂ) else 0) *
        (if l.val = k.val then 1 else 0) +
      (if a ≤ j.val ∧ i.val = 2 * (j.val - a) then 1 else 0) *
        (if k.val < q ∧ l.val = 2 * q + k.val then 1 else 0) +
      (if a ≤ j.val ∧ i.val = 2 * (j.val - a) + 1 then 1 else 0) *
        (if q ≤ k.val ∧ l.val = q + k.val then 1 else 0) =
      (if route h (j, k) = (i, l) then 1 else 0)
  by_cases hj : j.val < a
  · have hja : ¬ a ≤ j.val := by omega
    by_cases hi : i.val = j.val <;> by_cases hl : l.val = k.val <;>
      simp [route, hj, hja, hi, hl, Fin.ext_iff, eq_comm]
  · have hja : a ≤ j.val := by omega
    have hij : i.val ≠ j.val := by have := i.isLt; omega
    by_cases hk : k.val < q
    · have hqk : ¬ q ≤ k.val := by omega
      by_cases hi : i.val = 2 * (j.val - a) <;>
        by_cases hl : l.val = 2 * q + k.val <;>
        simp [route, hj, hja, hk, hqk, hij, hi, hl, Fin.ext_iff, eq_comm] <;> omega
    · have hqk : q ≤ k.val := by omega
      by_cases hi : i.val = 2 * (j.val - a) + 1 <;>
        by_cases hl : l.val = q + k.val <;>
        simp [route, hj, hja, hk, hqk, hij, hi, hl, Fin.ext_iff, eq_comm] <;> omega

/-- Rectangular factors admit an identity column Gram exactly at the dimension threshold. -/
theorem native_saturation_iff (a b q : ℕ) (_hab : a < b) (hq : 0 < q) :
    (∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin (3 * q)) (Fin (2 * q)) ℂ),
      (∑ r, kronecker (M r) (N r))ᴴ *
        (∑ r, kronecker (M r) (N r)) =
          (1 : Matrix (Fin b × Fin (2 * q)) (Fin b × Fin (2 * q)) ℂ)) ↔
      2 * b ≤ 3 * a := by
  constructor
  · rintro ⟨M, N, hF⟩
    have hr := (Matrix.rank_mul_le_right
      (∑ r, kronecker (M r) (N r))ᴴ
      (∑ r, kronecker (M r) (N r))).trans
        (Matrix.rank_le_card_height (∑ r, kronecker (M r) (N r)))
    rw [hF, Matrix.rank_one] at hr
    simp only [Fintype.card_prod, Fintype.card_fin] at hr
    nlinarith
  · intro h
    refine ⟨leftSlices a b, rightSlices q, ?_⟩
    rw [tensor_route h]
    exact D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinate_gram _

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation
