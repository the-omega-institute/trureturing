/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original width-three scalar-Gram witnesses in the first dimension region. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeSaturation

/-! An unbalanced split of the right coordinates handles odd and even input dimensions. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram

private def rightSlices (c d : ℕ) : Fin 3 → Matrix (Fin d) (Fin c) ℂ :=
  ![fun i j => if i.val = j.val then 1 else 0,
    fun i j => if j.val < c / 2 ∧ i.val = c + j.val then 1 else 0,
    fun i j => if c / 2 ≤ j.val ∧ i.val = c + (j.val - c / 2) then 1 else 0]

private def route {a b c d : ℕ} (hleft : 2 * b ≤ 3 * a) (hright : 3 * c ≤ 2 * d)
    (x : Fin b × Fin c) : Fin a × Fin d :=
  if hj : x.1.val < a then
    (⟨x.1.val, hj⟩, ⟨x.2.val, by have := x.2.isLt; omega⟩)
  else if hk : x.2.val < c / 2 then
    (⟨2 * (x.1.val - a), by have := x.1.isLt; omega⟩,
      ⟨c + x.2.val, by omega⟩)
  else
    (⟨2 * (x.1.val - a) + 1, by have := x.1.isLt; omega⟩,
      ⟨c + (x.2.val - c / 2), by have := x.2.isLt; omega⟩)

private theorem route_injective {a b c d : ℕ}
    (hleft : 2 * b ≤ 3 * a) (hright : 3 * c ≤ 2 * d) :
    Function.Injective (route hleft hright) := by
  intro x y he
  have hr := congrArg (fun z : Fin a × Fin d => z.1.val) he
  have hc := congrArg (fun z : Fin a × Fin d => z.2.val) he
  dsimp [route] at hr hc
  split_ifs at hr hc <;> simp only at hr hc <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

private theorem tensor_route {a b c d : ℕ}
    (hleft : 2 * b ≤ 3 * a) (hright : 3 * c ≤ 2 * d) :
    (∑ r, kronecker (NativeSaturation.leftSlices a b r) (rightSlices c d r)) =
      D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix
        (⟨route hleft hright, route_injective hleft hright⟩ :
          (Fin b × Fin c) ↪ (Fin a × Fin d)) := by
  ext i j
  rcases i with ⟨i, l⟩
  rcases j with ⟨j, k⟩
  rw [Fin.sum_univ_three]
  change
    (if i.val = j.val then (1 : ℂ) else 0) *
        (if l.val = k.val then 1 else 0) +
      (if a ≤ j.val ∧ i.val = 2 * (j.val - a) then 1 else 0) *
        (if k.val < c / 2 ∧ l.val = c + k.val then 1 else 0) +
      (if a ≤ j.val ∧ i.val = 2 * (j.val - a) + 1 then 1 else 0) *
        (if c / 2 ≤ k.val ∧ l.val = c + (k.val - c / 2) then 1 else 0) =
      (if route hleft hright (j, k) = (i, l) then 1 else 0)
  by_cases hj : j.val < a
  · have hja : ¬ a ≤ j.val := by omega
    by_cases hi : i.val = j.val <;> by_cases hl : l.val = k.val <;>
      simp [route, hj, hja, hi, hl, Fin.ext_iff, eq_comm]
  · have hja : a ≤ j.val := by omega
    have hij : i.val ≠ j.val := by have := i.isLt; omega
    by_cases hk : k.val < c / 2
    · have hqk : ¬ c / 2 ≤ k.val := by omega
      by_cases hi : i.val = 2 * (j.val - a) <;>
        by_cases hl : l.val = c + k.val <;>
        simp [route, hj, hja, hk, hqk, hij, hi, hl, Fin.ext_iff, eq_comm] <;> omega
    · have hqk : c / 2 ≤ k.val := by omega
      by_cases hi : i.val = 2 * (j.val - a) + 1 <;>
        by_cases hl : l.val = c + (k.val - c / 2) <;>
        simp [route, hj, hja, hk, hqk, hij, hi, hl, Fin.ext_iff, eq_comm] <;> omega

/-- Three original rectangular factors realize any positive real scalar Gram in the first region. -/
theorem native_scalar_gram_exists (a b c d : ℕ)
    (hleft : 2 * b ≤ 3 * a) (hright : 3 * c ≤ 2 * d)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (∑ r, kronecker (M r) (N r))ᴴ *
        (∑ r, kronecker (M r) (N r)) =
          (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ) := by
  let e : (Fin b × Fin c) ↪ (Fin a × Fin d) :=
    ⟨route hleft hright, route_injective hleft hright⟩
  refine ⟨fun r => (Real.sqrt lam : ℂ) • NativeSaturation.leftSlices a b r,
    rightSlices c d, ?_⟩
  have hs : (∑ r, kronecker ((Real.sqrt lam : ℂ) • NativeSaturation.leftSlices a b r)
      (rightSlices c d r)) = (Real.sqrt lam : ℂ) •
        D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix e := by
    calc
      _ = ∑ r, (Real.sqrt lam : ℂ) •
          kronecker (NativeSaturation.leftSlices a b r) (rightSlices c d r) :=
        Finset.sum_congr rfl (fun r _ => Matrix.smul_kronecker _ _ _)
      _ = _ := by rw [← Finset.smul_sum, tensor_route hleft hright]
  have hsquare : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hlam.le
  rw [hs, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinate_gram]
  simp only [Complex.star_def, Complex.conj_ofReal, hsquare]

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeScalarGram
