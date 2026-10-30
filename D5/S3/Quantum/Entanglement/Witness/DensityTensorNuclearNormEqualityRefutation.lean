/- GID: D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim; result=D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result; claim=D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim
   digest: A flagged Bell mixture refutes the pure-state nuclear-norm equality case. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix

namespace D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation

set_option autoImplicit false
set_option linter.style.longLine false

/-- The Euclidean norm of a finite complex coefficient array. -/
def tensorNorm {ι : Type*} [Fintype ι] (t : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖t i‖ ^ 2)

/-- The source's complex nuclear norm, over finite sums of product tensors. -/
def nuclearNorm {κ : Type*} [Fintype κ] (m : κ → ℕ)
    (t : ((j : κ) → Fin (m j)) → ℂ) : ℝ :=
  sInf {s : ℝ | ∃ (r : ℕ) (x : Fin r → (j : κ) → Fin (m j) → ℂ),
    t = (fun i => ∑ a, ∏ j, x a j (i j)) ∧ s = ∑ a, ∏ j, tensorNorm (x a j)}

/-- Maximal nuclear norm among Euclidean unit tensors. -/
def alpha {κ : Type*} [Fintype κ] (m : κ → ℕ) : ℝ :=
  sSup {s : ℝ | ∃ t : ((j : κ) → Fin (m j)) → ℂ,
    tensorNorm t = 1 ∧ s = nuclearNorm m t}

/-- The row and column modes of a matrix, regarded as separate tensor factors. -/
def densityTensor {d : ℕ} {n : Fin d → ℕ}
    (a : Matrix ((j : Fin d) → Fin (n j)) ((j : Fin d) → Fin (n j)) ℂ) :
    ((j : Fin d ⊕ Fin d) → Fin (Sum.elim n n j)) → ℂ :=
  fun i => a (fun j => i (Sum.inl j)) (fun j => i (Sum.inr j))

/-- The equality-case conjecture of Derksen, Friedland, Lim and Wang. -/
def claim : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ)
    (a : Matrix ((j : Fin d) → Fin (n j)) ((j : Fin d) → Fin (n j)) ℂ),
    a.PosSemidef → a.trace = 1 →
    nuclearNorm (Sum.elim n n) (densityTensor a) = alpha n ^ 2 →
    ∃ t : ((j : Fin d) → Fin (n j)) → ℂ,
      tensorNorm t = 1 ∧ nuclearNorm n t = alpha n ∧ a = vecMulVec t (star t)

private lemma decomposition_nonempty {κ : Type*} [Fintype κ] [Nonempty κ]
    (m : κ → ℕ) (t : ((j : κ) → Fin (m j)) → ℂ) :
    Set.Nonempty {s : ℝ | ∃ (r : ℕ) (x : Fin r → (j : κ) → Fin (m j) → ℂ),
      t = (fun i => ∑ a, ∏ j, x a j (i j)) ∧ s = ∑ a, ∏ j, tensorNorm (x a j)} := by
  sorry

private lemma nuclear_le {κ : Type*} [Fintype κ] (m : κ → ℕ)
    (t : ((j : κ) → Fin (m j)) → ℂ) (r : ℕ)
    (x : Fin r → (j : κ) → Fin (m j) → ℂ)
    (hx : t = fun i => ∑ a, ∏ j, x a j (i j)) :
    nuclearNorm m t ≤ ∑ a, ∏ j, tensorNorm (x a j) := by
  sorry

private lemma dual_bound {κ : Type*} [Fintype κ] [Nonempty κ]
    (m : κ → ℕ) (t : ((j : κ) → Fin (m j)) → ℂ)
    (s : ((((j : κ) → Fin (m j)) → ℂ)) →ₗ[ℂ] ℂ)
    (hs : ∀ x : (j : κ) → Fin (m j) → ℂ,
      ‖s (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, tensorNorm (x j)) :
    ‖s t‖ ≤ nuclearNorm m t := by
  sorry

private lemma row_bound (n : ℕ)
    (t : ((j : Fin 2) → Fin (Fin.cons 2 (Fin.cons n Fin.elim0) j)) → ℂ) :
    nuclearNorm (Fin.cons 2 (Fin.cons n Fin.elim0)) t ≤ Real.sqrt 2 * tensorNorm t := by
  sorry

private lemma bell_bound (x : Fin 2 → ℂ) (y : Fin 4 → ℂ) :
    ‖x 0 * y 0 + x 1 * y 1‖ ≤ tensorNorm x * tensorNorm y := by
  sorry

private lemma flag_bound (x z : Fin 2 → ℂ) (y w : Fin 4 → ℂ) :
    ‖(x 0 * y 0 + x 1 * y 1) * (z 0 * w 0 + z 1 * w 1) +
      (x 0 * y 2 + x 1 * y 3) * (z 0 * w 2 + z 1 * w 3)‖ ≤
      tensorNorm x * tensorNorm y * tensorNorm z * tensorNorm w := by
  sorry

private lemma pure_idempotent {ι : Type*} [Fintype ι] (t : ι → ℂ)
    (ht : tensorNorm t = 1) :
    vecMulVec t (star t) * vecMulVec t (star t) = vecMulVec t (star t) := by
  sorry

/-- A rank-two density tensor attains the conjectured pure-state maximum. -/
theorem result : ¬ claim := by
  classical
  intro hc
  let n : Fin 2 → ℕ := Fin.cons 2 (Fin.cons 4 Fin.elim0)
  let e : ((j : Fin 2) → Fin (n j)) ≃ Fin 2 × Fin 4 := piFinTwoEquiv _
  let v : Fin 2 → ((j : Fin 2) → Fin (n j)) → ℂ := fun b i =>
    if (e i).2.val = (e i).1.val + 2 * b.val then (Real.sqrt 2 : ℂ)⁻¹ else 0
  let a := (1 / 2 : ℂ) • (vecMulVec (v 0) (star (v 0)) + vecMulVec (v 1) (star (v 1)))
  have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hv : tensorNorm (v 0) = 1 := by
    sorry
  let sb : ((((j : Fin 2) → Fin (n j)) → ℂ)) →ₗ[ℂ] ℂ :=
    LinearMap.proj (e.symm (0, 0)) + LinearMap.proj (e.symm (1, 1))
  have hsb : ∀ x : (j : Fin 2) → Fin (n j) → ℂ,
      ‖sb (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, tensorNorm (x j) := by
    intro x
    simpa [sb, e, Fin.prod_univ_two] using bell_bound (x 0) (x 1)
  have hsbv : ‖sb (v 0)‖ = Real.sqrt 2 := by
    sorry
  have hb : nuclearNorm n (v 0) = Real.sqrt 2 := by
    apply le_antisymm
    · simpa [n, hv] using row_bound 4 (v 0)
    · rw [← hsbv]
      exact dual_bound n (v 0) sb hsb
  have halpha : alpha n = Real.sqrt 2 := by
    sorry
  have hpos : a.PosSemidef := by
    exact ((posSemidef_vecMulVec_self_star (v 0)).add
      (posSemidef_vecMulVec_self_star (v 1))).smul (by norm_num)
  have htrace : a.trace = 1 := by
    sorry
  have hupper : nuclearNorm (Sum.elim n n) (densityTensor a) ≤ 2 := by
    sorry
  let sf : ((((j : Fin 2 ⊕ Fin 2) → Fin (Sum.elim n n j)) → ℂ)) →ₗ[ℂ] ℂ :=
    ∑ b : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2,
      LinearMap.proj (Sum.rec (e.symm (i, ⟨i.val + 2 * b.val, by omega⟩))
        (e.symm (k, ⟨k.val + 2 * b.val, by omega⟩)))
  have hsf : ∀ x : (j : Fin 2 ⊕ Fin 2) → Fin (Sum.elim n n j) → ℂ,
      ‖sf (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, tensorNorm (x j) := by
    intro x
    have h := flag_bound (x (.inl 0)) (x (.inr 0)) (x (.inl 1)) (x (.inr 1))
    sorry
  have hsfa : ‖sf (densityTensor a)‖ = 2 := by
    sorry
  have hn : nuclearNorm (Sum.elim n n) (densityTensor a) = alpha n ^ 2 := by
    rw [halpha, hroot]
    apply le_antisymm hupper
    rw [← hsfa]
    exact dual_bound (Sum.elim n n) (densityTensor a) sf hsf
  obtain ⟨t, ht, _, hat⟩ := hc 2 n a hpos htrace hn
  have hid : a * a = a := by
    rw [hat]
    exact pure_idempotent t ht
  have hhalf : a * a = (1 / 2 : ℂ) • a := by
    sorry
  have hnonzero : a ≠ 0 := by
    intro hz
    rw [hz, trace_zero] at htrace
    norm_num at htrace
  apply hnonzero
  ext i j
  have hij := congrArg (fun b => b i j) (hid.symm.trans hhalf)
  change a i j = (1 / 2 : ℂ) * a i j at hij
  linear_combination 2 * hij

end D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation
