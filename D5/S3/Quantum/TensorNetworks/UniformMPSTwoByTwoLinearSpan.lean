/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The linear span of binary bond-two uniform matrix product states. -/

import D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan

open scoped BigOperators Matrix
open UniformMPSExpectedDimensionRefutation (traceWord uMPS)

noncomputable section

/-- De Lazzari–Motwani–Seynnaeve Conjecture 3.8, for positive word lengths. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192

private abbrev extraIndex (n : ℕ) :=
  {e : Fin 5 → Fin (n + 1) //
        (e 0).val + (e 1).val + 2 * (e 2).val + 2 * (e 3).val + 2 * (e 4).val + 4 = n}

private lemma evaluation_bridge (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
        fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)) := by
  classical
  let c := Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
    fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)
  let v := (Fin n → Fin 2) → ℂ
  let s : Submodule ℂ v := Submodule.span ℂ (uMPS 2 2 n)
  let r : Module.Dual ℂ v →ₗ[ℂ] ((Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) → ℂ) :=
    { toFun := fun f p => f (traceWord 2 2 n p)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : LinearMap.range r = c := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      have heq : r f = ∑ i : Fin n → Fin 2,
          f (Pi.single i 1) • (fun p => traceWord 2 2 n p i) := by
        funext p
        have h := (Pi.basisFun ℂ (Fin n → Fin 2)).sum_repr (traceWord 2 2 n p)
        simp only [Pi.basisFun_repr, Pi.basisFun_apply] at h
        change f (traceWord 2 2 n p) = _
        rw [← h, map_sum]
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [heq]
      apply (c).sum_mem
      intro i _
      exact (c).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨LinearMap.proj i, rfl⟩
  have hker : LinearMap.ker r = s.dualAnnihilator := by
    ext f
    change (fun p => f (traceWord 2 2 n p)) = 0 ↔ f ∈ s.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      have hs : s ≤ LinearMap.ker f := by
        apply Submodule.span_le.mpr
        rintro _ ⟨p, rfl⟩
        exact congrFun hf p
      exact hs hw
    · intro hf
      funext p
      exact hf _ (Submodule.subset_span ⟨p, rfl⟩)
  have h1 := r.finrank_range_add_finrank_ker
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq s
  rw [hrange, hker, Subspace.dual_finrank_eq] at h1
  change Module.finrank ℂ s = Module.finrank ℂ (c)
  omega

private lemma monomial_count_even (k : ℕ) :
    (Fintype.card (extraIndex (2 * k)) : ℚ) =
      ((2 * k : ℚ) ^ 4 - 4 * (2 * k) ^ 2) / 192 := by
  sorry

private lemma monomial_count_odd (k : ℕ) :
    (Fintype.card (extraIndex (2 * k + 1)) : ℚ) =
      ((2 * k + 1 : ℚ) ^ 4 - 10 * (2 * k + 1) ^ 2 + 9) / 192 := by
  sorry

private lemma normal_count (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) + Fintype.card (extraIndex n) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192 := by
  classical
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
  by_cases he : Even n
  · rw [if_pos he]
    obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by omega
    rw [hnk, monomial_count_even]
    push_cast
    ring
  · rw [if_neg he]
    obtain ⟨k, hk⟩ := (Nat.not_even_iff_odd.mp he).exists_bit1
    subst n
    rw [monomial_count_odd]
    push_cast
    ring

/-- The exact complex dimension of the span of binary bond-two uniform MPS. -/
theorem result : claim := by
  intro n hn
  rw [evaluation_bridge, UniformMPSTwoByTwoTraceWords.coordinate_dimension]
  exact normal_count n hn

end

end D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
