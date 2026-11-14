/- GID: D5/S1/Recurrence/PowerBaseDecimation
   generality: G
   mirror-B: D5/B/S1/Recurrence/PowerBaseDecimation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite families closed under all power-of-two-base decimations expand to finite binary decimation families over arbitrary commutative rings. -/

import D5.S1.Recurrence.BinaryDecimation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace D5.S1.Recurrence.BinaryDecimation

variable {R : Type*} [CommRing R]

/-- Every base-k digit acts by fixed coefficients on a literal finite indexed
family. No basis, independence or invertibility is assumed. -/
def BaseFamily (k : ℕ) (a : ℕ → R) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι;
    ∃ (b : ι → ℕ → R) (i0 : ι) (c : Fin k → ι → ι → R),
      (∀ n, b i0 n = a n) ∧
      (∀ (r : Fin k) i n, b i (k * n + r.val) = ∑ j, c r i j * b j n)

/-- Intermediate binary decimations give an actual finite indexed family.
Only finitely many offsets at levels j<h are adjoined. -/
theorem powerBase_binary (h : ℕ) (hh : 1 ≤ h) (a : ℕ → R)
    (ha : BaseFamily (2 ^ h) a) : ArbitraryFamily a := by
  classical
  obtain ⟨ι, hι, F, i0, c, hf, hstep⟩ := ha
  letI : Fintype ι := hι
  let J := (j : Fin h) × (Fin (2 ^ j.val) × ι)
  let G : J → ℕ → R := fun q n => F q.2.2 (2 ^ q.1.val * n + q.2.1.val)
  let S : Submodule R (ℕ → R) := Submodule.span R (Set.range G)
  have hlift (i : ι) : F i ∈ S := by
    apply Submodule.subset_span
    refine ⟨⟨⟨0, by omega⟩, ⟨⟨0, by simp⟩, i⟩⟩, ?_⟩
    funext n
    simp [G]
  have hdec (q : J) (eps : Fin 2) : (fun n => G q (2 * n + eps.val)) ∈ S := by
    let u := 2 ^ q.1.val * eps.val + q.2.1.val
    have hu : u < 2 ^ (q.1.val + 1) := by
      have hv := q.2.1.isLt
      have he := eps.isLt
      rw [pow_succ]
      dsimp [u]
      nlinarith
    by_cases hj : q.1.val + 1 < h
    · apply Submodule.subset_span
      refine ⟨⟨⟨q.1.val + 1, hj⟩, ⟨⟨u, hu⟩, q.2.2⟩⟩, ?_⟩
      funext n
      dsimp [G, u]
      congr 1
      rw [pow_succ]
      ring
    · have heq : q.1.val + 1 = h := by have := q.1.isLt; omega
      let r : Fin (2 ^ h) := ⟨u, by simpa only [heq] using hu⟩
      have he : (fun n => G q (2 * n + eps.val)) = ∑ i, c r q.2.2 i • F i := by
        funext n
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        dsimp only [G]
        have harg : 2 ^ q.1.val * (2 * n + eps.val) + q.2.1.val =
            2 ^ h * n + r.val := by
          dsimp [r, u]
          have hp : 2 ^ h = 2 ^ q.1.val * 2 :=
            (congrArg (fun x => (2 : ℕ) ^ x) heq.symm).trans (pow_succ _ _)
          rw [hp]
          ring
        rw [harg, hstep]
      rw [he]
      exact S.sum_mem fun i _ => S.smul_mem _ (hlift i)
  have hco (eps : Fin 2) (q : J) : ∃ d : J → R,
      ∀ n, G q (2 * n + eps.val) = ∑ i, d i * G i n := by
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hdec q eps)
    refine ⟨d, fun n => ?_⟩
    have he := congrFun hd n
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he.symm
  choose d hd using hco
  refine ⟨J, inferInstance, G, ⟨⟨0, by omega⟩, ⟨⟨0, by simp⟩, i0⟩⟩,
    d 0, d 1, ?_, ?_, ?_⟩
  · intro n
    simpa [G] using hf n
  · intro i n
    simpa using hd 0 i n
  · intro i n
    simpa using hd 1 i n

end D5.S1.Recurrence.BinaryDecimation
