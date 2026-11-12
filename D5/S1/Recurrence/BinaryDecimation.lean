/- GID: D5/S1/Recurrence/BinaryDecimation
   generality: G
   mirror-B: D5/B/S1/Recurrence/BinaryDecimation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binary decimation families over a commutative ring impose monic forward recurrences on dyadic observations. -/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.LinearRecurrence

/-! Binary decimation representations and their common forward-recurrence mechanism. -/

namespace D5.S1.Recurrence.BinaryDecimation

variable {R : Type*} [CommRing R]

/-- Fixed matrices over a commutative ring, all inputs, both digits, arbitrary positive dimension. -/
def MatrixFamily (a : ℕ → R) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → R,
    ∃ M0 M1 : Matrix (Fin d) (Fin d) R,
      (∀ n, F n ⟨0, hd⟩ = a n) ∧
      (∀ n, F (2 * n) = M0.mulVec (F n)) ∧
      (∀ n, F (2 * n + 1) = M1.mulVec (F n))

/-- A finite indexed family, with no independence or basis assumption. -/
def ClosedFamily (a : ℕ → R) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → R,
    ∃ c0 c1 : Fin d → Fin d → R,
      (∀ n, b ⟨0, hd⟩ n = a n) ∧
      (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧
      (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

/-- A literal arbitrary finite indexed family, with a distinguished member a.
The indexing type is arbitrary; different indices may carry equal sequences. -/
def ArbitraryFamily (a : ℕ → R) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι;
    ∃ (b : ι → ℕ → R) (i0 : ι) (c0 c1 : ι → ι → R),
      (∀ n, b i0 n = a n) ∧
      (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧
      (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

theorem closed_matrix_iff (a : ℕ → R) : ClosedFamily a ↔ MatrixFamily a := by
  constructor
  · rintro ⟨d, hd, b, c0, c1, ha, h0, h1⟩
    refine ⟨d, hd, fun n i => b i n, c0, c1, ha, ?_, ?_⟩
    · intro n
      funext i
      exact h0 i n
    · intro n
      funext i
      exact h1 i n
  · rintro ⟨d, hd, F, M0, M1, ha, h0, h1⟩
    refine ⟨d, hd, fun i n => F n i, M0, M1, ha, ?_, ?_⟩
    · intro i n
      exact congrFun (h0 n) i
    · intro i n
      exact congrFun (h1 n) i

theorem arbitrary_matrix_iff (a : ℕ → R) :
    ArbitraryFamily a ↔ MatrixFamily a := by
  classical
  constructor
  · rintro ⟨ι, hι, b, i0, c0, c1, ha, h0, h1⟩
    let : Fintype ι := hι
    let : Nonempty ι := ⟨i0⟩
    have hd : 0 < Fintype.card ι := Fintype.card_pos
    let z : Fin (Fintype.card ι) := ⟨0, hd⟩
    let e : ι ≃ Fin (Fintype.card ι) :=
      (Fintype.equivFin ι).trans (Equiv.swap ((Fintype.equivFin ι) i0) z)
    have hei : e i0 = z := by simp [e]
    have hez : e.symm z = i0 := by
      apply e.injective
      simp [hei]
    refine ⟨Fintype.card ι, hd, fun n i => b (e.symm i) n,
      (fun i j => c0 (e.symm i) (e.symm j)),
      (fun i j => c1 (e.symm i) (e.symm j)), ?_, ?_, ?_⟩
    · intro n
      change b (e.symm z) n = a n
      rw [hez]
      exact ha n
    · intro n
      funext i
      change b (e.symm i) (2 * n) = ∑ j, c0 (e.symm i) (e.symm j) * b (e.symm j) n
      rw [h0]
      exact (e.symm.sum_comp (fun j => c0 (e.symm i) j * b j n)).symm
    · intro n
      funext i
      change b (e.symm i) (2 * n + 1) = ∑ j, c1 (e.symm i) (e.symm j) * b (e.symm j) n
      rw [h1]
      exact (e.symm.sum_comp (fun j => c1 (e.symm i) j * b j n)).symm
  · rintro ⟨d, hd, F, M0, M1, ha, h0, h1⟩
    refine ⟨Fin d, inferInstance, (fun i n => F n i), ⟨0, hd⟩, M0, M1, ha, ?_, ?_⟩
    · intro i n
      exact congrFun (h0 n) i
    · intro i n
      exact congrFun (h1 n) i


/-- The given dimension d is exactly the monic forward recurrence order.
No independence, invertibility or torsion restriction is used. -/
theorem dyadic_fixed_matrix_recurrence [Nontrivial R] (a : ℕ → R)
    (d : ℕ) (hd : 0 < d) (F : ℕ → Fin d → R)
    (M0 M1 : Matrix (Fin d) (Fin d) R)
    (hf : ∀ n, F n ⟨0, hd⟩ = a n)
    (he : ∀ n, F (2 * n) = M0.mulVec (F n))
    (ho : ∀ n, F (2 * n + 1) = M1.mulVec (F n)) :
    ∃ E : LinearRecurrence R, E.order = d ∧
      E.IsSolution (fun n => a (2 ^ (n + 2) + 1)) := by
  classical
  let v (n : ℕ) := F (2 ^ (n + 1))
  have hstep (n : ℕ) : v (n + 1) = M0.mulVec (v n) := by
    dsimp [v]
    rw [show 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) by rw [pow_succ]; omega]
    exact he _
  have hpower (i n : ℕ) : (M0 ^ i).mulVec (v n) = v (n + i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      simpa only [Nat.add_assoc] using (hstep (n + i)).symm
  have hread (n : ℕ) : (M1.mulVec (v n)) ⟨0, hd⟩ = a (2 ^ (n + 2) + 1) := by
    rw [← ho]
    change F (2 * 2 ^ (n + 1) + 1) ⟨0, hd⟩ = _
    rw [hf]
    congr 2
    rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
    omega
  let E : LinearRecurrence R := ⟨d, fun i => -M0.charpoly.coeff i.val⟩
  refine ⟨E, rfl, ?_⟩
  intro n
  have hlead : M0.charpoly.coeff d = 1 := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using M0.charpoly_monic.coeff_natDegree
  have hCH : (∑ i ∈ Finset.range d, M0.charpoly.coeff i • M0 ^ i) + M0 ^ d = 0 := by
    have h := Matrix.aeval_self_charpoly M0
    rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Finset.sum_range_succ, hlead] at h
    simpa only [one_smul] using h
  have h := congrArg (fun M => (M1.mulVec (M.mulVec (v n))) ⟨0, hd⟩) hCH
  simp only [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.zero_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Matrix.mulVec_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    hpower, hread, Pi.zero_apply] at h
  change a (2 ^ (n + d + 2) + 1) =
    ∑ i : Fin d, -(M0.charpoly.coeff i.val) * a (2 ^ (n + i.val + 2) + 1)
  rw [Fin.sum_univ_eq_sum_range (fun i => -M0.charpoly.coeff i * a (2 ^ (n + i + 2) + 1)) d]
  simp only [neg_mul, Finset.sum_neg_distrib]
  linear_combination h

/-- A finite matrix family supplies a positive-order monic recurrence. -/
theorem dyadic_matrix_recurrence [Nontrivial R] (a : ℕ → R) (ha : MatrixFamily a) :
    ∃ E : LinearRecurrence R, 0 < E.order ∧
      E.IsSolution (fun n => a (2 ^ (n + 2) + 1)) := by
  obtain ⟨d, hd, F, M0, M1, hf, he, ho⟩ := ha
  obtain ⟨E, hE, hs⟩ := dyadic_fixed_matrix_recurrence a d hd F M0 M1 hf he ho
  exact ⟨E, hE.symm ▸ hd, hs⟩

/-- Every fixed linear combination of a forward shift and the original sequence
obeys the same recurrence, without dividing by its coefficient. -/
theorem shifted_sub_solution (E : LinearRecurrence R) (u : ℕ → R)
    (hu : E.IsSolution u) (t : R) :
    E.IsSolution (fun n => u (n + 1) - t * u n) := by
  intro n
  have h1 := hu (n + 1)
  have h0 := hu n
  simp only [mul_sub, mul_left_comm (E.coeffs _) t,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    congrArg₂ (fun x y => x - t * y) h1 h0

end D5.S1.Recurrence.BinaryDecimation
