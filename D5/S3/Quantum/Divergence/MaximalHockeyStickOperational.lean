/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickOperational
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickOperational
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Attained finite operational hockey infima equal the PSD overlap optimization. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
import D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate

/-! The three positive components realize both operational hockey orientations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickOperational

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual negative-orientation classical profile of a finite test. -/
def negativeHockey {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) (t : ℝ) : ℝ :=
  ∑ i, max (t * R.q i - R.p i) 0

/-- Infimum of the actual positive profile over all finite alphabets and tests. -/
def operationalHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf {z : ℝ | ∃ k : ℕ, ∃ R : ReverseTest A B k, z = R.hockey t}

/-- Infimum of the actual negative profile over the same entire source class. -/
def operationalNegativeHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sInf {z : ℝ | ∃ k : ℕ, ∃ R : ReverseTest A B k, z = negativeHockey R t}

/-- The two orientations differ by the original, unnormalized trace masses. -/
theorem negative_hockey_eq {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : ℝ) :
    negativeHockey R t = R.hockey t - A.trace.re + t * B.trace.re := by
  rw [negativeHockey, ReverseTest.hockey, left_mass R, right_mass R,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (R.p i) (t * R.q i) with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

/-- One actual test attains both overlap formulas at the given positive
threshold. The test has three labels in nonempty dimension and no labels in
empty dimension. Singular and zero components retain their exact masses. -/
theorem reverse_test_attains_hockey (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t) :
    ∃ k : ℕ, ∃ R : ReverseTest A B k,
      R.hockey t = maximalHockey A B t ∧
      negativeHockey R t = t * B.trace.re - overlapValue A (t • B) := by
  classical
  obtain ⟨X, hX, hvalue⟩ := overlap_attained A (t • B) hA (hB.smul ht.le)
  suffices hp : ∃ k : ℕ, ∃ R : ReverseTest A B k, R.hockey t = maximalHockey A B t by
    obtain ⟨k, R, hR⟩ := hp
    refine ⟨k, R, hR, ?_⟩
    rw [negative_hockey_eq, hR, maximalHockey]
    ring
  by_cases hn : Nonempty n
  · let i₀ : n := Classical.choice hn
    let G : Fin 3 → Matrix n n ℂ := ![X, A - X, t • B - X]
    have hG : ∀ i, (G i).PosSemidef := by
      intro i
      fin_cases i
      · exact hX.1.posSemidef
      · exact Matrix.le_iff.mp hX.2.1
      · exact Matrix.le_iff.mp hX.2.2
    let a : Fin 3 → ℝ := ![1, 1, 0]
    let b : Fin 3 → ℝ := ![t⁻¹, 0, t⁻¹]
    have ha : ∀ i, 0 ≤ a i := by intro i; fin_cases i <;> norm_num [a]
    have hb : ∀ i, 0 ≤ b i := by
      intro i
      fin_cases i <;> simp [b, inv_nonneg.mpr ht.le]
    have hleft : (∑ i, a i • G i) = A := by
      simp [a, G, Fin.sum_univ_succ]
    have hright : (∑ i, b i • G i) = B := by
      simp [b, G, Fin.sum_univ_succ]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    have hex := reverse_test_from_weighted_components (fun _ => i₀) G hG a b ha hb
    rw [hleft, hright] at hex
    obtain ⟨R, hR⟩ := hex
    have hprofile : R.hockey t = A.trace.re - X.trace.re := by
      rw [hR]
      simp [a, b, G, Fin.sum_univ_succ, mul_inv_cancel₀ ht.ne',
        Matrix.trace_sub, Complex.sub_re]
    exact ⟨_, R, by simpa only [maximalHockey, ← hvalue] using hprofile⟩
  · let : IsEmpty n := not_nonempty_iff.mp hn
    let R : ReverseTest A B 0 :=
      { p := Fin.elim0
        q := Fin.elim0
        p_nonneg := fun i => Fin.elim0 i
        q_nonneg := fun i => Fin.elim0 i
        state := Fin.elim0
        prepares_left := Subsingleton.elim _ _
        prepares_right := Subsingleton.elim _ _ }
    refine ⟨0, R, ?_⟩
    have htr (M : Matrix n n ℂ) : M.trace.re = 0 := by simp [Matrix.trace]
    simp only [ReverseTest.hockey, Finset.univ_eq_empty, Finset.sum_empty,
      maximalHockey, ← hvalue, htr, sub_zero]

/-- The finite operational positive infimum is exactly the PSD optimization.
This is the finite-matrix positive formula of HMT Proposition V.1. -/
theorem operational_hockey_eq (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t) :
    operationalHockey A B t = maximalHockey A B t := by
  obtain ⟨k, R, hR, -⟩ := reverse_test_attains_hockey A B hA hB t ht
  have hb : BddBelow {z : ℝ | ∃ k : ℕ, ∃ R : ReverseTest A B k, z = R.hockey t} := by
    refine ⟨maximalHockey A B t, ?_⟩
    rintro z ⟨k, R, rfl⟩
    exact R.maximal_hockey_le t ht.le
  exact le_antisymm ((csInf_le hb ⟨k, R, rfl⟩).trans_eq hR)
    (le_csInf ⟨_, k, R, rfl⟩ (by
      rintro z ⟨k, R, rfl⟩
      exact R.maximal_hockey_le t ht.le))

/-- The same actual finite source class gives the negative overlap formula. -/
theorem operational_negative_hockey_eq (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) (ht : 0 < t) :
    operationalNegativeHockey A B t = t * B.trace.re - overlapValue A (t • B) := by
  obtain ⟨k, R, -, hR⟩ := reverse_test_attains_hockey A B hA hB t ht
  have hl {k : ℕ} (R : ReverseTest A B k) :
      t * B.trace.re - overlapValue A (t • B) ≤ negativeHockey R t := by
    rw [negative_hockey_eq]
    have h := R.maximal_hockey_le t ht.le
    unfold maximalHockey at h
    linarith
  have hb : BddBelow {z : ℝ | ∃ k : ℕ, ∃ R : ReverseTest A B k,
      z = negativeHockey R t} := by
    refine ⟨t * B.trace.re - overlapValue A (t • B), ?_⟩
    rintro z ⟨k, R, rfl⟩
    exact hl R
  exact le_antisymm ((csInf_le hb ⟨k, R, rfl⟩).trans_eq hR)
    (le_csInf ⟨_, k, R, rfl⟩ (by rintro z ⟨k, R, rfl⟩; exact hl R))

end D5.S3.Quantum.Divergence.MaximalHockeyStickOperational
