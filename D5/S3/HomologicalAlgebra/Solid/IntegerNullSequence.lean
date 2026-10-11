/- GID: D5/S3/HomologicalAlgebra/Solid/IntegerNullSequence
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/IntegerNullSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.IntegerRounding
import D5.S3.HomologicalAlgebra.Solid.RealScalarSequence

/-!
Actual locally constant rounding matrices on the convergent sequence times
every light profinite test space. Their additive and binary defects are
uniformly bounded, and bounded input remains bounded. These are concrete
inputs for direct cancellation of M_Z/B_Z; no condensed action or vanishing
is asserted here. New proofs, Apache-2.0.
-/

noncomputable section
open CategoryTheory LightProfinite OnePoint Filter Topology

namespace LightCondensed.Solid

def integerBinaryRound (z : ℤ) (n : ℕ) : ℤ :=
  z.tdiv ((2 : ℤ) ^ Nat.log2 (n + 1))

theorem integerBinaryRound_eventually_zero (z : ℤ) :
    ∀ᶠ n : ℕ in atTop, integerBinaryRound z n = 0 := by
  have h := realBinaryDepth_tendsto.eventually (eventually_ge_atTop z.natAbs)
  exact h.mono fun n hn => integerRounding_dyadic_eventually_zero z _ hn

def integerBinaryRoundSequence (z : ℤ) : C(ℕ∪{∞}, ℤ) where
  toFun := OnePoint.rec 0 (integerBinaryRound z)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℤ)) atTop (𝓝 0)).congr'
      ((integerBinaryRound_eventually_zero z).mono fun _ h => h.symm)

@[simp] theorem integerBinaryRoundSequence_infty (z : ℤ) :
    integerBinaryRoundSequence z ∞ = 0 := rfl

@[simp] theorem integerBinaryRoundSequence_nat (z : ℤ) (n : ℕ) :
    integerBinaryRoundSequence z (n : ℕ∪{∞}) = integerBinaryRound z n := rfl

@[simp] theorem integerBinaryRound_zero (z : ℤ) : integerBinaryRound z 0 = z := by
  simp [integerBinaryRound, Nat.log2_def]

/-- The actual matrix is locally constant jointly in both variables. No
finite or nonempty assumption on the test space is imposed. -/
def integerBinaryRoundMatrix (S : LightProfinite) (c : LocallyConstant S ℤ) :
    LocallyConstant (ℕ∪{∞} × S) ℤ where
  toFun x := integerBinaryRoundSequence (c x.2) x.1
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    exact (continuous_eval : Continuous (fun x : C(ℕ∪{∞}, ℤ) × ℕ∪{∞} => x.1 x.2)).comp
      (((continuous_of_discreteTopology : Continuous integerBinaryRoundSequence).comp
        (c.continuous.comp continuous_snd)).prodMk continuous_fst)

@[simp] theorem integerBinaryRoundMatrix_infty (S : LightProfinite)
    (c : LocallyConstant S ℤ) (s : S) : integerBinaryRoundMatrix S c (∞, s) = 0 := rfl

@[simp] theorem integerBinaryRoundMatrix_nat (S : LightProfinite)
    (c : LocallyConstant S ℤ) (n : ℕ) (s : S) :
    integerBinaryRoundMatrix S c ((n : ℕ∪{∞}), s) = integerBinaryRound (c s) n := rfl

theorem integerBinaryRoundMatrix_add_defect (S : LightProfinite)
    (c d : LocallyConstant S ℤ) (a : ℕ∪{∞}) (s : S) :
    |integerBinaryRoundMatrix S (c + d) (a, s) - integerBinaryRoundMatrix S c (a, s) -
      integerBinaryRoundMatrix S d (a, s)| ≤ 2 := by
  cases a using OnePoint.rec
  · change |(0 : ℤ) - 0 - 0| ≤ 2
    norm_num
  · rename_i n
    exact integerRounding_add_defect (c s) (d s) _ (pow_pos (by norm_num) _)

theorem integerBinaryRoundMatrix_preserves_bound (S : LightProfinite)
    (c : LocallyConstant S ℤ) (N : ℤ) (hN : ∀ s, |c s| ≤ N) (a : ℕ∪{∞}) (s : S) :
    |integerBinaryRoundMatrix S c (a, s)| ≤ N := by
  cases a using OnePoint.rec
  · change |(0 : ℤ)| ≤ N
    simpa using (abs_nonneg (c s)).trans (hN s)
  · rename_i n
    exact integerRounding_preserves_bound _ _ _ (hN s)

theorem integerBinaryRound_children_defect (z : ℤ) (n : ℕ) :
    |integerBinaryRound z n -
      (integerBinaryRound z (2 * n + 1) + integerBinaryRound z (2 * n + 2))| ≤ 2 := by
  have hl : Nat.log2 (2 * n + 1 + 1) = Nat.log2 (n + 1) + 1 := by
    rw [Nat.log2_def (2 * n + 1 + 1), if_pos (by omega), show
      (2 * n + 1 + 1) / 2 = n + 1 from by omega]
  have hr : Nat.log2 (2 * n + 2 + 1) = Nat.log2 (n + 1) + 1 := by
    rw [Nat.log2_def (2 * n + 2 + 1), if_pos (by omega), show
      (2 * n + 2 + 1) / 2 = n + 1 from by omega]
  simp only [integerBinaryRound, hl, hr, pow_succ]
  rw [mul_comm ((2 : ℤ) ^ Nat.log2 (n + 1)) 2, ← two_mul]
  exact integerRounding_binary_defect z _ (pow_pos (by norm_num) _)

end LightCondensed.Solid
