/- GID: D5/S3/Quantum/Analysis/RefinedBMVWords
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact cyclic word multiplicities and the monotonicity of the cubic trace gap under scalar shifts. -/

import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Matrix
open scoped ComplexOrder

noncomputable section

namespace RefinedBMV

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The six-letter word mean. The four cyclic orbits of the twenty words have
sizes six, six, six, and two. -/
def wordMean (A B : Matrix n n ℂ) : ℂ :=
  (6 * trace (A * (A * (A * (B * (B * B))))) + 6 * trace (A * (A * (B * (A * (B * B))))) +
    6 * trace (A * (A * (B * (B * (A * B))))) + 2 * trace (A * (B * (A * (B * (A * B)))))) / 20

/-- Generate the words by placing one letter, reducing its remaining count.
The first count is the number of letters A and the second the number of letters B. -/
def balancedWords : ℕ → ℕ → List (List Bool)
  | 0, 0 => [[]]
  | 0, b + 1 => (balancedWords 0 b).map (false :: ·)
  | a + 1, 0 => (balancedWords a 0).map (true :: ·)
  | a + 1, b + 1 =>
    (balancedWords a (b + 1)).map (true :: ·) ++
      (balancedWords (a + 1) b).map (false :: ·)

/-- Ordered evaluation of a word in the two matrices. -/
def evalWord (A B : Matrix n n ℂ) : List Bool → Matrix n n ℂ
  | [] => 1
  | true :: w => A * evalWord A B w
  | false :: w => B * evalWord A B w

/-- The cyclic formula equals the average of the twenty ordered words. -/
theorem wordMean_eq_enumerated (A B : Matrix n n ℂ) :
    wordMean A B = ((balancedWords 3 3).map (fun w ↦ trace (evalWord A B w))).sum / 20 := by
  have hAABBBA : trace (A * (A * (B * (B * (B * A))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (A * (B * (B * B)))) (A)
  have hABAABB : trace (A * (B * (A * (A * (B * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * B) (A * (A * (B * B)))
  have hABABBA : trace (A * (B * (A * (B * (B * A))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * (A * (B * B)))) (A)
  have hABBAAB : trace (A * (B * (B * (A * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * B)) (A * (A * B))
  have hABBABA : trace (A * (B * (B * (A * (B * A))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * (B * (A * B)))) (A)
  have hABBBAA : trace (A * (B * (B * (B * (A * A))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * (B * B))) (A * A)
  have hBAAABB : trace (B * (A * (A * (A * (B * B))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (A * (B * B))))
  have hBAABAB : trace (B * (A * (A * (B * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (B * (A * B))))
  have hBAABBA : trace (B * (A * (A * (B * (B * A))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (B * (B * A))))
  have hBABAAB : trace (B * (A * (B * (A * (A * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (A * B)) (A * (A * B))
  have hBABABA : trace (B * (A * (B * (A * (B * A))))) = trace (A * (B * (A * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (B * (A * (B * A))))
  have hBABBAA : trace (B * (A * (B * (B * (A * A))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (A * (B * B))) (A * A)
  have hBBAAAB : trace (B * (B * (A * (A * (A * B))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * B) (A * (A * (A * B)))
  have hBBAABA : trace (B * (B * (A * (A * (B * A))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * B) (A * (A * (B * A)))
  have hBBABAA : trace (B * (B * (A * (B * (A * A))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (B * (A * B))) (A * A)
  have hBBBAAA : trace (B * (B * (B * (A * (A * A))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (B * B)) (A * (A * A))
  simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.sum_cons, List.sum_nil, evalWord, mul_one, wordMean,
    hAABBBA, hABAABB, hABABBA, hABBAAB, hABBABA, hABBBAA,
    hBAAABB, hBAABAB, hBAABBA, hBABAAB, hBABABA, hBABBAA,
    hBBAAAB, hBBAABA, hBBABAA, hBBBAAA]
  ring

/-- The cyclic word mean of Hermitian factors is real. -/
theorem wordMean_isSelfAdjoint (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : IsSelfAdjoint (wordMean A B) := by
  have hP : star (trace (A * (A * (A * (B * (B * B)))))) = trace (A * (A * (A * (B * (B * B))))) := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, hA.eq, hB.eq, mul_assoc]
    simpa only [mul_assoc] using trace_mul_comm (B * (B * B)) (A * (A * A))
  have hQ : star (trace (A * (A * (B * (A * (B * B)))))) = trace (A * (A * (B * (B * (A * B))))) := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, hA.eq, hB.eq, mul_assoc]
    simpa only [mul_assoc] using trace_mul_comm (B * (B * (A * B))) (A * A)
  have hQ' : star (trace (A * (A * (B * (B * (A * B)))))) = trace (A * (A * (B * (A * (B * B))))) := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, hA.eq, hB.eq, mul_assoc]
    simpa only [mul_assoc] using trace_mul_comm (B * (A * (B * B))) (A * A)
  have hR : star (trace (A * (B * (A * (B * (A * B)))))) = trace (A * (B * (A * (B * (A * B))))) := by
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul, hA.eq, hB.eq, mul_assoc]
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (B * (A * (B * A))))
  simp only [IsSelfAdjoint, wordMean, star_div₀, star_add, star_mul, star_ofNat, hP, hQ, hQ', hR]
  ring

/-- The alternating word has real trace for Hermitian factors. -/
theorem trace_cube_isSelfAdjoint (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : IsSelfAdjoint (trace ((A * B) ^ 3)) := by
  change star (trace ((A * B) ^ 3)) = _
  rw [← trace_conjTranspose]
  simp only [pow_succ, pow_zero, one_mul, conjTranspose_mul, hA.eq, hB.eq, mul_assoc]
  simpa only [mul_assoc] using trace_mul_comm (B) (A * (B * (A * (B * A))))

/-- The trace gap with its cyclic multiplicity removed. -/
def traceGap (A B : Matrix n n ℂ) : ℂ :=
  trace (A * (A * (A * (B * (B * B))))) + trace (A * (A * (B * (A * (B * B))))) +
    trace (A * (A * (B * (B * (A * B))))) - 3 * trace (A * (B * (A * (B * (A * B)))))

theorem traceGap_eq_mean (A B : Matrix n n ℂ) :
    traceGap A B = (10 / 3 : ℂ) * (wordMean A B - trace ((A * B) ^ 3)) := by
  simp only [traceGap, wordMean, pow_succ, pow_zero, one_mul, mul_assoc]
  ring

private theorem traceGap_eq_commutator (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceGap A B =
      trace ((A * B - B * A)ᴴ * A * (A * B - B * A) * B) +
        2 * trace ((A * B - B * A)ᴴ * (A * B - B * A) * (A * B + B * A)) := by
  have hBAAABB : trace (B * (A * (A * (A * (B * B))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (A * (B * B))))
  have hBAABAB : trace (B * (A * (A * (B * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (B * (A * B))))
  have hABAABB : trace (A * (B * (A * (A * (B * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * B) (A * (A * (B * B)))
  have hBAABBA : trace (B * (A * (A * (B * (B * A))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (B * (B * A))))
  have hBABAAB : trace (B * (A * (B * (A * (A * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (A * B)) (A * (A * B))
  have hBABABA : trace (B * (A * (B * (A * (B * A))))) = trace (A * (B * (A * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (B * (A * (B * A))))
  have hABABBA : trace (A * (B * (A * (B * (B * A))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * (A * (B * B)))) (A)
  have hABBAAB : trace (A * (B * (B * (A * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * B)) (A * (A * B))
  have hABBABA : trace (A * (B * (B * (A * (B * A))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * (B * (A * B)))) (A)
  simp only [conjTranspose_sub, conjTranspose_mul, hA.eq, hB.eq]
  simp only [traceGap, sub_mul, mul_sub, add_mul, mul_add, trace_sub, trace_add, mul_assoc,
    hBAAABB, hBAABAB, hABAABB, hBAABBA, hBABAAB, hBABABA, hABABBA, hABBAAB, hABBABA]
  ring

theorem traceGap_shift (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    (traceGap A B).re ≤ (traceGap (A + (t : ℂ) • 1) B).re := by
  let C := A * B - B * A
  have htA : (A + (t : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    exact hA.add (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hc : (A + (t : ℂ) • 1) * B - B * (A + (t : ℂ) • 1) = C := by
    simp only [C, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    abel
  have hs : (A + (t : ℂ) • 1) * B + B * (A + (t : ℂ) • 1) =
      A * B + B * A + (t : ℂ) • B + (t : ℂ) • B := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    abel
  have hn : 0 ≤ (trace (Cᴴ * C * B)).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef (posSemidef_conjTranspose_mul_self C) hB
  rw [traceGap_eq_commutator A B hA hB.isHermitian,
    traceGap_eq_commutator _ B htA hB.isHermitian, hc, hs]
  change (trace (Cᴴ * A * C * B) + 2 * trace (Cᴴ * C * (A * B + B * A))).re ≤ _
  have he : trace (Cᴴ * (A + (t : ℂ) • 1) * C * B) +
        2 * trace (Cᴴ * C * (A * B + B * A + (t : ℂ) • B + (t : ℂ) • B)) =
      trace (Cᴴ * A * C * B) + 2 * trace (Cᴴ * C * (A * B + B * A)) +
        (5 * (t : ℂ)) * trace (Cᴴ * C * B) := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      trace_add, trace_smul, smul_eq_mul]
    ring
  rw [he]
  have hnn : 0 ≤ ((5 * (t : ℂ)) * trace (Cᴴ * C * B)).re := by
    have hscale : (0 : ℝ) ≤ 5 * t := by positivity
    simpa [Complex.mul_re, Complex.mul_im] using mul_nonneg hscale hn
  simpa only [Complex.add_re] using
    (le_add_of_nonneg_right (a := (trace (Cᴴ * A * C * B) +
      2 * trace (Cᴴ * C * (A * B + B * A))).re) hnn)

theorem trace_conjugation (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    trace (Unitary.conjStarAlgAut ℂ _ U A) = trace A := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

theorem traceGap_conj (U : Matrix.unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    traceGap (Unitary.conjStarAlgAut ℂ _ U A) (Unitary.conjStarAlgAut ℂ _ U B) =
      traceGap A B := by
  simp only [traceGap, ← map_mul, trace_conjugation]

theorem traceGap_eq_compositions (A B : Matrix n n ℂ) :
    3 * traceGap A B =
      trace (A ^ 3 * B ^ 3) + trace (B * A ^ 3 * B ^ 2) + trace (B ^ 2 * A ^ 3 * B) +
      trace (A ^ 2 * B * A * B ^ 2) + trace (A ^ 2 * B ^ 2 * A * B) +
      trace (A * B * A ^ 2 * B ^ 2) + trace (B * A ^ 2 * B * A * B) +
      trace (A * B ^ 2 * A ^ 2 * B) + trace (B * A * B * A ^ 2 * B) -
      9 * trace ((A * B) ^ 3) := by
  have hBAAABB : trace (B * (A * (A * (A * (B * B))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (A * (B * B))))
  have hBBAAAB : trace (B * (B * (A * (A * (A * B))))) = trace (A * (A * (A * (B * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * B) (A * (A * (A * B)))
  have hABAABB : trace (A * (B * (A * (A * (B * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * B) (A * (A * (B * B)))
  have hBAABAB : trace (B * (A * (A * (B * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B) (A * (A * (B * (A * B))))
  have hABBAAB : trace (A * (B * (B * (A * (A * B))))) = trace (A * (A * (B * (A * (B * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (A * (B * B)) (A * (A * B))
  have hBABAAB : trace (B * (A * (B * (A * (A * B))))) = trace (A * (A * (B * (B * (A * B))))) := by
    simpa only [mul_assoc] using trace_mul_comm (B * (A * B)) (A * (A * B))
  simp only [traceGap, pow_succ, pow_zero, one_mul, mul_assoc,
    hBAAABB, hBBAAAB, hABAABB, hBAABAB, hABBAAB, hBABAAB]
  ring

#print axioms traceGap_eq_mean
#print axioms traceGap_shift
#print axioms traceGap_eq_compositions

end RefinedBMV
