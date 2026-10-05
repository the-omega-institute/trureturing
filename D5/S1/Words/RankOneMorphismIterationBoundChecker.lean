/- GID: D5/S1/Words/RankOneMorphismIterationBoundChecker
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundChecker
   mirror-E: none(waiver:actual-finite-checker)
   anchors: []
   utility: none
   digest: Total checker computed only from actual two finite image words. -/
import D5.S1.Words.RankOneMorphismIterationBoundFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound

/-- A computable, unnormalized integer charge from the actual first image. -/
def sourceCharge (f : Morphism) (w : Word) : ℤ :=
  (parikh (f 0) 1 : ℤ)*parikh w 0 - (parikh (f 0) 0 : ℤ)*parikh w 1

/-- Finite test of all actual gcd-spaced source cuts at a specified iteration. -/
def witnessChecker (f : Morphism) (K : ℕ) : Bool :=
  let P := Nat.gcd (image f K 0).length (image f K 1).length
  (List.range P).any (fun r =>
    (List.finRange 2).all (fun c =>
      (List.range ((image f K c).length/P)).all (fun j =>
        decide (sourceCharge f ((image f K c).take (r+j*P)) =
          sourceCharge f ((image f K 0).take r)))))

/-- Total computable on every pair of finite images, even outside the theorem domain. -/
def finiteChecker (f : Morphism) : Bool :=
  (List.range (iterationBound f)).any (fun t => witnessChecker f (t+1))

namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem sourceCharge_eq (w : Word) : sourceCharge f w = (p.n : ℤ)*p.charge w := by
  rw [sourceCharge, p.count_b, p.count_a]
  simp only [ite_true, charge, Nat.cast_mul]
  ring

theorem sourceCharge_eq_iff (u v : Word) :
    sourceCharge f u = sourceCharge f v ↔ p.charge u = p.charge v := by
  rw [p.sourceCharge_eq, p.sourceCharge_eq]
  constructor
  · exact mul_left_cancel₀ (show (p.n : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt p.n_pos)
  · intro h; rw [h]

theorem iterated_quotient (t : ℕ) (c : Letter) :
    (image f (t+1) c).length / Nat.gcd (image f (t+1) 0).length (image f (t+1) 1).length = p.mult c := by
  rw [p.iterated_gcd, p.iterated_length]
  exact Nat.mul_div_cancel _ (Nat.mul_pos p.d_pos (pow_pos (by have := p.lam_ge_two; omega) _))

theorem samples_reference (t : ℕ) : p.CutSamples t ↔
    ∃ r, r < p.d*p.lam^t ∧ ∀ c j, j < p.mult c →
      p.charge ((image f (t+1) c).take (r+j*(p.d*p.lam^t))) =
        p.charge ((image f (t+1) 0).take r) := by
  constructor
  · rintro ⟨r,hr,Z,h⟩
    have hz : p.charge ((image f (t+1) 0).take r) = Z := by
      simpa using h 0 0 (by simpa [mult] using p.n_pos)
    exact ⟨r,hr,fun c j hj => (h c j hj).trans hz.symm⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,_,h⟩

include p in
/-- The executable finite test is correct for the original complete cyclic witness. -/
theorem witnessChecker_correct (t : ℕ) :
    witnessChecker f (t+1) = true ↔ OriginalCyclicBlockWitness f (t+1) := by
  have hq (c : Letter) : (image f (t+1) c).length/(p.d*p.lam^t) = p.mult c := by
    simpa only [p.iterated_gcd] using p.iterated_quotient t c
  rw [p.original_iff_samples, p.samples_reference]
  simp only [witnessChecker, List.any_eq_true, List.all_eq_true, List.mem_range,
    List.mem_finRange, forall_true_left, decide_eq_true_eq,
    p.iterated_gcd, hq, p.sourceCharge_eq_iff]

include p in
/-- The actual source checker decides existence of the original four-word
    witness, and the source-specific 2^N bound is consumed in its correctness. -/
theorem finiteChecker_correct :
    finiteChecker f = true ↔ ∃ K : ℕ, 1 ≤ K ∧ OriginalCyclicBlockWitness f K := by
  rw [p.finite_witness_cutoff]
  simp only [finiteChecker, List.any_eq_true, List.mem_range, p.witnessChecker_correct]
  constructor
  · rintro ⟨t,ht,h⟩
    exact ⟨t+1,by omega,by omega,h⟩
  · rintro ⟨K,hK,hbound,h⟩
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    exact ⟨t,by omega,h⟩

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
