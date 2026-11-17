/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothMomentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted finite sieve moments equal the constrained Ramanujan exponential sums. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveRamanujan

/-! Finite character expansions identify smooth weighted moments with their raw sums. -/

open scoped BigOperators
open Set Finset
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem sampled_support (f : ℝ → ℝ) (hf : HasCompactSupport f)
    (H : ℝ) (hH : 0 < H) :
    (Function.support (fun d : ℕ => f ((d : ℝ) / H))).Finite := by
  obtain ⟨R, hR⟩ := hf.bddAbove
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨⌈R * H⌉₊, ?_⟩
  intro d hd
  have hdR := hR (subset_closure hd)
  have hd' : (d : ℝ) ≤ R * H := (div_le_iff₀ hH).mp hdR
  exact_mod_cast hd'.trans (Nat.le_ceil (R * H))

private theorem ef_eq_natural_sum (f : ℝ → ℝ) (hf : SmoothPositiveWeight f)
    (h : ℕ) (hh : 0 < h) (t : ℝ) :
    weightedExponentialSum h f t = ∑ᶠ d : ℕ, (f ((d : ℝ) / h) : ℂ) * unitCharacter ((d : ℝ) * t) := by
  classical
  let g : ℤ → ℂ := fun d => (f ((d : ℝ) / h) : ℂ) * unitCharacter ((d : ℝ) * t)
  have hs : Function.support g ⊆ Set.range (fun d : ℕ => (d : ℤ)) := by
    intro d hd
    have hfne : f ((d : ℝ) / h) ≠ 0 := by
      intro he
      exact hd (by simp [g, he])
    have hdpos : 0 < (d : ℝ) / h := hf.2.2 (subset_closure hfne)
    have hdnonneg : (0 : ℤ) ≤ d := by
      exact_mod_cast (le_of_lt ((div_pos_iff_of_pos_right (by exact_mod_cast hh)).mp hdpos))
    exact ⟨d.toNat, Int.toNat_of_nonneg hdnonneg⟩
  change (∑ᶠ d, g d) = _
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' g Set.univ
    (Set.range (fun d : ℕ => (d : ℤ))) (by
      intro d hd
      exact ⟨fun _ => hs hd, fun _ => Set.mem_univ d⟩)]
  simpa only [g, Int.cast_natCast] using
    (finsum_mem_range (f := g) (fun a b he => Int.natCast_inj.mp he))

private theorem weighted_ramanujan_expansion (Q : ℕ+) (hQ : Squarefree (Q : ℕ))
    (h : ℕ) (hh : 0 < h) (f : ℝ → ℝ) (hf : SmoothPositiveWeight f) (x : ZMod (Q : ℕ)) :
    (sieveWeightedSum Q h f x : ℂ) =
      ∑ q ∈ (Q : ℕ).divisors.erase 1,
        (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) *
          ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
            unitCharacter ((x.val : ℝ) * r / q) * weightedExponentialSum h f ((r : ℝ) / q) := by
  classical
  have hs := sampled_support f hf.2.1 h (by exact_mod_cast hh)
  let s := hs.toFinset
  have hsupp (d : ℕ) (hd : f ((d : ℝ) / h) ≠ 0) : d ∈ s := hs.mem_toFinset.mpr hd
  have hweighted : Function.support (fun d : ℕ => f ((d : ℝ) / h) * sieveVariable Q d x) ⊆ s := by
    intro d hd
    exact hsupp d (fun he => hd (by simp [he]))
  have he (t : ℝ) : weightedExponentialSum h f t = ∑ d ∈ s, (f ((d : ℝ) / h) : ℂ) * unitCharacter ((d : ℝ) * t) := by
    rw [ef_eq_natural_sum f hf h hh]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    apply hsupp
    intro he
    exact hd (by simp [he])
  rw [sieveWeightedSum, finsum_eq_sum_of_support_subset _ hweighted]
  push_cast
  simp_rw [sieve_centered_ramanujan_expansion Q hQ, ramanujanSum, he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro d hd
  have hc : Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * (x.val + d) / q)) =
      unitCharacter ((x.val : ℝ) * r / q) * unitCharacter ((d : ℝ) * (r / q)) := by
    rw [← sieve_character_add]
    unfold unitCharacter
    congr 1
    push_cast
    ring
  push_cast
  rw [hc]
  ring

private theorem tuple_ramanujan_expansion (k : ℕ) (Q : ℕ+) (hQ : Squarefree (Q : ℕ))
    (h : ℕ) (hh : 0 < h) (f : Fin k → ℝ → ℝ) (hf : ∀ i, SmoothPositiveWeight (f i))
    (x : ZMod (Q : ℕ)) :
    (∏ i, (sieveWeightedSum Q h (f i) x : ℂ)) =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin k => (Q : ℕ).divisors.erase 1),
        (∏ i, (ArithmeticFunction.moebius (q i) : ℂ) / (Nat.totient (q i) : ℂ)) *
          ∑ r ∈ Fintype.piFinset (fun i => (Finset.range (q i)).filter (fun r => r.Coprime (q i))),
            unitCharacter ((x.val : ℝ) * ∑ i, (r i : ℝ) / q i) *
              ∏ i, weightedExponentialSum h (f i) ((r i : ℝ) / q i) := by
  classical
  simp_rw [weighted_ramanujan_expansion Q hQ h hh _ (hf _)]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.prod_mul_distrib, Finset.prod_univ_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.prod_mul_distrib]
  congr 2
  simp only [unitCharacter, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum, mul_div_assoc]

/-- The uniform product moment is the constrained Ramanujan exponential sum. -/
theorem sieve_weighted_moment_eq_raw (k : ℕ) (Q : ℕ+) (hQ : Squarefree (Q : ℕ))
    (h : ℕ) (hh : 0 < h) (f : Fin k → ℝ → ℝ) (hf : ∀ i, SmoothPositiveWeight (f i)) :
    (sieveProductMoment Q (fun i => sieveWeightedSum Q h (f i)) : ℂ) = kuperbergRawMoment Q h f := by
  classical
  unfold sieveProductMoment sieveExpectation kuperbergRawMoment
  push_cast
  simp_rw [tuple_ramanujan_expansion k Q hQ h hh f hf, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hdiv (i : Fin k) : q i ∣ (Q : ℕ) :=
    Nat.dvd_of_mem_divisors (Finset.mem_erase.mp (Fintype.mem_piFinset.mp hq i)).2
  have hpos (i : Fin k) : 0 < q i := Nat.pos_of_dvd_of_pos (hdiv i) Q.pos
  have ho := sieve_character_orthogonality k Q q hdiv hpos r
  simp only [Finset.mul_sum] at ho
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [mul_div_assoc, mul_div_right_comm, ho]
  split_ifs <;> simp

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
