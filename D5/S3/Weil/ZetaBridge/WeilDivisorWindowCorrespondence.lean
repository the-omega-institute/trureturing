/- GID: D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence
   mirror-E: none(waiver:operator-Euler-product-and-origin-normalization-paper-bridges)
   anchors: []
   utility: none
   digest: Identify the actual finite divisor synthesis with the canonical Mellin window and its missing-divisor defect, then transport the full prime action. -/

import D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases

/-!
# Finite divisor data and the actual arithmetic Mellin window

The 5040 lane uses the finite divisor carrier `Nat.divisors`. Here its
unweighted arithmetic synthesis is independently specified on the very same
logarithmic window as `windowMellinSum`. We first compute the complete missing-
divisor defect, without assuming prefix coverage, and transport that identity
through the already-owned prime action. Coverage then removes the defect by
finite arithmetic rather than by assuming operator equality.

Only upper seed support is needed; the seed may be complex. Closed endpoints
are retained throughout. The sharper L2 threshold at the first missing divisor,
the Euler-product logarithmic-derivative identity, and origin-normalized Fourier
certificates are separate paper results in RH_RESEARCH_LANE_THEORY.md.
No Robin positivity, unknown eigenvector or spectral gap is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilDivisorWindowCorrespondence

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining

/-- Synthesis over the same actual positive-divisor carrier used by the
finite divisor partition. The half-density and support are independently given. -/
def divisorWindow (a : ℝ) (N : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Icc (-a) a).indicator
    (fun x => 4 * (Real.exp (x / 2) : ℂ) *
      ∑ d ∈ N.divisors, h ((d : ℝ) * Real.exp x)) x

/-- Every missing divisor in the visible integer prefix is retained as a
function, before any norm, absolute value or prime action is applied. -/
def missingDivisorWindow (a : ℝ) (N M : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Icc (-a) a).indicator
    (fun x => 4 * (Real.exp (x / 2) : ℂ) *
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬d ∣ N),
        h ((d : ℝ) * Real.exp x)) x

private theorem invisible_term (a : ℝ) (M : ℕ) (h : ℝ → ℂ)
    (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0) {x : ℝ} (hx : -a ≤ x)
    {d : ℕ} (hd : M < d) : h ((d : ℝ) * Real.exp x) = 0 := by
  have hfloor : Real.exp a ≤ (M : ℝ) * Real.exp x := by
    calc
      Real.exp a = Real.exp (2 * a) * Real.exp (-a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (M : ℝ) * Real.exp x := mul_le_mul hcap
        (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (Nat.cast_nonneg M)
  apply hs
  have hdr : (M : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact hfloor.trans_lt (mul_lt_mul_of_pos_right hdr (Real.exp_pos x))

private theorem divisor_sum_truncate (N M : ℕ) (hN : N ≠ 0)
    (F : ℕ → ℂ) (htail : ∀ d, M < d → F d = 0) :
    (∑ d ∈ N.divisors, F d) =
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ∣ N), F d := by
  classical
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hN⟩
  · intro d hd hnot
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hd).1
    have hgt : M < d := by
      by_contra h
      have hdM : d ≤ M := Nat.le_of_not_gt h
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hdpos, hdM⟩, hdvd⟩)
    exact htail d hgt

/-- Exact correspondence without a coverage hypothesis: the missing arithmetic
terms form precisely the defect. It is an equality of the actual functions
for every real x, not only an equality of scalar partition values. -/
theorem divisor_window_exact_defect (a : ℝ) (N M : ℕ) (h : ℝ → ℂ)
    (hN : N ≠ 0) (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0) (x : ℝ) :
    divisorWindow a N h x = windowMellinSum a M h x -
      missingDivisorWindow a N M h x := by
  classical
  by_cases hx : x ∈ Set.Icc (-a) a
  · simp only [divisorWindow, windowMellinSum, missingDivisorWindow,
      Set.indicator_of_mem hx]
    rw [divisor_sum_truncate N M hN (fun d => h ((d : ℝ) * Real.exp x))
      (fun d hd => invisible_term a M h hcap hs hx.1 hd)]
    have hsplit :
        (∑ d ∈ (Finset.Icc 1 M).filter (fun d => d ∣ N), h ((d : ℝ) * Real.exp x)) +
        (∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬d ∣ N), h ((d : ℝ) * Real.exp x)) =
        ∑ d ∈ Finset.Icc 1 M, h ((d : ℝ) * Real.exp x) := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d ∣ N <;> simp [hd]
    rw [← hsplit]
    ring
  · simp [divisorWindow, windowMellinSum, missingDivisorWindow, hx]

private theorem prime_forward_sub (a : ℝ) (M : ℕ) (f g : ℝ → ℂ) (x : ℝ) :
    primeForward a M (fun y => f y - g y) x =
      primeForward a M f x - primeForward a M g x := by
  classical
  by_cases hx : x ∈ Set.Icc (-a) a
  · simp only [primeForward, Set.indicator_of_mem hx, mul_sub,
      Finset.sum_sub_distrib]
  · simp [primeForward, hx]

/-- Transport the original prime-power action, including its complete
missing-divisor correction. No scalar positivity is used to discard the
complex arithmetic defect. The existing prime-Mellin identity is reused. -/
theorem divisor_window_prime_action (a : ℝ) (N M : ℕ) (h : ℝ → ℂ)
    (hN : N ≠ 0) (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0) (x : ℝ) :
    primeForward a M (divisorWindow a N h) x =
      divisorWindow a N (fun t => (Real.log t : ℂ) * h t) x -
        (x : ℂ) * divisorWindow a N h x +
      missingDivisorWindow a N M (fun t => (Real.log t : ℂ) * h t) x -
        (x : ℂ) * missingDivisorWindow a N M h x -
      primeForward a M (missingDivisorWindow a N M h) x := by
  have hslog : ∀ t, Real.exp a < t → (Real.log t : ℂ) * h t = 0 := by
    intro t ht
    rw [hs t ht, mul_zero]
  have heq : divisorWindow a N h = fun y =>
      windowMellinSum a M h y - missingDivisorWindow a N M h y := by
    funext y
    exact divisor_window_exact_defect a N M h hN hcap hs y
  simp only [heq]
  rw [prime_forward_sub, prime_forward_mellin_identity a M h hcap hs x]
  rw [divisor_window_exact_defect a N M _ hN hcap hslog x]
  ring

/-- Divisibility of the entire visible prefix is an explicit arithmetic
condition sufficient for exact equality with the already-owned window. -/
theorem divisor_window_prefix_correspondence (a : ℝ) (N M : ℕ) (h : ℝ → ℂ)
    (hN : N ≠ 0) (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0)
    (hcover : ∀ d ∈ Finset.Icc 1 M, d ∣ N) :
    divisorWindow a N h = windowMellinSum a M h := by
  classical
  funext x
  rw [divisor_window_exact_defect a N M h hN hcap hs x]
  have hempty : (Finset.Icc 1 M).filter (fun d => ¬d ∣ N) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact (Finset.mem_filter.mp hd).2 (hcover d (Finset.mem_filter.mp hd).1)
  simp [missingDivisorWindow, hempty]

/-- A concrete shared window: 5040 and 2520 encode the same Mellin synthesis
when exp(2a)<=10. They differ as divisor partitions outside this visible range.
The sharper L2 endpoint at exp(2a)=11 is a separate paper statement. -/
theorem divisor_windows_5040_and_2520 (a : ℝ) (h : ℝ → ℂ)
    (hcap : Real.exp (2 * a) ≤ 10)
    (hs : ∀ t, Real.exp a < t → h t = 0) :
    divisorWindow a 5040 h = windowMellinSum a 10 h ∧
      divisorWindow a 2520 h = windowMellinSum a 10 h := by
  constructor
  · apply divisor_window_prefix_correspondence a 5040 10 h (by norm_num) hcap hs
    intro d hd
    obtain ⟨hd1, hd10⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num
  · apply divisor_window_prefix_correspondence a 2520 10 h (by norm_num) hcap hs
    intro d hd
    obtain ⟨hd1, hd10⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num

#print axioms divisor_window_exact_defect
#print axioms divisor_window_prime_action
#print axioms divisor_window_prefix_correspondence
#print axioms divisor_windows_5040_and_2520

end D5.S3.Weil.ZetaBridge.WeilDivisorWindowCorrespondence
