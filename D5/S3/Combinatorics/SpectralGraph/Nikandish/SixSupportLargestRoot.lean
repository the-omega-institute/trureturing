/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRoot
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full largest-root unit interval, consumed by actual ideal graphs. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportLargestRootSigns
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! The original full real largest-root domain is retained. Positivity on the
whole upper half-line proves the upper spectral bound. Maximizing the finite
set of real quintic roots identifies the largest eigenvalue, independently of
which intermediate-value witness is initially obtained. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportLargestRoot

open Matrix Polynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportLargestRootSigns
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- The exact original largest real quotient eigenvalue, for every real
2≤a≤b≤c, b-a≥3 and c≥a²-a. -/
theorem result (a b c : ℝ) (ha : 2 ≤ a) (hab : a+3 ≤ b)
    (hbc : b ≤ c) (hc : a^2-a ≤ c) :
    ∃ e : ℝ, b*c+a+b+c < e ∧ e < b*c+a+b+c+1 ∧
      (∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient a b c *ᵥ z = e • z) ∧
      ∀ f : ℝ, ∀ z : Fin 6 → ℝ, z ≠ 0 → quotient a b c *ᵥ z = f • z → f ≤ e := by
  classical
  let M := b*c+a+b+c
  have hM : 0 < M := by
    dsimp [M]
    have hb : 0 < b := by linarith
    have hc0 : 0 < c := by linarith
    positivity
  have hneg : h a b c M < 0 := lower_negative a b c ha hab hbc
  have hpos : 0 < h a b c (M+1) := by
    simpa only [add_zero] using upper_halfline a b c 0 ha hab hbc hc (by norm_num)
  have hcont : Continuous (fun x : ℝ => h a b c x) := by
    unfold h
    exact Polynomial.continuous _
  obtain ⟨q, hq, hqroot⟩ := intermediate_value_Icc (show M ≤ M+1 by linarith)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Icc (h a b c M) (h a b c (M+1)) from
      ⟨hneg.le, hpos.le⟩)
  have hMq : M < q := by
    have hn : q ≠ M := by intro heq; subst q; linarith
    exact lt_of_le_of_ne hq.1 (Ne.symm hn)
  have hp : quintic a b c ≠ 0 := by
    intro hz
    have hd := reduced_degree_five (R := ℝ) a b c
    rw [← quintic_eq_reduced, hz] at hd
    norm_num at hd
  let S : Finset ℝ := (quintic a b c).roots.toFinset
  have hqin : q ∈ S := by
    apply Multiset.mem_toFinset.mpr
    exact (Polynomial.mem_roots hp).mpr hqroot
  let e := S.max' ⟨q, hqin⟩
  have hqe : q ≤ e := S.le_max' q hqin
  have heS : e ∈ S := S.max'_mem _
  have heroot : h a b c e = 0 := (Polynomial.mem_roots hp).mp
    (Multiset.mem_toFinset.mp heS)
  have heM : M < e := hMq.trans_le hqe
  have heU : e < M+1 := by
    by_contra hle
    have hy : 0 ≤ e-(M+1) := by linarith
    have hp' := upper_halfline a b c (e-(M+1)) ha hab hbc hc hy
    have heq : b*c+a+b+c+1+(e-(M+1)) = e := by dsimp [M]; ring
    rw [heq, heroot] at hp'
    linarith
  refine ⟨e, heM, heU, eigenpair_of_root a b c e heroot, ?_⟩
  intro f z hz hf
  by_cases hf0 : f = 0
  · subst f
    exact (hM.trans heM).le
  · have hfroot := root_of_eigenpair a b c f hf0 z hz hf
    have hfin : f ∈ S := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hfroot)
    exact S.le_max' f hfin

/-- Actual ideal graphs consume the entire integer largest-root family. -/
theorem actual_nonintegral (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 2 ≤ a)
    (hab : a+3 ≤ b) (hbc : b ≤ c) (hc : (a : ℤ)^2-a ≤ c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  obtain ⟨e, heM, heU, ⟨z, hz, heigen⟩, hmax⟩ := result a b c
    (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbc)
    (by exact_mod_cast hc)
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  have he0 : e ≠ 0 := by
    have hm : (0 : ℝ) < (b : ℝ)*(c : ℝ)+a+b+c := by positivity
    linarith
  have hroot := root_of_eigenpair (a : ℝ) (b : ℝ) (c : ℝ) e he0 z hz heigen
  apply nonintegral_of_unit_root p hp hinj a b c ha0 hb0 hc0 e he0 hroot
    ((b : ℤ)*c+a+b+c)
  · exact_mod_cast heM
  · exact_mod_cast heU

#print axioms result
#print axioms actual_nonintegral

end D5.S3.Combinatorics.SpectralGraph.SixSupportLargestRoot
