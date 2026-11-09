/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportBoundedGapFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportBoundedGapFamilies
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original four bounded-gap families with exact two-root and endpoint consumers. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportInertiaIntervals
import D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapEndpoints
import D5.S3.Combinatorics.SpectralGraph.ThreePrimeLaplacianClassification

/-! Source: entire low-spectrum section at revision
b93becea662a746badeadba42fdc3d3eb3db9382,
blob10576d85188447cea8efba1549722d8e14c050f2. The full graph
classification is reused only for the original small-minimum foundation;
the two-root/endpoint route is independently retained for every a>=4. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapFamilies
open Matrix Polynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
open D5.S3.Combinatorics.SpectralGraph.SixSupportInertiaIntervals
open D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapEndpoints
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- Exactly the original four gap pairs, not a diagnostic exponent sample. -/
def gaps : Fin 4 → ℕ × ℕ := ![(1,2),(1,3),(2,3),(3,4)]

/-- The exact upper-inertia differences in the four full real families. -/
theorem inertia_differences (a : ℝ) :
    (a+2-3)*(a+(a+1)+(a+2)-3)-3*a*(a+1) = -6*a ∧
    (a+3-3)*(a+(a+1)+(a+3)-3)-3*a*(a+1) = -2*a ∧
    (a+3-3)*(a+(a+2)+(a+3)-3)-3*a*(a+2) = -4*a ∧
    (a+4-3)*(a+(a+3)+(a+4)-3)-3*a*(a+3) = 4-2*a := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Exactly two positive roots below3 in each original full gap family. -/
theorem low_count (a : ℝ) (ha : 4 ≤ a) (i : Fin 4) :
    positiveBelow a (a+(gaps i).1) (a+(gaps i).2) 3 = 2 := by
  fin_cases i <;> norm_num [gaps]
  all_goals apply (upper_criterion _ _ _ _ (by linarith) (by linarith)
    (by linarith) (by norm_num) (by linarith) ?_).1
  all_goals nlinarith

private theorem real_endpoints (a : ℕ) (ha : 4 ≤ a) (i : Fin 4) :
    h (a : ℝ) (a+(gaps i).1) (a+(gaps i).2) 1 ≠ 0 ∧
    h (a : ℝ) (a+(gaps i).1) (a+(gaps i).2) 2 ≠ 0 := by
  have h1 := first_negative (a : ℝ) (by exact_mod_cast ha)
  have h2 := second_nonzero (a : ℤ) (by exact_mod_cast ha)
  have hr2 : h (a : ℝ) (a+1) (a+2) 2 ≠ 0 ∧ h (a : ℝ) (a+1) (a+3) 2 ≠ 0 ∧
      h (a : ℝ) (a+2) (a+3) 2 ≠ 0 ∧ h (a : ℝ) (a+3) (a+4) 2 ≠ 0 := by
    simp only [h_eq_value,SixSupportClassificationAlgebra.value] at h2 ⊢
    exact_mod_cast h2
  fin_cases i <;> norm_num [gaps]
  · exact ⟨h1.1.ne,hr2.1⟩
  · exact ⟨h1.2.1.ne,hr2.2.1⟩
  · exact ⟨h1.2.2.1.ne,hr2.2.2.1⟩
  · exact ⟨h1.2.2.2.ne,hr2.2.2.2⟩

/-- Every original four-gap ideal graph is nonintegral. For a>=4 the
consumer uses the complete two-low-root and endpoint certificates. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a : ℕ) (ha : 0 < a) (i : Fin 4) :
    ¬ActualLaplacianIntegral (modulus p (exponents a (a+(gaps i).1) (a+(gaps i).2))) := by
  have hd : 0 < (gaps i).1 ∧ (gaps i).1 < (gaps i).2 := by fin_cases i <;> decide
  by_cases ha4 : 4 ≤ a
  · classical
    have hc := low_count a (by exact_mod_cast ha4) i
    obtain ⟨t,ht,ht0,ht3⟩ := Multiset.countP_pos.mp (show 0 < positiveBelow a
        (a+(gaps i).1) (a+(gaps i).2) 3 by rw [hc]; norm_num)
    have he := (Polynomial.mem_roots
      (quotient a (a+(gaps i).1) (a+(gaps i).2)).charpoly_monic.ne_zero).mp ht
    change (quotient a (a+(gaps i).1) (a+(gaps i).2)).charpoly.eval t = 0 at he
    rw [Matrix.eval_charpoly,determinant] at he
    have hr := (mul_eq_zero.mp he).resolve_left ht0.ne'
    have hb : 0 < a+(gaps i).1 := by omega
    have hcpos : 0 < a+(gaps i).2 := by omega
    have hends := real_endpoints a ha4 i
    intro hint
    obtain ⟨z,hz⟩ := root_integral_of_actual_integral p hp hinj a
      (a+(gaps i).1) (a+(gaps i).2) ha hb hcpos hint t ht0.ne' (by simpa only [Nat.cast_add] using hr)
    have hz0 : 0 < z := by exact_mod_cast (show (0 : ℝ) < z by simpa [hz] using ht0)
    have hz3 : z < 3 := by exact_mod_cast (show (z : ℝ) < 3 by simpa [hz] using ht3)
    have hz12 : z = 1 ∨ z = 2 := by omega
    rcases hz12 with rfl | rfl
    · exact hends.1 (by simpa [hz] using hr)
    · exact hends.2 (by simpa [hz] using hr)
  · exact ThreePrimeLaplacianClassification.sorted p hp hinj a
      (a+(gaps i).1) (a+(gaps i).2) ha (by omega) (by omega)

#print axioms low_count
#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportBoundedGapFamilies
