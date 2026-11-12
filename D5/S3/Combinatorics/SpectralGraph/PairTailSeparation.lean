/- GID: D5/S3/Combinatorics/SpectralGraph/PairTailSeparation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairTailSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full middle-root separation and endpoint chain for the paired tensor. -/
import D5.S3.Combinatorics.SpectralGraph.PairTailOrdering

/-! Source: the complete large-tail and harmonic-tail manuscripts, supplied
PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. This retains
the original stronger upper-side root separation and the strict endpoint
chain. All values are those of the full operator, with multiplicity. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.PairTailSeparation
open PairedIdealIntersectionObstructions PairTailOrdering

private theorem below_largest (a b c e : ℝ) (hb : 0 < b) (hc : 0 < c)
    (v : Fin 2 × Fin 2 → ℝ) (hv : v ≠ 0)
    (hE : tensorK a b c *ᵥ v = e • v) : e ≤ values a b c 0 := by
  have hd : (tensorK a b c-e • 1).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v,hv,?_⟩
    rw [sub_mulVec,hE,smul_mulVec,one_mulVec,sub_self]
  rw [determinant a b c e hb hc] at hd
  have h1 := values_antitone a b c (show (0 : Fin 4) ≤ 1 by decide)
  have h2 := values_antitone a b c (show (0 : Fin 4) ≤ 2 by decide)
  have h3 := values_antitone a b c (show (0 : Fin 4) ≤ 3 by decide)
  rcases mul_eq_zero.mp hd with h012 | h03
  · rcases mul_eq_zero.mp h012 with h01 | h02
    · rcases mul_eq_zero.mp h01 with h00 | h01
      · linarith [sub_eq_zero.mp h00]
      · linarith [sub_eq_zero.mp h01]
    · linarith [sub_eq_zero.mp h02]
  · linarith [sub_eq_zero.mp h03]

private theorem largest_above (a b c u : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hu : u < (a+1)*(b+1)*(c+1)+a) : u < values a b c 0 := by
  let M := u • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)-symmetricK a b c
  have hM : M.IsHermitian := (show (u • (1 : Matrix (Fin 2 × Fin 2)
      (Fin 2 × Fin 2) ℝ)).IsHermitian by simp).sub (symmetric_hermitian a b c)
  have hn : ¬ M.PosSemidef := by
    intro hp
    have hd := hp.diag_nonneg (i := (0,0))
    have hi : M (0,0) (0,0) = u-((a+1)*(b+1)*(c+1)+a) := by
      simp [M,symmetricK,E,H,kroneckerMap_apply] <;> ring
    rw [hi] at hd
    linarith
  obtain ⟨e,he,z,hz,hZ⟩ := negative_eigenpair_of_not_posSemidef M hM hn
  have hS : symmetricK a b c *ᵥ z = (u-e) • z := by
    dsimp [M] at hZ
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hZ
    ext i
    have hi := congrFun hZ i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hi ⊢
    linarith
  obtain ⟨v,hv,hV⟩ := tensor_eigenpair_of_symmetric a b c hb hc (u-e) z hz hS
  have hm := below_largest a b c (u-e) hb hc v hv hV
  linarith

private theorem third_above (a b c u : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h0 : u < values a b c 0) (h2 : values a b c 2 < u)
    (hd : 0 < (tensorK a b c-u • 1).det) : u < values a b c 1 := by
  by_contra hn
  have h1 : values a b c 1-u ≤ 0 := by linarith
  have h3 : values a b c 3-u ≤ 0 := by
    have h := values_antitone a b c (show (2 : Fin 4) ≤ 3 by decide)
    linarith
  have hp01 : (values a b c 0-u)*(values a b c 1-u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h1
  have hp23 : 0 ≤ (values a b c 2-u)*(values a b c 3-u) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) h3
  have hp := mul_nonpos_of_nonpos_of_nonneg hp01 hp23
  rw [determinant a b c u hb hc] at hd
  nlinarith only [hd,hp]

/-- The full bounded endpoint lies strictly between the middle roots. -/
theorem bounded_separation (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 1 ≤ c) :
    a+1 < values a b c 2 ∧ values a b c 2 < (a+1)*(b+1) ∧
      (a+1)*(b+1) < values a b c 1 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hl,hu⟩ := bounded_window a b c ha hb hc
  have hdiag : (a+1)*(b+1) < (a+1)*(b+1)*(c+1)+a := by
    have hp : 0 < (a+1)*(b+1)*c+a := by positivity
    nlinarith
  have h0 := largest_above a b c _ hb hc0 hdiag
  exact ⟨hl,hu,third_above a b c _ hb hc0 h0 hu
    (PairTailSpectrum.upper_endpoint a b c ha hb hc)⟩

/-- The complete original harmonic chain, including both middle roots
and the strict endpoint comparison, on every original positive integer-sized domain. -/
theorem harmonic_separation (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbc : b < c) :
    a+b+1 < values a b c 2 ∧ values a b c 2 < a+1+2*b*c/(b+c) ∧
      a+1+2*b*c/(b+c) < values a b c 1 ∧ a+1+2*b*c/(b+c) < a+2*b+1 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hs : 0 < b+c := by linarith
  have he : a+1+2*b*c/(b+c) < a+2*b+1 := by
    have hi : 2*b*c/(b+c) < 2*b := (div_lt_iff₀ hs).mpr (by nlinarith)
    linarith
  have hd0 : a+2*b+1 < (a+1)*(b+1)*(c+1)+a := by
    have hcm : 0 ≤ c-1 := by linarith
    have hp : 0 < (c-1)*(a+1)*(b+1)+2*a*b+2*a+1 := by positivity
    nlinarith
  obtain ⟨hl,hu,_⟩ := harmonic_window a b c ha hb hbc
  have h0 := largest_above a b c _ hb0 hc0 (lt_trans he hd0)
  exact ⟨hl,hu,third_above a b c _ hb0 hc0 h0 hu
    (PairTailSpectrum.harmonic_endpoint a b c ha0 hb0 hbc),he⟩

/-- Every value of the entire ordered tensor spectrum is an actual
ideal-intersection graph Laplacian eigenvalue after the original lift. -/
theorem actual_spectrum (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (i : Fin 4) :
    IdealIntersectionObstructions.HasActualEigenvalue
      (IdealIntersectionSupport.modulus p (PairedIdealIntersectionLift.pairExponents a b c))
      ((((a+1)^2*(b+1)*(c+1)-2 : ℕ) : ℝ)+1-values (a:ℝ) (b:ℝ) (c:ℝ) i) := by
  obtain ⟨v,hv,hE⟩ := eigenpair (a:ℝ) (b:ℝ) (c:ℝ) (by positivity) (by positivity) i
  exact PairedIdealIntersectionLift.actual_paired_eigenvalue p hp hinj a b c ha hb hc _ v hv hE

/-- The full original middle-root separation and endpoint chain apply
to both actual graph eigenvalues for every distinct-prime assignment. -/
theorem actual_harmonic_separation (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hbc : b < c) :
    let V : ℝ := (((a+1)^2*(b+1)*(c+1)-2 : ℕ) : ℝ)
    (a:ℝ)+b+1 < values (a:ℝ) (b:ℝ) (c:ℝ) 2 ∧
      values (a:ℝ) (b:ℝ) (c:ℝ) 2 < (a:ℝ)+1+2*b*c/(b+c) ∧
      (a:ℝ)+1+2*b*c/(b+c) < values (a:ℝ) (b:ℝ) (c:ℝ) 1 ∧
      (a:ℝ)+1+2*b*c/(b+c) < (a:ℝ)+2*b+1 ∧
      IdealIntersectionObstructions.HasActualEigenvalue
        (IdealIntersectionSupport.modulus p (PairedIdealIntersectionLift.pairExponents a b c))
        (V+1-values (a:ℝ) (b:ℝ) (c:ℝ) 2) ∧
      IdealIntersectionObstructions.HasActualEigenvalue
        (IdealIntersectionSupport.modulus p (PairedIdealIntersectionLift.pairExponents a b c))
        (V+1-values (a:ℝ) (b:ℝ) (c:ℝ) 1) := by
  dsimp only
  obtain ⟨hl,hu,hs,he⟩ := harmonic_separation (a:ℝ) (b:ℝ) (c:ℝ)
    (by exact_mod_cast (show 1 ≤ a by omega))
    (by exact_mod_cast (show 1 ≤ b by omega)) (by exact_mod_cast hbc)
  exact ⟨hl,hu,hs,he,actual_spectrum p hp hinj a b c ha hb (by omega) 2,
    actual_spectrum p hp hinj a b c ha hb (by omega) 1⟩

end D5.S3.Combinatorics.SpectralGraph.PairTailSeparation
