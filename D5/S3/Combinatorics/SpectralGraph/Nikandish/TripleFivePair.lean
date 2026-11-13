/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/TripleFivePair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/TripleFivePair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete twenty-nine-offset arithmetic and actual triple-five nonintegrality. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairTailSpectrum
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairFourEndpoints

/-! Source: four-prime-tail-reduction, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. All twenty-nine
necessary quadratic offsets are covered: seven exact nonsquare rows,
the factored fifth row, the whole positive coefficient interval nine
through twenty-eight, and the negative-discriminant last row. No
finite tail cutoff scan or graph enumeration is substituted. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.TripleFivePair
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairTailArithmetic IdealIntersectionSupport IdealIntersectionObstructions
open PairedIdealIntersectionLift

def q (t c : ℤ) : ℤ :=
  (216*t^2-1080*t-6875)*c^2+t*(-42*t^2+1195*t+575)*c+
    t*(30-t)*(t*(30-t)+5*t+125)

theorem quadratic (t c : ℤ) :
    (tensorK 5 5 c-(6+t) • 1).det=q t c := by
  rw [det_tensorK_sub_scalar]
  unfold q
  ring

private theorem positive_range (t c : ℤ) (hl : 9 ≤ t) (hu : t ≤ 28) (hc : 0 < c) :
    0 < q t c := by
  have hA : 0 < 216*t^2-1080*t-6875 := by nlinarith [sq_nonneg (t-9)]
  have hprod : 0 ≤ (t-9)*(28-t) := mul_nonneg (by omega) (by omega)
  have hB : 0 < -42*t^2+1195*t+575 := by nlinarith
  have hH : 0 < PairTailArithmetic.H 5 5 t := H_positive 5 5 t (by norm_num) (by norm_num)
    (by omega) (by norm_num; omega)
  have hid : q t c=(216*t^2-1080*t-6875)*c^2+
      t*(-42*t^2+1195*t+575)*c+PairTailArithmetic.H 5 5 t := by unfold q PairTailArithmetic.H; ring
  rw [hid]
  positivity

set_option maxHeartbeats 1000000 in
/-- The complete original twenty-nine rows leave exactly the fifth row
and the positive tail five. This is a necessary-root result. -/
theorem integer_candidate (t c : ℤ) (ht : 0 < t) (hu : t < 30) (hc : 0 < c)
    (hz : q t c=0) : t=5 ∧ c=5 := by
  by_cases hm : 9 ≤ t ∧ t ≤ 28
  · exact ((positive_range t c hm.1 hm.2 hc).ne' hz).elim
  have hr : t ≤ 8 ∨ t=29 := by omega
  rcases hr with h8 | rfl
  · have h1 : 1 ≤ t := by omega
    interval_cases t
    · have hn : (-7739:ℤ)*c^2+1728*c+4611 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 12071 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hn : (-8171:ℤ)*c^2+5594*c+10696 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 19516 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hn : (-8171:ℤ)*c^2+11346*c+17901 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 26717 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hn : (-7739:ℤ)*c^2+18732*c+25896 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 33948 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hid : q 5 c = -6875*(c-5)*(c+1) := by unfold q; ring
      rw [hid] at hz
      have hh : c-5=0 := by
        rcases mul_eq_zero.mp hz with he | he
        · exact (mul_eq_zero.mp he).resolve_left (by norm_num)
        · omega
      exact ⟨rfl,by omega⟩
    · have hn : (-5579:ℤ)*c^2+37398*c+43056 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 48574 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hn : (-3851:ℤ)*c^2+48174*c+51681 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 55828 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
    · have hn : (-1691:ℤ)*c^2+59576*c+60016 ≠ 0 :=
        PairFourEndpoints.quadratic_gap _ _ _ c 62890 (by norm_num) (by norm_num) (by norm_num)
      apply False.elim
      apply hn
      simpa [q] using hz
  · have hsq := sq_nonneg (2*143461*c-2668)
    norm_num [q] at hz
    nlinarith

/-- The full quartic at the sole surviving algebraic candidate. -/
theorem diagonal_factor (x : ℝ) :
    (tensorK (5:ℝ) 5 5-x • 1).det=(x-11)*(x^3-288*x^2+14298*x-41261) := by
  rw [det_tensorK_sub_scalar]
  ring

/-- A genuine full-operator eigenpair in the original exceptional cubic interval. -/
theorem diagonal_eigenpair : ∃ e : ℝ, 3 < e ∧ e < 4 ∧
    ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧ tensorK (5:ℝ) 5 5*ᵥh=e • h := by
  let f := fun x : ℝ => x^3-288*x^2+14298*x-41261
  have hf : Continuous f := by dsimp [f]; fun_prop
  have h3 : f 3 < 0 := by norm_num [f]
  have h4 : 0 < f 4 := by norm_num [f]
  obtain ⟨e,he,hfe⟩ := intermediate_value_Icc (by norm_num : (3:ℝ) ≤ 4)
    hf.continuousOn (show (0:ℝ) ∈ Set.Icc (f 3) (f 4) from ⟨h3.le,h4.le⟩)
  have hel : 3 < e := by
    have hn : (3:ℝ) ≠ e := by intro h; rw [←h] at hfe; exact h3.ne hfe
    exact lt_of_le_of_ne he.1 hn
  have heu : e < 4 := by
    have hn : e ≠ (4:ℝ) := by intro h; rw [h] at hfe; exact h4.ne' hfe
    exact lt_of_le_of_ne he.2 hn
  have hd : (tensorK (5:ℝ) 5 5-e • 1).det=0 := by rw [diagonal_factor]; change (e-11)*f e=0; rw [hfe,mul_zero]
  obtain ⟨h,hh,hZ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hZ
  exact ⟨e,hel,heu,h,hh,sub_eq_zero.mp hZ⟩

/-- Every positive free tail is excluded on the actual graph, including
all tails below five and the exceptional fifth tail. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (c : ℕ) (hc : 0 < c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents 5 5 c)) := by
  intro HI
  obtain ⟨t,ht,hu,hz,_⟩ := PairTailSpectrum.actual_tail_candidate p hp hinj 5 5 c
    (by norm_num) (by norm_num) hc HI
  norm_num at ht hu
  change (tensorK (5:ℤ) 5 (c:ℤ)-(6+t) • 1).det=0 at hz
  rw [quadratic] at hz
  have hcc : c=5 := by
    have he := (integer_candidate t (c:ℤ) ht hu (by positivity) hz).2
    exact_mod_cast he
  subst c
  obtain ⟨e,hel,heu,h,hh,hE⟩ := diagonal_eigenpair
  have hactual := actual_paired_eigenvalue p hp hinj 5 5 5
    (by norm_num) (by norm_num) (by norm_num) e h hh hE
  obtain ⟨z,hz⟩ := HI _ hactual
  have he : e=((((5+1)^2*(5+1)*(5+1)-2:ℕ):ℤ)+1-z:ℤ) := by
    push_cast
    norm_num at hz ⊢
    linarith
  have hlz : (3:ℤ)<(((5+1)^2*(5+1)*(5+1)-2:ℕ):ℤ)+1-z := by exact_mod_cast (he ▸ hel)
  have huz : (((5+1)^2*(5+1)*(5+1)-2:ℕ):ℤ)+1-z<(4:ℤ) := by exact_mod_cast (he ▸ heu)
  omega

end D5.S3.Combinatorics.SpectralGraph.TripleFivePair
