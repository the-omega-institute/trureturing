/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairGapCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairGapCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete tail-gap three and four classifications on actual ideal graphs. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairGapSpectrum
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairFourSpectrum

/-! Sources: four-prime-weighted-midpoint and four-prime-even-midpoint,
PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All positive
a,b are retained. The small-tail rows are polynomial identities for
unbounded a, not an exponent scan. Unit and repeated-two/three/four
cases reuse their existing actual-graph theorems. The half-unit/even
windows are not asserted for every small case. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairGapCompletion
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

private theorem small_upper (a : ℝ) (ha : 5≤a) (b r : ℕ) (hb : 1≤b) (hb4 : b≤4)
    (hr : r=3 ∨ r=4) (hne : ¬(b=4 ∧ r=4)) :
    0<(tensorK a (b:ℝ) ((b+r:ℕ):ℝ)-(a+b+2) • 1).det := by
  let u:=a-5
  have hu : 0≤u := by dsimp [u]; linarith
  rcases hr with rfl | rfl
  · interval_cases b
    · have hid : (tensorK a 1 4-(a+3) • 1).det = 26*u^3+452*u^2+2638*u+5168 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 1 4-(a+3) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · have hid : (tensorK a 2 5-(a+4) • 1).det = 37*u^3+653*u^2+3905*u+7909 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 2 5-(a+4) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · have hid : (tensorK a 3 6-(a+5) • 1).det = 36*u^3+612*u^2+3644*u+7604 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 3 6-(a+5) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · have hid : (tensorK a 4 7-(a+6) • 1).det = 17*u^3+161*u^2+565*u+1265 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 4 7-(a+6) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
  · interval_cases b
    · have hid : (tensorK a 1 5-(a+3) • 1).det = 42*u^3+721*u^2+4168*u+8119 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 1 5-(a+3) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · have hid : (tensorK a 2 6-(a+4) • 1).det = 48*u^3+804*u^2+4629*u+9198 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 2 6-(a+4) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · have hid : (tensorK a 3 7-(a+5) • 1).det = 22*u^3+209*u^2+608*u+889 := by
        rw [det_tensorK_sub_scalar]
        dsimp [u]
        ring
      have hp : 0<(tensorK a 3 7-(a+5) • 1).det := by rw [hid]; positivity
      norm_num at hp ⊢
      convert hp using 1 <;> congr 3 <;> ring
    · exact (hne ⟨rfl,rfl⟩).elim

private theorem between (a b c l u : ℝ) (hlu : l<u)
    (hl : (tensorK a b c-l • 1).det<0)
    (hu : 0<(tensorK a b c-u • 1).det) :
    ∃ e : ℝ, l<e ∧ e<u ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a b c*ᵥh=e • h := by
  let f:=fun x : ℝ => (tensorK a b c-x • 1).det
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨e,he,hfe⟩:=intermediate_value_Icc hlu.le hf.continuousOn
    (show (0:ℝ)∈Set.Icc (f l) (f u) from ⟨hl.le,hu.le⟩)
  have hel : l<e := by
    have hn : l≠e := by intro h; rw [←h] at hfe; exact hl.ne hfe
    exact lt_of_le_of_ne he.1 hn
  have heu : e<u := by
    have hn : e≠u := by intro h; rw [h] at hfe; exact hu.ne' hfe
    exact lt_of_le_of_ne he.2 hn
  obtain ⟨h,hh,hZ⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hfe
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hZ
  exact ⟨e,hel,heu,h,hh,sub_eq_zero.mp hZ⟩

private theorem small_actual (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b r : ℕ) (ha : 5≤a) (hb : 0<b) (hb4 : b≤4)
    (hr : r=3 ∨ r=4) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+r))) := by
  have haR : (5:ℝ)≤a := by exact_mod_cast ha
  let l : ℕ := if b=4 ∧ r=4 then a+6 else a+b+1
  have hl : (tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)-(l:ℝ) • 1).det<0 := by
    by_cases hh : b=4 ∧ r=4
    · rcases hh with ⟨rfl,rfl⟩
      have hid : (tensorK (a:ℝ) 4 8-((a:ℝ)+6) • 1).det =
          -(48*((a:ℝ)-1)^3+848*((a:ℝ)-1)^2+1657*((a:ℝ)-1)+272) := by
        rw [det_tensorK_sub_scalar]
        ring
      have ha1 : (0:ℝ)<(a:ℝ)-1 := by linarith
      have hpos : 0<48*((a:ℝ)-1)^3+848*((a:ℝ)-1)^2+1657*((a:ℝ)-1)+272 := by positivity
      have hlv : l=a+6 := by simp [l]
      norm_num only [hlv, Nat.cast_add, Nat.cast_ofNat]
      change (tensorK (a:ℝ) 4 8-((a:ℝ)+6) • 1).det<0
      rw [hid]
      linarith
    · have hbc : (b:ℝ)<((b+r:ℕ):ℝ) := by
        have hr0 : 0<r := by rcases hr with rfl | rfl <;> omega
        exact_mod_cast (show b<b+r by omega)
      simpa only [l,if_neg hh,Nat.cast_add,Nat.cast_one] using
        PairGapSigns.unequal_lower_negative (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)
          (by linarith) (by exact_mod_cast (show 1≤b by omega)) hbc
  have hu : 0<(tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)-((l:ℝ)+1) • 1).det := by
    by_cases hh : b=4 ∧ r=4
    · rcases hh with ⟨rfl,rfl⟩
      have ht:=PairGapSigns.midpoint_positive (a:ℝ) 4 4 (by linarith) (by norm_num) (by norm_num)
      have hlv : l=a+6 := by simp [l]
      norm_num only [hlv, Nat.cast_add, Nat.cast_ofNat]
      have he : (a:ℝ)+6+1=(a:ℝ)+4+(4+2)/2 := by ring
      rw [he]
      convert ht using 1 <;> norm_num
    · have ht:=small_upper (a:ℝ) haR b r (by omega) hb4 hr hh
      simpa only [l,if_neg hh,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using ht
  obtain ⟨e,hel,heu,h,hh,hE⟩:=between (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ) (l:ℝ) ((l:ℝ)+1)
    (by linarith) hl hu
  have hact:=actual_paired_eigenvalue p hp hinj a b (b+r) (by omega) hb (by omega) e h hh hE
  intro H
  obtain ⟨z,hz⟩:=H _ hact
  let w : ℤ:=(((a+1)^2*(b+1)*(b+r+1)-2:ℕ):ℤ)+1-z
  have hew : e=(w:ℝ) := by dsimp [w]; push_cast; linarith
  have h1 : (l:ℤ)<w := by exact_mod_cast (hew ▸ hel)
  have h2 : w<(l:ℤ)+1 := by exact_mod_cast (hew ▸ heu)
  omega

private theorem small_repeated (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (ha4 : a≤4) (hb : 0<b) (hc : 0<c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b c)) := by
  have hk (i : Fin 4) : 0<pairExponents a b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  have ha1 : 1≤a := by omega
  interval_cases a
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 0 (by simp [pairExponents])).choose_spec.2.2.2
  · simpa only [Equiv.refl_apply] using FourPrimeIdealIntersectionObstructions.two_equal_obstruction p hp hinj (Equiv.refl _) b c hb hc
  · simpa only [Equiv.refl_apply] using (FourPrimeIdealIntersectionObstructions.three_equal_obstruction p hp hinj (Equiv.refl _) b c hb hc).1
  · exact PairFourSpectrum.actual_nonintegral p hp hinj b c hb hc

/-- Every positive tail gap three, with all small cases and all large a,b. -/
theorem actual_gap_three (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+3))) := by
  by_cases ha4 : a≤4
  · exact small_repeated p hp hinj a b (b+3) ha ha4 hb (by omega)
  have ha5 : 5≤a := by omega
  by_cases hb4 : b≤4
  · exact small_actual p hp hinj a b 3 ha5 hb hb4 (Or.inl rfl)
  have hb5 : 5≤b := by omega
  have hs : (2*a+1)*3^2≤4*a*b := by nlinarith [Nat.mul_le_mul_left a hb5]
  exact PairGapSpectrum.actual_weighted_gap p hp hinj a b 3 ha hb (by norm_num) hs

/-- Every positive tail gap four; the small b=4 case uses its own unit window. -/
theorem actual_gap_four (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+4))) := by
  by_cases ha4 : a≤4
  · exact small_repeated p hp hinj a b (b+4) ha ha4 hb (by omega)
  have ha5 : 5≤a := by omega
  by_cases hb4 : b≤4
  · exact small_actual p hp hinj a b 4 ha5 hb hb4 (Or.inr rfl)
  have hb5 : 5≤b := by omega
  have hs : (2*a+1)*4^2≤8*a*b := by nlinarith [Nat.mul_le_mul_left a hb5]
  exact PairGapSpectrum.actual_even_gap p hp hinj a b 4 ha hb (by norm_num) hs (by norm_num)

end D5.S3.Combinatorics.SpectralGraph.PairGapCompletion
