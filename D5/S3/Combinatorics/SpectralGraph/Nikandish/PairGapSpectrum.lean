/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairGapSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairGapSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full high-root unit and half-unit intervals on the actual repeated-pair ideal graph. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairGapSigns
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift

/-! Sources: four-prime-single-pair-small-gap, four-prime-single-pair-midpoint,
four-prime-weighted-midpoint and four-prime-even-midpoint, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The original exact gap/size/
parity hypotheses, full positive a,b domain and weighted equality faces
are retained. These are actual eigenvalues of the full tensor and actual
ideal graph. No general smallest-root or uniqueness assertion is made. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairGapSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions

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

private theorem half_noninteger (a b r : ℕ) (e : ℝ)
    (hl : (a:ℝ)+b+((r:ℝ)+1)/2<e)
    (hu : e<(a:ℝ)+b+((r:ℝ)+2)/2) : ¬∃ z : ℤ, e=z := by
  rintro ⟨z,hz⟩
  have h1 : (r:ℝ)+1<2*((z:ℝ)-a-b) := by rw [hz] at hl; linarith
  have h2 : 2*((z:ℝ)-a-b)<(r:ℝ)+2 := by rw [hz] at hu; linarith
  have hi1 : (r:ℤ)+1<2*(z-a-b) := by exact_mod_cast h1
  have hi2 : 2*(z-a-b)<(r:ℤ)+2 := by exact_mod_cast h2
  omega

private theorem actual_of_noninteger (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (e : ℝ) (hne : ¬∃ z : ℤ, e=z) (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0)
    (hE : tensorK (a:ℝ) (b:ℝ) (c:ℝ)*ᵥh=e • h) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b c)) := by
  have he:=actual_paired_eigenvalue p hp hinj a b c ha hb hc e h hh hE
  intro H
  obtain ⟨z,hz⟩:=H _ he
  apply hne
  refine ⟨((((a+1)^2*(b+1)*(c+1)-2:ℕ):ℤ)+1-z),?_⟩
  push_cast
  linarith

/-- The full small-gap unit interval, with no relative-size condition on a,b. -/
theorem small_gap_eigenpair (a b r : ℕ) (ha : 0<a) (hb : 0<b) (hr : r=1 ∨ r=2) :
    ∃ e : ℝ, (a:ℝ)+b+1<e ∧ e<(a:ℝ)+b+2 ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧
        tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)*ᵥh=e • h := by
  have haR : (0:ℝ)<a := by positivity
  have hbR : (0:ℝ)<b := by positivity
  have hr0 : (0:ℝ)<r := by rcases hr with rfl | rfl <;> norm_num
  have hl:=PairGapSigns.unequal_lower_negative (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)
    haR (by exact_mod_cast (show 1≤b by omega)) (by push_cast; linarith)
  have hu : 0<(tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)-((a:ℝ)+b+2) • 1).det := by
    rcases hr with rfl | rfl
    · have he : (tensorK (a:ℝ) (b:ℝ) ((b+1:ℕ):ℝ)-((a:ℝ)+b+2) • 1).det =
          (a:ℝ)*(b+1)*((a:ℝ)+b+2)*((a:ℝ)*b^2+(a:ℝ)*b+(b:ℝ)^2+a+b) := by
        rw [PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar]
        push_cast
        ring
      rw [he]
      positivity
    · simpa only [Nat.cast_add,Nat.cast_ofNat] using PairGapSigns.gap_two_positive (a:ℝ) (b:ℝ) haR hbR
  exact between (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ) _ _ (by linarith) hl hu

/-- Full midpoint-size half-unit interval including b=r squared. -/
theorem square_gap_eigenpair (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 2≤r) (hs : r^2≤b) :
    ∃ e : ℝ, (a:ℝ)+b+((r:ℝ)+1)/2<e ∧ e<(a:ℝ)+b+((r:ℝ)+2)/2 ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧
        tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)*ᵥh=e • h := by
  apply between _ _ _ _ _ (by linarith)
  · simpa only [Nat.cast_add] using PairGapSigns.square_lower_negative (a:ℝ) (b:ℝ) (r:ℝ)
      (by exact_mod_cast (show 1≤a by omega)) (by exact_mod_cast hr) (by exact_mod_cast hs)
  · simpa only [Nat.cast_add] using PairGapSigns.midpoint_positive (a:ℝ) (b:ℝ) (r:ℝ)
      (by positivity) (by positivity) (by exact_mod_cast (show 0<r by omega))

/-- Full weighted half-unit interval, including equality in 4ab. -/
theorem weighted_gap_eigenpair (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 3≤r) (hs : (2*a+1)*r^2≤4*a*b) :
    ∃ e : ℝ, (a:ℝ)+b+((r:ℝ)+1)/2<e ∧ e<(a:ℝ)+b+((r:ℝ)+2)/2 ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧
        tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)*ᵥh=e • h := by
  apply between _ _ _ _ _ (by linarith)
  · simpa only [Nat.cast_add] using PairGapSigns.weighted_lower_negative (a:ℝ) (b:ℝ) (r:ℝ)
      (by positivity) (by exact_mod_cast hr) (by exact_mod_cast hs)
  · simpa only [Nat.cast_add] using PairGapSigns.midpoint_positive (a:ℝ) (b:ℝ) (r:ℝ)
      (by positivity) (by positivity) (by exact_mod_cast (show 0<r by omega))

/-- The full even-gap sign window over all natural parameters. Its later
nonintegrality consumer requires even r and includes equality in 8ab. -/
theorem even_gap_eigenpair (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 2≤r) (hs : (2*a+1)*r^2≤8*a*b) :
    ∃ e : ℝ, (a:ℝ)+b+(r:ℝ)/2<e ∧ e<(a:ℝ)+b+(r:ℝ)/2+1 ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧
        tensorK (a:ℝ) (b:ℝ) ((b+r:ℕ):ℝ)*ᵥh=e • h := by
  apply between _ _ _ _ _ (by linarith)
  · simpa only [Nat.cast_add] using PairGapSigns.even_lower_negative (a:ℝ) (b:ℝ) (r:ℝ)
      (by positivity) (by exact_mod_cast hr) (by exact_mod_cast hs)
  · have he : (a:ℝ)+b+(r:ℝ)/2+1=(a:ℝ)+b+((r:ℝ)+2)/2 := by ring
    rw [he]
    simpa only [Nat.cast_add] using PairGapSigns.midpoint_positive (a:ℝ) (b:ℝ) (r:ℝ)
      (by positivity) (by positivity) (by exact_mod_cast (show 0<r by omega))

/-- Actual graph nonintegrality for both entire positive small-gap families. -/
theorem actual_small_gap (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b r : ℕ) (ha : 0<a) (hb : 0<b) (hr : r=1 ∨ r=2) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+r))) := by
  obtain ⟨e,hl,hu,h,hh,hE⟩:=small_gap_eigenpair a b r ha hb hr
  apply actual_of_noninteger p hp hinj a b (b+r) ha hb (by omega) e _ h hh hE
  rintro ⟨z,hz⟩
  have h1 : (a:ℤ)+b+1<z := by exact_mod_cast (hz ▸ hl)
  have h2 : z<(a:ℤ)+b+2 := by exact_mod_cast (hz ▸ hu)
  omega

/-- Actual graph nonintegrality for every original square-size half-unit case. -/
theorem actual_square_gap (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 2≤r) (hs : r^2≤b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+r))) := by
  obtain ⟨e,hl,hu,h,hh,hE⟩:=square_gap_eigenpair a b r ha hb hr hs
  exact actual_of_noninteger p hp hinj a b (b+r) ha hb (by omega) e
    (half_noninteger a b r e hl hu) h hh hE

/-- Actual graph nonintegrality under the complete weighted half-unit condition. -/
theorem actual_weighted_gap (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 3≤r) (hs : (2*a+1)*r^2≤4*a*b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+r))) := by
  obtain ⟨e,hl,hu,h,hh,hE⟩:=weighted_gap_eigenpair a b r ha hb hr hs
  exact actual_of_noninteger p hp hinj a b (b+r) ha hb (by omega) e
    (half_noninteger a b r e hl hu) h hh hE

/-- Actual graph nonintegrality for the complete even-gap condition. The
parity hypothesis is essential to this unit-interval argument. -/
theorem actual_even_gap (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b r : ℕ) (ha : 0<a) (hb : 0<b)
    (hr : 2≤r) (hs : (2*a+1)*r^2≤8*a*b) (heven : Even r) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b (b+r))) := by
  obtain ⟨e,hl,hu,h,hh,hE⟩:=even_gap_eigenpair a b r ha hb hr hs
  apply actual_of_noninteger p hp hinj a b (b+r) ha hb (by omega) e _ h hh hE
  rintro ⟨z,hz⟩
  obtain ⟨k,hk⟩:=heven
  have hrR : (r:ℝ)/2=k := by rw [hk]; push_cast; ring
  rw [hrR] at hl hu
  have h1 : (a:ℤ)+b+k<z := by exact_mod_cast (hz ▸ hl)
  have h2 : z<(a:ℤ)+b+k+1 := by exact_mod_cast (hz ▸ hu)
  omega

end D5.S3.Combinatorics.SpectralGraph.PairGapSpectrum
