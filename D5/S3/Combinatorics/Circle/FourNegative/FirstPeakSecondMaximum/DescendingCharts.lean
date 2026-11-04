/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/DescendingCharts
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Descending charts for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingCertificates

/-! DescendingCharts for the paired physical source construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
open private D A B L M E delta eps width cap reverseV reverseR
  oldSeam newSeam oldNext newNext Gates first_gates reverse_grid
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic
open private
  cert_interior_separation
  cert_interior_remainder
  cert_interior_width
  cert_interior_capacity
  cert_boundary_eight_separation
  cert_boundary_eight_remainder
  cert_boundary_eight_width
  cert_boundary_eight_capacity
  cert_boundary_large_separation
  cert_boundary_large_lower
  cert_boundary_large_upper
  cert_boundary_large_width
  cert_boundary_large_capacity
  cert_corner_2_old_seam_0
  cert_corner_2_old_peak_slack_0
  cert_corner_2_new_seam_0
  cert_corner_2_new_peak_slack_0
  cert_corner_2_old_seam_1
  cert_corner_2_old_peak_slack_1
  cert_corner_2_new_seam_1
  cert_corner_2_new_peak_slack_1
  cert_corner_2_old_seam_2
  cert_corner_2_old_peak_slack_2
  cert_corner_2_new_seam_2
  cert_corner_2_new_peak_slack_2
  cert_corner_2_old_seam_3
  cert_corner_2_old_peak_slack_3
  cert_corner_2_new_seam_3
  cert_corner_2_new_peak_slack_3
  cert_corner_4_old_seam_0
  cert_corner_4_old_peak_slack_0
  cert_corner_4_new_seam_0
  cert_corner_4_new_peak_slack_0
  cert_corner_4_old_seam_1
  cert_corner_4_old_peak_slack_1
  cert_corner_4_new_seam_1
  cert_corner_4_new_peak_slack_1
  cert_corner_4_old_seam_2
  cert_corner_4_old_peak_slack_2
  cert_corner_4_new_seam_2
  cert_corner_4_new_peak_slack_2
  cert_corner_4_old_seam_3
  cert_corner_4_old_peak_slack_3
  cert_corner_4_new_seam_3
  cert_corner_4_new_peak_slack_3
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingCertificates

private theorem positive_data (n y z t : ℤ)
    (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : y ≤ t) :
    0<A n y z t ∧ 0<M y z t ∧ z ≤ L n z t ∧ z + 1 ≤ D y z ∧ 
    0<E n y z ∧ 0<delta n y z t ∧ 1 ≤ 2 * M y z t-D y z := by
  have hn0 : 0<n := by omega
  have hz0 : 0<z := by omega
  have hy0 : 0<y := by omega
  have ht0 : 0<t := by omega
  have hD : z + 1 ≤ D y z := by
    dsimp [D]
    have h : z ≤ y * z := by
      simpa using mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ y by omega) hz0.le
    omega
  have hD0 : 0<D y z := by omega
  have hdelta : delta n y z t=n * (y * (t-z) + (t-y)-1) + 1 := by
    dsimp [delta,A,M,D]; ring
  have hinner : 0 ≤ y * (t-z) + (t-y)-1 := by
    have htz : 4 ≤ t-z := by omega
    have hm := mul_le_mul_of_nonneg_left htz hy0.le
    nlinarith only [hm,hy0,ht]
  refine ⟨?_,?_,?_,hD,?_,?_,?_⟩
  · dsimp [A]; positivity
  · dsimp [M]; positivity
  · have hzt := mul_nonneg hz0.le ht0.le
    have hnt := mul_nonneg (mul_nonneg hn0.le hz0.le) (sq_nonneg t)
    dsimp [L]
    nlinarith only [hzt,hnt]
  · dsimp [E]; positivity
  · rw [hdelta]; positivity
  · dsimp [M]; nlinarith [mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ y * z by positivity)]

set_option maxHeartbeats 2000000 in
private theorem grid_allocate (n y z t R : ℤ)
    (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : y ≤ t)
    (hR : 1 ≤ R) (hRn : R ≤ n)
    (hsep : 0<B n y t-2 * L n z t)
    (hrem : 0 ≤ L n z t-R * M y z t)
    (hw : 0 ≤ L n z t-E n y z-2 * width n y z t R)
    (hcap : 0<t * A n y z t-2 * B n y t) :
    let r := reverseR n y z t R
    let v := reverseV n y z t R
    1 ≤ r ∧ r ≤ n ∧ 0 ≤ v ∧ 2 * v<t ∧ Gates false n y z t r v := by
  obtain ⟨hA,hM,hL,hD,hE,hdelta,hMn⟩ := positive_data n y z t hn hz hy ht
  have hmul : R * M y z t ≤ n * M y z t := mul_le_mul_of_nonneg_right hRn hM.le
  have heps : 0<A n y z t-R * M y z t := by dsimp [delta] at hdelta; omega
  have grid := reverse_grid (A n y z t) (B n y t) (L n z t) (M y z t)
    (E n y z) z t R hA hM hR heps (by omega) (by omega) hL hE.le
    (by dsimp [width,eps] at hw; nlinarith only [hw]) (by omega)
  change 0 ≤ reverseV n y z t R ∧ 1 ≤ reverseR n y z t R ∧ 
    reverseR n y z t R ≤ R ∧ 
    0 ≤ cap n y z t-((reverseV n y z t R + 1) * A n y z t-reverseR n y z t R * M y z t) ∧ 
    cap n y z t-((reverseV n y z t R + 1) * A n y z t-reverseR n y z t R * M y z t)<width n y z t R ∧ 
    B n y t-L n z t<(reverseV n y z t R + 1) * A n y z t-reverseR n y z t R * M y z t ∧ 
    (reverseV n y z t R + 1) * A n y z t-reverseR n y z t R * M y z t ≤ cap n y z t ∧ 
    2 * reverseV n y z t R<t ∧ 
    4 * cap n y z t ≤ 4 * B n y t-2 * L n z t + z-2 * E n y z-2 at grid
  obtain ⟨hv,hr,hrR,hgap0,hgap1,hH,hHC,hvCap,hC⟩ := grid
  let r := reverseR n y z t R
  let v := reverseV n y z t R
  have hrn : r ≤ n := le_trans hrR hRn
  have hrM : 0 ≤ r * M y z t := mul_nonneg (by omega) hM.le
  have hrD : z + 1 ≤ r * D y z := by
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ D y z by omega)
    nlinarith only [h,hD]
  have hrE : r * D y z ≤ E n y z := by
    dsimp [E]; exact mul_le_mul_of_nonneg_right hrn (by omega)
  have hs1 : 0 ≤ L n z t-B n y t + (v + 1) * A n y z t-r * M y z t := by
    dsimp [r,v] at * ; omega
  have hs2 : 0 ≤ L n z t-r * M y z t := by
    have h := mul_le_mul_of_nonneg_right hrR hM.le
    dsimp [r] at * ; omega
  have hk1 : 0 ≤ 2 * L n z t-z-1-(2 * B n y t-1) + 2 * (v + 1) * A n y z t-r * (2 * M y z t-D y z) := by
    nlinarith only [hs1,hrD]
  have hk2 : 0 ≤ 2 * L n z t-z-1-r * (2 * M y z t-D y z) := by
    nlinarith only [hs2,hrD]
  have hp1 : 2 * (2 * L n z t-z-1-(2 * B n y t-1) + 2 * (v + 1) * A n y z t-r * (2 * M y z t-D y z)) ≤ 2 * L n z t-z-2 := by
    dsimp [r,v] at * ; nlinarith only [hHC,hC,hrE]
  have hp2 : 2 * (2 * L n z t-z-1-r * (2 * M y z t-D y z)) ≤ 2 * B n y t-2 := by
    have h := mul_nonneg (show 0 ≤ r by omega) (show 0 ≤ 2 * M y z t-D y z by omega)
    nlinarith only [h,hsep,hz]
  have first := first_gates n y z t hn hz hy ht
  refine ⟨hr,hrn,hv,hvCap,?_⟩
  intro j
  fin_cases j
  · dsimp [oldSeam,newSeam,oldNext,newNext]
    dsimp [delta,E] at first
    refine ⟨⟨first.1,first.2.1⟩,⟨?_,?_⟩⟩
    all_goals nlinarith only [first.2.2.1,first.2.2.2]
  · dsimp [oldSeam,newSeam,oldNext,newNext]
    refine ⟨⟨hs1,?_⟩,⟨hk1,by dsimp [r,v] at hp1; omega⟩⟩
    nlinarith only [hp1,hrD,hz]
  · dsimp [oldSeam,newSeam,oldNext,newNext]
    exact ⟨⟨hs2,by nlinarith only [hrM,hsep]⟩,⟨hk2,by dsimp [r] at hp2; omega⟩⟩
  · dsimp [oldSeam,newSeam,oldNext,newNext]
    exact ⟨⟨le_rfl,by omega⟩,⟨le_rfl,by omega⟩⟩

private theorem interior (n y z t : ℤ)
    (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : 2 * y ≤ t) :
    1 ≤ reverseR n y z t n ∧ reverseR n y z t n ≤ n ∧ 
    0 ≤ reverseV n y z t n ∧ 2 * reverseV n y z t n<t ∧ 
    Gates false n y z t (reverseR n y z t n) (reverseV n y z t n) := by
  exact grid_allocate n y z t n hn hz hy (by omega) (by omega) le_rfl
    (cert_interior_separation n y z t hn hz hy ht)
    (cert_interior_remainder n y z t hn hz hy ht).le
    (cert_interior_width n y z t hn hz hy ht).le
    (cert_interior_capacity n y z t hn hz hy ht)

private theorem eight (y z : ℤ) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    1 ≤ reverseR 8 y z y 7 ∧ reverseR 8 y z y 7 ≤ 8 ∧ 
    0 ≤ reverseV 8 y z y 7 ∧ 2 * reverseV 8 y z y 7<y ∧ 
    Gates false 8 y z y (reverseR 8 y z y 7) (reverseV 8 y z y 7) := by
  exact grid_allocate 8 y z y 7 (by norm_num) hz hy le_rfl (by norm_num) (by norm_num)
    (cert_boundary_eight_separation y z hz hy)
    (cert_boundary_eight_remainder y z hz hy).le
    (cert_boundary_eight_width y z hz hy).le
    (cert_boundary_eight_capacity y z hz hy)

/- The large boundary uses floor(L/M), NEVER the rejected n-1. -/
private theorem large (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    let R := L n z y/M y z y
    1 ≤ reverseR n y z y R ∧ reverseR n y z y R ≤ n ∧ 
    0 ≤ reverseV n y z y R ∧ 2 * reverseV n y z y R<y ∧ 
    Gates false n y z y (reverseR n y z y R) (reverseV n y z y R) := by
  obtain ⟨hA,hM,hL,hD,hE,hd,hMn⟩ := positive_data n y z y (by omega) hz hy le_rfl
  have hlower := cert_boundary_large_lower n y z hn hz hy
  have hupper := cert_boundary_large_upper n y z hn hz hy
  have hw := cert_boundary_large_width n y z hn hz hy
  let R := L n z y/M y z y
  have e0 := Int.emod_nonneg (L n z y) (ne_of_gt hM)
  have e1 := Int.emod_lt_of_pos (L n z y) hM
  have eqn := Int.emod_add_mul_ediv (L n z y) (M y z y)
  change L n z y%M y z y + M y z y * R=L n z y at eqn
  have hR : 1 ≤ R := by
    by_contra hnot
    have hR0 : R ≤ 0 := by omega
    have hm := mul_nonpos_of_nonpos_of_nonneg hR0 hM.le
    nlinarith only [hm,eqn,e1,hlower]
  have hRn : R<n := by
    by_contra hnot
    have hnR : n ≤ R := by omega
    have hm := mul_le_mul_of_nonneg_right hnR hM.le
    nlinarith only [hm,eqn,e0,hupper]
  have hrem : 0 ≤ L n z y-R * M y z y := by nlinarith
  have hwidth : 0 ≤ L n z y-E n y z-2 * width n y z y R := by
    dsimp [width,eps]; nlinarith only [eqn,e1,hw]
  exact grid_allocate n y z y R (by omega) hz hy le_rfl hR (by omega)
    (cert_boundary_large_separation n y z hn hz hy) hrem hwidth
    (cert_boundary_large_capacity n y z hn hz hy)

private theorem corner_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    Gates true 2 (2 * z * u) z (2 * z * u) (2-1) u := by
  intro j
  fin_cases j
  · have os := cert_corner_2_old_seam_0 z u hz hu
    have op := cert_corner_2_old_peak_slack_0 z u hz hu
    have ns := cert_corner_2_new_seam_0 z u hz hu
    have np := cert_corner_2_new_peak_slack_0 z u hz hu
    change (0 ≤ oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0 ∧
      2 * oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0 ≤ oldNext true 2 (2 * z * u) z (2 * z * u) 0 - 1) ∧
      (0 ≤ newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0 ∧
      2 * newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0 ≤ newNext true 2 (2 * z * u) z (2 * z * u) 0 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_2_old_seam_1 z u hz hu
    have op := cert_corner_2_old_peak_slack_1 z u hz hu
    have ns := cert_corner_2_new_seam_1 z u hz hu
    have np := cert_corner_2_new_peak_slack_1 z u hz hu
    change (0 ≤ oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1 ∧
      2 * oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1 ≤ oldNext true 2 (2 * z * u) z (2 * z * u) 1 - 1) ∧
      (0 ≤ newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1 ∧
      2 * newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1 ≤ newNext true 2 (2 * z * u) z (2 * z * u) 1 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_2_old_seam_2 z u hz hu
    have op := cert_corner_2_old_peak_slack_2 z u hz hu
    have ns := cert_corner_2_new_seam_2 z u hz hu
    have np := cert_corner_2_new_peak_slack_2 z u hz hu
    change (0 ≤ oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2 ∧
      2 * oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2 ≤ oldNext true 2 (2 * z * u) z (2 * z * u) 2 - 1) ∧
      (0 ≤ newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2 ∧
      2 * newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2 ≤ newNext true 2 (2 * z * u) z (2 * z * u) 2 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_2_old_seam_3 z u hz hu
    have op := cert_corner_2_old_peak_slack_3 z u hz hu
    have ns := cert_corner_2_new_seam_3 z u hz hu
    have np := cert_corner_2_new_peak_slack_3 z u hz hu
    change (0 ≤ oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3 ∧
      2 * oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3 ≤ oldNext true 2 (2 * z * u) z (2 * z * u) 3 - 1) ∧
      (0 ≤ newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3 ∧
      2 * newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3 ≤ newNext true 2 (2 * z * u) z (2 * z * u) 3 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

private theorem corner_4 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    Gates true 4 (2 * z * u) z (2 * z * u) (4-1) u := by
  intro j
  fin_cases j
  · have os := cert_corner_4_old_seam_0 z u hz hu
    have op := cert_corner_4_old_peak_slack_0 z u hz hu
    have ns := cert_corner_4_new_seam_0 z u hz hu
    have np := cert_corner_4_new_peak_slack_0 z u hz hu
    change (0 ≤ oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0 ∧
      2 * oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0 ≤ oldNext true 4 (2 * z * u) z (2 * z * u) 0 - 1) ∧
      (0 ≤ newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0 ∧
      2 * newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0 ≤ newNext true 4 (2 * z * u) z (2 * z * u) 0 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_4_old_seam_1 z u hz hu
    have op := cert_corner_4_old_peak_slack_1 z u hz hu
    have ns := cert_corner_4_new_seam_1 z u hz hu
    have np := cert_corner_4_new_peak_slack_1 z u hz hu
    change (0 ≤ oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1 ∧
      2 * oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1 ≤ oldNext true 4 (2 * z * u) z (2 * z * u) 1 - 1) ∧
      (0 ≤ newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1 ∧
      2 * newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1 ≤ newNext true 4 (2 * z * u) z (2 * z * u) 1 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_4_old_seam_2 z u hz hu
    have op := cert_corner_4_old_peak_slack_2 z u hz hu
    have ns := cert_corner_4_new_seam_2 z u hz hu
    have np := cert_corner_4_new_peak_slack_2 z u hz hu
    change (0 ≤ oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2 ∧
      2 * oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2 ≤ oldNext true 4 (2 * z * u) z (2 * z * u) 2 - 1) ∧
      (0 ≤ newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2 ∧
      2 * newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2 ≤ newNext true 4 (2 * z * u) z (2 * z * u) 2 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · have os := cert_corner_4_old_seam_3 z u hz hu
    have op := cert_corner_4_old_peak_slack_3 z u hz hu
    have ns := cert_corner_4_new_seam_3 z u hz hu
    have np := cert_corner_4_new_peak_slack_3 z u hz hu
    change (0 ≤ oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3 ∧
      2 * oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3 ≤ oldNext true 4 (2 * z * u) z (2 * z * u) 3 - 1) ∧
      (0 ≤ newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3 ∧
      2 * newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3 ≤ newNext true 4 (2 * z * u) z (2 * z * u) 3 - 1)
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

/- The ONLY parameter assumptions; dyadic exhaustion includes both unbounded corners. -/
private theorem allocate (a b c d : ℕ)
    (hc : 2 ≤ c) (hcb : c<b) (hbd : b ≤ d) (hda : d<a) :
    ∃ (corner : Bool) (r v : ℤ),
      1 ≤ r ∧ r ≤ (2:ℤ) ^ (a-d) ∧ 0 ≤ v ∧ 2 * v<(2:ℤ) ^ d ∧ 
      Gates corner (2 ^ (a-d)) (2 ^ b) (2 ^ c) (2 ^ d) r v ∧ 
      (corner=true → d=b ∧ ((2:ℤ) ^ (a-d)=2 ∨ (2:ℤ) ^ (a-d)=4) ∧ 
        r=(2:ℤ) ^ (a-d)-1 ∧ v=(2:ℤ) ^ (b-c-1)) := by
  let n : ℤ := 2 ^ (a-d)
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let t : ℤ := 2 ^ d
  have hn : 2 ≤ n := by
    dsimp [n]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 1 ≤ a-d by omega)
  have hz : 4 ≤ z := by
    dsimp [z]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hc
  have hy : 2 * z ≤ y := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show c + 1 ≤ b by omega)
    simpa [z,y,pow_succ,mul_comm] using hp
  by_cases hinterior : b<d
  · have ht : 2 * y ≤ t := by
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show b + 1 ≤ d by omega)
      simpa [y,t,pow_succ,mul_comm] using hp
    obtain ⟨hr,hrn,hv,hvc,hg⟩ := interior n y z t hn hz hy ht
    exact ⟨false,reverseR n y z t n,reverseV n y z t n,hr,hrn,hv,hvc,hg,by simp⟩
  · have hdb : d=b := by omega
    subst d
    change ∃ corner r v, 1 ≤ r ∧ r ≤ n ∧ 0 ≤ v ∧ 2 * v<y ∧ 
      Gates corner n y z y r v ∧ 
      (corner=true → b=b ∧ (n=2 ∨ n=4) ∧ r=n-1 ∧ v=(2:ℤ) ^ (b-c-1))
    by_cases he8 : a-b=3
    · have en : n=8 := by norm_num [n,he8]
      obtain ⟨hr,hrn,hv,hvc,hg⟩ := eight y z hz hy
      rw [en]
      exact ⟨false,reverseR 8 y z y 7,reverseV 8 y z y 7,hr,hrn,hv,hvc,hg,by simp⟩
    · by_cases helarge : 4 ≤ a-b
      · have hn16 : 16 ≤ n := by
          dsimp [n]
          simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) helarge
        obtain ⟨hr,hrn,hv,hvc,hg⟩ := large n y z hn16 hz hy
        exact ⟨false,reverseR n y z y (L n z y/M y z y),
          reverseV n y z y (L n z y/M y z y),hr,hrn,hv,hvc,hg,by simp⟩
      · have he : a-b=1 ∨ a-b=2 := by omega
        let u : ℤ := 2 ^ (b-c-1)
        have hu : 1 ≤ u := one_le_pow₀ (by norm_num)
        have hyu : y=2 * z * u := by
          dsimp [y,z,u]
          conv_lhs => rw [show b=(c + 1) + (b-c-1) by omega,pow_add,pow_succ]
          ring
        have hucap : 2 * u<y := by
          rw [hyu]
          have hm := mul_lt_mul_of_pos_right (show (1:ℤ)<z by omega) (show 0<u by omega)
          nlinarith only [hm]
        have hcases : n=2 ∨ n=4 := by
          rcases he with he|he <;> norm_num [n,he]
        have hg : Gates true n y z y (n-1) u := by
          rw [hyu]
          rcases hcases with en|en
          · rw [en]; exact corner_2 z u hz hu
          · rw [en]; exact corner_4 z u hz hu
        exact ⟨true,n-1,u,by omega,by omega,by omega,hucap,hg,
          by intro _; exact ⟨rfl,hcases,rfl,rfl⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
