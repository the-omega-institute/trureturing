/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/SpectralInverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/SpectralInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
physical_spectral_inverse:
  proof_shape: content
  escape_witness: jacobi_green_inverse: jacobiMatrix m a e * greenMatrix m a e L R = 1 under the two pivot recurrences and endpoint conditions. The actual physical pivots satisfy these conditions in local physicalTG, which is used to identify the spectral and Green inverses.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion
open D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality

lemma physical_spectral_inverse (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l) :
    physicalSpectralInverse n j l=physicalG n j l := by
  have channel_last (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) (hjl : j ≤ l) :
      channelLabel n j l (channelWidth n j l) = n+2*j := by
    clear * - n j l hj hl hjl
    unfold channelLabel channelBase channelWidth
    have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
    omega
  have channel_admissible (n j l t u : ℕ) (hj : j ≤ n)
      (hl : l ≤ n) (hjl : j ≤ l) (ht : t ≤ channelWidth n j l)
      (hu : u ≤ channelWidth n j l) :
      admissible n n (2*(l-j+u)) (2*j) (2*l) (channelLabel n j l t) := by
    clear * - n j l t u hj hl hjl ht hu
    have hm : max n (j+l)+min n (j+l)=n+(j+l) := max_add_min _ _
    unfold channelWidth at ht hu
    unfold channelLabel channelBase admissible triangle
    omega
  have physicalTU (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
      physicalT n j l*physicalU n j l=physicalU n j l*
        diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)) := by
    clear * - n j l hj hl hjl channel_admissible channel_last
    have normalizedSixJ_zero (a b u c d y : ℕ) (h : ¬admissible a b u c d y) :
        normalizedSixJ a b u c d y=0 := by
      clear * - a b u c d y h
      simp only [normalizedSixJ,sixJ,if_neg h,mul_zero]
    have channel_below_missing (n j l u : ℕ) (hjl : j≤l)
        (hy : 2≤channelBase n j l) :
        normalizedSixJ n n u (2*j) (2*l) (channelBase n j l-2)=0 := by
      clear * - n j l u hjl hy normalizedSixJ_zero
      apply normalizedSixJ_zero
      intro ha
      by_cases hn : j+l≤n
      · have hb : channelBase n j l=n-2*j := by unfold channelBase; omega
        have h := ha.2.2.1.2.1
        rw [hb] at hy h
        omega
      · have hb : channelBase n j l=2*l-n := by unfold channelBase; omega
        have h := ha.2.1.2.1
        rw [hb] at hy h
        omega
    have channel_above_missing (n j l u : ℕ) :
        normalizedSixJ n n u (2*j) (2*l) (n+2*j+2)=0 := by
      clear * - n j l u normalizedSixJ_zero
      apply normalizedSixJ_zero
      intro ha
      have h := ha.2.2.1.2.2.1
      omega
    have physicalU_finite (n j l : ℕ) :
        physicalU n j l=finiteSixJMatrix n n (2*j) (2*l) (channelBase n j l)
          (channelWidth n j l) (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val)) := by
      clear * - n j l
      exact rfl
    have he : channelBase n j l+2*channelWidth n j l+2=n+2*j+2 := by
      have h := channel_last n j l hj hl hjl
      unfold channelLabel at h
      omega
    have h := finiteSixJ_action n n (2*j) (2*l) (channelBase n j l) (channelWidth n j l)
      (fun i : Fin (channelWidth n j l+1) => 2*(l-j+i.val))
      (fun k i => channel_admissible n j l k.val i.val hj hl hjl
        (by omega) (by omega))
      (fun i hb => channel_below_missing n j l (2*(l-j+i.val)) hjl hb)
      (fun i => by rw [he]; exact channel_above_missing n j l (2*(l-j+i.val)))
    have hc : (fun i : Fin (channelWidth n j l+1) =>
        ((((2*(l-j+i.val) : ℕ) : ℚ)/2*(((2*(l-j+i.val) : ℕ) : ℚ)/2+1) : ℚ) : ℝ)) =
        fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val) := by
      funext i
      unfold casimir
      push_cast
      ring
    rw [hc,←physicalU_finite] at h
    exact h
  have physicalTG (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l) :
      physicalT n j l*physicalG n j l=1 := by
    clear * - n j l hj hl hjl channel_admissible channel_last
    have fourSpinDenominator_ne (y : ℚ) (hy : y ≠ 0)
        (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) : fourSpinDenominator y ≠ 0 := by
      clear * - y hy hy1 hy2
      unfold fourSpinDenominator
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hy) hy1) hy2
    have rawDiagonal_scaled (a b c d u y : ℚ)
        (hy : y ≠ 0) (hy1 : y+1 ≠ 0) :
        fourSpinDenominator y*(rawDiagonal a b c d y-u*(u+1)) =
          (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-
            (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))) := by
      clear * - a b c d u y hy hy1
      let v := (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))
      let w := a*(a+1)+b*(b+1)-u*(u+1)
      change fourSpinDenominator y*(a*(a+1)+b*(b+1)-v/(2*y*(y+1))-u*(u+1)) =
        (2*y+1)*(2*y*(y+1)*w-v)
      calc
        _ = (2*y+1)*(2*y*(y+1)*w-(2*y*(y+1))*(v/(2*y*(y+1)))) := by
          unfold fourSpinDenominator
          change _ = (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-_)
          ring
        _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hy) hy1)]
    have pivotLeft_scaled (s j l k : ℚ) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
        jacobiDenominator k*pivotLeft s j l k = k*pivotLeftNumerator s j l k := by
      clear * - s j l k hk1 hk2
      unfold jacobiDenominator pivotLeft
      calc
        _ = k*((2*(k+1)*(2*k+1))*(pivotLeftNumerator s j l k/(2*(k+1)*(2*k+1)))) := by ring
        _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk1) hk2)]
    have pivotRight_scaled (s j l k : ℚ) (hk : k ≠ 0) (hk2 : 2*k+1 ≠ 0) :
        jacobiDenominator k*pivotRight s j l k = (k+1)*pivotRightNumerator s j l k := by
      clear * - s j l k hk hk2
      unfold jacobiDenominator pivotRight
      calc
        _ = (k+1)*((2*k*(2*k+1))*(pivotRightNumerator s j l k/(2*k*(2*k+1)))) := by ring
        _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk) hk2)]
    have pivot_left_residual (s j l k : ℚ)
        (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
        rawDiagonal s s j l k-pivotLeft s j l k =
          (k-s+j)*(s+j+1-k)*(k+s-l)*(s+l+k+1)/(2*k*(2*k+1)) := by
      clear * - s j l k hk hk1 hk2 fourSpinDenominator_ne pivotLeft_scaled rawDiagonal_scaled
      have hD : jacobiDenominator k ≠ 0 := fourSpinDenominator_ne k hk hk1 hk2
      have ha := rawDiagonal_scaled s s j l 0 k hk hk1
      simp only [zero_mul, zero_add, sub_zero] at ha
      have hA : jacobiDenominator k*rawDiagonal s s j l k =
          (2*k+1)*(4*k*(k+1)*spinCasimir s-
            (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) := by
        simpa only [jacobiDenominator, fourSpinDenominator, spinCasimir, mul_comm, mul_left_comm,
          mul_assoc, ← two_mul, mul_add, show (2 : ℚ)*2 = 4 by ring] using ha
      apply mul_left_cancel₀ hD
      calc
        _ = (2*k+1)*(4*k*(k+1)*spinCasimir s-
            (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l))-
          k*pivotLeftNumerator s j l k := by
          rw [mul_sub, hA, pivotLeft_scaled s j l k hk1 hk2]
        _ = (k+1)*((k-s+j)*(s+j+1-k)*(k+s-l)*(s+l+k+1)) := by
          unfold pivotLeftNumerator spinCasimir
          ring
        _ = _ := by
          unfold jacobiDenominator
          conv_rhs => rw [show 2*k*(k+1)*(2*k+1)=(k+1)*(2*k*(2*k+1)) by ring, mul_assoc,
            mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk) hk2)]
    have pivot_right_residual (s j l k : ℚ)
        (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
        rawDiagonal s s j l k-pivotRight s j l k =
          (k-s+j+1)*(s+j-k)*(k+s-l+1)*(s+l+k+2)/(2*(k+1)*(2*k+1)) := by
      clear * - s j l k hk hk1 hk2 fourSpinDenominator_ne pivotRight_scaled rawDiagonal_scaled
      have hD : jacobiDenominator k ≠ 0 := fourSpinDenominator_ne k hk hk1 hk2
      have ha := rawDiagonal_scaled s s j l 0 k hk hk1
      simp only [zero_mul, zero_add, sub_zero] at ha
      have hA : jacobiDenominator k*rawDiagonal s s j l k =
          (2*k+1)*(4*k*(k+1)*spinCasimir s-
            (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) := by
        simpa only [jacobiDenominator, fourSpinDenominator, spinCasimir, mul_comm, mul_left_comm,
          mul_assoc, ← two_mul, mul_add, show (2 : ℚ)*2 = 4 by ring] using ha
      apply mul_left_cancel₀ hD
      calc
        _ = (2*k+1)*(4*k*(k+1)*spinCasimir s-
            (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l))-
          (k+1)*pivotRightNumerator s j l k := by
          rw [mul_sub, hA, pivotRight_scaled s j l k hk hk2]
        _ = k*((k-s+j+1)*(s+j-k)*(k+s-l+1)*(s+l+k+2)) := by
          unfold pivotRightNumerator spinCasimir
          ring
        _ = _ := by
          unfold jacobiDenominator
          conv_rhs => rw [show 2*k*(k+1)*(2*k+1)=k*(2*(k+1)*(2*k+1)) by ring, mul_assoc,
            mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hk1) hk2)]
    have channelSpin_succ (n j l t : ℕ) :
        channelSpin n j l (t+1)=channelSpin n j l t+1 := by
      clear * - n j l t
      unfold channelSpin channelLabel
      push_cast
      ring
    have channelSpin_bounds (n j l t : ℕ) (hj : j≤n) (hl : l≤n)
        (hjl : j<l) (ht : t≤channelWidth n j l) :
        0<channelSpin n j l t ∧ (n : ℚ)/2-j≤channelSpin n j l t ∧
          (l : ℚ)-(n : ℚ)/2≤channelSpin n j l t ∧ channelSpin n j l t≤(n : ℚ)/2+j := by
      clear * - n j l t hj hl hjl ht channel_admissible
      have ha := channel_admissible n j l t 0 hj hl hjl.le ht (by omega)
      have h1 : (n : ℚ)≤2*j+channelLabel n j l t := by exact_mod_cast ha.2.2.1.2.1
      have h2 : (2*l : ℚ)≤n+channelLabel n j l t := by exact_mod_cast ha.2.1.2.1
      have h3 : (channelLabel n j l t : ℚ)≤2*j+n := by exact_mod_cast ha.2.2.1.2.2.1
      have hjlq : (j : ℚ)<l := by exact_mod_cast hjl
      unfold channelSpin
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
    have physicalA_raw (n j l t : ℕ) (hp : 0<channelSpin n j l t) :
        physicalA n j l t=(rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l (channelSpin n j l t) : ℝ) := by
      clear * - n j l t hp
      have hz : channelLabel n j l t≠0 := by
        intro he
        simp [channelSpin,he] at hp
      simp only [physicalA,recurrenceDiagonalQ,if_neg hz,channelSpin]
      congr 1
      congr 1 <;> push_cast <;> ring
    have physicalE_sq (n j l t : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l)
        (ht : t<channelWidth n j l) :
        physicalE n j l t^2=(jacobiEdgeSq ((n : ℚ)/2) j l (channelSpin n j l (t+1)) : ℝ) := by
      clear * - n j l t hj hl hjl ht channelSpin_succ channel_admissible
      have raising_factors_positive (a b u c d y : ℕ)
          (had : admissible a b u c d y) (hp : admissible a b u c d (y+2)) :
          0 < raisingNumerator a b c d y ∧ 0 < raisingDenominator a b c d y := by
        clear * - a b u c d y had hp
        have deltaSq_raise_factors_positive (a b c : ℕ) (ht : triangle a b c)
            (hi : c+2 ≤ a+b) :
            (0 : ℚ) < ((c : ℚ)/2+1)^2-(((a : ℚ)-b)/2)^2 ∧
              (0 : ℚ) < (((a : ℚ)+b)/2+1)^2-((c : ℚ)/2+1)^2 := by
          clear * - a b c ht hi
          have triangle_difference_halves (a b c : ℕ) (ht : triangle a b c) :
              ((((a+b-c)/2 : ℕ) : ℚ) = ((a : ℚ)+b-c)/2) ∧
              ((((a+c-b)/2 : ℕ) : ℚ) = ((a : ℚ)+c-b)/2) ∧
              ((((b+c-a)/2 : ℕ) : ℚ) = ((b : ℚ)+c-a)/2) ∧
              ((((a+b+c)/2 : ℕ) : ℚ) = ((a : ℚ)+b+c)/2) := by
            clear * - a b c ht
            have half_cast (n : ℕ) (hn : n % 2 = 0) :
                (((n/2 : ℕ) : ℤ) : ℚ) = (n : ℚ)/2 := by
              clear * - n hn
              have he : 2*(n/2) = n := by omega
              have hq := congrArg (fun k : ℕ => (k : ℚ)) he
              simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
              simp only [Int.cast_natCast]
              apply (eq_div_iff (by positivity : (2 : ℚ) ≠ 0)).mpr
              simpa only [mul_comm] using hq
            rcases ht with ⟨ha,hb,hc,hp⟩
            have hp1 : (a+b-c)%2=0 := by omega
            have hp2 : (a+c-b)%2=0 := by omega
            have hp3 : (b+c-a)%2=0 := by omega
            have h1 := half_cast (a+b-c) hp1
            have h2 := half_cast (a+c-b) hp2
            have h3 := half_cast (b+c-a) hp3
            have h4 := half_cast (a+b+c) hp
            simp only [Int.cast_natCast,Nat.cast_sub hc,Nat.cast_sub hb,Nat.cast_sub ha,Nat.cast_add] at *
            exact ⟨h1,h2,h3,h4⟩
          rcases triangle_difference_halves a b c ht with ⟨h1,h2,h3,h4⟩
          have h1p : (0 : ℚ) < (((a+b-c)/2 : ℕ) : ℚ) := by
            exact_mod_cast (by omega : 0 < (a+b-c)/2)
          have h2p : (0 : ℚ) < (((a+c-b)/2 : ℕ) : ℚ)+1 := by positivity
          have h3p : (0 : ℚ) < (((b+c-a)/2 : ℕ) : ℚ)+1 := by positivity
          have h4p : (0 : ℚ) < (((a+b+c)/2 : ℕ) : ℚ)+2 := by positivity
          rw [h1] at h1p
          rw [h2] at h2p
          rw [h3] at h3p
          rw [h4] at h4p
          constructor
          · have h := mul_pos h2p h3p
            convert h using 1 <;> first | rfl | ring
          · have h := mul_pos h1p h4p
            convert h using 1 <;> first | rfl | ring
        have ha := deltaSq_raise_factors_positive a d y had.2.1 hp.2.1.2.2.1
        have hb := deltaSq_raise_factors_positive c b y had.2.2.1 hp.2.2.1.2.2.1
        constructor
        · unfold raisingNumerator
          have h := mul_pos ha.1 hb.1
          convert h using 1 <;> first | rfl | ring
        · unfold raisingDenominator
          have h := mul_pos ha.2 hb.2
          convert h using 1 <;> first | rfl | ring
      have normalizedUpper_sq (a b c d y : ℕ)
          (hpos : 0≤raisingNumerator a b c d y*raisingDenominator a b c d y) :
          normalizedUpper a b c d y^2 =
            (raisingNumerator a b c d y*raisingDenominator a b c d y : ℚ)/
              (((y : ℝ)+2)^2*((y : ℝ)+1)*((y : ℝ)+3)) := by
        clear * - a b c d y hpos
        unfold normalizedUpper recurrenceUpperCoefficient
        rw [div_pow,mul_pow,div_pow]
        rw [Real.sq_sqrt (by exact_mod_cast hpos),Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
        push_cast
        field_simp <;> ring
      have ha := channel_admissible n j l t 0 hj hl hjl (by omega) (by omega)
      have hb := channel_admissible n j l (t+1) 0 hj hl hjl (by omega) (by omega)
      have he : channelLabel n j l (t+1)=channelLabel n j l t+2 := by unfold channelLabel; omega
      rw [he] at hb
      have hp := raising_factors_positive n n (2*(l-j)) (2*j) (2*l) (channelLabel n j l t) ha hb
      unfold physicalE
      rw [normalizedUpper_sq _ _ _ _ _ (mul_pos hp.1 hp.2).le,channelSpin_succ]
      unfold jacobiEdgeSq raisingNumerator raisingDenominator channelSpin
      push_cast
      congr 1 <;> ring
    have physicalLP_nonzero (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
        (t : ℕ) (ht : t≤channelWidth n j l) : physicalLP n j l t≠0 := by
      clear * - n j l hj hl hjl t ht channelSpin_bounds channel_admissible
      have pivot_left_positive (s j l k : ℚ) (hs : 0 ≤ s) (hj : 0 ≤ j)
          (hjl : j < l) (hk : 0 < k) (hks : s-j ≤ k) (hkl : l-s ≤ k)
          (hkb : k ≤ s+j) : 0 < pivotLeft s j l k := by
        clear * - s j l k hs hj hjl hk hks hkl hkb
        have h1 : 0 < k+s-j+1 := by linarith
        have h2 : 0 < k+s+j+2 := by linarith
        have h3 : 0 < k-s+l+1 := by linarith
        have h4 : 0 < s+l-k := by linarith
        have he : pivotLeft s j l k =
            (k+s-j+1)*(k+s+j+2)*(k-s+l+1)*(s+l-k)/(2*(k+1)*(2*k+1)) := by
          unfold pivotLeft pivotLeftNumerator spinCasimir
          congr 1
          ring
        rw [he]
        exact div_pos (by positivity) (by positivity)
      have hb := channelSpin_bounds n j l t hj hl hjl ht
      have hp := pivot_left_positive ((n : ℚ)/2) j l (channelSpin n j l t)
        (by positivity) (by positivity) (by exact_mod_cast hjl) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
      apply ne_of_gt
      unfold physicalLP
      exact_mod_cast hp
    have physicalRP_nonzero (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
        (t : ℕ) (ht : t≤channelWidth n j l) : physicalRP n j l t≠0 := by
      clear * - n j l hj hl hjl t ht channelSpin_bounds channel_admissible
      have pivot_right_positive (s j l k : ℚ) (hs : 0 ≤ s) (hj : 0 ≤ j)
          (hjl : j < l) (hk : 0 < k) (hks : s-j ≤ k) (hkl : l-s ≤ k)
          (hkb : k ≤ s+j) : 0 < pivotRight s j l k := by
        clear * - s j l k hs hj hjl hk hks hkl hkb
        have h1 : 0 < k+s-j := by linarith
        have h2 : 0 < k+s+j+1 := by linarith
        have h3 : 0 < k-s+l := by linarith
        have h4 : 0 < s+l+1-k := by linarith
        have he : pivotRight s j l k =
            (k+s-j)*(k+s+j+1)*(k-s+l)*(s+l+1-k)/(2*k*(2*k+1)) := by
          unfold pivotRight pivotRightNumerator spinCasimir
          congr 1
          ring
        rw [he]
        exact div_pos (by positivity) (by positivity)
      have hb := channelSpin_bounds n j l t hj hl hjl ht
      have hp := pivot_right_positive ((n : ℚ)/2) j l (channelSpin n j l t)
        (by positivity) (by positivity) (by exact_mod_cast hjl) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
      apply ne_of_gt
      unfold physicalRP
      exact_mod_cast hp
    have physical_gap_nonzero (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
        (t : ℕ) (ht : t≤channelWidth n j l) :
        physicalLP n j l t+physicalRP n j l t-physicalA n j l t≠0 := by
      clear * - n j l hj hl hjl t ht channelSpin_bounds channel_admissible fourSpinDenominator_ne physicalA_raw pivotLeft_scaled pivotRight_scaled rawDiagonal_scaled
      have physical_gap (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
          (t : ℕ) (ht : t≤channelWidth n j l) :
          physicalLP n j l t+physicalRP n j l t-physicalA n j l t =
            ((n : ℝ)+1)*(casimir l-casimir j)/(2*(channelSpin n j l t : ℝ)+1) := by
        clear * - n j l hj hl hjl t ht channelSpin_bounds channel_admissible fourSpinDenominator_ne physicalA_raw pivotLeft_scaled pivotRight_scaled rawDiagonal_scaled
        have pivot_gap (s j l k : ℚ) (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) :
            pivotLeft s j l k+pivotRight s j l k-rawDiagonal s s j l k =
              (2*s+1)*(spinCasimir l-spinCasimir j)/(2*k+1) := by
          clear * - s j l k hk hk1 hk2 fourSpinDenominator_ne pivotLeft_scaled pivotRight_scaled rawDiagonal_scaled
          have pivot_gap_polynomial (s j l k : ℚ) :
              k*pivotLeftNumerator s j l k+(k+1)*pivotRightNumerator s j l k -
                (2*k+1)*(4*k*(k+1)*spinCasimir s-
                  (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) =
                2*k*(k+1)*(2*s+1)*(spinCasimir l-spinCasimir j) := by
            clear * - s j l k
            unfold pivotLeftNumerator pivotRightNumerator spinCasimir
            ring
          have hd : jacobiDenominator k ≠ 0 := fourSpinDenominator_ne k hk hk1 hk2
          have ha := rawDiagonal_scaled s s j l 0 k hk hk1
          simp only [zero_mul, zero_add, sub_zero] at ha
          have ha' : jacobiDenominator k*rawDiagonal s s j l k =
              (2*k+1)*(4*k*(k+1)*spinCasimir s-
                (k*(k+1)+spinCasimir s-spinCasimir j)*(k*(k+1)+spinCasimir s-spinCasimir l)) := by
            simpa only [jacobiDenominator, fourSpinDenominator, spinCasimir, mul_comm, mul_left_comm,
              mul_assoc, ← two_mul, mul_add, show (2 : ℚ)*2 = 4 by ring] using ha
          apply mul_left_cancel₀ hd
          conv_lhs => rw [mul_sub, mul_add]
          rw [pivotLeft_scaled s j l k hk1 hk2, pivotRight_scaled s j l k hk hk2, ha',
            pivot_gap_polynomial]
          unfold jacobiDenominator
          field_simp [hk2] <;> ring
        have hb := channelSpin_bounds n j l t hj hl hjl ht
        rw [physicalA_raw _ _ _ _ hb.1]
        have h := pivot_gap ((n : ℚ)/2) j l (channelSpin n j l t)
          (ne_of_gt hb.1) (by linarith) (by linarith)
        unfold physicalLP physicalRP casimir
        unfold spinCasimir at h
        exact_mod_cast (by convert h using 1 <;> ring :
          pivotLeft ((n : ℚ)/2) j l (channelSpin n j l t)+pivotRight ((n : ℚ)/2) j l (channelSpin n j l t)-
            rawDiagonal ((n : ℚ)/2) ((n : ℚ)/2) j l (channelSpin n j l t) =
              ((n : ℚ)+1)*((l : ℚ)*(l+1)-(j : ℚ)*(j+1))/(2*channelSpin n j l t+1))
      rw [physical_gap n j l hj hl hjl t ht]
      have hb := channelSpin_bounds n j l t hj hl hjl ht
      have hspin : (0 : ℝ)<(channelSpin n j l t : ℝ) := by exact_mod_cast hb.1
      have hdiff : 0<casimir l-casimir j := by
        unfold casimir
        have hjlR : (j : ℝ)<l := by exact_mod_cast hjl
        have hjR : (0 : ℝ)≤j := by positivity
        nlinarith
      exact ne_of_gt (by positivity)
    have physical_left_endpoint (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l) :
        physicalA n j l 0=physicalLP n j l 0 := by
      clear * - n j l hj hl hjl channelSpin_bounds channel_admissible fourSpinDenominator_ne physicalA_raw pivotLeft_scaled pivot_left_residual rawDiagonal_scaled
      have pivot_left_boundary (s j l : ℚ) (ha : 0 < max (s-j) (l-s)) :
          pivotLeft s j l (max (s-j) (l-s)) = rawDiagonal s s j l (max (s-j) (l-s)) := by
        clear * - s j l ha fourSpinDenominator_ne pivotLeft_scaled pivot_left_residual rawDiagonal_scaled
        have h := pivot_left_residual s j l (max (s-j) (l-s))
          (ne_of_gt ha) (by linarith) (by linarith)
        have hz : (max (s-j) (l-s)-s+j)*(max (s-j) (l-s)+s-l) = 0 := by
          rcases le_total (s-j) (l-s) with he | he
          · rw [max_eq_right he]; ring
          · rw [max_eq_left he]; ring
        have hf : (max (s-j) (l-s)-s+j)*(s+j+1-max (s-j) (l-s))*
            (max (s-j) (l-s)+s-l)*(s+l+max (s-j) (l-s)+1) = 0 := by
          linear_combination (s+j+1-max (s-j) (l-s))*(s+l+max (s-j) (l-s)+1)*hz
        rw [hf, zero_div] at h
        linarith
      have channelSpin_first (n j l : ℕ) (hjl : j≤l) :
          channelSpin n j l 0=max ((n : ℚ)/2-j) ((l : ℚ)-(n : ℚ)/2) := by
        clear * - n j l hjl
        by_cases hn : j+l≤n
        · have hb : channelLabel n j l 0+2*j=n := by unfold channelLabel channelBase; omega
          have hq : (channelLabel n j l 0 : ℚ)+2*j=n := by exact_mod_cast hb
          have hnp : (j : ℚ)+l≤n := by exact_mod_cast hn
          rw [max_eq_left (by linarith)]
          unfold channelSpin
          linarith
        · have hb : channelLabel n j l 0+n=2*l := by unfold channelLabel channelBase; omega
          have hq : (channelLabel n j l 0 : ℚ)+n=2*l := by exact_mod_cast hb
          have hnp : (n : ℚ)<(j : ℚ)+l := by exact_mod_cast (by omega : n<j+l)
          rw [max_eq_right (by linarith)]
          unfold channelSpin
          linarith
      have hb := channelSpin_bounds n j l 0 hj hl hjl (by omega)
      rw [physicalA_raw n j l 0 hb.1]
      unfold physicalLP
      rw [channelSpin_first n j l hjl.le]
      have hp : (0 : ℚ)<max ((n : ℚ)/2-j) ((l : ℚ)-(n : ℚ)/2) := by
        rw [channelSpin_first n j l hjl.le] at hb
        exact hb.1
      exact_mod_cast (pivot_left_boundary ((n : ℚ)/2) j l hp).symm
    have physical_right_endpoint (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l) :
        physicalA n j l (channelWidth n j l)=physicalRP n j l (channelWidth n j l) := by
      clear * - n j l hj hl hjl channelSpin_bounds channel_admissible channel_last fourSpinDenominator_ne physicalA_raw pivotRight_scaled pivot_right_residual rawDiagonal_scaled
      have pivot_right_boundary (s j l : ℚ) (hb : 0 < s+j) :
          pivotRight s j l (s+j) = rawDiagonal s s j l (s+j) := by
        clear * - s j l hb fourSpinDenominator_ne pivotRight_scaled pivot_right_residual rawDiagonal_scaled
        have h := pivot_right_residual s j l (s+j) (ne_of_gt hb) (by linarith) (by linarith)
        rw [sub_self, mul_zero, zero_mul, zero_mul, zero_div] at h
        linarith
      have channelSpin_last (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j≤l) :
          channelSpin n j l (channelWidth n j l)=(n : ℚ)/2+j := by
        clear * - n j l hj hl hjl channel_last
        unfold channelSpin
        rw [channel_last n j l hj hl hjl]
        push_cast
        ring
      have hb := channelSpin_bounds n j l (channelWidth n j l) hj hl hjl le_rfl
      rw [physicalA_raw _ _ _ _ hb.1]
      unfold physicalRP
      rw [channelSpin_last n j l hj hl hjl.le]
      have hp : (0 : ℚ)<(n : ℚ)/2+j := by
        rw [channelSpin_last n j l hj hl hjl.le] at hb
        exact hb.1
      exact_mod_cast (pivot_right_boundary ((n : ℚ)/2) j l hp).symm
    have physical_left_edge (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
        (t : ℕ) (ht0 : 0<t) (ht : t≤channelWidth n j l) :
        physicalE n j l (t-1)^2=physicalLP n j l (t-1)*(physicalA n j l t-physicalLP n j l t) := by
      clear * - n j l hj hl hjl t ht0 ht channelSpin_bounds channelSpin_succ channel_admissible fourSpinDenominator_ne physicalA_raw physicalE_sq pivotLeft_scaled pivot_left_residual rawDiagonal_scaled
      have pivot_left_edge (s j l k : ℚ)
          (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) (hkm : 2*k-1 ≠ 0) :
          jacobiEdgeSq s j l k =
            pivotLeft s j l (k-1)*(rawDiagonal s s j l k-pivotLeft s j l k) := by
        clear * - s j l k hk hk1 hk2 hkm fourSpinDenominator_ne pivotLeft_scaled pivot_left_residual rawDiagonal_scaled
        rw [pivot_left_residual s j l k hk hk1 hk2]
        unfold jacobiEdgeSq pivotLeft pivotLeftNumerator spinCasimir
        rw [show k-1+1=k by ring, show 2*(k-1)+1=2*k-1 by ring]
        field_simp [hk,hk2,hkm]
        ring
      have hb := channelSpin_bounds n j l t hj hl hjl ht
      have hbp := channelSpin_bounds n j l (t-1) hj hl hjl (by omega)
      have hs : channelSpin n j l (t-1)+1=channelSpin n j l t := by
        rw [←channelSpin_succ,show t-1+1=t by omega]
      have hkm : 2*channelSpin n j l t-1≠0 := by
        have hp := hbp.1
        linarith
      rw [physicalE_sq n j l (t-1) hj hl hjl.le (by omega),show t-1+1=t by omega,
        physicalA_raw n j l t hb.1]
      have hp := pivot_left_edge ((n : ℚ)/2) j l (channelSpin n j l t)
        (ne_of_gt hb.1) (by linarith) (by linarith) hkm
      have he : channelSpin n j l t-1=channelSpin n j l (t-1) := by linarith
      rw [he] at hp
      unfold physicalLP
      exact_mod_cast hp
    have physical_right_edge (n j l : ℕ) (hj : j≤n) (hl : l≤n) (hjl : j<l)
        (t : ℕ) (ht : t<channelWidth n j l) :
        physicalE n j l t^2=physicalRP n j l (t+1)*(physicalA n j l t-physicalRP n j l t) := by
      clear * - n j l hj hl hjl t ht channelSpin_bounds channelSpin_succ channel_admissible fourSpinDenominator_ne physicalA_raw physicalE_sq pivotRight_scaled pivot_right_residual rawDiagonal_scaled
      have pivot_right_edge (s j l k : ℚ)
          (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (hk2 : 2*k+1 ≠ 0) (hkp : 2*k+3 ≠ 0) :
          jacobiEdgeSq s j l (k+1) =
            pivotRight s j l (k+1)*(rawDiagonal s s j l k-pivotRight s j l k) := by
        clear * - s j l k hk hk1 hk2 hkp fourSpinDenominator_ne pivotRight_scaled pivot_right_residual rawDiagonal_scaled
        rw [pivot_right_residual s j l k hk hk1 hk2]
        unfold jacobiEdgeSq pivotRight pivotRightNumerator spinCasimir
        rw [show 2*(k+1)-1=2*k+1 by ring, show 2*(k+1)+1=2*k+3 by ring]
        field_simp [hk1,hk2,hkp]
        ring
      have hb := channelSpin_bounds n j l t hj hl hjl (by omega)
      rw [physicalE_sq n j l t hj hl hjl.le ht,physicalA_raw n j l t hb.1]
      have hp := pivot_right_edge ((n : ℚ)/2) j l (channelSpin n j l t)
        (ne_of_gt hb.1) (by linarith) (by linarith) (by linarith)
      rw [←channelSpin_succ] at hp
      unfold physicalRP
      exact_mod_cast hp
    exact jacobi_green_inverse (channelWidth n j l) (physicalA n j l) (physicalE n j l)
      (physicalLP n j l) (physicalRP n j l)
      (physicalLP_nonzero n j l hj hl hjl) (physicalRP_nonzero n j l hj hl hjl)
      (physical_gap_nonzero n j l hj hl hjl)
      (physical_left_endpoint n j l hj hl hjl) (physical_right_endpoint n j l hj hl hjl)
      (physical_left_edge n j l hj hl hjl) (physical_right_edge n j l hj hl hjl)
  have hinv : physicalT n j l*physicalSpectralInverse n j l=1 := by
    unfold physicalSpectralInverse
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,physicalTU n j l hj hl hjl.le,
      Matrix.mul_assoc (physicalU n j l)]
    have hd : diagonal (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val))*
        diagonal (fun i : Fin (channelWidth n j l+1) => (casimir (l-j+i.val))⁻¹)=1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hf : (fun i : Fin (channelWidth n j l+1) => casimir (l-j+i.val)*(casimir (l-j+i.val))⁻¹)=
          fun _ => (1 : ℝ) := by
        funext i
        apply mul_inv_cancel₀
        unfold casimir
        have hp : 0<l-j+i.val := by omega
        have hpr : (0 : ℝ)<(l-j+i.val : ℕ) := by exact_mod_cast hp
        positivity
      rw [hf,Matrix.diagonal_one]
    rw [hd,Matrix.mul_one,physicalU_orthogonality n j l hj hl hjl.le]
  have hleft := mul_eq_one_comm.mp (physicalTG n j l hj hl hjl)
  calc
    _ = (physicalG n j l*physicalT n j l)*physicalSpectralInverse n j l := by rw [hleft,Matrix.one_mul]
    _ = physicalG n j l*(physicalT n j l*physicalSpectralInverse n j l) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [hinv,Matrix.mul_one]

end D5.S3.Quantum.Algebra.ZeitlinSixJ.SpectralInverse
