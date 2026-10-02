/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Racah finite sums and the Zeitlin six-j identities. -/

/-
four_spin_raw_recurrence:
  proof_shape: content
  escape_witness: Local four_spin_wz_step: rawAlpha*offsetTerm q.raise z + (rawDiagonal-u*(u+1))*offsetTerm q z + rawGamma*offsetTerm q.lower z = offsetFlux q (fourSpinCertificate a b c d u y) (z+1) - offsetFlux q (fourSpinCertificate a b c d u y) z. The finite summation and both endpoint cancellations use it.
racahSum_recurrence:
  proof_shape: content
  escape_witness: four_spin_raw_recurrence: the three shifted, zero-extended offsetTerm sums satisfy the exact arbitrary-spin recurrence, under compatibility and nonzero denominator hypotheses; it is transported to the actual racahSum supports.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
open Finset Polynomial Matrix
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion

lemma four_spin_raw_recurrence (q : RacahOffsets) (a b c d u y : ℚ)
    (hq : q.compatible a b c d u y) (htc : 0 ≤ q.tc)
    (e : ℕ) (he : q.e = (e : ℤ))
    (hy : y ≠ 0) (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) :
    rawAlpha a b c d y*(∑ z ∈ range (e+1), offsetTerm q.raise z) +
      (rawDiagonal a b c d y-u*(u+1))*(∑ z ∈ range (e+1), offsetTerm q z) +
      rawGamma a b c d y*(∑ z ∈ range (e+1), offsetTerm q.lower z) = 0 := by
  have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
    simp only [invFactorial, if_neg (not_le.mpr hz)]
  have four_spin_wz_step (q : RacahOffsets) (a b c d u y : ℚ)
      (hq : q.compatible a b c d u y)
      (hy : y ≠ 0) (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) (z : ℕ) :
      rawAlpha a b c d y*offsetTerm q.raise z +
        (rawDiagonal a b c d y-u*(u+1))*offsetTerm q z +
        rawGamma a b c d y*offsetTerm q.lower z =
          offsetFlux q (fourSpinCertificate a b c d u y) (z+1) -
            offsetFlux q (fourSpinCertificate a b c d u y) z := by
    have invFactorial_step (z : ℤ) :
        invFactorial (z-1) = (z : ℚ)*invFactorial z := by
      by_cases hz : 0 < z
      · have hz0 : 0 ≤ z := by omega
        have hz1 : 0 ≤ z-1 := by omega
        have he : z.toNat = (z-1).toNat+1 := by omega
        have hc : ((z-1).toNat+1 : ℚ) = (z : ℚ) := by
          have h : (((z-1).toNat+1 : ℕ) : ℤ) = z := by omega
          exact_mod_cast h
        have hn0 : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
        have hf0 : (Nat.factorial (z-1).toNat : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        simp only [invFactorial, if_pos hz0, if_pos hz1]
        rw [he, Nat.factorial_succ, Nat.cast_mul]
        simp only [Nat.cast_add, Nat.cast_one]
        rw [hc]
        field_simp
      · have hz1 : z-1 < 0 := by omega
        rw [invFactorial_neg _ hz1]
        by_cases he : z = 0
        · subst z; simp only [Int.cast_zero, zero_mul]
        · rw [invFactorial_neg _ (by omega)]; simp only [mul_zero]
    have four_spin_certificate_identity (a b c d u y z : ℚ)
        (hy : y ≠ 0) (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) :
      rawAlpha a b c d y *
          (z-(a+d+y))*(z-(a+d+y)+1)*(z-(b+c+y))*(z-(b+c+y)+1) +
        (rawDiagonal a b c d y-u*(u+1))*
          (z-(a+d+y)+1)*(z-(b+c+y)+1)*(a+c+u+y-z+1)*(b+d+u+y-z+1) +
        rawGamma a b c d y *
          (a+c+u+y-z)*(a+c+u+y-z+1)*(b+d+u+y-z)*(b+d+u+y-z+1) =
        -(z+2)*(a+b+c+d-z)*(a+c+u+y-z+1)*(b+d+u+y-z+1)*
            fourSpinCertificate a b c d u y (z+1) -
          (z-(a+b+u))*(z-(c+d+u))*(z-(a+d+y)+1)*(z-(b+c+y)+1)*
            fourSpinCertificate a b c d u y z := by
      have fourSpinDenominator_ne (y : ℚ) (hy : y ≠ 0)
          (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) : fourSpinDenominator y ≠ 0 := by
        unfold fourSpinDenominator
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hy) hy1) hy2
      have rawAlpha_scaled (a b c d y : ℚ)
          (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) :
          fourSpinDenominator y*rawAlpha a b c d y =
            y*(((y+1)^2-(a-d)^2)*((y+1)^2-(b-c)^2)) := by
        let v := (((y+1)^2-(a-d)^2)*((y+1)^2-(b-c)^2))
        change fourSpinDenominator y*(v/(2*(y+1)*(2*y+1))) = y*v
        calc
          _ = y*((2*(y+1)*(2*y+1))*(v/(2*(y+1)*(2*y+1)))) := by
            unfold fourSpinDenominator; ring
          _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hy1) hy2)]
      have rawGamma_scaled (a b c d y : ℚ)
          (hy : y ≠ 0) (hy2 : 2*y+1 ≠ 0) :
          fourSpinDenominator y*rawGamma a b c d y =
            (y+1)*(((a+d+1)^2-y^2)*((b+c+1)^2-y^2)) := by
        let v := (((a+d+1)^2-y^2)*((b+c+1)^2-y^2))
        change fourSpinDenominator y*(v/(2*y*(2*y+1))) = (y+1)*v
        calc
          _ = (y+1)*((2*y*(2*y+1))*(v/(2*y*(2*y+1)))) := by
            unfold fourSpinDenominator; ring
          _ = _ := by rw [mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (by positivity) hy) hy2)]
      have rawDiagonal_scaled (a b c d u y : ℚ)
          (hy : y ≠ 0) (hy1 : y+1 ≠ 0) :
          fourSpinDenominator y*(rawDiagonal a b c d y-u*(u+1)) =
            (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-
              (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))) := by
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
      have fourSpinCertificate_scaled (a b c d u y z : ℚ)
          (hy : y ≠ 0) (hy1 : y+1 ≠ 0) (hy2 : 2*y+1 ≠ 0) :
          fourSpinDenominator y*fourSpinCertificate a b c d u y z =
            fourSpinCertificateNumerator a b c d u y z := by
        unfold fourSpinCertificate
        exact mul_div_cancel₀ _ (fourSpinDenominator_ne y hy hy1 hy2)
      have four_spin_polynomial_certificate (a b c d u y z : ℚ) :
        y*(((y+1)^2-(a-d)^2)*((y+1)^2-(b-c)^2))*
            ((z-(a+d+y))*(z-(a+d+y)+1)*(z-(b+c+y))*(z-(b+c+y)+1)) +
          ((2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-
            (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))))*
            ((z-(a+d+y)+1)*(z-(b+c+y)+1))*((a+c+u+y-z+1)*(b+d+u+y-z+1)) +
          ((y+1)*(((a+d+1)^2-y^2)*((b+c+1)^2-y^2)))*
            ((a+c+u+y-z)*(b+d+u+y-z))*((a+c+u+y-z+1)*(b+d+u+y-z+1)) =
          -((z+2)*(a+b+c+d-z))*((a+c+u+y-z+1)*(b+d+u+y-z+1))*
              fourSpinCertificateNumerator a b c d u y (z+1) -
            ((z-(a+b+u))*(z-(c+d+u)))*((z-(a+d+y)+1)*(z-(b+c+y)+1))*
              fourSpinCertificateNumerator a b c d u y z := by
        have compressed_polynomial_certificate (m h v p q y x : ℚ) :
          compressedAlpha h v p q y*((x-h)*(x-h+1)*x*(x+1)) +
            compressedBeta m h v p q y*((x-h+1)*(x+1))*compressedV v p x +
            compressedGamma m h y*compressedV v p (x+1)*compressedV v p x =
            -(compressedZ m h y x)*compressedV v p x*compressedCertificate m h v p q y (x+1) -
              compressedQ v q y x*((x-h+1)*(x+1))*compressedCertificate m h v p q y x := by
          unfold compressedAlpha compressedBeta compressedGamma compressedV compressedZ compressedQ
            compressedCertificate
          ring
        have compressedAlpha_bridge (a b c d u y : ℚ) :
          y*(((y+1)^2-(a-d)^2)*((y+1)^2-(b-c)^2)) =
            compressedAlpha (a+d-b-c) (a-b+u+1+(d-c+u+1))
              ((a-b+u+1)*(d-c+u+1)) ((a-c+u-y)*(d-b+u-y)) y := by
          unfold compressedAlpha
          ring
        have compressedBeta_bridge (a b c d u y : ℚ) :
          (2*y+1)*(2*y*(y+1)*(a*(a+1)+b*(b+1)-u*(u+1))-
              (y*(y+1)+a*(a+1)-d*(d+1))*(y*(y+1)+b*(b+1)-c*(c+1))) =
            compressedBeta ((b+c+1-y)*(a+d+y+1)) (a+d-b-c) (a-b+u+1+(d-c+u+1))
              ((a-b+u+1)*(d-c+u+1)) ((a-c+u-y)*(d-b+u-y)) y := by
          unfold compressedBeta
          ring
        have compressedGamma_bridge (a b c d y : ℚ) :
          (y+1)*(((a+d+1)^2-y^2)*((b+c+1)^2-y^2)) =
            compressedGamma ((b+c+1-y)*(a+d+y+1)) (a+d-b-c) y := by
          unfold compressedGamma
          ring
        have compressedCertificate_bridge (a b c d u y z : ℚ) :
          fourSpinCertificateNumerator a b c d u y z =
            compressedCertificate ((b+c+1-y)*(a+d+y+1)) (a+d-b-c) (a-b+u+1+(d-c+u+1))
              ((a-b+u+1)*(d-c+u+1)) ((a-c+u-y)*(d-b+u-y)) y (z-(b+c+y)) := by
          unfold fourSpinCertificateNumerator compressedCertificate
          ring
        have compressedV_bridge (a b c d u y z : ℚ) :
          (a+c+u+y-z+1)*(b+d+u+y-z+1) =
            compressedV (a-b+u+1+(d-c+u+1)) ((a-b+u+1)*(d-c+u+1)) (z-(b+c+y)) := by
          unfold compressedV
          ring
        have compressedZ_bridge (a b c d u y z : ℚ) :
          (z+2)*(a+b+c+d-z) =
            compressedZ ((b+c+1-y)*(a+d+y+1)) (a+d-b-c) y (z-(b+c+y)) := by
          unfold compressedZ
          ring
        have compressedQ_bridge (a b c d u y z : ℚ) :
          (z-(a+b+u))*(z-(c+d+u)) =
            compressedQ (a-b+u+1+(d-c+u+1)) ((a-c+u-y)*(d-b+u-y)) y (z-(b+c+y)) := by
          unfold compressedQ
          ring
        let m := (b+c+1-y)*(a+d+y+1)
        let h := a+d-b-c
        let v := a-b+u+1+(d-c+u+1)
        let p := (a-b+u+1)*(d-c+u+1)
        let q := (a-c+u-y)*(d-b+u-y)
        let x := z-(b+c+y)
        have ha : z-(a+d+y) = x-h := by dsimp [x, h]; ring
        have hz : z+1-(b+c+y) = x+1 := by dsimp [x]; ring
        have hdown : (a+c+u+y-z)*(b+d+u+y-z) = compressedV v p (x+1) := by
          have hc := compressedV_bridge a b c d u y (z+1)
          have he : a+c+u+y-(z+1)+1 = a+c+u+y-z := by ring
          have hf : b+d+u+y-(z+1)+1 = b+d+u+y-z := by ring
          rw [he, hf, hz] at hc
          exact hc
        rw [compressedAlpha_bridge, compressedBeta_bridge, compressedGamma_bridge,
          compressedCertificate_bridge a b c d u y (z+1),
          compressedCertificate_bridge a b c d u y z,
          compressedV_bridge, compressedZ_bridge a b c d u y z, compressedQ_bridge]
        change compressedAlpha h v p q y*((z-(a+d+y))*(z-(a+d+y)+1)*x*(x+1)) +
          compressedBeta m h v p q y*((z-(a+d+y)+1)*(x+1))*compressedV v p x +
          compressedGamma m h y*((a+c+u+y-z)*(b+d+u+y-z))*compressedV v p x =
          -(compressedZ m h y x)*compressedV v p x*compressedCertificate m h v p q y (z+1-(b+c+y)) -
            compressedQ v q y x*((z-(a+d+y)+1)*(x+1))*compressedCertificate m h v p q y x
        rw [ha, hz, hdown]
        exact compressed_polynomial_certificate m h v p q y x
      have hp := four_spin_polynomial_certificate a b c d u y z
      rw [← rawAlpha_scaled a b c d y hy1 hy2,
        ← rawDiagonal_scaled a b c d u y hy hy1, ← rawGamma_scaled a b c d y hy hy2,
        ← fourSpinCertificate_scaled a b c d u y (z+1) hy hy1 hy2,
        ← fourSpinCertificate_scaled a b c d u y z hy hy1 hy2] at hp
      apply mul_left_cancel₀ (fourSpinDenominator_ne y hy hy1 hy2)
      conv_lhs => rw [mul_add, mul_add]
      conv_rhs => rw [mul_sub]
      simpa only [mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hp
    have invFactorial_shift (z : ℤ) :
        invFactorial z = ((z : ℚ)+1)*invFactorial (z+1) := by
      have h := invFactorial_step (z+1)
      simpa only [add_sub_cancel_right, Int.cast_add, Int.cast_one] using h
    have offsetTerm_base (q : RacahOffsets) (z : ℕ) :
        offsetTerm q z = ((z : ℚ)-q.ta+1)*((z : ℚ)-q.tb+1)*
          ((q.f : ℚ)-z+1)*((q.g : ℚ)-z+1)*offsetBase q z := by
      unfold offsetTerm offsetBase
      rw [invFactorial_shift ((z : ℤ)-q.ta), invFactorial_shift ((z : ℤ)-q.tb),
        invFactorial_shift (q.f-z), invFactorial_shift (q.g-z)]
      push_cast
      ring
    have offsetTerm_raise_base (q : RacahOffsets) (z : ℕ) :
        offsetTerm q.raise z = ((z : ℚ)-q.ta)*((z : ℚ)-q.ta+1)*
          ((z : ℚ)-q.tb)*((z : ℚ)-q.tb+1)*offsetBase q z := by
      have ha := invFactorial_step ((z : ℤ)-q.ta)
      have hb := invFactorial_step ((z : ℤ)-q.tb)
      unfold offsetTerm RacahOffsets.raise offsetBase
      dsimp only
      rw [show (z : ℤ)-(q.ta+1) = (z : ℤ)-q.ta-1 by ring,
        show (z : ℤ)-(q.tb+1) = (z : ℤ)-q.tb-1 by ring,
        show q.f+1-z = q.f-z+1 by ring, show q.g+1-z = q.g-z+1 by ring,
        ha, hb, invFactorial_shift ((z : ℤ)-q.ta), invFactorial_shift ((z : ℤ)-q.tb)]
      push_cast
      ring
    have offsetTerm_lower_base (q : RacahOffsets) (z : ℕ) :
        offsetTerm q.lower z = ((q.f : ℚ)-z)*((q.f : ℚ)-z+1)*
          ((q.g : ℚ)-z)*((q.g : ℚ)-z+1)*offsetBase q z := by
      unfold offsetTerm RacahOffsets.lower offsetBase
      dsimp only
      rw [show (z : ℤ)-(q.ta-1) = (z : ℤ)-q.ta+1 by ring,
        show (z : ℤ)-(q.tb-1) = (z : ℤ)-q.tb+1 by ring,
        show q.f-1-z = q.f-z-1 by ring, show q.g-1-z = q.g-z-1 by ring,
        invFactorial_step (q.f-z), invFactorial_step (q.g-z),
        invFactorial_shift (q.f-z), invFactorial_shift (q.g-z)]
      push_cast
      ring
    have offsetFlux_base (q : RacahOffsets) (P : ℚ → ℚ) (z : ℕ) :
        offsetFlux q P z = ((z : ℚ)-q.tc)*((z : ℚ)-q.td)*
          ((z : ℚ)-q.ta+1)*((z : ℚ)-q.tb+1)*P z*offsetBase q z := by
      unfold offsetFlux offsetBase
      rw [invFactorial_step ((z : ℤ)-q.tc), invFactorial_step ((z : ℤ)-q.td),
        invFactorial_shift ((z : ℤ)-q.ta), invFactorial_shift ((z : ℤ)-q.tb)]
      push_cast
      ring
    have offsetFlux_succ_base (q : RacahOffsets) (P : ℚ → ℚ) (z : ℕ) :
        offsetFlux q P (z+1) =
          -((z : ℚ)+2)*((q.e : ℚ)-z)*((q.f : ℚ)-z+1)*((q.g : ℚ)-z+1)*
            P ((z : ℚ)+1)*offsetBase q z := by
      unfold offsetFlux offsetBase
      rw [pow_succ, Nat.factorial_succ]
      simp only [Int.natCast_add, Int.natCast_one, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      rw [show (z : ℤ)+1-q.ta = (z : ℤ)-q.ta+1 by ring,
        show (z : ℤ)+1-q.tb = (z : ℤ)-q.tb+1 by ring,
        show (z : ℤ)+1-q.tc-1 = (z : ℤ)-q.tc by ring,
        show (z : ℤ)+1-q.td-1 = (z : ℤ)-q.td by ring,
        show q.e-((z : ℤ)+1) = q.e-z-1 by ring,
        show q.f-((z : ℤ)+1)+1 = q.f-z by ring,
        show q.g-((z : ℤ)+1)+1 = q.g-z by ring,
        invFactorial_step (q.e-z), invFactorial_shift (q.f-z), invFactorial_shift (q.g-z)]
      push_cast
      ring
    rcases hq with ⟨hta, htb, htc, htd, he, hf, hg⟩
    rw [offsetTerm_raise_base, offsetTerm_base, offsetTerm_lower_base,
      offsetFlux_succ_base, offsetFlux_base, hta, htb, htc, htd, he, hf, hg]
    have hc := congrArg (fun v : ℚ => v*offsetBase q z)
      (four_spin_certificate_identity a b c d u y z hy hy1 hy2)
    conv at hc => lhs; rw [add_mul, add_mul]
    conv at hc => rhs; rw [sub_mul]
    simpa only [mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hc
  have offsetFlux_zero (q : RacahOffsets) (P : ℚ → ℚ) (htc : 0 ≤ q.tc) :
      offsetFlux q P 0 = 0 := by
    unfold offsetFlux
    simp only [Int.natCast_zero]
    rw [invFactorial_neg ((0 : ℤ)-q.tc-1) (by omega)]
    simp only [mul_zero, zero_mul]
  have offsetFlux_end (q : RacahOffsets) (P : ℚ → ℚ) (e : ℕ)
      (he : q.e = (e : ℤ)) : offsetFlux q P (e+1) = 0 := by
    unfold offsetFlux
    simp only [Int.natCast_add, Int.natCast_one]
    rw [he, invFactorial_neg ((e : ℤ)-(e+1)) (by omega)]
    simp only [mul_zero, zero_mul]
  simp only [mul_sum, ← sum_add_distrib]
  calc
    _ = ∑ z ∈ range (e+1),
        (offsetFlux q (fourSpinCertificate a b c d u y) (z+1) -
          offsetFlux q (fourSpinCertificate a b c d u y) z) := by
      apply sum_congr rfl
      intro z _
      exact four_spin_wz_step q a b c d u y hq hy hy1 hy2 z
    _ = 0 := by rw [sum_range_sub, offsetFlux_zero q _ htc, offsetFlux_end q _ e he, sub_self]

def racahOffsets (a b u c d y : ℕ) : RacahOffsets :=
  ⟨(((a+d+y)/2 : ℕ) : ℤ), (((c+b+y)/2 : ℕ) : ℤ),
    (((a+b+u)/2 : ℕ) : ℤ), (((c+d+u)/2 : ℕ) : ℤ),
    (((a+b+c+d)/2 : ℕ) : ℤ), (((u+a+y+c)/2 : ℕ) : ℤ),
    (((b+u+d+y)/2 : ℕ) : ℤ)⟩

lemma racahSum_recurrence (a b u c d y : ℕ) (hy : 2 ≤ y)
    (had : admissible a b u c d y) :
    rawAlpha ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2)*
        racahSum a b u c d (y+2) +
      (rawDiagonal ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2)-
        ((u : ℚ)/2)*((u : ℚ)/2+1))*racahSum a b u c d y +
      rawGamma ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((y : ℚ)/2)*
        racahSum a b u c d (y-2) = 0 := by
  have offsetSum_racahSum (a b u c d y : ℕ) :
      (∑ z ∈ range ((a+b+c+d)/2+1), offsetTerm (racahOffsets a b u c d y) z) =
        racahSum a b u c d y := by
    have invFactorial_neg (z : ℤ) (hz : z < 0) : invFactorial z = 0 := by
      simp only [invFactorial, if_neg (not_le.mpr hz)]
    have invFactorial_nat (n : ℕ) :
        invFactorial (n : ℤ) = (Nat.factorial n : ℚ)⁻¹ := by
      simp only [invFactorial, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    have invFactorial_nat_sub (n m : ℕ) (h : m ≤ n) :
        invFactorial ((n : ℤ)-(m : ℤ)) = (Nat.factorial (n-m) : ℚ)⁻¹ := by
      rw [← Int.natCast_sub h, invFactorial_nat]
    have offsetTerm_left_zero (q : RacahOffsets) (z : ℕ)
        (hz : (z : ℤ) < q.ta ∨ (z : ℤ) < q.tb ∨ (z : ℤ) < q.tc ∨ (z : ℤ) < q.td) :
        offsetTerm q z = 0 := by
      rcases hz with h | h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_right_zero (q : RacahOffsets) (z : ℕ)
        (hz : q.e < z ∨ q.f < z ∨ q.g < z) : offsetTerm q z = 0 := by
      rcases hz with h | h | h <;>
        simp only [offsetTerm, invFactorial_neg _ (sub_neg.mpr h), mul_zero, zero_mul]
    have offsetTerm_racahTerm (a b u c d y z : ℕ)
        (hl : lower a b u c d y ≤ z) (hu : z ≤ upper a b u c d y) :
        offsetTerm (racahOffsets a b u c d y) z = racahTerm a b u c d y z := by
      have hl' := hl
      unfold lower at hl'
      have hu' := hu
      unfold upper at hu'
      have hta : (a+d+y)/2 ≤ z :=
        le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hl')
      have htc : (a+b+u)/2 ≤ z :=
        le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hl')
      have htb : (c+b+y)/2 ≤ z :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hl')
      have htd : (c+d+u)/2 ≤ z :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hl')
      have he : z ≤ (a+b+c+d)/2 := le_trans hu' (min_le_left _ _)
      have hf : z ≤ (u+a+y+c)/2 :=
        le_trans hu' (le_trans (min_le_right _ _) (min_le_right _ _))
      have hg : z ≤ (b+u+d+y)/2 :=
        le_trans hu' (le_trans (min_le_right _ _) (min_le_left _ _))
      unfold offsetTerm racahOffsets racahTerm
      dsimp only
      rw [invFactorial_nat_sub z ((a+d+y)/2) hta,
        invFactorial_nat_sub z ((c+b+y)/2) htb,
        invFactorial_nat_sub z ((a+b+u)/2) htc,
        invFactorial_nat_sub z ((c+d+u)/2) htd,
        invFactorial_nat_sub ((a+b+c+d)/2) z he,
        invFactorial_nat_sub ((u+a+y+c)/2) z hf,
        invFactorial_nat_sub ((b+u+d+y)/2) z hg]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ac_rfl
    have hu : upper a b u c d y ≤ (a+b+c+d)/2 := by
      unfold upper
      exact min_le_left _ _
    have hsub : range (upper a b u c d y+1) ⊆ range ((a+b+c+d)/2+1) :=
      range_mono (Nat.add_le_add_right hu 1)
    have htrim : (∑ z ∈ range (upper a b u c d y+1),
        offsetTerm (racahOffsets a b u c d y) z) =
        ∑ z ∈ range ((a+b+c+d)/2+1), offsetTerm (racahOffsets a b u c d y) z := by
      apply sum_subset hsub
      intro z _ hz
      apply offsetTerm_right_zero
      simp only [racahOffsets]
      have ht : upper a b u c d y < z := by
        have ht : ¬ z < upper a b u c d y+1 := by simpa only [mem_range] using hz
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_not_lt ht)
      unfold upper at ht
      rcases min_lt_iff.mp ht with he | hfg
      · left
        exact_mod_cast he
      · rcases min_lt_iff.mp hfg with hg | hf
        · right; right
          exact_mod_cast hg
        · right; left
          exact_mod_cast hf
    rw [← htrim]
    unfold racahSum
    apply sum_congr rfl
    intro z hz
    by_cases hl : lower a b u c d y ≤ z
    · rw [if_pos hl]
      exact offsetTerm_racahTerm a b u c d y z hl (Nat.le_of_lt_succ (mem_range.mp hz))
    · rw [if_neg hl]
      apply offsetTerm_left_zero
      simp only [racahOffsets]
      have ht : z < lower a b u c d y := Nat.lt_of_not_ge hl
      unfold lower at ht
      rcases lt_max_iff.mp ht with hab | hcd
      · rcases lt_max_iff.mp hab with htc | hta
        · right; right; left
          exact_mod_cast htc
        · left
          exact_mod_cast hta
      · rcases lt_max_iff.mp hcd with htb | htd
        · right; left
          exact_mod_cast htb
        · right; right; right
          exact_mod_cast htd
  have half_cast (n : ℕ) (hn : n % 2 = 0) :
      (((n/2 : ℕ) : ℤ) : ℚ) = (n : ℚ)/2 := by
    have he : 2*(n/2) = n := by omega
    have hq := congrArg (fun k : ℕ => (k : ℚ)) he
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
    simp only [Int.cast_natCast]
    apply (eq_div_iff (by positivity : (2 : ℚ) ≠ 0)).mpr
    simpa only [mul_comm] using hq
  have racahOffsets_compatible (a b u c d y : ℕ)
      (had : admissible a b u c d y) :
      (racahOffsets a b u c d y).compatible
        ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((u : ℚ)/2) ((y : ℚ)/2) := by
    rcases had with ⟨⟨_, _, _, htc⟩, ⟨_, _, _, hta⟩, ⟨_, _, _, htb⟩, ⟨_, _, _, htd⟩⟩
    have htb' : (b+c+y)%2 = 0 := by omega
    have he : (a+b+c+d)%2 = 0 := by omega
    have hf : (u+a+y+c)%2 = 0 := by omega
    have hg : (b+u+d+y)%2 = 0 := by omega
    unfold racahOffsets RacahOffsets.compatible
    dsimp only
    rw [half_cast _ hta, half_cast _ htb, half_cast _ htc, half_cast _ htd,
      half_cast _ he, half_cast _ hf, half_cast _ hg]
    push_cast
    exact ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩
  have racahOffsets_raise (a b u c d y : ℕ) :
      racahOffsets a b u c d (y+2) = (racahOffsets a b u c d y).raise := by
    unfold racahOffsets RacahOffsets.raise
    congr 1 <;> push_cast <;> omega
  have racahOffsets_lower (a b u c d y : ℕ) (hy : 2 ≤ y) :
      racahOffsets a b u c d (y-2) = (racahOffsets a b u c d y).lower := by
    unfold racahOffsets RacahOffsets.lower
    congr 1 <;> push_cast <;> omega
  have hpos : (0 : ℚ) < (y : ℚ)/2 := by
    have hyq : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
    positivity
  have hq := racahOffsets_compatible a b u c d y had
  have ht : 0 ≤ (racahOffsets a b u c d y).tc := by simp only [racahOffsets]; positivity
  have he : (racahOffsets a b u c d y).e = (((a+b+c+d)/2 : ℕ) : ℤ) := rfl
  have hr := four_spin_raw_recurrence (racahOffsets a b u c d y)
    ((a : ℚ)/2) ((b : ℚ)/2) ((c : ℚ)/2) ((d : ℚ)/2) ((u : ℚ)/2) ((y : ℚ)/2)
    hq ht ((a+b+c+d)/2) he (ne_of_gt hpos) (by linarith) (by linarith)
  rw [← racahOffsets_raise, ← racahOffsets_lower _ _ _ _ _ _ hy,
    offsetSum_racahSum, offsetSum_racahSum, offsetSum_racahSum] at hr
  exact hr

def zeroOffsets (a b q : ℕ) : RacahOffsets := ⟨a, b, q, q, ((a+b : ℕ) : ℤ), q, q⟩

def spinCasimir (x : ℚ) : ℚ := x*(x+1)

def jacobiDenominator (k : ℚ) : ℚ := 2*k*(k+1)*(2*k+1)

def pivotLeftNumerator (s j l k : ℚ) : ℚ :=
  (spinCasimir l-spinCasimir (k-s))*(spinCasimir (k+s+1)-spinCasimir j)

def pivotRightNumerator (s j l k : ℚ) : ℚ :=
  (spinCasimir l-spinCasimir (k-s-1))*(spinCasimir (k+s)-spinCasimir j)

def pivotLeft (s j l k : ℚ) : ℚ := pivotLeftNumerator s j l k/(2*(k+1)*(2*k+1))

def pivotRight (s j l k : ℚ) : ℚ := pivotRightNumerator s j l k/(2*k*(2*k+1))

def endpointKernel (n p d i : ℕ) : ℚ :=
  Nat.factorial (i+d) * invFactorial ((n : ℤ)-i) * invFactorial ((p : ℤ)-i) *
    invFactorial ((i : ℤ)-d) * invFactorial ((n : ℤ)+i+1) *
    invFactorial ((p : ℤ)+i+1)

def endpointBase (n p d i : ℕ) : ℚ :=
  Nat.factorial (i+d) * invFactorial ((n : ℤ)+1-i) * invFactorial ((p : ℤ)-i) *
    invFactorial ((i : ℤ)+1-d) * invFactorial ((n : ℤ)+i+2) *
    invFactorial ((p : ℤ)+i+1)

def endpointConstant (n p d : ℕ) : ℚ :=
  Nat.factorial (n-d) * Nat.factorial p * Nat.factorial (p-d) * Nat.factorial n *
    Nat.factorial (n+p+1) * invFactorial d * invFactorial ((n : ℤ)+p-d)

def signedEndpointConstant (n p d : ℕ) : ℚ :=
  Nat.factorial (n-d) * Nat.factorial (p-d) * Nat.factorial (n+p+1)

def endpointWeight (n p d i : ℕ) : ℚ :=
  endpointConstant n p d * (2*(i : ℚ)+1) * endpointKernel n p d i

def signedEndpointWeight (n p d i : ℕ) : ℚ :=
  (-1)^i * signedEndpointConstant n p d * (2*(i : ℚ)+1) * endpointKernel n p d i

def endpointFlux (n p d i : ℕ) : ℚ :=
  -((i : ℚ)*((i : ℚ)-d)*((p : ℚ)+i+1)*((n : ℚ)+i+2)*
    endpointConstant (n+1) p d * endpointKernel (n+1) p d i) /
      (((n : ℚ)+1-d)*((n : ℚ)+1)*((n : ℚ)+p+2))

def signedEndpointFlux (n p d i : ℕ) : ℚ :=
  -((-1)^i*((i : ℚ)-d)*((p : ℚ)+i+1)*((n : ℚ)+i+2)*
    signedEndpointConstant (n+1) p d * endpointKernel (n+1) p d i) /
      (((n : ℚ)+1-d)*((n : ℚ)+p+2))

end D5.S3.Quantum.Algebra.ZeitlinSixJ.RawRecurrence
