/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original four-point mode identity from a common holomorphic function with the actual channel germs. -/

import D5.S3.AnalyticClosure.ThreePunctureResidue
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointChartGluing

/-! The original charge-coset identity from the three raw germs of one holomorphic function. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMActualChart (parameter)
open OriginalFourPointChartGluing (Ω U_A U_B U_D doubleSlit
  exists_common_four_point_germ)
open FourPoint.FourPointChannelCoefficients
open D5.S3.AnalyticClosure
open ThreePunctureResidue (aChart aChart_residue_invariant residue_sum_of_differential_expansions)

private theorem hasPrincipalPart_weighted_sum {ι : Type*} [Fintype ι]
    {N : ℕ} {f : ι → ℂ → ℂ} {s : ι → ℂ}
    (w : ι → ℂ) (h : ∀ a, HasPrincipalPart N (f a) (s a)) :
    HasPrincipalPart N (fun t ↦ ∑ a, w a * f a t) (∑ a, w a * s a) := by
  classical
  choose c W hW hc he using h
  refine ⟨fun j ↦ ∑ a, w a * c a j, fun t ↦ ∑ a, w a * W a t, ?_, ?_, ?_⟩
  · apply Finset.analyticAt_fun_sum
    intro a _
    exact analyticAt_const.mul (hW a)
  · by_cases hN : 0 < N
    · simp only [simpleCoeff, ite_eq_left hN] at hc ⊢
      simp only [hc]
    · simp only [simpleCoeff, ite_eq_right hN] at hc ⊢
      simp only [← hc, mul_zero, Finset.sum_const_zero]
  · filter_upwards [eventually_all.mpr he] with t ht
    simp only [ht, mul_add, Finset.sum_add_distrib, principalPart, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm (s := Finset.univ)]

private theorem hasPrincipalPart_const_mul {N : ℕ} {f : ℂ → ℂ} {s : ℂ}
    (w : ℂ) (h : HasPrincipalPart N f s) :
    HasPrincipalPart N (fun t ↦ w * f t) (w * s) := by
  obtain ⟨c, W, hW, hc, he⟩ := h
  refine ⟨fun j ↦ w * c j, fun t ↦ w * W t, analyticAt_const.mul hW, ?_, ?_⟩
  · rw [← hc]
    by_cases hN : 0 < N <;> simp [simpleCoeff, hN]
  · filter_upwards [he] with t ht
    simp only [ht, mul_add, principalPart, Finset.mul_sum, mul_assoc]

private theorem aChart_sub_one (z : ℂ) :
    aChart (z - 1) = (1 - z) / z := by
  rw [aChart, neg_sub, show 1 + (z - 1) = z by ring]

private theorem iterate_chart_weight {z : ℂ} (hz : z ≠ 0) (m r : ℤ) :
    let t := aChart (z - 1)
    t ^ r * (1 + t) ^ m * deriv aChart (z - 1) = -((1 - z) ^ r * z ^ (-m - r - 2)) := by
  have hden : 1 + (z - 1) ≠ 0 := by rwa [show 1 + (z - 1) = z by ring]
  have hd : deriv aChart (z - 1) = -((z ^ 2)⁻¹) := by
    have h : HasDerivAt aChart (-((1 + (z - 1)) ^ 2)⁻¹) (z - 1) := by
      convert (hasDerivAt_id (z - 1)).neg.fun_div
        ((hasDerivAt_id (z - 1)).const_add 1) hden using 1
      · ext y
        simp [aChart]
      · change -((1 + (z - 1)) ^ 2)⁻¹ =
          (-1 * (1 + (z - 1)) - (-(z - 1)) * 1) / (1 + (z - 1)) ^ 2
        rw [div_eq_mul_inv]
        have hnum : -1 * (1 + (z - 1)) - (-(z - 1)) * 1 = -1 := by ring
        rw [hnum, neg_one_mul]
    rw [h.deriv, show 1 + (z - 1) = z by ring]
  have ht : 1 + (1 - z) / z = z⁻¹ := by
    rw [one_add_div hz, show z + (1 - z) = 1 by ring, one_div]
  dsimp only
  rw [hd, aChart_sub_one, ht, div_zpow, inv_zpow, ← zpow_neg, div_eq_mul_inv, ← zpow_neg,
    ← zpow_natCast z 2, ← zpow_neg]
  calc
    _ = -((1 - z) ^ r * (z ^ (-m) * z ^ (-r) * z ^ (-2 : ℤ))) := by ring_nf
    _ = _ := by
      rw [← zpow_add₀ hz, ← zpow_add₀ hz]
      rfl

private theorem inverse_chart_weight {u : ℂ} (hu : u ≠ 0) (m r : ℤ) :
    (1 - u⁻¹) ^ r * (u⁻¹) ^ (-m - r - 2) * deriv (fun v : ℂ ↦ v⁻¹) u =
      -(u ^ m * (u - 1) ^ r) := by
  have ht : 1 - u⁻¹ = (u - 1) / u := by
    field_simp [hu]
  rw [(hasDerivAt_inv hu).deriv, ht, div_zpow, inv_zpow, ← zpow_neg, div_eq_mul_inv,
    ← zpow_neg, ← zpow_natCast u 2, ← zpow_neg]
  calc
    _ = -((u - 1) ^ r * (u ^ (-r) * u ^ (-(-m - r - 2)) * u ^ (-2 : ℤ))) := by ring_nf
    _ = -((u - 1) ^ r * u ^ m) := by
      rw [← zpow_add₀ hu, ← zpow_add₀ hu, show -r + -(-m - r - 2) + -2 = m by omega]
    _ = _ := by rw [mul_comm]

/-- For each output sector, the three native punctured germs of a common holomorphic
function imply the original charge-coset identity. The numerator hypotheses identify
the Taylor coefficients with the native diagonal coset kernels. -/
theorem identityK_of_common_four_point_germ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D)
    (UA : ModTwoCharge D → ℂ → ℂ) (UB UD : ModTwoCharge D → ℕ → ℂ → ℂ)
    (hUA : ∀ a, IsDiagonalNumerator D hu H K (m + n + r) P Q R S a (UA a))
    (hUB : ∀ b ell, ell < loweringCutoff H K L m n r →
      IsDiagonalNumerator D hu K L (m + n + r + (ell : ℤ)) Q R P
        ((oscillatorLower D ^ ell) S) b (UB b ell))
    (hUD : ∀ a ell, ell < loweringCutoff H K L m n r →
      IsDiagonalNumerator D hu H L (m + n + r + (ell : ℤ)) P R Q
        ((oscillatorLower D ^ ell) S) a (UD a ell))
    (hGerm : ∀ b : ModTwoCharge D, ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F ({0, 1}ᶜ : Set ℂ) ∧
      (F =ᶠ[𝓝[≠] 1] fun z ↦ ∑ a, quadraticSign D a * fourierSign D a b *
        laurent ((H : ℤ) + (K : ℤ)) (UA a) ((1 - z) / z)) ∧
      (F =ᶠ[𝓝[≠] 0] fun z ↦ (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) *
        loweredLaurent ((K : ℤ) + (L : ℤ)) (m + n + r)
          (loweringCutoff H K L m n r) (UB b) z) ∧
      ((fun u ↦ F u⁻¹) =ᶠ[𝓝[≠] 0] fun u ↦ ∑ a, quadraticSign D (a + b) *
        loweredLaurent ((H : ℤ) + (L : ℤ)) (m + n + r)
          (loweringCutoff H K L m n r) (UD a) u)) :
    identityK D hu H K L m n r P Q R S := by
  classical
  intro b
  obtain ⟨F, hF, hFA, hFB, hFD⟩ := hGerm b
  let G : ℂ → ℂ := fun z ↦ (1 - z) ^ r * z ^ (-m - r - 2) * F z
  have hG (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) : DifferentiableAt ℂ G z := by
    have hf : DifferentiableAt ℂ F z := by
      apply hF.differentiableAt
      filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hz1] with y hy0 hy1
      simpa using And.intro hy0 hy1
    exact (((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).zpow
      (Or.inl (sub_ne_zero.mpr hz1.symm))).mul
      (differentiableAt_id.zpow (Or.inl hz0)) |>.mul hf

  -- At zero the two powers of z combine to z^n.
  let gB := loweredLaurent ((K : ℤ) + (L : ℤ)) (m + n + r)
    (loweringCutoff H K L m n r) (UB b)
  have hWeightedB : G =ᶠ[𝓝[≠] 0] fun z ↦ (2 : ℂ) ^ 12 * (z ^ n * (1 - z) ^ r * gB z) := by
    filter_upwards [hFB, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have hzpow : z ^ (-m - r - 2) * z ^ (m + n + r + 2) = z ^ n := by
      rw [← zpow_add₀ hz0', show -m - r - 2 + (m + n + r + 2) = n by omega]
    change (1 - z) ^ r * z ^ (-m - r - 2) * F z = _
    rw [hz]
    change (1 - z) ^ r * z ^ (-m - r - 2) *
      ((2 : ℂ) ^ 12 * z ^ (m + n + r + 2) * gB z) = _
    linear_combination ((2 : ℂ) ^ 12 * (1 - z) ^ r * gB z) * hzpow
  obtain ⟨cB, WB, hWB, hcB, heB⟩ := hasPrincipalPart_const_mul ((2 : ℂ) ^ 12)
    (hasPrincipalPart_channelB D hu hD H K L m n r P Q R S b (hUB b))
  have hExpB : G =ᶠ[𝓝[≠] 0] fun z ↦
      ThreePunctureResidue.principalPart 0 ((K : ℤ) + (L : ℤ) - n).toNat cB z + WB z := by
    simpa only [ThreePunctureResidue.principalPart, sub_zero, principalPart] using
      hWeightedB.trans heB

  -- At one use the iterate coordinate t = -u/(1+u), with u = z - 1.
  let fA (a : ModTwoCharge D) := laurent ((H : ℤ) + (K : ℤ)) (UA a)
  let wA (a : ModTwoCharge D) := -(quadraticSign D a * fourierSign D a b)
  let A : ℂ → ℂ := fun t ↦ ∑ a, wA a * (t ^ r * (1 + t) ^ m * fA a t)
  have hA : HasPrincipalPart ((H : ℤ) + (K : ℤ) - r).toNat A
      (∑ a, wA a * channelA D hu H K m n r P Q R S a) :=
    hasPrincipalPart_weighted_sum wA fun a ↦ hasPrincipalPart_channelA D hu hD H K m n r
      P Q R S a (hUA a)
  obtain ⟨cA, WA, hWA, hcA, heA⟩ := hA
  have heA' : A =ᶠ[𝓝[≠] 0] fun t ↦
      ThreePunctureResidue.principalPart 0 ((H : ℤ) + (K : ℤ) - r).toNat cA t + WA t := by
    simpa only [ThreePunctureResidue.principalPart, sub_zero, principalPart] using heA
  obtain ⟨c1, W1, hW1, he1, hc1⟩ := aChart_residue_invariant hWA heA'
  have hShift : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) 1 := by fun_prop
  have hTendsto : Tendsto (fun z : ℂ ↦ z - 1) (𝓝[≠] 1) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have ht : Tendsto (fun z : ℂ ↦ z - 1) (𝓝[≠] 1) (𝓝 ((1 : ℂ) - 1)) :=
        hShift.continuousAt.continuousWithinAt
      simpa only [sub_self] using ht
    · filter_upwards [self_mem_nhdsWithin (s := ({1}ᶜ : Set ℂ)) (a := (1 : ℂ))] with z hz
      exact sub_ne_zero.mpr hz
  have hW1' : AnalyticAt ℂ (fun z ↦ W1 (z - 1)) 1 := by
    exact AnalyticAt.comp_of_eq (f := fun z : ℂ ↦ z - 1) hW1 hShift (sub_self 1)
  have hWeightedA : G =ᶠ[𝓝[≠] 1] fun z ↦ A (aChart (z - 1)) * deriv aChart (z - 1) := by
    filter_upwards [hFA, eventually_ne_nhdsWithin (s := ({1}ᶜ : Set ℂ))
      (show (1 : ℂ) ≠ 0 by norm_num)] with z hz hz0
    change (1 - z) ^ r * z ^ (-m - r - 2) * F z = _
    rw [hz]
    unfold A
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hweight := iterate_chart_weight hz0 m r
    dsimp only at hweight
    rw [← aChart_sub_one z]
    dsimp only [wA, fA]
    linear_combination
      (quadraticSign D a * fourierSign D a b * laurent ((H : ℤ) + (K : ℤ))
        (UA a) (aChart (z - 1))) * hweight
  have hExpA : G =ᶠ[𝓝[≠] 1] fun z ↦
      ThreePunctureResidue.principalPart 1 ((H : ℤ) + (K : ℤ) - r).toNat c1 z +
        W1 (z - 1) := by
    simpa only [Function.comp_def, ThreePunctureResidue.principalPart, sub_zero] using
      hWeightedA.trans (he1.comp_tendsto hTendsto)

  -- At infinity the inverse derivative supplies the minus sign.
  let gD (a : ModTwoCharge D) := loweredLaurent ((H : ℤ) + (L : ℤ)) (m + n + r)
    (loweringCutoff H K L m n r) (UD a)
  let wD (a : ModTwoCharge D) := -quadraticSign D (a + b)
  have hWeightedD : (fun u : ℂ ↦ G u⁻¹ * deriv (fun v : ℂ ↦ v⁻¹) u) =ᶠ[𝓝[≠] 0]
      fun u ↦ ∑ a, wD a * (u ^ m * (u - 1) ^ r * gD a u) := by
    filter_upwards [hFD, self_mem_nhdsWithin] with u hFu hu0
    have hu0' : u ≠ 0 := hu0
    change (1 - u⁻¹) ^ r * (u⁻¹) ^ (-m - r - 2) * F u⁻¹ *
      deriv (fun v : ℂ ↦ v⁻¹) u = _
    change F u⁻¹ = ∑ a, quadraticSign D (a + b) * gD a u at hFu
    rw [hFu, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    dsimp only [wD]
    linear_combination (quadraticSign D (a + b) * gD a u) * inverse_chart_weight hu0' m r
  obtain ⟨cD, WD, hWD, hcD, heD⟩ := hasPrincipalPart_weighted_sum wD
    (fun a ↦ hasPrincipalPart_channelD D hu hD H K L m n r P Q R S a (hUD a))
  have hExpD : (fun u : ℂ ↦ G u⁻¹ * deriv (fun v : ℂ ↦ v⁻¹) u) =ᶠ[𝓝[≠] 0]
      fun u ↦ ThreePunctureResidue.principalPart 0 ((H : ℤ) + (L : ℤ) - m).toNat cD u +
        WD u := by
    simpa only [ThreePunctureResidue.principalPart, sub_zero, principalPart] using
      hWeightedD.trans heD

  have hResidues := residue_sum_of_differential_expansions hG hWB hW1' hWD hExpB hExpA hExpD
  change simpleCoeff _ cB + simpleCoeff _ c1 + simpleCoeff _ cD = 0 at hResidues
  change simpleCoeff _ c1 = simpleCoeff _ cA at hc1
  rw [hcB, hc1, hcA, hcD] at hResidues
  simp only [wA, wD, neg_mul, Finset.sum_neg_distrib] at hResidues
  linear_combination -hResidues

/-- The actual iterate germ in the residue coordinate. -/
def actualChannelA (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D a * fourierSign D a b *
    laurent ((H : ℤ) + K) (actualDiagonalNumerator D hD H K s P Q R S a) t

/-- The actual B germ in its native coordinate, before the chart prefactor. -/
def actualChannelB (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) : ℂ → ℂ :=
  loweredLaurent ((K : ℤ) + L) (m + n + r) (loweringCutoff H K L m n r)
    (fun ell ↦ actualDiagonalNumerator D hD K L (m + n + r + (ell : ℤ))
      Q R P ((oscillatorLower D ^ ell) S) b)

/-- The actual D germ in the inverse coordinate. -/
def actualChannelD (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D (a + b) *
    loweredLaurent ((H : ℤ) + L) (m + n + r) (loweringCutoff H K L m n r)
      (fun ell ↦ actualDiagonalNumerator D hD H L (m + n + r + (ell : ℤ))
        P R Q ((oscillatorLower D ^ ell) S) a) t

/-- A common holomorphic function with the three actual germs implies the original
charge-coset identity for all signed modes. The numerator data come from the sewn sums. -/
theorem identityK_of_common_actual_channel_germs (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D)
    (hGerm : ∀ b : ModTwoCharge D, ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F ({0, 1}ᶜ : Set ℂ) ∧
      (F =ᶠ[𝓝[≠] 1] fun z ↦ actualChannelA D hD H K (m + n + r) P Q R S b ((1 - z) / z)) ∧
      (F =ᶠ[𝓝[≠] 0] fun z ↦ (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) *
        actualChannelB D hD H K L m n r P Q R S b z) ∧
      ((fun u ↦ F u⁻¹) =ᶠ[𝓝[≠] 0] actualChannelD D hD H K L m n r P Q R S b)) :
    identityK D hu H K L m n r P Q R S :=
  identityK_of_common_four_point_germ D hu hD H K L m n r P Q R S
    (fun a ↦ actualDiagonalNumerator D hD H K (m + n + r) P Q R S a)
    (fun b ell ↦ actualDiagonalNumerator D hD K L (m + n + r + (ell : ℤ))
      Q R P ((oscillatorLower D ^ ell) S) b)
    (fun a ell ↦ actualDiagonalNumerator D hD H L (m + n + r + (ell : ℤ))
      P R Q ((oscillatorLower D ^ ell) S) a)
    (fun a ↦ (actualDiagonalNumerator_spec D hu hD H K _ P Q R S a).1)
    (fun b ell _ ↦ (actualDiagonalNumerator_spec D hu hD K L _ Q R P
      ((oscillatorLower D ^ ell) S) b).1)
    (fun a ell _ ↦ (actualDiagonalNumerator_spec D hu hD H L _ P R Q
      ((oscillatorLower D ^ ell) S) a).1)
    hGerm

/-- Native continuations with the specified local germs and two interior overlap
equalities give the original identity by gluing and taking residues. -/
theorem identityK_of_native_chart_germs (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D)
    (hCharts : ∀ b : ModTwoCharge D, ∃ (A B C : ℂ → ℂ) (x y : ℂ),
      DifferentiableOn ℂ A Ω ∧ DifferentiableOn ℂ B Ω ∧ DifferentiableOn ℂ C Ω ∧
      x ∈ doubleSlit ∧
      (∃ᶠ z in 𝓝[≠] x,
        A (parameter .A z) = (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) * B (parameter .B z)) ∧
      ((y ∈ U_A ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y, A (parameter .A z) = C (parameter .D z)) ∨
       (y ∈ U_B ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y,
         (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) * B (parameter .B z) = C (parameter .D z))) ∧
      (A =ᶠ[𝓝[≠] 0] fun t ↦ actualChannelA D hD H K (m + n + r) P Q R S b (-t)) ∧
      (B =ᶠ[𝓝[≠] 0] actualChannelB D hD H K L m n r P Q R S b) ∧
      (C =ᶠ[𝓝[≠] 0] actualChannelD D hD H K L m n r P Q R S b)) :
    identityK D hu H K L m n r P Q R S := by
  apply identityK_of_common_actual_channel_germs D hu hD H K L m n r P Q R S
  intro b
  obtain ⟨A, B, C, x, y, hA, hB, hC, hx, hAB, hDOverlap, hAgerm, hBgerm, hCgerm⟩ := hCharts b
  exact exists_common_four_point_germ (m + n + r + 2)
    hA hB hC hx hAB hDOverlap hAgerm hBgerm hCgerm

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
