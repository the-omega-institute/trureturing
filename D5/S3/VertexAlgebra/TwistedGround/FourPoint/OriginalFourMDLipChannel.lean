import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSector
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialOverlap

/-! Local continuation of the literal D channel and its interior overlap. -/

open Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open FourPoint.FourPointChannelCoefficients
open OriginalFourMSectorContinuation
open OriginalFourMPeriodSource (dLip)
open OriginalFourPointChartGluing (Ω isOpen_Ω U_A U_D rA rB rD radial_AB_overlap radial_AD_overlap)
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private slitDiagonal slitLaurent slitLowered slitLaurent_diff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

private def dLipLaurent (D : LatticeData) (upperA : Bool) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  (-t) ^ (-((H : ℤ) + K)) *
    projectOccupations D H K 0 (s - H - K + 1) P Q R S
      (fun betaL gammaL betaR gammaR =>
        dLipChargeSector D upperA a betaL gammaL betaR gammaR t)

private theorem dLipLaurent_analyticAt (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (upperA : Bool)
    (H K : ℕ) (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipLaurent D upperA H K s P Q R S a) (t : ℂ) := by
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hPow : AnalyticAt ℂ (fun r : ℂ => (-r) ^ (-((H : ℤ) + K))) (t : ℂ) :=
    analyticAt_id.neg.zpow (neg_ne_zero.mpr ht₀)
  have hSector (b c e f : Exponent D) :
      AnalyticAt ℂ (dLipChargeSector D upperA a b c e f) (t : ℂ) :=
    dLipChargeSector_analyticAt D hD upperA a b c e f ht
  unfold dLipLaurent
  apply hPow.mul
  unfold projectOccupations
  fun_prop

private theorem dLipLaurent_eq_slit (D : LatticeData) (upperA : Bool) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) {t : ℂ} (ht : t ∈ dLip upperA) :
    dLipLaurent D upperA H K s P Q R S a t = slitLaurent D H K s P Q R S a t := by
  unfold dLipLaurent slitLaurent slitDiagonal
  simp only [dLipChargeSector_eq_slit D upperA a _ _ _ _ ht]

def dLipChannel (D : LatticeData) (upperA : Bool) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D (a + b) *
    ∑ ell ∈ Finset.range (loweringCutoff H K L m n r), loweringWeight (m + n + r) ell *
      dLipLaurent D upperA H L (m + n + r + ell) P R Q ((oscillatorLower D ^ ell) S) a t

theorem dLipChannel_analyticAt (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (upperA : Bool)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipChannel D upperA H K L m n r P Q R S b) (t : ℂ) := by
  unfold dLipChannel
  apply Finset.analyticAt_fun_sum
  intro a _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro ell _
  exact analyticAt_const.mul (dLipLaurent_analyticAt D hD upperA _ _ _ _ _ _ _ _ ht)

theorem dLipChannel_eq_slit (D : LatticeData) (upperA : Bool)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D)
    {t : ℂ} (ht : t ∈ dLip upperA) :
    dLipChannel D upperA H K L m n r P Q R S b t = slitChannelD D H K L m n r P Q R S b t := by
  unfold dLipChannel slitChannelD slitLowered
  simp only [dLipLaurent_eq_slit D upperA _ _ _ _ _ _ _ _ ht]

/-- The real A/D check with the actual continued D channel supplies the
interior overlap used in the original residue identity. -/
theorem slit_AD_overlap (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (upperA : Bool) (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (b : ModTwoCharge D)
    {t : ℝ} (ht : 1 < t)
    (h : ∀ᶠ s : ℝ in 𝓝 t, slitChannelA D H K (m + n + r) P Q R S b (1 - (s : ℂ)) =
      dLipChannel D upperA H K L m n r P Q R S b (s : ℂ)) :
    ∃ y ∈ U_A ∩ U_D, ∃ᶠ z in 𝓝[≠] y,
      slitChannelA D H K (m + n + r) P Q R S b (rA z) =
        slitChannelD D H K L m n r P Q R S b (rD z) := by
  have hmem : 1 - (t : ℂ) ∈ Ω := by
    refine ⟨?_, sub_ne_zero.mpr (by exact_mod_cast ht.ne)⟩
    rw [sub_sub_cancel]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using (zero_lt_one.trans ht)))
  have hDiff : DifferentiableOn ℂ (slitChannelA D H K (m + n + r) P Q R S b) Ω := by
    unfold slitChannelA
    apply DifferentiableOn.fun_sum
    intro a _
    exact (slitLaurent_diff D hD _ _ _ _ _ _ _ _).const_mul _
  have hA := (hDiff.analyticOnNhd isOpen_Ω _ hmem).comp (f := fun u : ℂ => 1 - u)
    (analyticAt_const.sub analyticAt_id)
  exact radial_AD_overlap upperA hA
    (dLipChannel_analyticAt D hD upperA H K L m n r P Q R S b ht)
    h (eventuallyEq_nhdsWithin_of_eqOn fun _ hz =>
      dLipChannel_eq_slit D upperA H K L m n r P Q R S b hz)

/-- The original signed residue relation follows from the two coefficient
comparisons on the real common coordinate and the designated D boundary. -/
theorem identityK_of_radial_crossings (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (upperA : Bool) (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D)
    {x t : ℝ} (hx : 0 < x) (hx₁ : x < 1) (ht : 1 < t)
    (hAB : ∀ b : ModTwoCharge D, ∀ᶠ z : ℝ in 𝓝 x,
      slitChannelA D H K (m + n + r) P Q R S b (rA (z : ℂ)) =
        (2 : ℂ) ^ 12 * (z : ℂ) ^ (m + n + r + 2) *
          slitChannelB D H K L m n r P Q R S b (rB (z : ℂ)))
    (hAD : ∀ b : ModTwoCharge D, ∀ᶠ s : ℝ in 𝓝 t,
      slitChannelA D H K (m + n + r) P Q R S b (1 - (s : ℂ)) =
        dLipChannel D upperA H K L m n r P Q R S b (s : ℂ)) :
    identityK D hu H K L m n r P Q R S := by
  apply identityK_of_slitChart_crossing D hu hD h24 H K L m n r P Q R S
  intro b
  obtain ⟨hx', hAB'⟩ := radial_AB_overlap hx hx₁ (hAB b)
  obtain ⟨y, hy, hAD'⟩ := slit_AD_overlap D hD upperA H K L m n r P Q R S b ht (hAD b)
  exact ⟨(x : ℂ), y, hx', hAB', Or.inl ⟨hy, hAD'⟩⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
