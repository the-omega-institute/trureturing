/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three continued native cusp germs for the original four-point identity. -/

import D5.S3.Analytic.LocalEvenSquareDescent
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointIdentityK

/-! The three continued native cusp germs for the original four-point identity. -/

set_option maxRecDepth 4096

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open Filter Set Metric
open scoped Topology
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeTwistedGroundRealization.SignQuotient
open FourPoint.FourPointChannelCoefficients
open FourPoint.OriginalFourMChargeGerm (diagonalSewn)
open OriginalFourMSectorContinuation
open OriginalFourMActualChart (parameter)
open OriginalFourPointChartGluing (Ω U_A U_B U_D doubleSlit)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain)
open D5.S3.Analytic.LocalEvenSquareDescent
open private isOpen_slitDomain from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private chargeSectorSewn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm

private abbrev GramPos (D : LatticeData) := Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))

private def slitDiagonal (D : LatticeData) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  projectOccupations D H K 0 (s - H - K + 1) P Q R S
    (fun betaL gammaL betaR gammaR => slitChargeSector D a betaL gammaL betaR gammaR t)

private theorem slitDiagonal_diff (D : LatticeData) (hD : GramPos D) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    DifferentiableOn ℂ (slitDiagonal D H K s P Q R S a) slitDomain := by
  have hSector (betaL gammaL betaR gammaR : Exponent D) :
      DifferentiableOn ℂ (slitChargeSector D a betaL gammaL betaR gammaR) slitDomain :=
    slitChargeSector_differentiableOn D hD a betaL gammaL betaR gammaR
  unfold slitDiagonal projectOccupations
  fun_prop

private theorem slitDiagonal_native (D : LatticeData) (hD : GramPos D) (h24 : D.rank = 24)
    (H K : ℕ) (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D)
    {w : ℂ} (hw : ‖w‖ < 1) :
    slitDiagonal D H K s P Q R S a (w ^ 2) =
      diagonalSewn D H K (s - H - K + 1) P Q R S a w := by
  unfold slitDiagonal diagonalSewn
  congr 1
  funext betaL gammaL betaR gammaR
  unfold slitChargeSector chargeSectorSewn
  apply tsum_congr
  intro q
  rw [slitChargeTerm_eq_native D hD h24 _ _ _ _ q hw]

private theorem slitDiagonal_cusp (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : GramPos D) (h24 : D.rank = 24) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    (fun t => slitDiagonal D H K s P Q R S a t) =ᶠ[𝓝 0]
      fun t => actualDiagonalNumerator D hD H K s P Q R S a (-t) := by
  let B := slitDiagonal D H K s P Q R S a
  let U := (fun z : ℂ => -z) ⁻¹' slitDomain
  let f := fun w : ℂ => B (w ^ 2)
  have hU : IsOpen U := isOpen_slitDomain.preimage continuous_neg
  have hf : DifferentiableOn ℂ f {z | -(z ^ 2) ∈ U} :=
    (slitDiagonal_diff D hD H K s P Q R S a).comp (differentiable_id.pow 2).differentiableOn
      (fun z hz => by simpa [U] using hz)
  obtain ⟨F, _, _, huniq⟩ := even_neg_square_descent_on hU hf
  have heven (w : ℂ) : f (-w) = f w := by simp [f]
  have hF := huniq (fun t => B (-t)) (Eventually.of_forall fun w => by
    rw [heven, neg_neg]
    change f w = (f w + f w) / 2
    ring)
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
    exact mem_ball_zero_iff.mp hw
  have hG := huniq (actualDiagonalNumerator D hD H K s P Q R S a) (by
    filter_upwards [(actualDiagonalNumerator_spec D hu hD H K s P Q R S a).2, hsmall] with w hw hs
    rwa [show f w = _ from slitDiagonal_native D hD h24 H K s P Q R S a hs,
      show f (-w) = _ from slitDiagonal_native D hD h24 H K s P Q R S a (by simpa using hs)])
  simpa only [neg_neg, Function.comp_def] using
    ((hF.symm.trans hG).comp_tendsto (show Tendsto (fun t : ℂ => -t) (𝓝 0) (𝓝 0) by
      simpa using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto))

private def slitLaurent (D : LatticeData) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  (-t) ^ (-((H : ℤ) + K)) * slitDiagonal D H K s P Q R S a t

private theorem slitLaurent_diff (D : LatticeData) (hD : GramPos D) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    DifferentiableOn ℂ (slitLaurent D H K s P Q R S a) Ω :=
  ((differentiable_id.neg.differentiableOn.zpow (.inl fun _ hz => neg_ne_zero.mpr hz.2))).mul
    ((slitDiagonal_diff D hD H K s P Q R S a).mono fun _ hz => hz.1)

private theorem slitLaurent_cusp (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : GramPos D) (h24 : D.rank = 24) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    slitLaurent D H K s P Q R S a =ᶠ[𝓝 0]
      fun t => laurent ((H : ℤ) + K) (actualDiagonalNumerator D hD H K s P Q R S a) (-t) :=
  (slitDiagonal_cusp D hu hD h24 H K s P Q R S a).mono fun t ht => by
    simp only [slitLaurent, laurent, ht]

/-- Continued A channel in its native parameter, with the original charge signs. -/
def slitChannelA (D : LatticeData) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D a * fourierSign D a b * slitLaurent D H K s P Q R S a t

private def slitLowered (D : LatticeData) (H K : ℕ) (s : ℤ) (N : ℕ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range N, loweringWeight s ell *
    slitLaurent D H K (s + ell) P Q R ((oscillatorLower D ^ ell) S) a t

private theorem slitLowered_diff (D : LatticeData) (hD : GramPos D) (H K : ℕ) (s : ℤ) (N : ℕ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    DifferentiableOn ℂ (slitLowered D H K s N P Q R S a) Ω := by
  unfold slitLowered
  apply DifferentiableOn.fun_sum
  intro ell _
  exact (slitLaurent_diff D hD _ _ _ _ _ _ _ _).const_mul _

private theorem slitLowered_cusp (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : GramPos D) (h24 : D.rank = 24) (H K : ℕ) (s : ℤ) (N : ℕ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    slitLowered D H K s N P Q R S a =ᶠ[𝓝 0]
      loweredLaurent ((H : ℤ) + K) s N
        (fun ell => actualDiagonalNumerator D hD H K (s + ell) P Q R
          ((oscillatorLower D ^ ell) S) a) := by
  filter_upwards [eventually_all_finset (Finset.range N) |>.mpr fun ell _ =>
    slitLaurent_cusp D hu hD h24 H K (s + ell) P Q R ((oscillatorLower D ^ ell) S) a] with t ht
  unfold slitLowered loweredLaurent
  exact Finset.sum_congr rfl fun ell he => congrArg (_ * ·) (ht ell he)

/-- Continued B channel with its native lowering weights. -/
def slitChannelB (D : LatticeData) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) : ℂ → ℂ :=
  slitLowered D K L (m + n + r) (loweringCutoff H K L m n r) Q R P S b

/-- Continued D channel in the inverse coordinate. -/
def slitChannelD (D : LatticeData) (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) (t : ℂ) : ℂ :=
  ∑ a, quadraticSign D (a + b) *
    slitLowered D H L (m + n + r) (loweringCutoff H K L m n r) P R Q S a t

/-- The explicit slit continuations are holomorphic and have all three actual cusp germs. -/
theorem slitChartGerms (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ)
    (P Q R S : Oscillator D) (b : ModTwoCharge D) :
    let A := slitChannelA D H K (m + n + r) P Q R S b
    let B := slitChannelB D H K L m n r P Q R S b
    let C := slitChannelD D H K L m n r P Q R S b
    DifferentiableOn ℂ A Ω ∧ DifferentiableOn ℂ B Ω ∧ DifferentiableOn ℂ C Ω ∧
      (A =ᶠ[𝓝[≠] 0] fun t => actualChannelA D hD H K (m + n + r) P Q R S b (-t)) ∧
      (B =ᶠ[𝓝[≠] 0] actualChannelB D hD H K L m n r P Q R S b) ∧
      (C =ᶠ[𝓝[≠] 0] actualChannelD D hD H K L m n r P Q R S b) := by
  dsimp only
  refine ⟨?_, slitLowered_diff D hD _ _ _ _ _ _ _ _ _, ?_, ?_,
    (slitLowered_cusp D hu hD h24 _ _ _ _ _ _ _ _ _).filter_mono nhdsWithin_le_nhds, ?_⟩
  · unfold slitChannelA
    apply DifferentiableOn.fun_sum
    intro a _
    exact (slitLaurent_diff D hD _ _ _ _ _ _ _ _).const_mul _
  · unfold slitChannelD
    apply DifferentiableOn.fun_sum
    intro a _
    exact (slitLowered_diff D hD _ _ _ _ _ _ _ _ _).const_mul _
  · apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
    filter_upwards [eventually_all.mpr fun a =>
      slitLaurent_cusp D hu hD h24 H K (m + n + r) P Q R S a] with t ht
    unfold slitChannelA actualChannelA
    exact Finset.sum_congr rfl fun a _ => congrArg (_ * ·) (ht a)
  · apply Filter.EventuallyEq.filter_mono _ nhdsWithin_le_nhds
    filter_upwards [eventually_all.mpr fun a => slitLowered_cusp D hu hD h24 H L (m + n + r)
      (loweringCutoff H K L m n r) P R Q S a] with t ht
    unfold slitChannelD actualChannelD
    exact Finset.sum_congr rfl fun a _ => congrArg (_ * ·) (ht a)

/-- Only the two interior crossing equalities for the explicit continued channels
are needed to derive the original identity for arbitrary signed modes. -/
theorem identityK_of_slitChart_crossing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D)
    (hcross : ∀ b : ModTwoCharge D,
      let A := slitChannelA D H K (m + n + r) P Q R S b
      let B := slitChannelB D H K L m n r P Q R S b
      let C := slitChannelD D H K L m n r P Q R S b
      ∃ x y : ℂ, x ∈ doubleSlit ∧
        (∃ᶠ z in 𝓝[≠] x,
          A (parameter .A z) = (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) * B (parameter .B z)) ∧
        ((y ∈ U_A ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y, A (parameter .A z) = C (parameter .D z)) ∨
         (y ∈ U_B ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y,
           (2 : ℂ) ^ 12 * z ^ (m + n + r + 2) * B (parameter .B z) = C (parameter .D z)))) :
    identityK D hu H K L m n r P Q R S := by
  apply identityK_of_native_chart_germs D hu hD H K L m n r P Q R S
  intro b
  obtain ⟨x, y, hx, hAB, hDOverlap⟩ := hcross b
  obtain ⟨hA, hB, hC, hAgerm, hBgerm, hCgerm⟩ := slitChartGerms D hu hD h24 H K L m n r P Q R S b
  exact ⟨_, _, _, x, y, hA, hB, hC, hx, hAB, hDOverlap, hAgerm, hBgerm, hCgerm⟩

#print axioms slitChartGerms
#print axioms identityK_of_slitChart_crossing

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
