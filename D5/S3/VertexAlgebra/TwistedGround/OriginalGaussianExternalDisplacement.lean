/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalDisplacement
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalDisplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed displacement contracted against the actual all-mode external columns. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequency

/-! All frequency factors act on actual summable external columns. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianDifferentiation
open OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianBilinearTranspose

/-- The signed finite difference includes the predecessor input zero column. -/
def modeFrequency (out : Bool) (p : ℕ) (f : Bool → ℕ → ℂ) : ℂ :=
  externalParameter out p * (f out p - f (predecessor out p).1 (predecessor out p).2)

private lemma frequency_pair_left (out : Bool) (p : ℕ) (z : ℂ) (y : H) :
    sourceBilinearFunctional (frequencyVector out p z) y =
      modeFrequency out p (fun e k => sourceBilinearFunctional (externalVector e k z) y) := by
  rw [sourceBilinearFunctional_comm, frequencyVector, map_smul, map_sub]
  simp only [smul_eq_mul, modeFrequency]
  rw [sourceBilinearFunctional_comm y, sourceBilinearFunctional_comm y]

private lemma frequency_pair_right (out : Bool) (p : ℕ) (z : ℂ) (y : H)
    (A : H →L[ℂ] H) :
    sourceBilinearFunctional y (A (frequencyVector out p z)) =
      modeFrequency out p (fun e k => sourceBilinearFunctional y (A (externalVector e k z))) := by
  simp only [frequencyVector, map_smul, map_sub, smul_eq_mul, modeFrequency]

private lemma weighted_expansion_left (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    sourceBilinearFunctional (frequencyVector out p z) (A (externalVector out' q z)) =
      ∑' st : ℕ × ℕ, (st.1 + 1 : ℂ) * externalColumn out p z st.1 *
        A (basis st.2) st.1 * externalColumn out' q z st.2 := by
  rw [frequency_pair_left]
  simp only [modeFrequency, sourceBilinearFunctional]
  rw [external_bilinear_expansion out p out' q hz A,
    external_bilinear_expansion (predecessor out p).1 (predecessor out p).2 out' q hz A,
    ← (external_double_summable out p out' q hz A).of_norm.tsum_sub
      (external_double_summable (predecessor out p).1 (predecessor out p).2 out' q hz A).of_norm,
    ← tsum_mul_left]
  apply tsum_congr
  intro st
  have h := frequencyVector_apply out p hz st.1
  change externalParameter out p *
    (externalVector out p z st.1 -
      externalVector (predecessor out p).1 (predecessor out p).2 z st.1) = _ at h
  rw [externalVector_apply out p hz,
    externalVector_apply (predecessor out p).1 (predecessor out p).2 hz] at h
  linear_combination A (basis st.2) st.1 * externalColumn out' q z st.2 * h

private lemma weighted_expansion_right (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    sourceBilinearFunctional (externalVector out p z) (A (frequencyVector out' q z)) =
      ∑' st : ℕ × ℕ, externalColumn out p z st.1 * A (basis st.2) st.1 *
        ((st.2 + 1 : ℂ) * externalColumn out' q z st.2) := by
  rw [frequency_pair_right]
  simp only [modeFrequency, sourceBilinearFunctional]
  rw [external_bilinear_expansion out p out' q hz A,
    external_bilinear_expansion out p (predecessor out' q).1 (predecessor out' q).2 hz A,
    ← (external_double_summable out p out' q hz A).of_norm.tsum_sub
      (external_double_summable out p (predecessor out' q).1 (predecessor out' q).2 hz A).of_norm,
    ← tsum_mul_left]
  apply tsum_congr
  intro st
  have h := frequencyVector_apply out' q hz st.2
  change externalParameter out' q *
    (externalVector out' q z st.2 -
      externalVector (predecessor out' q).1 (predecessor out' q).2 z st.2) = _ at h
  rw [externalVector_apply out' q hz,
    externalVector_apply (predecessor out' q).1 (predecessor out' q).2 hz] at h
  linear_combination externalColumn out p z st.1 * A (basis st.2) st.1 * h

private lemma weighted_summable_left (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    Summable (fun st : ℕ × ℕ => (st.1 + 1 : ℂ) * externalColumn out p z st.1 *
      A (basis st.2) st.1 * externalColumn out' q z st.2) := by
  have h₁ := (external_double_summable out p out' q hz A).of_norm
  have h₂ := (external_double_summable (predecessor out p).1
    (predecessor out p).2 out' q hz A).of_norm
  apply ((h₁.sub h₂).mul_left (externalParameter out p)).congr
  intro st
  have h := frequencyVector_apply out p hz st.1
  change externalParameter out p *
    (externalVector out p z st.1 -
      externalVector (predecessor out p).1 (predecessor out p).2 z st.1) = _ at h
  rw [externalVector_apply out p hz,
    externalVector_apply (predecessor out p).1 (predecessor out p).2 hz] at h
  linear_combination A (basis st.2) st.1 * externalColumn out' q z st.2 * h

private lemma weighted_summable_right (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (A : H →L[ℂ] H) :
    Summable (fun st : ℕ × ℕ => externalColumn out p z st.1 * A (basis st.2) st.1 *
      ((st.2 + 1 : ℂ) * externalColumn out' q z st.2)) := by
  have h₁ := (external_double_summable out p out' q hz A).of_norm
  have h₂ := (external_double_summable out p (predecessor out' q).1
    (predecessor out' q).2 hz A).of_norm
  apply ((h₁.sub h₂).mul_left (externalParameter out' q)).congr
  intro st
  have h := frequencyVector_apply out' q hz st.2
  change externalParameter out' q *
    (externalVector out' q z st.2 -
      externalVector (predecessor out' q).1 (predecessor out' q).2 z st.2) = _ at h
  rw [externalVector_apply out' q hz,
    externalVector_apply (predecessor out' q).1 (predecessor out' q).2 hz] at h
  linear_combination externalColumn out p z st.1 * A (basis st.2) st.1 * h

private lemma product_expansion (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) (a b : H) :
    sourceBilinearFunctional (externalVector out p z) a *
      sourceBilinearFunctional (externalVector out' q z) b =
      ∑' st : ℕ × ℕ, externalColumn out p z st.1 * a st.1 *
        (externalColumn out' q z st.2 * b st.2) := by
  have hs (e : Bool) (k : ℕ) (v : H) :
      Summable (fun n : ℕ => ‖externalColumn e k z n * v n‖) := by
    simpa only [norm_mul, externalVector_apply e k hz] using
      (lp.summable_mul (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two)
        (externalVector e k z) v)
  rw [sourceBilinearFunctional_apply, sourceBilinearFunctional_apply]
  simp_rw [externalVector_apply out p hz, externalVector_apply out' q hz]
  exact tsum_mul_tsum_of_summable_norm (hs out p a) (hs out' q b)

private lemma signed_contraction (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    let z : ℂ := Real.sqrt r
    let w := weightedSource r hr hr1
    (sourceBilinearFunctional (frequencyVector out p z)
      (resolvent z (externalVector out' q z)) -
      sourceBilinearFunctional (externalVector out p z)
        (oppositeResolvent z (frequencyVector out' q z)) =
      sourceBilinearFunctional (externalVector out p z) (oppositeResolvent z w) *
        sourceBilinearFunctional (externalVector out' q z) (resolvent z w)) ∧
    (sourceBilinearFunctional (frequencyVector out p z)
      (oppositeResolvent z (externalVector out' q z)) -
      sourceBilinearFunctional (externalVector out p z)
        (resolvent z (frequencyVector out' q z)) =
      -(sourceBilinearFunctional (externalVector out p z) (resolvent z w) *
        sourceBilinearFunctional (externalVector out' q z) (oppositeResolvent z w))) := by
  dsimp only
  have hz := radial_norm_lt_one hr1
  rw [weighted_expansion_left out p out' q hz,
    weighted_expansion_right out p out' q hz,
    weighted_expansion_left out p out' q hz,
    weighted_expansion_right out p out' q hz,
    product_expansion out p out' q hz, product_expansion out p out' q hz,
    ← (weighted_summable_left out p out' q hz _).tsum_sub
      (weighted_summable_right out p out' q hz _),
    ← (weighted_summable_left out p out' q hz _).tsum_sub
      (weighted_summable_right out p out' q hz _), ← tsum_neg]
  constructor <;> apply tsum_congr <;> intro st
  · have h := (OriginalGaussianDisplacement.signed_resolvent_displacement
      hr hr1 st.1 st.2).1
    linear_combination externalColumn out p (Real.sqrt r : ℂ) st.1 *
      externalColumn out' q (Real.sqrt r : ℂ) st.2 * h
  · have h := (OriginalGaussianDisplacement.signed_resolvent_displacement
      hr hr1 st.1 st.2).2
    linear_combination externalColumn out p (Real.sqrt r : ℂ) st.1 *
      externalColumn out' q (Real.sqrt r : ℂ) st.2 * h

/-- Both raw finite source equations hold for every pair of original signed external modes. -/
theorem external_displacement (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    let z : ℂ := Real.sqrt r
    let w := weightedSource r hr hr1
    let a := fun e k => sourceBilinearFunctional (externalVector e k z)
      (oppositeResolvent z w)
    let b := fun e k => sourceBilinearFunctional (externalVector e k z) (resolvent z w)
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) =
        (a out p * b out' q + b out p * a out' q) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
        (a out p * b out' q - b out p * a out' q) / 2) := by
  dsimp only
  let z : ℂ := Real.sqrt r
  let X := externalVector out p z
  let Y := externalVector out' q z
  let DX := frequencyVector out p z
  let DY := frequencyVector out' q z
  have hz : ‖z‖ < 1 := radial_norm_lt_one hr1
  have h := signed_contraction out p out' q hr hr1
  dsimp only at h
  have hS : squareResolvent z = (1 / 2 : ℂ) • (resolvent z + oppositeResolvent z) := by
    rw [(signed_square_factorization hz).1, (signed_square_factorization hz).2]
    have he : (1 + operator z) * squareResolvent z +
        (1 - operator z) * squareResolvent z = (2 : ℂ) • squareResolvent z := by
      rw [two_smul]
      noncomm_ring
    rw [he, smul_smul]
    norm_num
  have hj (e : Bool) (k : ℕ) (f : Bool) (l : ℕ) :
      sourceBilinearFunctional (externalVector e k z)
        (oddResolvent z (externalVector f l z)) = externalJ e k f l z :=
    (external_contractions_explicit e k f l hz).2.2.1
  have ht (e : Bool) (k : ℕ) (f : Bool) (l : ℕ) :
      sourceBilinearFunctional (externalVector e k z)
        (squareResolvent z (externalVector f l z)) = externalT e k f l z :=
    (external_contractions_explicit e k f l hz).2.2.2.1
  have hjl : sourceBilinearFunctional DX (oddResolvent z Y) =
      modeFrequency out p (fun e k => externalJ e k out' q z) := by
    rw [frequency_pair_left]
    simp only [modeFrequency, hj, Y]
  have hjr : sourceBilinearFunctional X (oddResolvent z DY) =
      modeFrequency out' q (fun e k => externalJ out p e k z) := by
    rw [frequency_pair_right]
    simp only [modeFrequency, hj, X]
  have htl : sourceBilinearFunctional DX (squareResolvent z Y) =
      modeFrequency out p (fun e k => externalT e k out' q z) := by
    rw [frequency_pair_left]
    simp only [modeFrequency, ht, Y]
  have htr : sourceBilinearFunctional X (squareResolvent z DY) =
      modeFrequency out' q (fun e k => externalT out p e k z) := by
    rw [frequency_pair_right]
    simp only [modeFrequency, ht, X]
  change _ = _ ∧ _ = _
  rw [← hjl, ← hjr, ← htl, ← htr, odd_eq_half_difference hz, hS]
  change sourceBilinearFunctional DX
      ((1 / 2 : ℂ) • (resolvent z Y - oppositeResolvent z Y)) +
      sourceBilinearFunctional X
        ((1 / 2 : ℂ) • (resolvent z DY - oppositeResolvent z DY)) = _ ∧
    sourceBilinearFunctional DX
      ((1 / 2 : ℂ) • (resolvent z Y + oppositeResolvent z Y)) -
      sourceBilinearFunctional X
        ((1 / 2 : ℂ) • (resolvent z DY + oppositeResolvent z DY)) = _
  simp only [map_smul, map_sub, map_add, smul_eq_mul]
  constructor
  · linear_combination (h.1 - h.2) / 2
  · linear_combination (h.1 + h.2) / 2

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement
