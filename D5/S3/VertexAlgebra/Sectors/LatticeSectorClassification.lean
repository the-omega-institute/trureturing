/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorClassification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native ground-evaluation classification of actual neutral-sector intertwiners. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorGroundRigidity

/-!
The ground uniqueness argument is a coefficient induction using the actual
current commutant and conformal zero mode. It starts from the statewise
truncation of the one ground pair. The two oscillator recurrences then
reconstruct the full IO, independently of an occurrence enumeration.
The inverse Gram hypotheses are over complex matrices in both orders.
This is classical Heisenberg-sector mathematics, not a novelty claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeAllStateField
open LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeActualConformalState
open MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

private theorem action_conformal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (δ : Charge D) (n : ℤ) :
    action D δ (conformalPolynomial D H) n = sectorSugawaraMode D H δ (n - 1) := by
  apply LinearMap.ext
  intro v
  have h := single_action D δ (conformalPolynomial D H) v n
  change Finsupp.single δ _ = ((Y D (omega D H))[[n]]) (Finsupp.single δ v) at h
  rw [← show n - 1 + 1 = n by omega, omega_modes, sugawaraMode_single_sector] at h
  simpa [action, canonical, inclusion, projection, sectorSugawaraMode] using
    congrArg (fun w : Carrier D => w δ) h

private theorem conformal_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (δ : Charge D) :
    action D δ (conformalPolynomial D H) 1 1 = ((bilinear D δ δ : ℂ) / 2) • (1 : Oscillator D) := by
  rw [action_conformal]
  have h := congrArg (fun w : Carrier D => w δ) (sugawaraMode_ground_zero D H δ)
  rw [chargeQuadratic_eq D H hHG hGH] at h
  simpa [sectorSugawaraMode] using h

theorem conformal_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (δ : Charge D) :
    action D δ (conformalPolynomial D H) 0 = sectorT D δ := by
  rw [action_conformal]
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : Module.End ℂ (Carrier D) => (f (Finsupp.single δ v)) δ)
    (sugawaraMode_minus_one_eq_translation D H hHG hGH)
  simpa [sectorSugawaraMode, sectorT, sectorTranslation] using h

private theorem scalar_ground_constraint (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (I : IO D α β (α + β)) (n : ℤ)
    (hs : I.val 1 n 1 = constantCoeff (I.val 1 n 1) • (1 : Oscillator D)) :
    ((n : ℂ) + (bilinear D α β : ℂ) + 1) * constantCoeff (I.val 1 n 1) = 0 := by
  let a := conformalPolynomial D H
  have h := (ward D α β (α + β) I a 1 1 1 n).2
  have left : (∑ᶠ j : ℕ, leftTerm D α β (α + β) I.val a 1 1 1 n 0 j) =
      I.val (sectorT D α 1) (n + 1) 1 +
        ((bilinear D α α : ℂ) / 2) • I.val 1 n 1 := by
    have finite : Function.support (leftTerm D α β (α + β) I.val a 1 1 1 n 0) ⊆
        ({0, 1} : Finset ℕ) := by
      intro j hj
      by_contra outside
      have high : 1 < j := by simp at outside; omega
      have choose : Ring.choose (1 : ℤ) j = 0 := by
        simpa using (Ring.choose_natCast (R := ℤ) 1 j).trans
          (by simp [Nat.choose_eq_zero_of_lt high])
      exact hj (by simp [leftTerm, integerBinomial, choose])
    rw [finsum_eq_sum_of_support_subset _ finite]
    simp only [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), leftTerm,
      integerBinomial, Ring.choose_zero_right, Ring.choose_one_right,
      Int.cast_one, one_smul, Nat.cast_zero, Nat.cast_one, zero_add,
      add_zero, sub_zero, add_sub_cancel_left]
    rw [conformal_translation D H hHG hGH, conformal_ground D H hHG hGH]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
    simp only [show 1 + n = n + 1 by omega, show 1 + n - 1 = n by omega]
  rw [left] at h
  have derivative := congrArg (fun f : Sector D β →ₗ[ℂ] Sector D (α + β) => f 1)
    (I.property.source 1 (n + 1))
  simp only [LinearMap.smul_apply, show n + 1 - 1 = n by omega] at derivative
  rw [derivative, conformal_ground D H hHG hGH β, map_smul] at h
  have target : action D (α + β) a 1 (I.val 1 n 1) =
      ((bilinear D (α + β) (α + β) : ℂ) / 2) • I.val 1 n 1 := by
    rw [hs, map_smul, conformal_ground D H hHG hGH]
    rw [smul_comm]
  rw [target] at h
  have cross : (bilinear D (α + β) (α + β) : ℂ) =
      (bilinear D α α : ℂ) + 2 * (bilinear D α β : ℂ) + (bilinear D β β : ℂ) := by
    have e : bilinear D (α + β) (α + β) =
        bilinear D α α + 2 * bilinear D α β + bilinear D β β := by
      rw [LatticeActualGeneratorLocality.bilinear_add_right,
        bilinear_symmetric D (α + β) α, LatticeActualGeneratorLocality.bilinear_add_right,
        bilinear_symmetric D (α + β) β, LatticeActualGeneratorLocality.bilinear_add_right,
        bilinear_symmetric D β α]
      ring
    exact_mod_cast e
  have scalar := congrArg (constantCoeff : Oscillator D →+* ℂ) h
  simp only [map_sub, map_add, MvPolynomial.constantCoeff_smul, smul_eq_mul] at scalar
  rw [cross] at scalar
  push_cast at scalar
  linear_combination scalar

/-- A single normalized ground coefficient detects every IO in the sum sector. -/
theorem normalized_ground_detects_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (I : IO D α β (α + β))
    (heval : constantCoeff (I.val 1 (-bilinear D α β - 1) 1) = 0) : I = 0 := by
  have step (n : ℤ) (higher : ∀ m : ℤ, n < m → I.val 1 m 1 = 0) :
      I.val 1 n 1 = 0 := by
    have positive (i : Fin D.rank) (r : ℕ) :
        neutralPolynomialMode D i (α + β) ((r : ℤ) + 1) (I.val 1 n 1) = 0 := by
      have h := ground_current_ward D α β (α + β) I i 1 ((r : ℤ) + 1) n
      rw [higher ((r : ℤ) + 1 + n) (by omega)] at h
      rw [neutralPolynomialMode_positive, neutralPolynomialMode_positive] at h
      rw [neutralPolynomialMode_positive]
      simpa [LatticeSugawaraCurrents.weightedPartial, pderiv_one] using h
    have scalar := scalar_of_positive_currents D H hHG (α + β) (I.val 1 n 1) positive
    have constraint := scalar_ground_constraint D H hHG hGH α β I n scalar
    have cc : constantCoeff (I.val 1 n 1) = 0 := by
      by_cases index : n = -bilinear D α β - 1
      · simpa only [index] using heval
      · apply (mul_eq_zero.mp constraint).resolve_left
        intro bad
        have integer : n + bilinear D α β + 1 = 0 := by exact_mod_cast bad
        omega
    rw [scalar, cc, zero_smul]
  obtain ⟨N, hN⟩ := I.property.truncation 1 1
  have all (k : ℕ) : ∀ n : ℤ, (N - n).toNat = k → I.val 1 n 1 = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hn
      by_cases high : N ≤ n
      · exact hN n high
      · apply step n
        intro m hm
        by_cases highm : N ≤ m
        · exact hN m highm
        · exact ih (N - m).toNat (by omega) m rfl
  exact ground_sequence_detects_zero D α β (α + β) I (fun n => all _ n rfl)

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
