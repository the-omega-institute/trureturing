/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual current Ward and negative-source recurrence reconstruct every oscillator input. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorChargeSelection

/-!
Native reconstruction on both oscillator arguments. The input recurrence
uses the actual negative polynomial currents. The source recurrence is
extracted from full mixed Jacobi, not from a commutant assertion. Polynomial
induction proves the result on the polynomial itself and thus needs no
assumed choice or independence of an oscillator occurrence order.
These are the classical free-boson Ward and residue recurrences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

/-- The current Ward identity on the ground source, for every integer current mode. -/
theorem ground_current_ward (D : LatticeData) (α β γ : Charge D) (I : IO D α β γ)
    (i : Fin D.rank) (v : Sector D β) (m n : ℤ) :
    neutralPolynomialMode D i γ m (I.val 1 n v) -
      I.val 1 n (neutralPolynomialMode D i β m v) =
        (bilinear D (unitCharge D i) α : ℂ) • I.val 1 (m + n) v := by
  have h := (ward D α β γ I (X (i, 0)) 1 v m n).2
  have sum : (∑ᶠ j : ℕ, leftTerm D α β γ I.val (X (i, 0)) 1 v m n 0 j) =
      (bilinear D (unitCharge D i) α : ℂ) • I.val 1 (m + n) v := by
    rw [finsum_eq_single _ 0]
    · simp [leftTerm, integerBinomial, action_current, neutralPolynomialMode]
    · intro j hj
      have positive : 0 < (j : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hj
      simp [leftTerm, action_current, neutralPolynomialMode,
        not_lt.mpr (le_of_lt positive), hj, LinearMap.smul_apply, LinearMap.sum_apply,
        Derivation.coeFn_coe, pderiv_one]
  rw [sum, action_current, action_current] at h
  exact h

private theorem reconstruct_input (D : LatticeData) (α β γ : Charge D) (I : IO D α β γ)
    (hground : ∀ n : ℤ, I.val 1 n 1 = 0) (v : Sector D β) :
    ∀ n : ℤ, I.val 1 n v = 0 := by
  induction v using MvPolynomial.induction_on with
  | C c =>
    intro n
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul], map_smul, hground,
      smul_zero]
  | add p q hp hq => intro n; rw [map_add, hp, hq, add_zero]
  | mul_X p x hp =>
    intro n
    have h := ground_current_ward D α β γ I x.1 p (-(x.2 : ℤ) - 1) n
    rw [hp n, hp (-(x.2 : ℤ) - 1 + n), map_zero, smul_zero, zero_sub,
      neg_eq_zero] at h
    rw [neutralPolynomialMode_negative, LinearMap.mulLeft_apply] at h
    simpa only [Prod.eta, mul_comm] using h

private theorem reconstruct_source (D : LatticeData) (α β γ : Charge D) (I : IO D α β γ)
    (hground : ∀ n v, I.val 1 n v = 0) (u : Sector D α) :
    ∀ n v, I.val u n v = 0 := by
  induction u using MvPolynomial.induction_on with
  | C c =>
    intro n v
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul], map_smul]
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, hground, smul_zero]
  | add p q hp hq =>
    intro n v
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hp, hq, add_zero]
  | mul_X p x hp =>
    intro n v
    let r : ℤ := -(x.2 : ℤ) - 1
    have h := (I.property.jacobi (X (x.1, 0)) p v 0 n r).2.2.2
    have left : (∑ᶠ j : ℕ, leftTerm D α β γ I.val (X (x.1, 0)) p v 0 n r j) =
        I.val (action D α (X (x.1, 0)) r p) n v := by
      rw [finsum_eq_single _ 0]
      · simp [leftTerm, integerBinomial]
      · intro j hj
        simp [leftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
    rw [left] at h
    simp only [firstTerm, secondTerm, hp, map_zero, smul_zero, finsum_zero, sub_zero] at h
    rw [action_current, show r = -(x.2 : ℤ) - 1 from rfl,
      neutralPolynomialMode_negative, LinearMap.mulLeft_apply] at h
    simpa only [Prod.eta, mul_comm] using h

/-- The complete ground-to-ground Laurent sequence detects a lawful IO.
This includes reconstruction of all source descendants, not only its action
on the second Fock space. -/
theorem ground_sequence_detects_zero (D : LatticeData) (α β γ : Charge D)
    (I : IO D α β γ) (hground : ∀ n : ℤ, I.val 1 n 1 = 0) : I = 0 := by
  have hi (n : ℤ) (v : Sector D β) : I.val 1 n v = 0 :=
    reconstruct_input D α β γ I hground v n
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  funext n
  apply LinearMap.ext
  intro v
  exact reconstruct_source D α β γ I hi u n v

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
