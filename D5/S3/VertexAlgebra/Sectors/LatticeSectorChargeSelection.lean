/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-current Ward forces the Gram-kernel charge selection and nonsingular vanishing. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround

/-!
Charge selection for every lawful mixed IO. The zero-current Ward law gives
a Gram-kernel constraint even for degenerate lattices. Only the final charge
reflection uses an inverse Gram matrix over the complex numbers. There is
no positivity, nonzero charge, positive rank or integer unimodularity premise.
Classical source: the neutral current calculus of Bakalov--Kac, section 4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeActualConformalState LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix
noncomputable section

/-- The restricted current is the actual polynomial current in each sector. -/
theorem action_current (D : LatticeData) (δ : Charge D) (i : Fin D.rank) (n : ℤ) :
    action D δ (MvPolynomial.X (i, 0)) n = neutralPolynomialMode D i δ n := by
  apply LinearMap.ext
  intro v
  have h := single_action D δ (MvPolynomial.X (i, 0)) v n
  change Finsupp.single δ _ =
    ((Y D (currentState D i))[[n]]) (Finsupp.single δ v) at h
  rw [current_state_field, neutralField_ncoeff, neutralMode_single] at h
  simpa [action, canonical, inclusion, projection] using
    congrArg (fun w : Carrier D => w δ) h

/-- Zero-current Ward, with no division by a pairing or a state. -/
theorem zero_current_ward (D : LatticeData) (α β γ : Charge D)
    (I : IO D α β γ) (i : Fin D.rank) (u : Sector D α) (v : Sector D β) (n : ℤ) :
    (((bilinear D (unitCharge D i) γ : ℂ) -
      (bilinear D (unitCharge D i) α : ℂ) -
      (bilinear D (unitCharge D i) β : ℂ))) • I.val u n v = 0 := by
  have h := (ward D α β γ I (MvPolynomial.X (i, 0)) u v 0 n).2
  have left : (∑ᶠ j : ℕ, leftTerm D α β γ I.val
      (MvPolynomial.X (i, 0)) u v 0 n 0 j) =
      I.val (action D α (MvPolynomial.X (i, 0)) 0 u) n v := by
    rw [finsum_eq_single _ 0]
    · simp [leftTerm, integerBinomial]
    · intro j hj
      simp [leftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  rw [left, action_current, action_current, action_current] at h
  simp only [neutralPolynomialMode, lt_irrefl, if_false, if_true,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul, Pi.smul_apply,
    RingHom.id_apply] at h
  rw [sub_smul, sub_smul]
  linear_combination h

/-- A nonzero coefficient reflects exact charge addition under inverse Gram. -/
theorem nonzero_coefficient_charge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (α β γ : Charge D) (I : IO D α β γ)
    (u : Sector D α) (v : Sector D β) (n : ℤ) (hne : I.val u n v ≠ 0) :
    γ = α + β := by
  have row (i : Fin D.rank) :
      (bilinear D (unitCharge D i) γ : ℂ) -
        (bilinear D (unitCharge D i) α : ℂ) -
        (bilinear D (unitCharge D i) β : ℂ) = 0 :=
    (smul_eq_zero.mp (zero_current_ward D α β γ I i u v n)).resolve_right hne
  let d : Fin D.rank → ℂ := fun j => (γ j : ℂ) - (α j : ℂ) - (β j : ℂ)
  have kernel : gramComplex D *ᵥ d = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, gramComplex, d, bilinear, unitCharge,
      Int.cast_sum, Int.cast_mul, mul_sub, Finset.sum_sub_distrib] using row i
  have inverse := congrArg (fun x : Fin D.rank → ℂ => H *ᵥ x) kernel
  rw [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec, Matrix.mulVec_zero] at inverse
  ext i
  have hc : (γ i : ℂ) - (α i : ℂ) - (β i : ℂ) = 0 := by
    simpa only [d, Pi.zero_apply] using congrFun inverse i
  have hi : γ i - α i - β i = 0 := by exact_mod_cast hc
  change γ i = α i + β i
  omega

/-- Every wrong-charge lawful intertwiner vanishes on its full input domain. -/
theorem wrong_charge_vanishing (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (α β γ : Charge D) (hγ : γ ≠ α + β) (I : IO D α β γ) : I = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  funext n
  apply LinearMap.ext
  intro v
  change I.val u n v = 0
  by_contra hne
  exact hγ (nonzero_coefficient_charge D H hHG α β γ I u v n hne)

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
