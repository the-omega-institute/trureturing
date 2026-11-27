/- GID: D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A reducible real charge action gives two independent actual fixed weight-two states. -/

import D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantGramProjector
import D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

/-!
Actual mode minus one expresses the two-oscillator state as a product of
currents. Its covariance therefore depends only on the induced charge action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticePositiveEnergy
open LatticeAllStateField LatticeAllStateReconstruction LatticeActualConformalState
open IsometryLift InvariantQuadraticConformalState InvariantGramProjector
open ConformalGroundTransport (current)
open Lattice.Orbifold.DiagonalCharacterConjugacy (PreservesModes ground)
open LinearMap (BilinForm)
open scoped BigOperators Matrix VertexOperator

open private mixingMatrix charge_coordinates mixing_inverse from
  D5.S3.VertexAlgebra.Lattice.IsometryLift
open private mixing_gram from
  D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState
open private current_lift_charge from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

noncomputable section

private def realMixingMatrix (D : LatticeData) (g : Charge D ≃+ Charge D) :
    Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  fun i j => (g (unitCharge D j) i : ℝ)

private theorem complexify_mixing (D : LatticeData) (g : Charge D ≃+ Charge D) :
    (realMixingMatrix D g).map Complex.ofRealHom = mixingMatrix D g := by
  ext i j
  simp [realMixingMatrix, mixingMatrix]

private theorem real_mixing_inverse (D : LatticeData) (g h : Charge D ≃+ Charge D)
    (hinv : ∀ a, g (h a) = a) :
    realMixingMatrix D g * realMixingMatrix D h = 1 := by
  apply Matrix.map_injective Complex.ofReal_injective
  change (realMixingMatrix D g * realMixingMatrix D h).map Complex.ofRealHom =
    Complex.ofRealHom.mapMatrix (1 : Matrix (Fin D.rank) (Fin D.rank) ℝ)
  rw [Matrix.map_mul, complexify_mixing, complexify_mixing, map_one]
  exact mixing_inverse D g h hinv

/-- The charge automorphism extended to real coordinates. -/
def realChargeAction (D : LatticeData) (g : Charge D ≃+ Charge D) :
    (Fin D.rank → ℝ) ≃ₗ[ℝ] (Fin D.rank → ℝ) :=
  Matrix.toLin'OfInv
    (real_mixing_inverse D g.symm g g.symm_apply_apply)
    (real_mixing_inverse D g g.symm g.apply_symm_apply)

/-- The real Cartan representation of the additive automorphisms of the charge lattice. -/
def realChargeRepresentation (D : LatticeData) :
    Representation ℝ (Multiplicative (AddAut (Charge D))) (Fin D.rank → ℝ) where
  toFun g := (realChargeAction D g.toAdd).toLinearMap
  map_one' := by
    change Matrix.toLin' (realMixingMatrix D (0 : AddAut (Charge D))) = LinearMap.id
    have hOne : realMixingMatrix D (0 : AddAut (Charge D)) = 1 := by
      ext i j
      simp [realMixingMatrix, Matrix.one_apply, unitCharge, apply_ite]
    rw [hOne, Matrix.toLin'_one]
  map_mul' g h := by
    change Matrix.toLin' (realMixingMatrix D (g.toAdd + h.toAdd)) =
      (Matrix.toLin' (realMixingMatrix D g.toAdd)).comp
        (Matrix.toLin' (realMixingMatrix D h.toAdd))
    have hMul : realMixingMatrix D (g.toAdd + h.toAdd) =
        realMixingMatrix D g.toAdd * realMixingMatrix D h.toAdd := by
      apply Matrix.map_injective Complex.ofReal_injective
      change (realMixingMatrix D (g.toAdd + h.toAdd)).map Complex.ofRealHom =
        (realMixingMatrix D g.toAdd * realMixingMatrix D h.toAdd).map Complex.ofRealHom
      rw [Matrix.map_mul, complexify_mixing, complexify_mixing, complexify_mixing]
      ext i j
      change (g.toAdd (h.toAdd (unitCharge D j)) i : ℂ) =
        (mixingMatrix D g.toAdd * mixingMatrix D h.toAdd) i j
      simpa only [Matrix.mul_apply, mixingMatrix, mul_comm] using
        charge_coordinates D g.toAdd (h.toAdd (unitCharge D j)) i
    rw [hMul, Matrix.toLin'_mul]

private theorem real_action_toMatrix (D : LatticeData) (g : Charge D ≃+ Charge D) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin D.rank)) (Pi.basisFun ℝ (Fin D.rank))
      (realChargeAction D g).toLinearMap = realMixingMatrix D g := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' _

private theorem real_action_isometry (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) :
    let B := (D.G.map (Int.cast : ℤ → ℝ)).toBilin'
    ∀ x y, B (realChargeAction D g x) (realChargeAction D g y) = B x y := by
  let G := D.G.map (Int.cast : ℤ → ℝ)
  have hG : G.map Complex.ofRealHom = gramComplex D := by
    ext i j
    simp [G, gramComplex]
  have hcongr : (realMixingMatrix D g)ᵀ * G * realMixingMatrix D g = G := by
    apply Matrix.map_injective Complex.ofReal_injective
    change ((realMixingMatrix D g)ᵀ * G * realMixingMatrix D g).map Complex.ofRealHom =
      G.map Complex.ofRealHom
    simpa only [Matrix.map_mul, Matrix.transpose_map, complexify_mixing, hG] using
      mixing_gram D g hg
  have h := Matrix.toBilin'_comp G (realMixingMatrix D g) (realMixingMatrix D g)
  rw [hcongr] at h
  change ∀ x y, G.toBilin' (realChargeAction D g x) (realChargeAction D g y) = G.toBilin' x y
  intro x y
  exact congrArg (fun B : BilinForm ℝ (Fin D.rank → ℝ) => B x y) h

private theorem omega_eq_current_products (D : LatticeData)
    (A : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    omega D A = (2 : ℂ)⁻¹ • ∑ i, ∑ j, A i j •
      mu D (currentState D i) (-1) (currentState D j) := by
  let includeNeutral : Oscillator D →ₗ[ℂ] Carrier D := Finsupp.lsingle 0
  change includeNeutral ((2 : ℂ)⁻¹ • ∑ i, ∑ j, A i j •
    (MvPolynomial.X (i, 0) * MvPolynomial.X (j, 0))) = _
  simp only [map_smul, map_sum, current_minus_one_current]
  rfl

/-- The actual quadratic of any complex matrix transforms by congruence under
every mode-preserving lift of the given integral charge isometry. -/
theorem actual_omega_covariance (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (phase : Charge D → ℂˣ)
    (hMode : PreservesModes D U)
    (hGround : ∀ a, U (ground D a) = (phase a : ℂ) • ground D (g a))
    (A : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    U (omega D A) = omega D (mixingMatrix D g * A * (mixingMatrix D g)ᵀ) := by
  have hLiftMode := (lift_compatible D g hg).2.2.1
  have hLiftGround (a : Charge D) :
      lift D g (ground D a) = (IsometryLift.phase D g a : ℂ) • ground D (g a) := by
    simp only [ground, lift_single, map_one]
  have hCurrent (i : Fin D.rank) : U (currentState D i) = lift D g (currentState D i) := by
    have hUnit : current D (fun j => (unitCharge D i j : ℂ)) = currentState D i := by
      classical
      simp only [current, unitCharge, apply_ite, Int.cast_one, Int.cast_zero, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hUnit]
    exact (current_lift_charge D g hg U phase hMode hGround (unitCharge D i)).trans
      (current_lift_charge D g hg (lift D g) (IsometryLift.phase D g)
        (fun u v n => hLiftMode u n v) hLiftGround (unitCharge D i)).symm
  have hPair (i j : Fin D.rank) :
      U (mu D (currentState D i) (-1) (currentState D j)) =
        lift D g (mu D (currentState D i) (-1) (currentState D j)) := by
    simp only [mu, hMode, hLiftMode, hCurrent]
  calc
    U (omega D A) = lift D g (omega D A) := by
      simp only [omega_eq_current_products D A, map_smul, map_sum, hPair]
    _ = omega D (mixingMatrix D g * A * (mixingMatrix D g)ᵀ) := lift_omega D g A

/-- A proper nonzero invariant real Cartan subspace gives the full
inverse-Gram state and its projector quadratic. Both have actual conformal
weight two and are pointwise fixed under the specified mode-preserving lifts. -/
theorem reducible_action_fixed_weight_two (D : LatticeData) {ι : Type*}
    (hpos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (g : ι → Charge D ≃+ Charge D)
    (hg : ∀ t a b, bilinear D (g t a) (g t b) = bilinear D a b)
    (U : ι → Carrier D ≃ₗ[ℂ] Carrier D) (phase : ι → Charge D → ℂˣ)
    (hMode : ∀ t, PreservesModes D (U t))
    (hGround : ∀ t a, U t (ground D a) = (phase t a : ℂ) • ground D (g t a))
    (W : Submodule ℝ (Fin D.rank → ℝ)) (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤)
    (hW : ∀ t x, x ∈ W → realChargeAction D (g t) x ∈ W) :
    ∃ H P : Matrix (Fin D.rank) (Fin D.rank) ℂ,
      H * gramComplex D = 1 ∧
      let q : Fin 2 → Carrier D := ![omega D (P * H), omega D H]
      (∀ i, q i ∈ grade D 2) ∧
      (∀ i, ((Y D (omega D H))[[1]]) (q i) = (2 : ℂ) • q i) ∧
      (∀ t i, U t (q i) = q i) ∧ LinearIndependent ℂ q := by
  classical
  let G := D.G.map (Int.cast : ℤ → ℝ)
  let B := G.toBilin'
  let b := Pi.basisFun ℝ (Fin D.rank)
  have hBsymm : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr (by
    ext i j
    exact congrArg (fun z : ℤ => (z : ℝ)) (D.symmetric j i))
  have hBpos : ∀ x, x ≠ 0 → 0 < B x x := by
    intro x hx
    rw [Matrix.toBilin'_apply']
    simpa only [star_trivial] using hpos.dotProduct_mulVec_pos hx
  have hBmatrix : B.toMatrix b = G := by
    rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin']
  have hG : (B.toMatrix b).map Complex.ofRealHom = gramComplex D := by
    rw [hBmatrix]
    ext i j
    simp [G, gramComplex]
  have hWiff (t : ι) (x : Fin D.rank → ℝ) : realChargeAction D (g t) x ∈ W ↔ x ∈ W := by
    let e := realChargeAction D (g t)
    have he : W.map e.toLinearMap = W :=
      Submodule.eq_of_le_of_finrank_eq
        (Submodule.map_le_iff_le_comap.mpr (hW t)) (e.finrank_map_eq W)
    refine ⟨?_, hW t x⟩
    intro hx
    rw [← he] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    exact e.injective hyx ▸ hy
  obtain ⟨P, hP, hP₀, hP₁, hSelf, hComm⟩ :=
    exists_invariant_projector_complex_matrix b B hBsymm hBpos W hW₀ hW₁
      (fun t => realChargeAction D (g t)) (fun t => real_action_isometry D (g t) (hg t)) hWiff
  rw [hG] at hSelf
  have hComm' (t : ι) : Commute (mixingMatrix D (g t)) P := by
    have ht := hComm t
    change Commute
      ((LinearMap.toMatrix (Pi.basisFun ℝ (Fin D.rank)) (Pi.basisFun ℝ (Fin D.rank))
        (realChargeAction D (g t)).toLinearMap).map Complex.ofRealHom) P at ht
    rwa [real_action_toMatrix, complexify_mixing] at ht
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hpos
  have hGramSymm : (gramComplex D).IsSymm := by
    ext i j
    exact congrArg (fun z : ℤ => (z : ℂ)) (D.symmetric j i)
  have hH : H.IsSymm := by
    have ht := congrArg Matrix.transpose hGH
    rw [Matrix.transpose_mul, hGramSymm.eq, Matrix.transpose_one] at ht
    exact Matrix.mul_left_injective_of_inv (gramComplex D) H hGH (ht.trans hHG.symm)
  obtain ⟨hGradeH, hGradePH, hWeightH, hWeightPH, hFixed, hIndependent⟩ :=
    projector_fixed_weight_two D g hg H P hH hHG hP hP₀ hP₁ hSelf hComm'
  have hActual (t : ι) (A : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
      U t (omega D A) = lift D (g t) (omega D A) :=
    (actual_omega_covariance D (g t) (hg t) (U t) (phase t) (hMode t) (hGround t) A).trans
      (lift_omega D (g t) A).symm
  refine ⟨H, P, hHG, ?_, ?_, ?_, hIndependent⟩
  · intro i
    fin_cases i
    · exact hGradePH
    · exact hGradeH
  · intro i
    fin_cases i
    · exact hWeightPH
    · exact hWeightH
  · intro t i
    fin_cases i
    · exact (hActual t (P * H)).trans (hFixed t).2
    · exact (hActual t H).trans (hFixed t).1

#print axioms actual_omega_covariance
#print axioms reducible_action_fixed_weight_two

end
end D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo
