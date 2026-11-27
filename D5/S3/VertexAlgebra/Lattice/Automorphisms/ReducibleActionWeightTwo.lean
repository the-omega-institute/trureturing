import D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantGramProjector
import D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantQuadraticConformalState

/-! A reducible real charge action gives two fixed quadratic states in the actual lattice fields. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.ReducibleActionWeightTwo

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticePositiveEnergy
open LatticeAllStateField LatticeAllStateReconstruction LatticeActualConformalState
open IsometryLift InvariantQuadraticConformalState InvariantGramProjectorDraft
open LinearMap (BilinForm)
open scoped Matrix VertexOperator

open private mixingMatrix mixing_inverse from D5.S3.VertexAlgebra.Lattice.IsometryLift
open private mixing_gram from D5.S3.VertexAlgebra.Lattice.Automorphisms.InvariantQuadraticConformalState

noncomputable section

/-- The real matrix of a charge automorphism in the standard lattice basis.
Its columns are the images of the integral unit charges. -/
def realMixingMatrix (D : LatticeData) (g : Charge D ≃+ Charge D) :
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

/-- Positive definiteness and a proper nonzero invariant real subspace produce
two independent fixed quadratic states in the actual lattice carrier. Both
have eigenvalue two for the mode of the full inverse-Gram state. -/
theorem reducible_action_fixed_weight_two (D : LatticeData) {ι : Type*}
    (hpos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (g : ι → Charge D ≃+ Charge D)
    (hg : ∀ t a b, bilinear D (g t a) (g t b) = bilinear D a b)
    (W : Submodule ℝ (Fin D.rank → ℝ)) (hW₀ : W ≠ ⊥) (hW₁ : W ≠ ⊤)
    (hW : ∀ t x, x ∈ W → realChargeAction D (g t) x ∈ W) :
    ∃ H P : Matrix (Fin D.rank) (Fin D.rank) ℂ,
      H.IsSymm ∧ H * gramComplex D = 1 ∧
      (P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
        Pᵀ * gramComplex D = gramComplex D * P ∧
        (∀ t, Commute (mixingMatrix D (g t)) P)) ∧
      omega D H ∈ grade D 2 ∧ omega D (P * H) ∈ grade D 2 ∧
      ((Y D (omega D H))[[1]]) (omega D H) = (2 : ℂ) • omega D H ∧
      ((Y D (omega D H))[[1]]) (omega D (P * H)) = (2 : ℂ) • omega D (P * H) ∧
      (∀ t, lift D (g t) (omega D H) = omega D H ∧
        lift D (g t) (omega D (P * H)) = omega D (P * H)) ∧
      LinearIndependent ℂ ![omega D (P * H), omega D H] := by
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
  exact ⟨H, P, hH, hHG, ⟨hP, hP₀, hP₁, hSelf, hComm'⟩,
    projector_fixed_weight_two D g hg H P hH hHG hP hP₀ hP₁ hSelf hComm'⟩

#print axioms realChargeAction
#print axioms reducible_action_fixed_weight_two
#check @reducible_action_fixed_weight_two

end
end D5.S3.VertexAlgebra.Lattice.ReducibleActionWeightTwo
