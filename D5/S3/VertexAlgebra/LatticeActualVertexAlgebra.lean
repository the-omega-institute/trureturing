/- GID: D5/S3/VertexAlgebra/LatticeActualVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual lattice state-field construction is an ungraded vertex algebra. -/

import D5.S3.VertexAlgebra.LatticeAllStateJacobi

/- Concrete ungraded vertex algebra on the actual lattice carrier.
The local interface records the usual state-field axioms and full finite
Borcherds identity. The immutable library has VertexOperator and reconstruction
suppliers but no bundled VertexAlgebra type; no supplier or cache is changed.
This is a consumer of the substantive actual locality/Jacobi proof package,
not a separate admission claim or a conformal/grading/VOA assertion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open StateFieldResidueReconstruction (integerBinomial)
open scoped VertexOperator
noncomputable section

/-- Standard state-field data, including the full integer Borcherds identity. -/
structure StateFieldVertexAlgebra (V : Type*) [AddCommGroup V] [Module ℂ V] where
  stateField : V →ₗ[ℂ] VertexOperator ℂ V
  vacuum : V
  translation : Module.End ℂ V
  vacuum_field : stateField vacuum = FieldNormalProduct.identityField
  creation : ∀ a : V, ((stateField a)[[-1]]) vacuum = a
  creativity : ∀ (a : V) (n : ℤ), 0 ≤ n → ((stateField a)[[n]]) vacuum = 0
  translation_vacuum : translation vacuum = 0
  covariance : ∀ (a : V) (n : ℤ),
    translation * ((stateField a)[[n]]) - ((stateField a)[[n]]) * translation =
      -(n : ℂ) • ((stateField a)[[n-1]])
  locality : ∀ a b : V, ∃ N : ℕ, FieldNormalProductLocality.delta^[N]
    (FieldNormalProductLocality.commutator (stateField a) (stateField b)) = 0
  borcherds : ∀ (a b c : V) (p q r : ℤ),
    let mu : V → ℤ → V → V := fun a n b => ((stateField a)[[n]]) b
    let left : ℕ → V := fun i => integerBinomial p i • mu (mu a (r+i) b) (p+q-i) c
    let first : ℕ → V := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) • mu a (p+r-i) (mu b (q+i) c)
    let second : ℕ → V := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (mu a (p+r-i) (mu b (q+i) c) -
              StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c))

/-- Intrinsic translation agrees with the already constructed concrete T. -/
theorem translation_as_mode (D : LatticeData) (v : Carrier D) :
    translation D v = ((Y D v)[[-2]]) (vacuum D) := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (vacuum D))
    (stateField_covariance D v (-1))
  simpa only [LinearMap.sub_apply,Module.End.mul_apply,stateField_creation,
    translation_kills_vacuum,map_zero,sub_zero,Int.cast_neg,Int.cast_one,
    neg_neg,one_smul,show (-1 : ℤ)-1 = -2 by norm_num] using h

/-- Every integral symmetric even-diagonal finite lattice, including rank zero. -/
def actualVertexAlgebra (D : LatticeData) : StateFieldVertexAlgebra (Carrier D) where
  stateField := Y D
  vacuum := LatticeAllStateField.vacuum D
  translation := LatticeSugawaraConformal.translation D
  vacuum_field := stateField_vacuum D
  creation := stateField_creation D
  creativity := stateField_creativity D
  translation_vacuum := translation_kills_vacuum D
  covariance := stateField_covariance D
  locality := LatticeAllStateLocality.stateField_locality D
  borcherds a b c p q r := by
    have h := LatticeAllStateJacobi.borcherds D a b c p q r
    dsimp only [LatticeAllStateJacobi.jacobiLeftTerm,
      LatticeAllStateJacobi.jacobiRightFirstTerm,LatticeAllStateJacobi.jacobiRightSecondTerm,
      LatticeAllStateReconstruction.mu] at h
    exact h

end
end D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
