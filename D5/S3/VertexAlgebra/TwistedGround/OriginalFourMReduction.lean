/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMReduction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state original Jacobi reduction to explicit charge-coset channels. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInputs
import Batteries.Tactic.OpenPrivate

/-! Finite trilinear input expansion of the original three channels. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeInvolution
open HalfFock.LatticeHalfFockParityField MixedIntertwiner
open OriginalFourMInputs
open private jacobiLeftTerm jacobiFirstTerm jacobiSecondTerm from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients

private def jacobiTriples (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ]
        (ℕ → (paritySpace D hu (-1)) × (paritySpace D hu (-1)) × (paritySpace D hu (-1))) where
  toFun a := {
    toFun u := {
      toFun v := fun j => (jacobiLeftTerm D hu hD m n r a u v j,
        jacobiFirstTerm D hu hD m n r a u v j, jacobiSecondTerm D hu hD m n r a u v j)
      map_add' v w := by
        funext j
        simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_add,
          LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      map_smul' z v := by
        funext j
        simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_smul,
          LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
        apply Prod.ext
        · module
        · apply Prod.ext <;> module }
    map_add' u w := by
      apply LinearMap.ext
      intro v
      funext j
      simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_add,
        LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    map_smul' z u := by
      apply LinearMap.ext
      intro v
      funext j
      simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_smul,
        LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
      apply Prod.ext
      · module
      · apply Prod.ext <;> module }
  map_add' a b := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    funext j
    simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_add,
      LinearMap.add_apply, smul_add, Prod.mk_add_mk, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' z a := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    funext j
    simp only [jacobiLeftTerm, jacobiFirstTerm, jacobiSecondTerm, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_smul, Prod.smul_mk, Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply Prod.ext
    · module
    · apply Prod.ext <;> module

private theorem jacobi_triples_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : paritySpace D hu (-1)) (u v : paritySpace D hu (-1)) :
    Function.HasFiniteSupport (jacobiTriples D hu hD m n r a u v) := by
  have hl := original_jacobi_left_finite D hu hD m n r a u v
  have hf := original_jacobi_first_finite D hu hD m n r a u v
  have hs := original_jacobi_second_finite D hu hD m n r a u v
  change (Function.support (fun j => (jacobiLeftTerm D hu hD m n r a u v j,
    jacobiFirstTerm D hu hD m n r a u v j, jacobiSecondTerm D hu hD m n r a u v j))).Finite
  rw [Function.support_prodMk, Function.support_prodMk]
  exact hl.union (hf.union hs)

private def jacobiBalance (D : LatticeData) (hu : IsUnit D.G.det) :
    ((paritySpace D hu (-1)) × (paritySpace D hu (-1)) × (paritySpace D hu (-1))) →ₗ[ℂ]
      paritySpace D hu (-1) where
  toFun x := x.1-x.2.1+x.2.2
  map_add' x y := by dsimp; abel
  map_smul' z x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_add, RingHom.id_apply]

set_option maxHeartbeats 4000000 in
private def jacobiResidual (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m n r : ℤ) :
    paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) where
  toFun a := {
    toFun u := {
      toFun v := jacobiBalance D hu (∑ᶠ j, jacobiTriples D hu hD m n r a u v j)
      map_add' v w := by
        simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
        rw [finsum_add_distrib (jacobi_triples_finite D hu hD m n r a u v)
          (jacobi_triples_finite D hu hD m n r a u w), map_add]
      map_smul' z v := by
        simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← smul_finsum, map_smul] }
    map_add' u w := by
      apply LinearMap.ext
      intro v
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [finsum_add_distrib (jacobi_triples_finite D hu hD m n r a u v)
        (jacobi_triples_finite D hu hD m n r a w v), map_add]
    map_smul' z u := by
      apply LinearMap.ext
      intro v
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← smul_finsum, map_smul] }
  map_add' a b := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [finsum_add_distrib (jacobi_triples_finite D hu hD m n r a u v)
      (jacobi_triples_finite D hu hD m n r b u v), map_add]
  map_smul' z a := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← smul_finsum, map_smul]

private theorem jacobi_residual_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (a : paritySpace D hu (-1)) (u v : paritySpace D hu (-1)) :
    jacobiResidual D hu hD m n r a u v =
      (∑ᶠ j, jacobiLeftTerm D hu hD m n r a u v j) -
      (∑ᶠ j, jacobiFirstTerm D hu hD m n r a u v j) +
      (∑ᶠ j, jacobiSecondTerm D hu hD m n r a u v j) := by
  let F := jacobiTriples D hu hD m n r a u v
  have finite := jacobi_triples_finite D hu hD m n r a u v
  have fst := map_finsum (LinearMap.fst ℂ (paritySpace D hu (-1))
    (paritySpace D hu (-1) × paritySpace D hu (-1))) finite
  have snd := map_finsum (LinearMap.snd ℂ (paritySpace D hu (-1))
    (paritySpace D hu (-1) × paritySpace D hu (-1))) finite
  have finiteSnd : Function.HasFiniteSupport (fun j => (F j).2) := finite.snd
  have sf := map_finsum (LinearMap.fst ℂ (paritySpace D hu (-1)) (paritySpace D hu (-1))) finiteSnd
  have ss := map_finsum (LinearMap.snd ℂ (paritySpace D hu (-1)) (paritySpace D hu (-1))) finiteSnd
  change (∑ᶠ j, F j).1-(∑ᶠ j, F j).2.1+(∑ᶠ j, F j).2.2 = _
  change (∑ᶠ j, F j).1 = ∑ᶠ j, (F j).1 at fst
  change (∑ᶠ j, F j).2 = ∑ᶠ j, (F j).2 at snd
  change (∑ᶠ j, (F j).2).1 = ∑ᶠ j, (F j).2.1 at sf
  change (∑ᶠ j, (F j).2).2 = ∑ᶠ j, (F j).2.2 at ss
  rw [fst, snd, sf, ss]
  rfl


private theorem jacobi_residual_zero_iff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    jacobiResidual D hu hD m n r u v w = 0 ↔ originalJacobi D hu hD m n r u v w := by
  rw [jacobi_residual_expansion, originalJacobi]
  rw [show (∑ᶠ j, jacobiLeftTerm D hu hD m n r u v w j) -
      (∑ᶠ j, jacobiFirstTerm D hu hD m n r u v w j) +
      (∑ᶠ j, jacobiSecondTerm D hu hD m n r u v w j) =
      (∑ᶠ j, jacobiLeftTerm D hu hD m n r u v w j) -
        ((∑ᶠ j, jacobiFirstTerm D hu hD m n r u v w j) -
          (∑ᶠ j, jacobiSecondTerm D hu hD m n r u v w j)) by abel,
    sub_eq_zero]

/-- The detector polynomial is quantified before ground elimination. All four
actual ground variables are unrestricted; no output-weight premise is added. -/
theorem homogeneous_jacobi_iff_identityK (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (P Q R : Oscillator D)
    (hP : CompatiblePolynomial D H P) (hQ : CompatiblePolynomial D K Q)
    (hR : CompatiblePolynomial D L R) :
    (∀ x y z : ActualGround D hu,
      originalJacobi D hu hD m n r (tensorInput D hu P hP.1 x)
        (tensorInput D hu Q hQ.1 y) (tensorInput D hu R hR.1 z)) ↔
    ∀ S : Oscillator D, identityK D hu H K L m n r P Q R S := by
  have tensors (x y z : ActualGround D hu) := original_jacobi_tensor_kernel D hu hD h24
    H K L m n r (tensorInput D hu P hP.1 x) (tensorInput D hu Q hQ.1 y)
    (tensorInput D hu R hR.1 z) P Q R x y z rfl rfl rfl
    (tensor_input_energy D hu h24 H P hP x)
    (tensor_input_energy D hu h24 K Q hQ y)
    (tensor_input_energy D hu h24 L R hR z)
  constructor
  · intro jacobi S
    apply (coset_ground_elimination D hu h24 H K L m n r P Q R S).mp
    intro x y z t
    exact (tensors x y z).mp (jacobi x y z) S t
  · intro kernels x y z
    apply (tensors x y z).mpr
    intro S t
    exact (coset_ground_elimination D hu h24 H K L m n r P Q R S).mpr
      (kernels S) x y z t

/-- All original M states and arbitrary signed integer modes on the vector
Jacobi side, equivalent to the independent explicit EnergyFiber coset law on
all compatible original homogeneous odd polynomials. This proves a reduction,
not K itself, crossing, or a VOA completion. -/
theorem original_jacobi_iff_identityK (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) :
    (∀ u v w : paritySpace D hu (-1), originalJacobi D hu hD m n r u v w) ↔
    ∀ (H K L : ℕ) (P Q R : Oscillator D),
      CompatiblePolynomial D H P → CompatiblePolynomial D K Q →
      CompatiblePolynomial D L R →
      ∀ S : Oscillator D, identityK D hu H K L m n r P Q R S := by
  constructor
  · intro allStates H K L P Q R hP hQ hR
    apply (homogeneous_jacobi_iff_identityK D hu hD h24 H K L m n r P Q R hP hQ hR).mp
    intro x y z
    exact allStates _ _ _
  · intro kernels
    have zero : ∀ u v w, jacobiResidual D hu hD m n r u v w = 0 := by
      apply input_trilinear_ext D hu h24 (jacobiResidual D hu hD m n r)
      intro H K L P Q R hP hQ hR x y z _ _ _
      apply (jacobi_residual_zero_iff D hu hD m n r _ _ _).mpr
      exact (homogeneous_jacobi_iff_identityK D hu hD h24 H K L m n r P Q R hP hQ hR).mpr
        (kernels H K L P Q R hP hQ hR) x y z
    intro u v w
    exact (jacobi_residual_zero_iff D hu hD m n r u v w).mp (zero u v w)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
