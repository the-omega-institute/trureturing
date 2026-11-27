/- GID: D5/S3/Geometry/Lorentz/HodgeChiralLie
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/HodgeChiralLie
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real Lorentz Lie algebra, complex chiral decomposition, and Lorentzian Hodge eigenspaces. -/

import D5.S3.Geometry.Lorentz.Urbantke
import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Lorentz.HodgeChiralLie

open Matrix
open scoped Matrix TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The (-,+,+,+) Lorentz metric. -/
def eta (K : Type*) [Ring K] : Matrix (Fin 4) (Fin 4) K :=
  diagonal ![-1, 1, 1, 1]

/-- The Lorentz Lie algebra as skew-adjoint matrices relative to the Lorentz metric. -/
abbrev lorentzLie (K : Type*) [Field K] :=
  skewAdjointMatricesLieSubalgebra (eta K)

private abbrev Triple (K : Type*) := Fin 3 → K

private def lorentzMatrix {K : Type*} [Ring K] (a b : Triple K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, b 0, b 1, b 2;
     b 0, 0, -a 2, a 1;
     b 1, a 2, 0, -a 0;
     b 2, -a 1, a 0, 0]

private def lorentzOf {K : Type*} [Field K] (a b : Triple K) : lorentzLie K := by
  refine ⟨lorentzMatrix a b, ?_⟩
  rw [lorentzLie, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  change (lorentzMatrix a b)ᵀ * eta K = eta K * (-lorentzMatrix a b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta, lorentzMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]

private def rotations {K : Type*} [Field K] (X : lorentzLie K) : Triple K :=
  ![-X.val 2 3, -X.val 3 1, -X.val 1 2]

private def boosts {K : Type*} [Field K] (X : lorentzLie K) : Triple K :=
  ![X.val 0 1, X.val 0 2, X.val 0 3]

private theorem lorentzOf_coords {K : Type*} [Field K] [CharZero K] (X : lorentzLie K) :
    lorentzOf (rotations X) (boosts X) = X := by
  have h : X.valᵀ * eta K = eta K * (-X.val) := by
    have h : (eta K).IsSkewAdjoint X.val := by
      simpa only [lorentzLie, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] using X.property
    exact h
  have he (i j : Fin 4) := congrFun (congrFun h i) j
  apply Subtype.ext
  ext i j
  have h' := he i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzOf, lorentzMatrix, rotations, boosts] <;>
    simp [eta, Matrix.mul_diagonal, Matrix.diagonal_mul] at h' <;>
    first | exact h' | exact h'.symm | linear_combination h' | linear_combination -h' |
      linear_combination h' / 2 | linear_combination -h' / 2

/-- Rotation and boost coordinates give all six independent entries. -/
def lorentzCoords (K : Type*) [Field K] [CharZero K] :
    lorentzLie K ≃ₗ[K] Triple K × Triple K where
  toFun X := (rotations X, boosts X)
  invFun p := lorentzOf p.1 p.2
  left_inv := lorentzOf_coords
  right_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [rotations, boosts, lorentzOf, lorentzMatrix]
  map_add' X Y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [rotations, boosts] <;> ring
  map_smul' k X := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [rotations, boosts]

/-- The oriented cross product of two three-component vectors. -/
def cross {K : Type*} [CommRing K] (a b : Triple K) : Triple K :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

set_option maxHeartbeats 1000000 in
private theorem lorentzOf_bracket {K : Type*} [Field K]
    (a b c d : Triple K) :
    ⁅lorentzOf a b, lorentzOf c d⁆ =
      lorentzOf (cross a c - cross b d) (cross a d + cross b c) := by
  apply Subtype.ext
  change lorentzMatrix a b * lorentzMatrix c d - lorentzMatrix c d * lorentzMatrix a b = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzOf, lorentzMatrix, cross] <;> ring

set_option maxHeartbeats 1000000 in
/-- The four families of Lorentz brackets in rotation and boost coordinates. -/
theorem lorentz_coords_bracket {K : Type*} [Field K] [CharZero K] (X Y : lorentzLie K) :
    lorentzCoords K ⁅X, Y⁆ =
      (cross (lorentzCoords K X).1 (lorentzCoords K Y).1 -
        cross (lorentzCoords K X).2 (lorentzCoords K Y).2,
       cross (lorentzCoords K X).1 (lorentzCoords K Y).2 +
        cross (lorentzCoords K X).2 (lorentzCoords K Y).1) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (lorentzCoords K).symm.surjective X
  obtain ⟨⟨c,d⟩, rfl⟩ := (lorentzCoords K).symm.surjective Y
  simp only [LinearEquiv.apply_symm_apply]
  change lorentzCoords K ⁅lorentzOf a b, lorentzOf c d⁆ = _
  rw [lorentzOf_bracket]
  exact (lorentzCoords K).apply_symm_apply (cross a c - cross b d, cross a d + cross b c)

/-- The real Lorentz Lie algebra is six-dimensional. -/
theorem finrank_lorentz_real : Module.finrank ℝ (lorentzLie ℝ) = 6 := by
  rw [(lorentzCoords ℝ).finrank_eq, Module.finrank_prod]
  simp

/-- Standard complex traceless two-by-two matrices. -/
abbrev SL2C := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

private def pauliMatrix (z : Triple ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I * z 2 / 2, (-Complex.I * z 0 - z 1) / 2;
     (-Complex.I * z 0 + z 1) / 2, Complex.I * z 2 / 2]

/-- The Pauli basis normalized by minus i over two. -/
def pauli (z : Triple ℂ) : SL2C := by
  refine ⟨pauliMatrix z, ?_⟩
  change Matrix.trace (pauliMatrix z) = 0
  simp [Matrix.trace, Fin.sum_univ_two, pauliMatrix] <;> ring

private def pauliRead (M : SL2C) : Triple ℂ :=
  ![Complex.I * (M.val 0 1 + M.val 1 0), M.val 1 0 - M.val 0 1,
    2 * Complex.I * M.val 0 0]

private theorem pauli_read_inverse (M : SL2C) : pauli (pauliRead M) = M := by
  have ht : M.val 0 0 + M.val 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using (show Matrix.trace M.val = 0 from M.property)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliMatrix, pauliRead] <;>
    ring_nf <;> simp [Complex.I_sq] <;> first | exact (neg_eq_iff_add_eq_zero).2 ht | linear_combination -ht | ring

/-- Traceless two-by-two matrices have unique Pauli coordinates. -/
def pauliCoords : Triple ℂ ≃ₗ[ℂ] SL2C where
  toFun := pauli
  invFun := pauliRead
  left_inv z := by
    funext i
    fin_cases i <;> simp [pauli, pauliMatrix, pauliRead] <;>
      ring_nf <;> simp [Complex.I_sq]
  right_inv := pauli_read_inverse
  map_add' z w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli, pauliMatrix] <;> ring
  map_smul' k z := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli, pauliMatrix] <;> ring

/-- Pauli commutators reproduce the oriented cross product. -/
theorem pauli_bracket (z w : Triple ℂ) : ⁅pauli z, pauli w⁆ = pauli (cross z w) := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliMatrix, cross] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

private def realPauliCoords : Triple ℂ ≃ₗ[ℝ] RestrictScalars ℝ ℂ SL2C :=
  { pauliCoords.toEquiv with
    map_add' := pauliCoords.map_add
    map_smul' := fun c z => pauliCoords.map_smul (c : ℂ) z }

private def realComplexCoords : (Triple ℝ × Triple ℝ) ≃ₗ[ℝ] Triple ℂ where
  toFun p := fun i => (p.1 i : ℂ) - Complex.I * (p.2 i : ℂ)
  invFun z := (fun i => (z i).re, fun i => -(z i).im)
  left_inv p := by
    apply Prod.ext <;> funext i <;> simp
  right_inv z := by
    funext i
    apply Complex.ext <;> simp
  map_add' p q := by
    funext i
    simp
    ring
  map_smul' c p := by
    funext i
    simp [Complex.real_smul]
    ring

/-- The concrete real-linear Lie isomorphism sends (a,b) to the Pauli matrix of a-i b. -/
def lorentz_real_sl2 : lorentzLie ℝ ≃ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ SL2C :=
  { (lorentzCoords ℝ).trans
    (realComplexCoords.trans realPauliCoords) with
    map_lie' := by
      intro X Y
      change pauli (realComplexCoords (lorentzCoords ℝ ⁅X,Y⁆)) =
        ⁅pauli (realComplexCoords (lorentzCoords ℝ X)), pauli (realComplexCoords (lorentzCoords ℝ Y))⁆
      rw [lorentz_coords_bracket, pauli_bracket]
      congr 1
      funext i
      fin_cases i <;> simp [realComplexCoords, cross] <;>
        ring_nf <;> simp [Complex.I_sq] <;> ring }

private def chiralCoords : (Triple ℂ × Triple ℂ) ≃ₗ[ℂ] (Triple ℂ × Triple ℂ) where
  toFun p := (fun i => p.1 i - Complex.I * p.2 i, fun i => p.1 i + Complex.I * p.2 i)
  invFun p := (fun i => (p.1 i + p.2 i) / 2, fun i => -Complex.I * (p.2 i - p.1 i) / 2)
  left_inv p := by
    apply Prod.ext <;> funext i <;> dsimp <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  right_inv p := by
    apply Prod.ext <;> funext i <;> dsimp <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  map_add' p q := by
    apply Prod.ext <;> funext i <;> simp <;> ring
  map_smul' c p := by
    apply Prod.ext <;> funext i <;> simp <;> ring

/-- The two factors correspond to the coordinates a-i b and a+i b. -/
def lorentz_chiral_sl2_prod : lorentzLie ℂ ≃ₗ⁅ℂ⁆ SL2C × SL2C :=
  { (lorentzCoords ℂ).trans
    (chiralCoords.trans (pauliCoords.prodCongr pauliCoords)) with
    map_lie' := by
      intro X Y
      change (pauli (chiralCoords (lorentzCoords ℂ ⁅X,Y⁆)).1,
      pauli (chiralCoords (lorentzCoords ℂ ⁅X,Y⁆)).2) =
      (⁅pauli (chiralCoords (lorentzCoords ℂ X)).1, pauli (chiralCoords (lorentzCoords ℂ Y)).1⁆,
       ⁅pauli (chiralCoords (lorentzCoords ℂ X)).2, pauli (chiralCoords (lorentzCoords ℂ Y)).2⁆)
      rw [lorentz_coords_bracket, pauli_bracket, pauli_bracket]
      apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd] <;> congr 1 <;> funext i <;> fin_cases i <;>
        simp [chiralCoords, cross] <;> ring_nf <;> simp [Complex.I_sq] <;> ring }

private def coordinateBaseChange :
    (ℂ ⊗[ℝ] lorentzLie ℝ) ≃ₗ[ℂ] Triple ℂ × Triple ℂ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) (lorentzCoords ℝ)).trans
    ((TensorProduct.prodRight ℝ ℂ ℂ (Triple ℝ) (Triple ℝ)).trans
      ((TensorProduct.piScalarRight ℝ ℂ ℂ (Fin 3)).prodCongr
        (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin 3))))

private theorem coordinateBaseChange_tmul (z : ℂ) (X : lorentzLie ℝ) :
    coordinateBaseChange (z ⊗ₜ[ℝ] X) =
      (fun i => z * ((lorentzCoords ℝ X).1 i : ℂ),
       fun i => z * ((lorentzCoords ℝ X).2 i : ℂ)) := by
  simp [coordinateBaseChange, Complex.real_smul, mul_comm]

private def baseChangeLinear :
    (ℂ ⊗[ℝ] lorentzLie ℝ) ≃ₗ[ℂ] lorentzLie ℂ :=
  coordinateBaseChange.trans (lorentzCoords ℂ).symm

/-- Extension from the real Lorentz matrices gives the full complex Lorentz Lie algebra. -/
def lorentz_base_change : (ℂ ⊗[ℝ] lorentzLie ℝ) ≃ₗ⁅ℂ⁆ lorentzLie ℂ :=
  { baseChangeLinear with
    map_lie' := by
      intro X Y
      change baseChangeLinear ⁅X,Y⁆ = ⁅baseChangeLinear X, baseChangeLinear Y⁆
      induction X using TensorProduct.inductionOn with
      | add x y hx hy => simp [add_lie, hx, hy]
      | tmul z x =>
        induction Y using TensorProduct.inductionOn with
        | add u v hu hv =>
          rw [show ⁅z ⊗ₜ[ℝ] x, u + v⁆ = ⁅z ⊗ₜ[ℝ] x, u⁆ + ⁅z ⊗ₜ[ℝ] x, v⁆ from (LieAlgebra.ExtendScalars.instLieRingModule ℝ ℂ (lorentzLie ℝ) (lorentzLie ℝ)).lie_add _ _ _,
            map_add, hu, hv, map_add, lie_add]
        | tmul w y =>
          apply (lorentzCoords ℂ).injective
          simp only [LieAlgebra.ExtendScalars.bracket_tmul, lorentz_coords_bracket (K := ℂ)]
          simp only [baseChangeLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
          rw [coordinateBaseChange_tmul, coordinateBaseChange_tmul, coordinateBaseChange_tmul,
            lorentz_coords_bracket (K := ℝ)]
          apply Prod.ext <;> funext i <;> fin_cases i <;>
            simp [cross] <;> push_cast <;> ring }

/-- The complexification of the real algebra splits as the product of two complex simple factors. -/
def complexified_chiral_sl2_prod :
    (ℂ ⊗[ℝ] lorentzLie ℝ) ≃ₗ⁅ℂ⁆ SL2C × SL2C :=
  lorentz_base_change.trans lorentz_chiral_sl2_prod

/-- Rotation generator about the indicated axis. -/
def J (i : Fin 3) : lorentzLie ℂ := lorentzOf (Pi.single i 1) 0
/-- Boost generator along the indicated axis. -/
def K (i : Fin 3) : lorentzLie ℂ := lorentzOf 0 (Pi.single i 1)

/-- Complex chiral generators, normalized to the Pauli bracket. -/
def chiralPlus (i : Fin 3) : lorentzLie ℂ :=
  (2 : ℂ)⁻¹ • (J i + Complex.I • K i)
def chiralMinus (i : Fin 3) : lorentzLie ℂ :=
  (2 : ℂ)⁻¹ • (J i - Complex.I • K i)

private theorem J_coords (i : Fin 3) : lorentzCoords ℂ (J i) = (Pi.single i 1, 0) :=
  (lorentzCoords ℂ).apply_symm_apply (Pi.single i 1, 0)
private theorem K_coords (i : Fin 3) : lorentzCoords ℂ (K i) = (0, Pi.single i 1) :=
  (lorentzCoords ℂ).apply_symm_apply (0, Pi.single i 1)

theorem chiral_generator_images (i : Fin 3) :
    lorentz_chiral_sl2_prod (chiralPlus i) = (pauli (Pi.single i 1), 0) ∧
    lorentz_chiral_sl2_prod (chiralMinus i) = (0, pauli (Pi.single i 1)) := by
  have hp : chiralCoords (lorentzCoords ℂ (chiralPlus i)) = (Pi.single i 1, 0) := by
    unfold chiralPlus
    simp only [map_smul, map_add, J_coords, K_coords]
    apply Prod.ext <;> funext j <;> simp [chiralCoords] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  have hm : chiralCoords (lorentzCoords ℂ (chiralMinus i)) = (0, Pi.single i 1) := by
    unfold chiralMinus
    simp only [map_smul, map_sub, J_coords, K_coords]
    apply Prod.ext <;> funext j <;> simp [chiralCoords] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  change (pauliCoords.prodCongr pauliCoords)
      (chiralCoords (lorentzCoords ℂ (chiralPlus i))) = _ ∧
    (pauliCoords.prodCongr pauliCoords)
      (chiralCoords (lorentzCoords ℂ (chiralMinus i))) = _
  rw [hp, hm]
  simp only [LinearEquiv.prodCongr_apply, map_zero, pauliCoords]
  exact ⟨rfl, rfl⟩

/-- The two normalized chiral families commute with each other. -/
theorem chiral_mixed_bracket (i j : Fin 3) : ⁅chiralPlus i, chiralMinus j⁆ = 0 := by
  apply lorentz_chiral_sl2_prod.injective
  simp [(chiral_generator_images i).1, (chiral_generator_images j).2]

open Urbantke

private abbrev PairMatrix (K : Type*) := Matrix PairIndex PairIndex K

private def pairSigns (K : Type*) [Ring K] : PairIndex → K :=
  Sum.elim (fun _ => -1) (fun _ => 1)

private def starBlocks (K : Type*) [Ring K] : PairMatrix K :=
  fromBlocks 0 1 (-1) 0

private def pairL : PairIndex → Fin 4
  | .inl _ => 0
  | .inr i => ![2,3,1] i
private def pairR : PairIndex → Fin 4
  | .inl i => i.succ
  | .inr i => ![3,1,2] i

private theorem eta_exterior {K : Type*} [Field K] :
    exteriorSquare (eta K) = diagonal (pairSigns K) := by
  ext i j
  change eta K (pairL i) (pairL j) * eta K (pairR i) (pairR j) -
    eta K (pairL i) (pairR j) * eta K (pairR i) (pairL j) = _
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [pairL, pairR, eta, pairSigns, diagonal_apply]

private theorem eta_exterior_inv {K : Type*} [Field K] :
    (exteriorSquare (eta K))⁻¹ = exteriorSquare (eta K) := by
  apply Matrix.inv_eq_left_inv
  rw [eta_exterior, Matrix.diagonal_mul_diagonal]
  ext i j
  rcases i <;> rcases j <;> simp [pairSigns, Matrix.diagonal_apply, Matrix.one_apply]

/-- The signed Hodge action is (E,B) ↦ (B,-E) in the frozen oriented pair basis. -/
theorem lorentz_hodge_blocks (K : Type*) [Field K] :
    hodge (eta K) 1 = starBlocks K := by
  rw [hodge, one_smul, eta_exterior_inv, eta_exterior]
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_diagonal, W, starBlocks, pairSigns]

/-- The real Lorentz Hodge star squares to minus the identity. -/
theorem real_hodge_square :
    hodge (eta ℝ) 1 * hodge (eta ℝ) 1 = -(1 : PairMatrix ℝ) := by
  rw [lorentz_hodge_blocks]
  simp only [starBlocks, fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add, mul_one]
  ext i j
  rcases i <;> rcases j <;> simp [Matrix.one_apply]

/-- Lowering the first index of the Lorentz matrix in the oriented pair basis. -/
def lorentz_to_twoForm {K : Type*} [Field K] (X : lorentzLie K) : PairIndex → K :=
  Sum.elim (fun i => (eta K * X.val) 0 i.succ)
    (fun i => (eta K * X.val) (![2,3,1] i) (![3,1,2] i))

theorem twoForm_coords {K : Type*} [Field K] (X : lorentzLie K) :
    lorentz_to_twoForm X = Sum.elim (-boosts X) (-rotations X) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [lorentz_to_twoForm, eta, boosts, rotations, Matrix.diagonal_mul]

private theorem hodge_apply {K : Type*} [Field K] (x : PairIndex → K) :
    hodge (eta K) 1 *ᵥ x = Sum.elim (fun i => x (.inr i)) (fun i => -x (.inl i)) := by
  rw [lorentz_hodge_blocks]
  funext i
  rcases i <;> simp [starBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- The minus-i Hodge eigenspace is precisely the first chiral graph, and plus-i the second. -/
theorem hodge_eigenspaces_eq_chiral (X : lorentzLie ℂ) :
    (hodge (eta ℂ) 1 *ᵥ lorentz_to_twoForm X =
        (-Complex.I) • lorentz_to_twoForm X ↔ (lorentz_chiral_sl2_prod X).2 = 0) ∧
    (hodge (eta ℂ) 1 *ᵥ lorentz_to_twoForm X =
        Complex.I • lorentz_to_twoForm X ↔ (lorentz_chiral_sl2_prod X).1 = 0) := by
  rw [twoForm_coords, hodge_apply]
  change (_ ↔ pauli ((chiralCoords (lorentzCoords ℂ X)).2) = 0) ∧
    (_ ↔ pauli ((chiralCoords (lorentzCoords ℂ X)).1) = 0)
  have pzero (v : Triple ℂ) : pauli v = 0 ↔ v = 0 := by
    change pauliCoords v = 0 ↔ v = 0
    rw [← map_zero pauliCoords]
    exact pauliCoords.injective.eq_iff
  rw [pzero, pzero]
  constructor <;> constructor
  · intro h
    funext i
    have hi := congrFun h (.inl i)
    change -rotations X i = -Complex.I * -boosts X i at hi
    change rotations X i + Complex.I * boosts X i = 0
    linear_combination -hi
  · intro h
    funext i
    rcases i with i | i
    all_goals
      have hi := congrFun h i
      change rotations X i + Complex.I * boosts X i = 0 at hi
      simp
    · have ha : rotations X i = -Complex.I * boosts X i := by linear_combination hi
      rw [ha] <;> ring
    · have ha : rotations X i = -Complex.I * boosts X i := by linear_combination hi
      rw [ha] <;> ring_nf <;> simp [Complex.I_sq]
  · intro h
    funext i
    have hi := congrFun h (.inl i)
    change -rotations X i = Complex.I * -boosts X i at hi
    change rotations X i - Complex.I * boosts X i = 0
    linear_combination -hi
  · intro h
    funext i
    rcases i with i | i
    all_goals
      have hi := congrFun h i
      change rotations X i - Complex.I * boosts X i = 0 at hi
      simp
    · have ha : rotations X i = Complex.I * boosts X i := by linear_combination hi
      rw [ha] <;> ring
    · have ha : rotations X i = Complex.I * boosts X i := by linear_combination hi
      rw [ha] <;> ring_nf <;> simp [Complex.I_sq]

/-- All chiral brackets are represented by the standard cross-product table in the two factors. -/
theorem chiral_brackets (i j : Fin 3) :
    lorentz_chiral_sl2_prod ⁅chiralPlus i, chiralPlus j⁆ =
      (pauli (cross (Pi.single i 1) (Pi.single j 1)), 0) ∧
    lorentz_chiral_sl2_prod ⁅chiralMinus i, chiralMinus j⁆ =
      (0, pauli (cross (Pi.single i 1) (Pi.single j 1))) ∧
    ⁅chiralPlus i, chiralMinus j⁆ = 0 := by
  refine ⟨?_, ?_, chiral_mixed_bracket i j⟩
  · rw [LieEquiv.map_lie, (chiral_generator_images i).1, (chiral_generator_images j).1]
    change (⁅pauli (Pi.single i 1), pauli (Pi.single j 1)⁆, ⁅(0 : SL2C), 0⁆) = _
    rw [pauli_bracket, lie_zero]
  · rw [LieEquiv.map_lie, (chiral_generator_images i).2, (chiral_generator_images j).2]
    change (⁅(0 : SL2C), 0⁆, ⁅pauli (Pi.single i 1), pauli (Pi.single j 1)⁆) = _
    rw [pauli_bracket, lie_zero]

/-- The three-dimensional graph of magnetic coefficients over electric coefficients. -/
def chiralGraph (z : ℂ) : Matrix PairIndex (Fin 3) ℂ
  | .inl i => (1 : Matrix (Fin 3) (Fin 3) ℂ) i
  | .inr i => (z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) i

/-- Each Hodge eigenvector is determined by three electric entries. -/
theorem hodge_eigen_graph (z : ℂ) (hz : z ^ 2 = -1) (x : PairIndex → ℂ) :
    hodge (eta ℂ) 1 *ᵥ x = z • x ↔
    ∀ i, x (.inr i) = z * x (.inl i) := by
  rw [hodge_apply]
  constructor
  · intro h i
    exact congrFun h (.inl i)
  · intro h
    funext i
    rcases i with i | i
    · exact h i
    · change -x (.inl i) = z * x (.inr i)
      rw [h i, ← mul_assoc, ← pow_two, hz, neg_one_mul]

/-- The wedge pairing is nondegenerate on either graph of a square root of minus one. -/
theorem chiral_graph_gram (z : ℂ) :
    wedgeGram (chiralGraph z) = (2*z) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  simp [wedgeGram, W, chiralGraph, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  split_ifs <;> ring

/-- Complex conjugation exchanges the two chiral graphs. -/
theorem chiral_graph_conj : (chiralGraph Complex.I).map star = chiralGraph (-Complex.I) := by
  ext i j
  rcases i with i | i <;>
    simp [chiralGraph, Matrix.one_apply] <;> split_ifs <;> simp

/-- The frozen Urbantke normalization is the graph of the positive imaginary unit. -/
theorem urbantke_chiral_graph :
    urbantke (chiralGraph Complex.I) = -eta ℂ ∧
    density (chiralGraph Complex.I) = -Complex.I := by
  obtain ⟨_, h, _, hD⟩ := urbantke_lorentz_witness
  refine ⟨?_, hD⟩
  change urbantke (chiralGraph Complex.I) = _ at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, Matrix.diagonal_apply]

/-- The bivector coordinates of the frozen null screen wedge. -/
def screenWedge (r : WeylNullScreen.FutureNullRay) : PairIndex → ℂ :=
  fun p => WeylNullScreen.screenVector r (pairL p) * (WeylNullScreen.nullGenerator r (pairR p) : ℂ) -
    WeylNullScreen.screenVector r (pairR p) * (WeylNullScreen.nullGenerator r (pairL p) : ℂ)

/-- In raw oriented pair coefficients the frozen null screen lies in the minus-i Hodge plane. -/
theorem weyl_screen_in_chiral_plane (r : WeylNullScreen.FutureNullRay) :
    hodge (eta ℂ) 1 *ᵥ screenWedge r = -Complex.I • screenWedge r := by
  apply (hodge_eigen_graph (-Complex.I) (by simp [Complex.I_sq]) _).2
  intro i
  cases r with
  | none =>
    fin_cases i <;> simp [screenWedge, pairL, pairR, WeylNullScreen.screenVector, WeylNullScreen.nullGenerator] <;> ring
  | some z =>
    fin_cases i <;> apply Complex.ext <;>
      simp [screenWedge, pairL, pairR, WeylNullScreen.screenVector, WeylNullScreen.nullGenerator,
        Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

end D5.S3.Geometry.Lorentz.HodgeChiralLie
