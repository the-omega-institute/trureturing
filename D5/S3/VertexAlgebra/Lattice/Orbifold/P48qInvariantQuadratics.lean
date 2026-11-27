/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qInvariantQuadratics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invariant orthogonal blocks give independent fixed lattice states of weight two. -/

import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
A Gram-dual basis sum of current products gives the quadratic state of a
rational block in the actual untwisted lattice carrier. Its mode one projects
currents onto the block. The prime-to-three reducibility theorem supplies the
block for the rank-48 Nebe lattice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticePositiveEnergy
open LatticeSugawaraCurrents
open Lattice.Automorphisms.ConformalGroundTransport (current)
open scoped BigOperators Matrix VertexOperator

noncomputable section

abbrev RationalCartan (D : LatticeData) := Fin D.rank → ℚ

/-- The integral Gram matrix extended to the rational Cartan space. -/
def rationalGram (D : LatticeData) : LinearMap.BilinForm ℚ (RationalCartan D) :=
  (D.G.map (Int.cast : ℤ → ℚ)).toBilin'

/-- The actual current of a rational Cartan direction. -/
def rationalCurrent (D : LatticeData) (x : RationalCartan D) : Carrier D :=
  current D (fun i => (x i : ℂ))

private abbrev gram (D : LatticeData) := (gramComplex D).toBilin'

private theorem rationalGram_symm (D : LatticeData) : (rationalGram D).IsSymm := by
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  exact Matrix.IsSymm.ext fun i j => congrArg (Int.castRingHom ℚ) (D.symmetric j i)

private theorem gram_cast (D : LatticeData) (x y : RationalCartan D) :
    gram D (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) = (rationalGram D x y : ℂ) := by
  simp [rationalGram, gramComplex, Matrix.toBilin'_apply]

private theorem rationalGram_self_ne_zero (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x : RationalCartan D) (hx : x ≠ 0) : rationalGram D x x ≠ 0 := by
  let r : Fin D.rank → ℝ := fun i => (x i : ℝ)
  have hr : r ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi : (x i : ℝ) = 0 := congrFun h i
    exact_mod_cast hi
  have hp : 0 < r ⬝ᵥ ((D.G.map (Int.cast : ℤ → ℝ)) *ᵥ r) := by
    simpa using hPos.dotProduct_mulVec_pos hr
  have he : (rationalGram D x x : ℝ) = r ⬝ᵥ ((D.G.map (Int.cast : ℤ → ℝ)) *ᵥ r) := by
    simp [rationalGram, Matrix.toBilin'_apply', r, dotProduct, Matrix.mulVec]
  intro h
  rw [← he, h, Rat.cast_zero] at hp
  exact (lt_irrefl 0) hp

private theorem restrict_nondegenerate (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) : ((rationalGram D).restrict W).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro x hx
  by_contra hn
  have hself := LinearMap.congr_fun hx x
  exact rationalGram_self_ne_zero D hPos x (fun h => hn (Subtype.ext h)) hself

private def product (D : LatticeData) (n : ℤ) :
    Carrier D →ₗ[ℂ] Carrier D →ₗ[ℂ] Carrier D where
  toFun a := (Y D a)[[n]]
  map_add' a b := by simp
  map_smul' c a := by simp

private theorem product_apply (D : LatticeData) (n : ℤ) (a b : Carrier D) :
    product D n a b = mu D a n b := rfl

private def currentLinear (D : LatticeData) : (Fin D.rank → ℂ) →ₗ[ℂ] Carrier D where
  toFun := current D
  map_add' x y := by simp [current, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [current, Finset.smul_sum, mul_smul]

private theorem current_single (D : LatticeData) (i : Fin D.rank) :
    currentLinear D (Pi.single i 1) = currentState D i := by
  classical
  change current D _ = _
  simp [current, Pi.single_apply, Finset.sum_ite_eq']

private theorem current_injective (D : LatticeData) : Function.Injective (currentLinear D) := by
  intro x y h
  funext i
  have hcoeff (v : Fin D.rank → ℂ) :
      ((currentLinear D v) 0).coeff (Finsupp.single (i, 0) 1) = v i := by
    classical
    change ((∑ j, v j • currentState D j) 0 : Oscillator D).coeff _ = _
    simp only [currentState, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.X,
      MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have hne : Finsupp.single (j, 0) (1 : ℕ) ≠ Finsupp.single (i, 0) 1 := by
        intro he
        exact hj (congrArg Prod.fst ((Finsupp.single_left_inj (by decide)).mp he))
      simp [hne]
    · simp
  rw [← hcoeff x, ← hcoeff y, h]

private theorem rationalCurrent_ne_zero (D : LatticeData) {x : RationalCartan D} (hx : x ≠ 0) :
    rationalCurrent D x ≠ 0 := by
  intro h
  have he := current_injective D
    (show currentLinear D (fun i => (x i : ℂ)) = currentLinear D 0 by
      rw [map_zero]
      exact h)
  apply hx
  funext i
  have hi : (x i : ℂ) = 0 := congrFun he i
  exact_mod_cast hi

private def currentPair (D : LatticeData) :
    (Fin D.rank → ℂ) →ₗ[ℂ] (Fin D.rank → ℂ) →ₗ[ℂ] Carrier D :=
  (product D (-1)).compl₁₂ (currentLinear D) (currentLinear D)

private theorem basis_pair_one (D : LatticeData) (i j k : Fin D.rank) :
    mu D (mu D (currentState D i) (-1) (currentState D j)) 1 (currentState D k) =
      (D.G j k : ℂ) • currentState D i + (D.G i k : ℂ) • currentState D j := by
  have h := LinearMap.congr_fun (quadraticSummand_current_commutator D i j k 0 (-1)) (vacuum D)
  have hz : ((quadraticSummand D i j)[[1]]) (vacuum D) = 0 := by
    rw [← quadratic_state_field]
    exact stateField_creativity D _ 1 (by decide)
  have hc (a : Fin D.rank) : neutralMode D a (-1) (vacuum D) = currentState D a := by
    rw [← neutralField_ncoeff]
    exact current_state_creation D a
  simp only [zero_add, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.add_apply, hz, hc, map_zero, sub_zero] at h
  rw [mu, current_minus_one_current, quadratic_state_field]
  simpa using h

private theorem pair_one (D : LatticeData) (x y z : Fin D.rank → ℂ) :
    product D 1 (currentPair D x y) (currentLinear D z) =
      gram D y z • currentLinear D x + gram D x z • currentLinear D y := by
  let b := Pi.basisFun ℂ (Fin D.rank)
  let left (x y z : Fin D.rank → ℂ) := product D 1 (currentPair D x y) (currentLinear D z)
  let right (x y z : Fin D.rank → ℂ) :=
    gram D y z • currentLinear D x + gram D x z • currentLinear D y
  change left x y z = right x y z
  have extend (f g : (Fin D.rank → ℂ) →ₗ[ℂ] Carrier D)
      (h : ∀ i, f (b i) = g (b i)) (v : Fin D.rank → ℂ) : f v = g v :=
    LinearMap.congr_fun (b.ext h) v
  have hx (y z : Fin D.rank → ℂ)
      (h : ∀ i, left (b i) y z = right (b i) y z) : left x y z = right x y z :=
    extend (((product D 1).flip (currentLinear D z)).comp ((currentPair D).flip y))
      (gram D y z • currentLinear D +
        (LinearMap.id.smulRight (currentLinear D y)).comp ((gram D).flip z)) h x
  have hy (x z : Fin D.rank → ℂ)
      (h : ∀ i, left x (b i) z = right x (b i) z) : left x y z = right x y z :=
    extend (((product D 1).flip (currentLinear D z)).comp (currentPair D x))
      ((LinearMap.id.smulRight (currentLinear D x)).comp ((gram D).flip z) +
        gram D x z • currentLinear D) h y
  have hz (x y : Fin D.rank → ℂ)
      (h : ∀ i, left x y (b i) = right x y (b i)) : left x y z = right x y z :=
    extend ((product D 1 (currentPair D x y)).comp (currentLinear D))
      (((gram D) y).smulRight (currentLinear D x) +
        ((gram D) x).smulRight (currentLinear D y)) h z
  apply hx y z
  intro i
  apply hy (b i) z
  intro j
  apply hz (b i) (b j)
  intro k
  have hb (a : Fin D.rank) : b a = Pi.single a 1 := Pi.basisFun_apply _ _ _
  have hg (a c : Fin D.rank) :
      gram D (Pi.single a 1) (Pi.single c 1) = (D.G a c : ℂ) := by
    classical
    rw [Matrix.toBilin'_apply']
    simp [gramComplex]
  simpa only [left, right, LinearMap.compl₁₂_apply, currentPair, Function.comp_apply,
    product_apply, hb, current_single, hg] using basis_pair_one D i j k

private def castCoordinates (D : LatticeData) : RationalCartan D →ₗ[ℚ] (Fin D.rank → ℂ) where
  toFun x i := (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' c x := by
    ext i
    change ((c * x i : ℚ) : ℂ) = c • (x i : ℂ)
    rw [Rat.cast_mul, ← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]

private def rationalPair (D : LatticeData) :
    RationalCartan D →ₗ[ℚ] RationalCartan D →ₗ[ℚ] Carrier D :=
  ((LinearMap.restrictScalarsₗ ℚ ℂ _ _ ℚ).comp ((currentPair D).restrictScalars ℚ)).compl₁₂
    (castCoordinates D) (castCoordinates D)

private theorem rational_pair_one (D : LatticeData) (x y z : RationalCartan D) :
    product D 1 (rationalPair D x y) (rationalCurrent D z) =
      (rationalGram D y z : ℂ) • rationalCurrent D x +
        (rationalGram D x z : ℂ) • rationalCurrent D y := by
  change product D 1 (currentPair D (castCoordinates D x) (castCoordinates D y))
    (currentLinear D (castCoordinates D z)) = _
  rw [pair_one]
  change gram D (fun i => (y i : ℂ)) (fun i => (z i : ℂ)) • rationalCurrent D x +
    gram D (fun i => (x i : ℂ)) (fun i => (z i : ℂ)) • rationalCurrent D y = _
  rw [gram_cast, gram_cast]

private theorem dual_pair_repr {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Finite ι] [DecidableEq ι] (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ V) (i : ι) (x : V) :
    B (B.dualBasis hB b i) x = b.repr x i := by
  let := b.finiteDimensional_of_finite
  rw [LinearMap.BilinForm.dualBasis, Module.Basis.map_apply, Module.Basis.coe_dualBasis,
    B.apply_toDual_symm_apply, Module.Basis.coord_apply]

private def quadraticOfBasis (D : LatticeData)
    (W : Submodule ℚ (RationalCartan D))
    (hB : ((rationalGram D).restrict W).Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ W) : Carrier D :=
  (2 : ℂ)⁻¹ • ∑ i, rationalPair D (b i : RationalCartan D)
    (((rationalGram D).restrict W).dualBasis hB b i : RationalCartan D)

/-- The actual half-normalized quadratic state of a rational Cartan block. -/
def blockQuadratic (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) : Carrier D :=
  quadraticOfBasis D W (restrict_nondegenerate D hPos W) (Module.finBasis ℚ W)

set_option maxHeartbeats 1500000 in
-- Expanding both finite basis sums requires reducing the Gram-dual basis maps.
private theorem quadratic_basis_independent (D : LatticeData)
    (W : Submodule ℚ (RationalCartan D))
    (hB : ((rationalGram D).restrict W).Nondegenerate)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℚ W) (c : Module.Basis κ ℚ W) :
    quadraticOfBasis D W hB b = quadraticOfBasis D W hB c := by
  let B := (rationalGram D).restrict W
  let P := (rationalPair D).compl₁₂ W.subtype W.subtype
  let db := B.dualBasis hB b
  let dc := B.dualBasis hB c
  have hdual (j : κ) : ∑ i, c.repr (b i) j • db i = dc j := by
    calc
      _ = ∑ i, db.repr (dc j) i • db i := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        change c.repr (b i) j = (B.dualBasis hB b).repr (dc j) i
        rw [B.dualBasis_repr_apply]
        exact (dual_pair_repr B hB c j (b i)).symm
      _ = dc j := db.sum_repr (dc j)
  change (2 : ℂ)⁻¹ • (∑ i, P (b i) (db i)) = (2 : ℂ)⁻¹ • ∑ j, P (c j) (dc j)
  congr 1
  calc
    (∑ i, P (b i) (db i)) = ∑ i, ∑ j, c.repr (b i) j • P (c j) (db i) := by
      apply Finset.sum_congr rfl
      intro i _
      change P.flip (db i) (b i) = ∑ j, c.repr (b i) j • P.flip (db i) (c j)
      simp only [← map_smul, ← map_sum, Module.Basis.sum_repr]
    _ = ∑ j, ∑ i, c.repr (b i) j • P (c j) (db i) := Finset.sum_comm
    _ = ∑ j, P (c j) (dc j) := by simp only [← map_smul, ← map_sum, hdual]

private theorem rationalCurrent_grade_one (D : LatticeData) (x : RationalCartan D) :
    rationalCurrent D x ∈ grade D 1 := by
  classical
  unfold rationalCurrent current
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [mem_grade_iff]
  intro a ha
  by_cases hcharge : a.1 = 0
  · by_cases hexp : a.2 = Finsupp.single (i, 0) 1
    · exfalso
      apply ha
      simp [energy, hcharge, hexp, oscillatorEnergy, Finsupp.weight_single]
    · simp [currentState, hcharge, MvPolynomial.X, MvPolynomial.coeff_monomial, Ne.symm hexp]
  · simp [currentState, hcharge]

private theorem block_grade_two (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) :
    blockQuadratic D hPos W ∈ grade D 2 := by
  unfold blockQuadratic quadraticOfBasis
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  change mu D (rationalCurrent D _) (-1) (rationalCurrent D _) ∈ grade D 2
  simpa only [mu, show (1 : ℤ) + 1 - (-1) - 1 = 2 by decide] using
    positive_actual_mode_grade D hPos 1 1 (-1) _ _
      (rationalCurrent_grade_one D _) (rationalCurrent_grade_one D _)

set_option maxHeartbeats 1500000 in
-- Changing the mode expression to a Gram-dual basis sum requires extra elaboration.
/-- A block's quadratic mode one fixes each current from that block. -/
theorem blockQuadratic_mode_one_of_mem (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) (x : W) :
    mu D (blockQuadratic D hPos W) 1 (rationalCurrent D x) = rationalCurrent D x := by
  let B := (rationalGram D).restrict W
  let b := Module.finBasis ℚ W
  let db := B.dualBasis (restrict_nondegenerate D hPos W) b
  let J := ((currentLinear D).restrictScalars ℚ).comp ((castCoordinates D).comp W.subtype)
  let hB := restrict_nondegenerate D hPos W
  have hsym (u v : W) : B u v = B v u := (rationalGram_symm D).eq _ _
  have hrepr (i : Fin (Module.finrank ℚ W)) : B (db i) x = b.repr x i :=
    dual_pair_repr B hB b i x
  have hrepr' (i : Fin (Module.finrank ℚ W)) : B (b i) x = db.repr x i :=
    (hsym _ _).trans (B.dualBasis_repr_apply hB b x i).symm
  have hfirst : ∑ i, (B (db i) x : ℂ) • J (b i) = J x := by
    simp only [hrepr, Rat.cast_smul_eq_qsmul, ← map_smul, ← map_sum, Module.Basis.sum_repr]
  have hsecond : ∑ i, (B (b i) x : ℂ) • J (db i) = J x := by
    simp only [hrepr', Rat.cast_smul_eq_qsmul, ← map_smul, ← map_sum, Module.Basis.sum_repr]
  change (product D 1).flip (rationalCurrent D x)
    ((2 : ℂ)⁻¹ • ∑ i, rationalPair D (b i) (db i)) = _
  simp only [map_smul, map_sum, LinearMap.flip_apply, rational_pair_one]
  change (2 : ℂ)⁻¹ • (∑ i, ((B (db i) x : ℂ) • J (b i) +
    (B (b i) x : ℂ) • J (db i))) = J x
  rw [Finset.sum_add_distrib, hfirst, hsecond, ← two_smul ℂ, smul_smul]
  norm_num

set_option maxHeartbeats 1500000 in
-- Changing the mode expression to a Gram-dual basis sum requires extra elaboration.
/-- A block's quadratic mode one vanishes on each perpendicular current. -/
theorem blockQuadratic_mode_one_of_orthogonal (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) {x : RationalCartan D}
    (hx : x ∈ (rationalGram D).orthogonal W) :
    mu D (blockQuadratic D hPos W) 1 (rationalCurrent D x) = 0 := by
  let b := Module.finBasis ℚ W
  let db := ((rationalGram D).restrict W).dualBasis (restrict_nondegenerate D hPos W) b
  change (product D 1).flip (rationalCurrent D x)
    ((2 : ℂ)⁻¹ • ∑ i, rationalPair D (b i) (db i)) = _
  simp only [map_smul, map_sum, LinearMap.flip_apply, rational_pair_one]
  have ho := LinearMap.BilinForm.mem_orthogonal_iff.mp hx
  simp only [ho _ (Subtype.property (db _)), ho _ (Subtype.property (b _)), Rat.cast_zero,
    zero_smul, add_zero, Finset.sum_const_zero, smul_zero]

variable {G : Type*} [Group G]

set_option maxHeartbeats 1500000 in
-- Transporting the dual basis through the restricted action requires extra elaboration.
private theorem block_fixed (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (ρ : Representation ℚ G (RationalCartan D)) (A : Representation ℂ G (Carrier D))
    (hGram : ∀ g x y, rationalGram D (ρ g x) (ρ g y) = rationalGram D x y)
    (hCurrent : ∀ g x, A g (rationalCurrent D x) = rationalCurrent D (ρ g x))
    (hMode : ∀ g u n v, A g (mu D u n v) = mu D (A g u) n (A g v))
    (W : Submodule ℚ (RationalCartan D)) (hW : ∀ g, W ≤ W.comap (ρ g)) (g : G) :
    A g (blockQuadratic D hPos W) = blockQuadratic D hPos W := by
  classical
  let B := (rationalGram D).restrict W
  let hB := restrict_nondegenerate D hPos W
  let b := Module.finBasis ℚ W
  let T := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  have hm : W.map (ρ g) = W := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr (hW g)
    · intro x hx
      exact ⟨ρ g⁻¹ x, hW g⁻¹ hx, ρ.self_inv_apply g x⟩
  let e := T.ofSubmodules W W hm
  have he (x : W) : (e x : RationalCartan D) = ρ g x := rfl
  let c := b.map e
  have hc (i : Fin (Module.finrank ℚ W)) : c i = e (b i) := Module.Basis.map_apply _ _ _
  have hdual (i : Fin (Module.finrank ℚ W)) :
      B.dualBasis hB c i = e (B.dualBasis hB b i) := by
    refine congrFun ((B.dualBasis_eq_iff hB c (fun j => e (B.dualBasis hB b j))).mpr ?_) i
    intro j k
    rw [hc]
    change rationalGram D (e (B.dualBasis hB b j)) (e (b k)) = _
    rw [he, he, hGram]
    exact B.apply_dualBasis_left hB b j k
  change A g (quadraticOfBasis D W hB b) = quadraticOfBasis D W hB b
  have hact : A g (quadraticOfBasis D W hB b) = quadraticOfBasis D W hB c := by
    unfold quadraticOfBasis
    change A g ((2 : ℂ)⁻¹ • ∑ i, mu D (rationalCurrent D (b i)) (-1)
      (rationalCurrent D (B.dualBasis hB b i))) =
      (2 : ℂ)⁻¹ • ∑ i, mu D (rationalCurrent D (c i)) (-1)
        (rationalCurrent D (B.dualBasis hB c i))
    simp only [map_smul, map_sum, hMode, hCurrent, hc, hdual, he]
  exact hact.trans (quadratic_basis_independent D W hB c b)

/-- A nonzero proper invariant rational Cartan subspace supplies two degree-two
states of the actual untwisted lattice algebra, fixed by the lifted action. -/
theorem invariant_block_quadratics (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (ρ : Representation ℚ G (RationalCartan D)) (A : Representation ℂ G (Carrier D))
    (hGram : ∀ g x y, rationalGram D (ρ g x) (ρ g y) = rationalGram D x y)
    (hCurrent : ∀ g x, A g (rationalCurrent D x) = rationalCurrent D (ρ g x))
    (hMode : ∀ g u n v, A g (mu D u n v) = mu D (A g u) n (A g v))
    (W : Submodule ℚ (RationalCartan D)) (hbot : W ≠ ⊥) (htop : W ≠ ⊤)
    (hW : ∀ g, W ≤ W.comap (ρ g)) :
    let q : Fin 2 → Carrier D :=
      ![blockQuadratic D hPos W, blockQuadratic D hPos ((rationalGram D).orthogonal W)]
    (∀ i, q i ∈ grade D 2) ∧ (∀ g i, A g (q i) = q i) ∧ LinearIndependent ℂ q := by
  classical
  intro q
  let P := (rationalGram D).orthogonal W
  have hP : ∀ g, P ≤ P.comap (ρ g) := by
    intro g x hx
    change ρ g x ∈ (rationalGram D).orthogonal W
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro y hy
    have he := hGram g (ρ g⁻¹ y) x
    rw [ρ.self_inv_apply] at he
    exact he.trans (hx _ (hW g⁻¹ hy))
  have hcompl := (rationalGram D).isCompl_orthogonal_of_restrict_nondegenerate
    (rationalGram_symm D).isRefl (restrict_nondegenerate D hPos W)
  have hPbot : P ≠ ⊥ := by
    intro he
    have hs := hcompl.sup_eq_top
    change W ⊔ P = ⊤ at hs
    rw [he, sup_bot_eq] at hs
    exact htop hs
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact block_grade_two D hPos W
    · exact block_grade_two D hPos P
  · intro g i
    fin_cases i
    · exact block_fixed D hPos ρ A hGram hCurrent hMode W hW g
    · exact block_fixed D hPos ρ A hGram hCurrent hMode P hP g
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPbot
    rw [linearIndependent_fin2]
    change blockQuadratic D hPos P ≠ 0 ∧
      ∀ a : ℂ, a • blockQuadratic D hPos P ≠ blockQuadratic D hPos W
    constructor
    · intro he
      have h := blockQuadratic_mode_one_of_mem D hPos P ⟨y, hy⟩
      change (product D 1).flip (rationalCurrent D y) (blockQuadratic D hPos P) =
        rationalCurrent D y at h
      rw [he, map_zero] at h
      exact rationalCurrent_ne_zero D hy0 h.symm
    · intro a he
      have h := congrArg ((product D 1).flip (rationalCurrent D x)) he
      have hxP : x ∈ (rationalGram D).orthogonal P :=
        LinearMap.BilinForm.mem_orthogonal_iff.mpr fun z hz =>
          ((rationalGram_symm D).eq z x).trans ((LinearMap.BilinForm.mem_orthogonal_iff.mp hz) x hx)
      rw [map_smul] at h
      change a • mu D (blockQuadratic D hPos P) 1 (rationalCurrent D x) =
        mu D (blockQuadratic D hPos W) 1 (rationalCurrent D x) at h
      rw [blockQuadratic_mode_one_of_orthogonal D hPos P hxP,
        blockQuadratic_mode_one_of_mem D hPos W ⟨x, hx⟩, smul_zero] at h
      exact rationalCurrent_ne_zero D hx0 h.symm

open P48qGramCertificate (nebeLatticeData)

/-- Every compatible lift of a faithful prime-to-three subgroup action on
the Nebe lattice has two independent invariant states of actual weight two. -/
theorem p48q_prime_to_three_fixed_weight_two
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 47)))
    (hH : ¬ 3 ∣ Nat.card H)
    (ρ : Representation ℚ H (RationalCartan nebeLatticeData))
    (hρ : Function.Injective ρ) (A : Representation ℂ H (Carrier nebeLatticeData))
    (hGram : ∀ g x y, rationalGram nebeLatticeData (ρ g x) (ρ g y) =
      rationalGram nebeLatticeData x y)
    (hCurrent : ∀ g x, A g (rationalCurrent nebeLatticeData x) =
      rationalCurrent nebeLatticeData (ρ g x))
    (hMode : ∀ g u n v, A g (mu nebeLatticeData u n v) =
      mu nebeLatticeData (A g u) n (A g v)) :
    ∃ q : Fin 2 → Carrier nebeLatticeData,
      (∀ i, q i ∈ grade nebeLatticeData 2) ∧ (∀ g i, A g (q i) = q i) ∧
        LinearIndependent ℂ q := by
  have hr : Module.finrank ℚ (RationalCartan nebeLatticeData) = 48 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rfl
  obtain ⟨W, hbot, htop, hW⟩ :=
    ExtremalC48.sl47_prime_to_three_exists_invariant_subspace H hH ρ hρ hr
  let hPos := P48qGramPositivity.nebeGram_posDef
  refine ⟨![blockQuadratic nebeLatticeData hPos W,
    blockQuadratic nebeLatticeData hPos ((rationalGram nebeLatticeData).orthogonal W)], ?_⟩
  exact invariant_block_quadratics nebeLatticeData hPos ρ A hGram hCurrent hMode W hbot htop hW

run_cmd do
  for name in [``blockQuadratic_mode_one_of_mem, ``blockQuadratic_mode_one_of_orthogonal,
      ``invariant_block_quadratics, ``p48q_prime_to_three_fixed_weight_two] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
