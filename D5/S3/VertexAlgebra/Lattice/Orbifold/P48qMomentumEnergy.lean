/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMomentumEnergy
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed Cartan zero modes and their quadratic energy on P48q momenta. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairingDraft
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-!
The fixed Cartan zero modes and their quadratic Casimir on the P48q twisted
ground charge representation. The index of a ground vector is the integral
numerator of its physical momentum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy

open LatticeGeneratingFieldLocality P48qTwistedChargeAction
open P48qFixedRankCertificateDraft P48qGramCertificateDraft
open ThirdEigenspacePairing (p48qAction p48qForm)
open scoped BigOperators Matrix

noncomputable section

local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "shiftMomentum" => ThirdTwistedChargeAction.shift lattice g

/-- The fixed complex subspace in the same Nebe coordinates as the charge action. -/
abbrev Fixed := LinearMap.ker (p48qAction - 1)

private theorem mem_fixed_iff (x : Fin 48 → ℂ) : x ∈ Fixed ↔ p48qAction x = x := by
  simp only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem fixed_finrank : Module.finrank ℂ Fixed = 16 :=
  rowAction_fixedRank16_of_certificate ℂ nebeOrderThree
    nebeOrderThree_cube nebeOrderThree_trace nebeOrderThree_trace_square

/-- A basis of the actual fixed space indexed by its certified rank. -/
def fixedBasis : Module.Basis (Fin 16) ℂ Fixed :=
  Module.finBasisOfFinrankEq ℂ _ fixed_finrank

/-- The restriction of the complex bilinear Gram form to fixed currents. -/
def fixedGram : LinearMap.BilinForm ℂ Fixed := p48qForm.restrict Fixed

theorem fixedGram_symm : fixedGram.IsSymm := by
  have h : p48qForm.IsSymm := by
    change ((nebeGram.map (Int.castRingHom ℂ)).toBilin').IsSymm
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    exact Matrix.IsSymm.ext fun i j => congrArg (Int.castRingHom ℂ) (lattice.symmetric j i)
  exact h.restrict Fixed

private theorem action_cube : p48qAction ^ 3 = 1 := by
  let c := Int.castRingHom ℂ
  change (c.mapMatrix nebeOrderThreeᵀ).toLin' ^ 3 = 1
  have ht : nebeOrderThreeᵀ ^ 3 = 1 := by
    rw [← Matrix.transpose_pow, nebeOrderThree_cube, Matrix.transpose_one]
  rw [← Matrix.toLin'_pow, ← map_pow, ht, map_one, Matrix.toLin'_one, ← Module.End.one_eq_id]

private theorem gram_invariant (x y : Fin 48 → ℂ) :
    p48qForm (p48qAction x) (p48qAction y) = p48qForm x y := by
  let c := Int.castRingHom ℂ
  let G := c.mapMatrix nebeGram
  let P := c.mapMatrix nebeOrderThreeᵀ
  have h : Pᵀ * G * P = G := by
    change c.mapMatrix nebeOrderThree * c.mapMatrix nebeGram * c.mapMatrix nebeOrderThreeᵀ = G
    rw [← map_mul, ← map_mul, gram_isometry_certificate]
  change (G.toBilin'.comp P.toLin' P.toLin') x y = G.toBilin' x y
  rw [Matrix.toBilin'_comp, h]

private theorem gram_nondegenerate : p48qForm.Nondegenerate := by
  let c := Int.castRingHom ℂ
  let G := c.mapMatrix nebeGram
  change G.toBilin'.Nondegenerate
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  have hInv : c.mapMatrix nebeGramInverse * Gᵀ = 1 := by
    change c.mapMatrix nebeGramInverse * c.mapMatrix nebeGramᵀ = 1
    rw [← map_mul, gram_inverse_certificate, map_one]
  have hdet := congrArg Matrix.det hInv
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  intro h
  rw [h, mul_zero] at hdet
  exact zero_ne_one hdet

/-- A fixed vector pairs with any vector as it does with its order-three average.
The ambient inverse Gram certificate therefore gives nondegeneracy on the fixed space. -/
theorem fixedGram_nondegenerate : fixedGram.Nondegenerate := by
  let P : Module.End ℂ (Fin 48 → ℂ) := (3 : ℂ)⁻¹ • (1 + p48qAction + p48qAction ^ 2)
  have hP : LinearMap.IsProj Fixed P := orderThreeAverage_isProj p48qAction action_cube
  have hLeft : fixedGram.SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : Fin 48 → ℂ) = 0
    apply gram_nondegenerate.1
    intro y
    have hfix := (mem_fixed_iff _).mp x.property
    have hstep (z : Fin 48 → ℂ) : p48qForm (x : Fin 48 → ℂ) (p48qAction z) =
        p48qForm (x : Fin 48 → ℂ) z := by
      simpa only [hfix] using gram_invariant (x : Fin 48 → ℂ) z
    have hzero : p48qForm (x : Fin 48 → ℂ) (P y) = 0 := hx ⟨P y, hP.1 y⟩
    calc
      p48qForm (x : Fin 48 → ℂ) y = p48qForm (x : Fin 48 → ℂ) (P y) := by
        simp only [P, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
          pow_two, Module.End.mul_apply, LinearMap.BilinForm.smul_right,
          LinearMap.BilinForm.add_right, hstep]
        ring
      _ = 0 := hzero
  exact ⟨hLeft, fun x hx => hLeft x fun y => (fixedGram_symm.eq x y).trans (hx y)⟩

/-- Transport the algebraic dual basis through the restricted Gram form. -/
def fixedGramDual {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Fixed) :
    Module.Basis ι ℂ Fixed :=
  fixedGram.dualBasis fixedGram_nondegenerate b

theorem fixedGram_pair_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Fixed) (i j : ι) :
    fixedGram (b i) (fixedGramDual b j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right fixedGram_nondegenerate fixedGram_symm b i j

/-- The complex coordinates of an integral charge. -/
def chargeVector (a : Charge lattice) : Fin 48 → ℂ := fun i => (a i : ℂ)

private theorem gram_on_charges (K : Type*) [Field K] (a b : Charge lattice) :
    (nebeGram.map (Int.castRingHom K)).toBilin' (fun i => (a i : K)) (fun i => (b i : K)) =
      (bilinear lattice a b : K) := by
  change (lattice.G.map (Int.castRingHom K)).toBilin'
    (fun i => (a i : K)) (fun i => (b i : K)) = _
  simp only [Matrix.toBilin'_apply, Matrix.map_apply, Int.coe_castRingHom,
    bilinear, Int.cast_sum, Int.cast_mul]

private theorem action_chargeVector (a : Charge lattice) :
    p48qAction (chargeVector a) = chargeVector (g a) := by
  change (nebeOrderThreeᵀ).map (Int.castRingHom ℂ) *ᵥ chargeVector a = chargeVector (g a)
  rw [g_apply, ← Matrix.mulVec_transpose]
  exact funext fun i => ((Int.castRingHom ℂ).map_mulVec nebeOrderThreeᵀ a i).symm

private theorem momentum_numerator_fixed (p : Momentum) : chargeVector p.1 ∈ Fixed := by
  obtain ⟨a, ha⟩ := (show ∃ a, N a = p.1 from p.2)
  have h := ThirdTwistedChargeAction.norm_fixed lattice g g_cube a
  rw [ha] at h
  exact (mem_fixed_iff _).mpr (by rw [action_chargeVector, h])

/-- The norm-image index encodes the physical momentum by division by three. -/
def physicalMomentum (p : Momentum) : Fixed :=
  (3 : ℂ)⁻¹ • (⟨chargeVector p.1, momentum_numerator_fixed p⟩ : Fixed)

private theorem pairing_physicalMomentum (h : Fixed) (p : Momentum) :
    fixedGram h (physicalMomentum p) = p48qForm (h : Fin 48 → ℂ) (chargeVector p.1) / 3 := by
  change p48qForm (h : Fin 48 → ℂ) ((3 : ℂ)⁻¹ • chargeVector p.1) = _
  rw [LinearMap.BilinForm.smul_right, div_eq_mul_inv, mul_comm]

/-- The zero mode of a fixed Cartan current acts on the ground carrier. -/
def cartanZeroMode (h : Fixed) : Module.End ℂ Ground :=
  Finsupp.lsum ℂ fun p => fixedGram h (physicalMomentum p) • Finsupp.lsingle p

theorem cartanZeroMode_single (h : Fixed) (p : Momentum) (z : ℂ) :
    cartanZeroMode h (Finsupp.single p z) =
      fixedGram h (physicalMomentum p) • Finsupp.single p z := by
  simp only [cartanZeroMode, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

private theorem pairing_shift (h : Fixed) (a : Charge lattice) (p : Momentum) :
    fixedGram h (physicalMomentum (shiftMomentum a p)) =
      fixedGram h (physicalMomentum p) + p48qForm (h : Fin 48 → ℂ) (chargeVector (N a)) / 3 := by
  have hshift : chargeVector (shiftMomentum a p).1 = chargeVector p.1 + chargeVector (N a) := by
    change chargeVector (p.1 + N a) = _
    funext i
    simp only [chargeVector, Pi.add_apply, Int.cast_add]
  simp only [pairing_physicalMomentum, hshift, map_add, add_div]

private theorem cartanZeroMode_U_single (h : Fixed) (a : Charge lattice) (p : Momentum) (z : ℂ) :
    cartanZeroMode h (U a (Finsupp.single p z)) =
      fixedGram h (physicalMomentum (shiftMomentum a p)) • U a (Finsupp.single p z) := by
  have hU : ∃ c : ℂ, U a (Finsupp.single p z) = c • Finsupp.single (shiftMomentum a p) z := by
    unfold U
    exact ⟨_, ThirdTwistedChargeAction.U_single lattice g multiplier liftPhase movingExact _ a p z⟩
  obtain ⟨c, hc⟩ := hU
  rw [hc, map_smul, cartanZeroMode_single]
  simp only [smul_smul, mul_comm]

/-- The Cartan commutator uses the exact shift of the native twisted charge operator. -/
theorem cartanZeroMode_commutator_U (h : Fixed) (a : Charge lattice) :
    (cartanZeroMode h).comp (U a) - (U a).comp (cartanZeroMode h) =
      (p48qForm (h : Fin 48 → ℂ) (chargeVector (N a)) / 3) • U a := by
  apply Finsupp.lhom_ext
  intro p z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    cartanZeroMode_U_single, cartanZeroMode_single, map_smul, ← sub_smul, pairing_shift,
    add_sub_cancel_left]

private theorem gram_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Fixed) (x : Fixed) :
    (∑ i, fixedGram (fixedGramDual b i) x * fixedGram (b i) x) = fixedGram x x := by
  have h : (∑ i, fixedGram (b i) x • fixedGramDual b i) = x := by
    simpa only [fixedGramDual, LinearMap.BilinForm.dualBasis_repr_apply, fixedGram_symm.eq x]
      using (fixedGramDual b).sum_repr x
  calc
    _ = fixedGram (∑ i, fixedGram (b i) x • fixedGramDual b i) x := by
      rw [LinearMap.BilinForm.sum_left]
      simp only [LinearMap.BilinForm.smul_left, mul_comm]
    _ = fixedGram x x := by rw [h]

/-- The quadratic zero-mode Casimir with the fixed Gram-dual basis. -/
def momentumCasimir {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Fixed) :
    Module.End ℂ Ground :=
  (2 : ℂ)⁻¹ • ∑ i, (cartanZeroMode (fixedGramDual b i)).comp (cartanZeroMode (b i))

private theorem half_momentum_square (p : Momentum) :
    (2 : ℂ)⁻¹ * fixedGram (physicalMomentum p) (physicalMomentum p) =
      (bilinear lattice p.1 p.1 : ℂ) / 18 := by
  change (2 : ℂ)⁻¹ * p48qForm ((3 : ℂ)⁻¹ • chargeVector p.1)
    ((3 : ℂ)⁻¹ • chargeVector p.1) = _
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  have h : p48qForm (chargeVector p.1) (chargeVector p.1) = (bilinear lattice p.1 p.1 : ℂ) :=
    gram_on_charges ℂ p.1 p.1
  rw [h]
  ring

/-- Each norm-image line has zero-mode energy half the squared physical momentum. -/
theorem momentumCasimir_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Fixed) (p : Momentum) (z : ℂ) :
    momentumCasimir b (Finsupp.single p z) =
      ((bilinear lattice p.1 p.1 : ℂ) / 18) • Finsupp.single p z := by
  let x := physicalMomentum p
  calc
    _ = ((2 : ℂ)⁻¹ * ∑ i, fixedGram (fixedGramDual b i) x * fixedGram (b i) x) •
          Finsupp.single p z := by
      simp only [momentumCasimir, LinearMap.smul_apply, LinearMap.sum_apply,
        LinearMap.comp_apply, cartanZeroMode_single, map_smul, smul_smul, ← Finset.sum_smul, x]
      have hsum :
          (∑ i, fixedGram (b i) (physicalMomentum p) *
            fixedGram (fixedGramDual b i) (physicalMomentum p)) =
          ∑ i, fixedGram (fixedGramDual b i) (physicalMomentum p) *
            fixedGram (b i) (physicalMomentum p) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact mul_comm _ _
      rw [hsum]
    _ = _ := by rw [gram_contraction, half_momentum_square]

/-- The Casimir acts diagonally on every finitely supported ground vector. -/
theorem momentumCasimir_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Fixed) (v : Ground) (p : Momentum) :
    momentumCasimir b v p = ((bilinear lattice p.1 p.1 : ℂ) / 18) * v p := by
  have h : (Finsupp.lapply p : Ground →ₗ[ℂ] ℂ).comp (momentumCasimir b) =
      ((bilinear lattice p.1 p.1 : ℂ) / 18) • (Finsupp.lapply p : Ground →ₗ[ℂ] ℂ) := by
    apply Finsupp.lhom_ext
    intro q z
    simp only [LinearMap.comp_apply, momentumCasimir_single, LinearMap.smul_apply,
      Finsupp.lapply_apply, Finsupp.smul_apply]
    by_cases hp : p = q
    · subst q
      rfl
    · simp only [Finsupp.single_eq_of_ne hp, smul_zero]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
    using DFunLike.congr_fun h v

/-- The resulting endomorphism is independent of the chosen fixed-space basis. -/
theorem momentumCasimir_basis_independent {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℂ Fixed) (b' : Module.Basis κ ℂ Fixed) :
    momentumCasimir b = momentumCasimir b' := by
  apply Finsupp.lhom_ext
  intro p z
  rw [momentumCasimir_single b p z, momentumCasimir_single b' p z]

private theorem nonzero_norm_of_posDef
    (hPos : (nebeGram.map (Int.castRingHom ℝ)).PosDef) {p : Momentum} (hp : p ≠ 0) :
    (bilinear lattice p.1 p.1 : ℂ) ≠ 0 := by
  let x : Fin 48 → ℝ := fun i => (p.1 i : ℝ)
  have hx : x ≠ 0 := by
    intro he
    apply hp
    apply Subtype.ext
    funext i
    change p.1 i = 0
    have hi : (p.1 i : ℝ) = 0 := congrFun he i
    exact_mod_cast hi
  have hquad : 0 < (nebeGram.map (Int.castRingHom ℝ)).toBilin' x x := by
    rw [Matrix.toBilin'_apply']
    simpa only [star_trivial] using hPos.dotProduct_mulVec_pos hx
  have hnorm : 0 < (bilinear lattice p.1 p.1 : ℝ) := by
    rw [← gram_on_charges ℝ p.1 p.1]
    exact hquad
  intro h
  have hz : bilinear lattice p.1 p.1 = 0 := by exact_mod_cast h
  simp [hz] at hnorm

/-- Real Gram positivity implies that only the zero-momentum line has energy zero. -/
theorem momentumCasimir_ker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Fixed) (hPos : (nebeGram.map (Int.castRingHom ℝ)).PosDef) :
    (momentumCasimir b).ker =
      Submodule.span ℂ ({Finsupp.single (0 : Momentum) (1 : ℂ)} : Set Ground) := by
  apply Submodule.ext
  intro v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    apply Finsupp.ext
    intro p
    by_cases hp : p = 0
    · subst p
      simp [Finsupp.smul_apply]
    · have h := momentumCasimir_coeff b v p
      rw [hv, Finsupp.zero_apply] at h
      have hz : v p = 0 := (mul_eq_zero.mp h.symm).resolve_left
        (div_ne_zero (nonzero_norm_of_posDef hPos hp) (by norm_num))
      simp [Finsupp.smul_apply, Finsupp.single_eq_of_ne hp, hz]
  · rintro ⟨c, rfl⟩
    rw [map_smul, momentumCasimir_single]
    simp [bilinear]

/-- The Gram matrix used by the twisted charge action is positive definite. -/
theorem nebeGram_posDef : (nebeGram.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hGram : nebeGram = P48qGramCertificate.nebeGram := by
    with_unfolding_all rfl
  rw [hGram]
  exact P48qGramPositivity.nebeGram_posDef

/-- The zero eigenspace of the concrete momentum Casimir is the zero-momentum line. -/
theorem momentumCasimir_ker_fixedBasis :
    (momentumCasimir fixedBasis).ker =
      Submodule.span ℂ ({Finsupp.single (0 : Momentum) (1 : ℂ)} : Set Ground) :=
  momentumCasimir_ker fixedBasis nebeGram_posDef

#print axioms cartanZeroMode_commutator_U
#print axioms momentumCasimir_single
#print axioms momentumCasimir_ker

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
