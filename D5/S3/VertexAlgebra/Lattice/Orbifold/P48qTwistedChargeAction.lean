/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedChargeAction
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedChargeAction.lattice; premises=D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedChargeAction.gram_symmetric,D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedChargeAction.gram_diagonal
   digest: Construct the even Nebe lattice and its P48q twisted ground charge action. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificateDraft
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingLatticeCertificateDraft
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
import Mathlib.GroupTheory.OrderOfElement

/-!
The P48q momentum-space charge operators in Nebe's integral row coordinates.
In Bakalov–Kac, arXiv:math/0402315v3, the coefficient in (4.42) is
`ε(a,b) * B(a,b)⁻¹` with `B` from (4.37). The basis index is the integral
numerator of the fixed projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction

open LatticeGeneratingFieldLocality
open P48qFixedRankCertificateDraft P48qGramCertificateDraft P48qMovingLatticeCertificateDraft
open scoped Matrix

noncomputable section

local notation "A" => nebeOrderThree

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private theorem gram_symmetric : ∀ i j : Fin 48, nebeGram i j = nebeGram j i := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem gram_diagonal (i : Fin 48) :
    nebeGram i i = nebeGram i i / 2 + nebeGram i i / 2 := by
  fin_cases i <;> decide +kernel

/-- The native even lattice in the basis of the Nebe certificates. -/
def lattice : LatticeData where
  rank := 48
  G := nebeGram
  symmetric := gram_symmetric
  even_diagonal i := ⟨nebeGram i i / 2, gram_diagonal i⟩

private theorem transpose_cube : (Aᵀ) ^ 3 = 1 := by
  rw [← Matrix.transpose_pow, nebeOrderThree_cube, Matrix.transpose_one]

/-- The integral additive equivalence given by right multiplication on rows. -/
def g : AddAut (Charge lattice) :=
  (Matrix.toLin'OfInv (M := (Aᵀ) ^ 2) (M' := Aᵀ)
    (by rw [← pow_succ]; exact transpose_cube)
    (by rw [← pow_succ']; exact transpose_cube)).toAddEquiv

theorem g_apply (a : Charge lattice) : g a = a ᵥ* A := by
  change Aᵀ *ᵥ a = a ᵥ* A
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]

theorem g_cube (a : Charge lattice) : g (g (g a)) = a := by
  have h : (A * A) * A = 1 := by
    rw [← pow_two, ← pow_succ, nebeOrderThree_cube]
  simp only [g_apply, Matrix.vecMul_vecMul, ← mul_assoc, h, Matrix.vecMul_one]

theorem g_order : addOrderOf g = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply AddEquiv.ext
    intro a
    change g (g (g a)) = a
    exact g_cube a
  · intro h
    let i : Fin 48 := 0
    let e : Fin 48 → ℤ := Pi.single i 1
    have he : (g e) i = e i := congrArg (fun s : AddAut (Charge lattice) => s e i) h
    rw [g_apply] at he
    dsimp only [e] at he
    rw [Matrix.single_one_vecMul, Pi.single_eq_same] at he
    exact (by decide +kernel : A 0 0 ≠ 1) he

theorem g_isometry (a b : Charge lattice) :
    bilinear lattice (g a) (g b) = bilinear lattice a b := by
  have hForm := Matrix.toBilin'_comp nebeGram Aᵀ Aᵀ
  rw [Matrix.transpose_transpose, gram_isometry_certificate] at hForm
  have h := congrArg (fun f : LinearMap.BilinForm ℤ (Charge lattice) => f a b) hForm
  change nebeGram.toBilin' (g a) (g b) = nebeGram.toBilin' a b at h
  simpa only [Matrix.toBilin'_apply, bilinear, lattice] using h

/-- Scalar extension of the same Gram isometry in Nebe's real coordinates. -/
theorem real_isometry (a b : Fin 48 → ℝ) :
    (nebeGram.map (Int.castRingHom ℝ)).toBilin' (rowAction ℝ A a) (rowAction ℝ A b) =
      (nebeGram.map (Int.castRingHom ℝ)).toBilin' a b := by
  let cast := Int.castRingHom ℝ
  let G := nebeGram.map cast
  let M := (Aᵀ).map cast
  have hMapped := congrArg (cast.mapMatrix (m := Fin 48)) gram_isometry_certificate
  simp only [map_mul] at hMapped
  have hGram : Mᵀ * G * M = G := by
    change ((Aᵀ).map cast)ᵀ * nebeGram.map cast * (Aᵀ).map cast = nebeGram.map cast
    rw [← Matrix.transpose_map, Matrix.transpose_transpose]
    exact hMapped
  have hForm := Matrix.toBilin'_comp G M M
  rw [hGram] at hForm
  exact congrArg (fun f : LinearMap.BilinForm ℝ (Fin 48 → ℝ) => f a b) hForm

theorem norm_row (a : Charge lattice) :
    ThirdTwistedChargeAction.N lattice g a = a ᵥ* (1 + A + A ^ 2) := by
  simp only [ThirdTwistedChargeAction.N_apply, g_apply, Matrix.vecMul_vecMul,
    Matrix.vecMul_add, Matrix.vecMul_one, pow_two]

theorem movingExact : ThirdTwistedChargeAction.MovingExact lattice g := by
  intro m hm
  obtain ⟨a, ha⟩ := (nebeOrderThree_moving_exact m).mp ((norm_row m).symm.trans hm)
  exact ⟨a, by
    simpa only [ThirdTwistedChargeAction.d_apply, g_apply, Matrix.vecMul_sub,
      Matrix.vecMul_one] using ha⟩

local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g
local notation "ζ" => ThirdTwistedChargeCocycle.zeta

def multiplier : ThirdTwistedChargeAction.Multiplier lattice g where
  c := c₃
  zeta := ζ
  cube := ThirdTwistedChargeCocycle.zeta_primitive.zpow_eq_one
  zero_mul a := (ThirdTwistedChargeCocycle.c_normalized lattice g a).1
  mul_zero a := (ThirdTwistedChargeCocycle.c_normalized lattice g a).2
  add_left := ThirdTwistedChargeCocycle.c_add_left lattice g
  add_right := ThirdTwistedChargeCocycle.c_add_right lattice g
  commutator := ThirdTwistedChargeCocycle.commutator_difference lattice g g_isometry g_cube

private theorem multiplier_rescale (a b : Charge lattice) :
    (multiplier.c a b : ℂ) * epsilon lattice a b =
      (multiplier.c (g a) (g b) : ℂ) * epsilon lattice (g a) (g b) := by
  have cancelEpsilon (x y : Charge lattice) :
      (multiplier.c x y : ℂ) * epsilon lattice x y =
        (↑((ThirdTwistedChargeCocycle.B lattice g x y)⁻¹) : ℂ) := by
    have hs : epsilon lattice x y * epsilon lattice x y = 1 := by
      unfold epsilon paritySign
      split_ifs <;> norm_num
    change (c₃ x y : ℂ) * epsilon lattice x y = _
    rw [ThirdTwistedChargeCocycle.c, Units.val_mul, ThirdTwistedChargeCocycle.coe_epsilonUnit,
      mul_right_comm (epsilon lattice x y), hs, one_mul]
  rw [cancelEpsilon a b, cancelEpsilon (g a) (g b),
    ThirdTwistedChargeCocycle.B_isometry lattice g g_isometry a b]

/-- The standard native lift, transferred from epsilon to the multiplier (4.42). -/
def liftPhase : ThirdTwistedChargeAction.LiftPhase lattice g multiplier :=
  ThirdTwistedChargeAction.nativeLiftPhase lattice g g_cube g_isometry
    multiplier multiplier_rescale

/-- The row `p` represents the physical momentum `p / 3` in the fixed subspace. -/
abbrev Momentum := ThirdTwistedChargeAction.Momentum lattice g

theorem momentum_index_iff (p : Charge lattice) :
    p ∈ (ThirdTwistedChargeAction.N lattice g).range ↔
      ∃ a : Charge lattice, a ᵥ* (1 + A + A ^ 2) = p := by
  change (∃ a : Charge lattice, ThirdTwistedChargeAction.N lattice g a = p) ↔ _
  simp only [norm_row]

abbrev Ground := ThirdTwistedChargeAction.Ground lattice g

private def momentumSection : ThirdTwistedChargeAction.MomentumSection lattice g :=
  ThirdTwistedChargeAction.chooseSection lattice g

def U (a : Charge lattice) : Module.End ℂ Ground :=
  ThirdTwistedChargeAction.U lattice g multiplier liftPhase movingExact momentumSection a

theorem U_zero : U 0 = LinearMap.id :=
  ThirdTwistedChargeAction.U_zero lattice g g_cube g_isometry
    multiplier liftPhase movingExact momentumSection

/-- Bakalov–Kac (4.42) on the P48q momentum carrier. -/
theorem U_comp (a b : Charge lattice) : (U a).comp (U b) = (c₃ a b : ℂ) • U (a + b) :=
  ThirdTwistedChargeAction.U_comp lattice g g_cube g_isometry
    multiplier liftPhase movingExact momentumSection a b

theorem U_comp_single (a b : Charge lattice) (p : Momentum) (z : ℂ) :
    U a (U b (Finsupp.single p z)) = (c₃ a b : ℂ) • U (a + b) (Finsupp.single p z) :=
  DFunLike.congr_fun (U_comp a b) (Finsupp.single p z)

/-- The phase of (4.46) at `p / 3`, expressed in terms of its integral numerator
`p`. The moving certificate represents every moving charge as `a ᵥ* (1 - A)`. -/
theorem U_difference_single (a : Charge lattice) (p : Momentum) (z : ℂ) :
    U (a ᵥ* ((1 : Matrix (Fin 48) (Fin 48) ℤ) - A)) (Finsupp.single p z) =
      (↑((liftPhase.eta a)⁻¹ * c₃ (g a) (a - g a) *
          ζ ^ (-ThirdTwistedChargeAction.q lattice g a) *
          ζ ^ (-bilinear lattice a p.1)) : ℂ) • Finsupp.single p z := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, ← g_apply a]
  have h := ThirdTwistedChargeAction.U_difference_single lattice g g_cube g_isometry
    multiplier liftPhase movingExact momentumSection a p z
  rw [ThirdTwistedChargeAction.fAt,
    ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry a (momentumSection.lift p),
    momentumSection.right_inv p] at h
  exact h

#print axioms U_comp
#print axioms U_difference_single

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
