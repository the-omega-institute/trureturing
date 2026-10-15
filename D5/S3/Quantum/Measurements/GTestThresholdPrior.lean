/- GID: D5/S3/Quantum/Measurements/GTestThresholdPrior
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/GTestThresholdPrior
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The G-test threshold prior is its orbit count divided by word count plus orbit count. -/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The position action uses inverse permutations. The fixed-unitary twirl has the same tested
probability as the Haar mixture after unitary independence is proved. Burnside is applied to
fixed points after double-counting the stabilizer sum. No optimality over all tests is asserted.
-/

namespace D5.S3.Quantum.Measurements.GTestThresholdPrior

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

abbrev Word (n d : ℕ) :=
  Fin n → Fin d

abbrev TensorVec (n d : ℕ) :=
  Word n d → ℂ

abbrev TensorMat (n d : ℕ) :=
  Matrix (Word n d) (Word n d) ℂ

local instance wordAction (n d : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (Word n d) :=
  arrowAction

abbrev WordOrbit {n d : ℕ} (w : Word n d) :=
  ↥(MulAction.orbit (Equiv.Perm (Fin n)) w)

def orbitMap {n d : ℕ} (w : Word n d)
    (π : Equiv.Perm (Fin n)) : WordOrbit w :=
  ⟨π • w, MulAction.mem_orbit w π⟩

def M {n d : ℕ} (w : Word n d) : ℕ :=
  Fintype.card (WordOrbit w)

def O {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d) : ℕ :=
  Fintype.card
    (MulAction.orbitRel.Quotient G (WordOrbit w))

def psi {n d : ℕ} :
    Equiv.Perm (Fin n) →* TensorMat n d :=
  (Matrix.permMatrixHom (n := Word n d) (R := ℂ)).comp
    (MulAction.toPermHom
      (Equiv.Perm (Fin n)) (Word n d))

def ket {n d : ℕ} (w : Word n d) : TensorVec n d :=
  fun x => if x = w then 1 else 0

def pure {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

def tensorPower (n : ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : TensorMat n d :=
  Matrix.of (fun x y => ∏ j : Fin n, A (x j) (y j))

def repeatKet (n : ℕ) {d : ℕ}
    (φ : Fin d → ℂ) : TensorVec n d :=
  fun x => ∏ j : Fin n, φ (x j)

def equalState (n : ℕ) {d : ℕ}
    (φ : Fin d → ℂ) : TensorMat n d :=
  pure (repeatKet n φ)

def UnitVector {d : ℕ} (φ : Fin d → ℂ) : Prop :=
  (∑ i : Fin d, star (φ i) * φ i) = (1 : ℂ)

def PiG {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) : TensorMat n d :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, psi (d := d) (g : Equiv.Perm (Fin n))

def rhoTilde {n d : ℕ}
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : TensorMat n d :=
  let T := tensorPower n (U : Matrix (Fin d) (Fin d) ℂ)
  (n.factorial : ℂ)⁻¹ •
    ∑ π : Equiv.Perm (Fin n),
      psi (d := d) π *
        (T * pure (ket w) * T.conjTranspose) *
        psi (d := d) (π⁻¹)

def completeness {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (φ : Fin d → ℂ) : ℝ :=
  (Matrix.trace (PiG G * equalState n φ)).re

def soundnessError {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  (Matrix.trace (PiG G * rhoTilde w U)).re

def soundness {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  1 - soundnessError G w U

def P_G {n d : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ : Fin d → ℂ) (p : ℝ) : ℝ :=
  p * completeness G φ + (1 - p) * soundness G w U

def P_T (p : ℝ) : ℝ :=
  1 - p

def claim : Prop :=
  ∀ (n d : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ : Fin d → ℂ)
    (p : ℝ),
    (∃ i j : Fin n, w i ≠ w j) →
    UnitVector φ →
    p ∈ Set.Icc (0 : ℝ) 1 →
    (((P_G G w U φ p > P_T p) ↔
        p > (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ))) ∧
     ((P_G G w U φ p = P_T p) ↔
        p = (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ)))) ∧
    Matrix.trace (PiG G * rhoTilde w U) =
      (O G w : ℂ) / (M w : ℂ)

variable {n d : ℕ}

private theorem word_smul_apply
    (π : Equiv.Perm (Fin n)) (x : Word n d) (j : Fin n) :
    (π • x) j = x (π⁻¹ j) := rfl

private theorem psi_apply
    (π : Equiv.Perm (Fin n)) (x y : Word n d) :
    psi (d := d) π x y = if x = π • y then 1 else 0 := by
  change ((MulAction.toPermHom (Equiv.Perm (Fin n)) (Word n d) π)⁻¹).permMatrix ℂ x y = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  congr 1
  change (π⁻¹ • x = y) = (x = π • y)
  exact propext inv_smul_eq_iff

private theorem psi_mulVec
    (π : Equiv.Perm (Fin n)) (v : TensorVec n d) :
    psi (d := d) π *ᵥ v = fun x => v (π⁻¹ • x) := by
  change ((MulAction.toPermHom (Equiv.Perm (Fin n)) (Word n d) π)⁻¹).permMatrix ℂ *ᵥ v = _
  rw [Matrix.permMatrix_mulVec]
  rfl

private theorem psi_adjoint (π : Equiv.Perm (Fin n)) :
    (psi (d := d) π).conjTranspose = psi (d := d) (π⁻¹) := by
  change (((MulAction.toPermHom (Equiv.Perm (Fin n)) (Word n d) π)⁻¹).permMatrix ℂ).conjTranspose =
    _
  rw [Matrix.conjTranspose_permMatrix]
  change _ = ((MulAction.toPermHom (Equiv.Perm (Fin n)) (Word n d) (π⁻¹))⁻¹).permMatrix ℂ
  rw [map_inv, inv_inv]

private theorem psi_ket (π : Equiv.Perm (Fin n)) (w : Word n d) :
    psi (d := d) π *ᵥ ket w = ket (π • w) := by
  rw [psi_mulVec]
  funext x
  unfold ket
  simp only [inv_smul_eq_iff]

private theorem trace_mul_pure {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    Matrix.trace (A * pure v) = ∑ x : ι, star (v x) * (A *ᵥ v) x := by
  unfold pure
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem pure_conjugate {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    A * pure v * A.conjTranspose = pure (A *ᵥ v) := by
  unfold pure
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private theorem trace_word (A : TensorMat n d) (x : Word n d) :
    Matrix.trace (A * pure (ket x)) = A x x := by
  rw [trace_mul_pure]
  simp [ket.eq_1, Matrix.mulVec, dotProduct]


private theorem sum_product (f : Fin n → Fin d → ℂ) :
    (∑ x : Word n d, ∏ j : Fin n, f j (x j)) = ∏ j : Fin n, ∑ a : Fin d, f j a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private theorem tensor_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    tensorPower n (A * B) = tensorPower n A * tensorPower n B := by
  ext x y
  simp only [tensorPower.eq_1, Matrix.of_apply, Matrix.mul_apply]
  rw [← sum_product]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

private theorem tensor_one :
    tensorPower n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [tensorPower.eq_1, Matrix.of_apply, Matrix.one_apply,
    Fintype.prod_boole, ← funext_iff]

private theorem tensor_adjoint (A : Matrix (Fin d) (Fin d) ℂ) :
    (tensorPower n A).conjTranspose = tensorPower n A.conjTranspose := by
  ext x y
  simp only [tensorPower.eq_1, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

private theorem tensor_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (tensorPower n (U : Matrix (Fin d) (Fin d) ℂ)).conjTranspose *
      tensorPower n (U : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [tensor_adjoint, ← tensor_mul]
  rw [← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, tensor_one]

private theorem psi_comm_tensor (π : Equiv.Perm (Fin n))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    psi (d := d) π * tensorPower n A = tensorPower n A * psi (d := d) π := by
  ext x y
  simp only [Matrix.mul_apply, psi_apply]
  have hleft : (∑ z : Word n d, (if x = π • z then 1 else 0) * tensorPower n A z y) =
      tensorPower n A (π⁻¹ • x) y := by
    simp_rw [eq_comm (a := x), smul_eq_iff_eq_inv_smul, ite_mul, one_mul, zero_mul]
    simp
  rw [hleft]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [tensorPower.eq_1, Matrix.of_apply, word_smul_apply, inv_inv]
  exact Fintype.prod_equiv π (fun j => A (x (π j)) (y j))
    (fun j => A (x j) (y (π⁻¹ j))) (by intro j; simp)

private theorem PiG_comm_tensor (G : Subgroup (Equiv.Perm (Fin n)))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    PiG G * tensorPower n A = tensorPower n A * PiG G := by
  unfold PiG
  rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => psi_comm_tensor g.val A)

private theorem trace_conjugate (P T R : TensorMat n d)
    (hT : T.conjTranspose * T = 1) (hPT : P * T = T * P) :
    Matrix.trace (P * (T * R * T.conjTranspose)) = Matrix.trace (P * R) := by
  rw [← Matrix.mul_assoc P, ← Matrix.mul_assoc P, hPT,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc T.conjTranspose T P, hT, Matrix.one_mul]


private theorem PiG_diagonal (G : Subgroup (Equiv.Perm (Fin n))) (x : Word n d) :
    PiG G x x = (Fintype.card (MulAction.stabilizer G x) : ℂ) / (Fintype.card G : ℂ) := by
  unfold PiG
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, psi_apply]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  change (∑ g : G, if x = g • x then (1 : ℂ) else 0) =
    (Fintype.card {g : G // g • x = x} : ℂ)
  simp only [Fintype.card_subtype, eq_comm (a := x), Finset.sum_boole]

private theorem twirl_trace_average (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.trace (PiG G * rhoTilde w U) =
      (n.factorial : ℂ)⁻¹ * ∑ π : Equiv.Perm (Fin n), PiG G (π • w) (π • w) := by
  unfold rhoTilde
  rw [Matrix.mul_smul, Finset.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
  change _ * _ = _ * _
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  rw [← psi_adjoint π, pure_conjugate, pure_conjugate]
  rw [Matrix.mulVec_mulVec, psi_comm_tensor, ← Matrix.mulVec_mulVec, psi_ket]
  rw [← pure_conjugate]
  rw [trace_conjugate _ _ _ (tensor_unitary U) (PiG_comm_tensor G _), trace_word]

private theorem orbit_card_pos (w : Word n d) : 0 < M w := by
  exact Fintype.card_pos_iff.mpr ⟨⟨w, MulAction.mem_orbit_self w⟩⟩

private theorem orbitMap_fiber_card (w : Word n d) (x : WordOrbit w) :
    Fintype.card {π : Equiv.Perm (Fin n) // orbitMap w π = x} =
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) w) := by
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp x.property
  let f : MulAction.stabilizer (Equiv.Perm (Fin n)) w →
      {π : Equiv.Perm (Fin n) // orbitMap w π = x} := fun h =>
    ⟨τ * h.val, Subtype.ext (by
      change (τ * h.val) • w = x.val
      rw [mul_smul, h.property, hτ])⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val h)
    · intro π
      have hπ := congrArg Subtype.val π.property
      change π.val • w = x.val at hπ
      refine ⟨⟨τ⁻¹ * π.val, ?_⟩, ?_⟩
      · change (τ⁻¹ * π.val) • w = w
        rw [mul_smul, hπ, ← hτ, inv_smul_smul]
      · apply Subtype.ext
        change τ * (τ⁻¹ * π.val) = π.val
        exact mul_inv_cancel_left _ _
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm

private theorem orbit_average (w : Word n d) (f : WordOrbit w → ℂ) :
    (n.factorial : ℂ)⁻¹ * (∑ π : Equiv.Perm (Fin n), f (orbitMap w π)) =
      (M w : ℂ)⁻¹ * ∑ x : WordOrbit w, f x := by
  have hs := Fintype.sum_fiberwise' (orbitMap w) f
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, orbitMap_fiber_card] at hs
  have hc : M w * Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) w) =
      n.factorial := by
    simpa only [M.eq_1, Fintype.card_perm, Fintype.card_fin] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm (Fin n)) w
  have hm : (M w : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (orbit_card_pos w))
  have hh : (Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) w) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcast := congrArg (fun k : ℕ => (k : ℂ)) hc
  simp only [Nat.cast_mul] at hcast
  rw [← hs, ← hcast, ← Finset.mul_sum]
  field_simp

private theorem burnside_stabilizer_sum (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d) :
    (∑ x : WordOrbit w, Fintype.card (MulAction.stabilizer G (x : Word n d))) =
      O G w * Fintype.card G := by
  have hstab (x : WordOrbit w) :
      Fintype.card (MulAction.stabilizer G (x : Word n d)) =
        ∑ g : G, if g • x = x then 1 else 0 := by
    change Fintype.card {g : G // g • (x : Word n d) = x.val} = _
    simp only [Fintype.card_subtype, Finset.sum_boole]
    congr 1
    apply Finset.filter_congr
    intro g _
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp_rw [hstab]
  rw [Finset.sum_comm]
  have hfix (g : G) :
      (∑ x : WordOrbit w, if g • x = x then 1 else 0) =
        Fintype.card (MulAction.fixedBy (WordOrbit w) g) := by
    simp only [Finset.sum_boole]
    exact (Fintype.card_subtype _).symm
  simp_rw [hfix]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (WordOrbit w)

private theorem trace_eq_orbit_ratio (G : Subgroup (Equiv.Perm (Fin n)))
    (w : Word n d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.trace (PiG G * rhoTilde w U) = (O G w : ℂ) / (M w : ℂ) := by
  rw [twirl_trace_average]
  change (n.factorial : ℂ)⁻¹ * (∑ π, (fun x : WordOrbit w => PiG G x.val x.val)
    (orbitMap w π)) = _
  rw [orbit_average w (fun x : WordOrbit w => PiG (d := d) G x.val x.val)]
  simp_rw [PiG_diagonal, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hcast := congrArg (fun k : ℕ => (k : ℂ)) (burnside_stabilizer_sum G w)
  simp only [Nat.cast_sum, Nat.cast_mul] at hcast
  rw [hcast]
  have hg : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp


end

end D5.S3.Quantum.Measurements.GTestThresholdPrior
