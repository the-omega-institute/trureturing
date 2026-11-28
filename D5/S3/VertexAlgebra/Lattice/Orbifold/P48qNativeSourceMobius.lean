/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeSourceMobius
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeSourceMobius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous Mobius commutators of the actual untwisted P48q source modes. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
import D5.S3.VertexAlgebra.LatticeActualConformalWard
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Lie.OfAssociative
import OmegaBuild.Commands

/-! The normalized modes in this file are those of the untwisted lattice
state-field map `Y` on the P48q source carrier. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSourceMobius

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalWard (wardTerm ward_commutator)
open LatticeActualStateDerivative (state_derivative_modes)
open LatticeAllStateField (Y)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeSugawaraConformal (sugawaraMode_minus_one_eq_translation)
open LatticeSugawaraCurrents (sugawaraMode)
open LatticeSugawaraVirasoro (sugawaraMode_virasoro)
open P48qTwistedChargeAction (lattice)
open StateFieldResidueReconstruction (integerBinomial)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "adL₁" => LieAlgebra.ad ℂ (Module.End ℂ (Carrier lattice)) L₁

/-- The actual homogeneous Ward identity at `ω₂ = L(1)`. The ordinary
Borcherds commutator has precisely the three candidate indices `0, 1, 2`. -/
theorem sourceLOne_mode_commutator (a : Carrier lattice) (d : ℂ)
    (ha : L₀ a = d • a) (m : ℤ) :
    L₁ * ((Y lattice a)[[m]]) - ((Y lattice a)[[m]]) * L₁ =
      ((Y lattice (L₁ a))[[m]]) + (2 * d - (m : ℂ) - 2) • ((Y lattice a)[[m + 1]]) := by
  let H := actualInverse lattice
  have h := ward_commutator lattice H a 1 m
  have support : Function.support (wardTerm lattice H a 1 m) ⊆ ↑(Finset.range 3) := by
    intro j hj
    by_contra outside
    have hj' : 2 < j := Nat.lt_of_not_ge fun hle =>
      outside (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    have hChoose : Ring.choose (2 : ℤ) j = 0 := by
      change Ring.choose ((2 : ℕ) : ℤ) j = 0
      rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hj']
      rfl
    apply hj
    change integerBinomial 2 j • _ = 0
    simp [integerBinomial, hChoose]
  rw [finsum_eq_sum_of_support_subset _ support] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have hTranslation := sugawaraMode_minus_one_eq_translation lattice H
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
  have h0 : wardTerm lattice H a 1 m 0 =
      -((m + 2 : ℤ) : ℂ) • ((Y lattice a)[[m + 1]]) := by
    change integerBinomial 2 0 •
      ((Y lattice (sugawaraMode lattice H (-1) a))[[1 + m + 1 - 0]]) = _
    rw [show (1 : ℤ) + m + 1 - 0 = m + 2 by omega, hTranslation]
    simpa only [integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul,
      show m + 2 - 1 = m + 1 by omega] using state_derivative_modes lattice a (m + 2)
  have h1 : wardTerm lattice H a 1 m 1 = (2 * d) • ((Y lattice a)[[m + 1]]) := by
    change integerBinomial 2 1 • ((Y lattice (L₀ a))[[1 + m + 1 - 1]]) = _
    rw [show (1 : ℤ) + m + 1 - 1 = m + 1 by omega, ha, map_smul, map_smul,
      Pi.smul_apply, smul_smul]
    norm_num [integerBinomial, Ring.choose_one_right]
  have h2 : wardTerm lattice H a 1 m 2 = ((Y lattice (L₁ a))[[m]]) := by
    have hChoose : integerBinomial 2 2 = 1 := by
      change ((Ring.choose ((2 : ℕ) : ℤ) 2 : ℤ) : ℂ) = 1
      rw [Ring.choose_natCast, Nat.choose_self] <;> norm_num
    change integerBinomial 2 2 • ((Y lattice (L₁ a))[[1 + m + 1 - 2]]) = _
    rw [show (1 : ℤ) + m + 1 - 2 = m by omega, hChoose, one_smul]
  rw [h0, h1, h2, ← add_smul] at h
  have hScalar : -((m + 2 : ℤ) : ℂ) + 2 * d = 2 * d - (m : ℂ) - 2 := by
    push_cast
    ring
  rw [hScalar] at h
  exact h.trans (add_comm _ _)

private theorem sourceLOne_pow_weight (a : Carrier lattice) (d : ℂ) (ha : L₀ a = d • a)
    (j : ℕ) : L₀ ((L₁ ^ j) a) = (d - (j : ℂ)) • (L₁ ^ j) a := by
  have virasoro := sugawaraMode_virasoro lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit) 0 1
  have commutator : L₀ * L₁ - L₁ * L₀ = (-1 : ℂ) • L₁ := by
    simpa only [zero_add, zero_sub, Int.cast_neg, Int.cast_one, one_ne_zero, if_false,
      zero_smul, add_zero] using virasoro
  induction j with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero] using ha
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := LinearMap.congr_fun commutator ((L₁ ^ j) a)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      ih, map_smul] at h
    have hScalar : (-1 : ℂ) + (d - (j : ℂ)) = d - ((j + 1 : ℕ) : ℂ) := by
      push_cast <;> ring
    rw [eq_add_of_sub_eq h, ← add_smul, hScalar]

private def dividedAd {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (r : ℕ) (A : Module.End ℂ W) : Module.End ℂ W :=
  (r.factorial : ℂ)⁻¹ • (LieAlgebra.ad ℂ (Module.End ℂ W) T ^ r) A

private theorem dividedAd_succ {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (r : ℕ) (A : Module.End ℂ W) :
    (r + 1 : ℂ) • dividedAd T (r + 1) A =
      LieAlgebra.ad ℂ (Module.End ℂ W) T (dividedAd T r A) := by
  have hFactorial : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hSucc : (r + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  simp only [dividedAd, map_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, smul_smul, pow_succ', Module.End.mul_apply]
  congr 1
  field_simp

-- The scalar recurrence follows the finite-sum argument in HalfFock.ActualMobiusAllOrder.
-- Extending the coefficients by zero makes the upper endpoint of the sum uniform.
private def coefficient (α : ℂ) (r j : ℕ) : ℂ :=
  if j ≤ r then Ring.choose (α - (j : ℂ)) (r - j) / (j.factorial : ℂ) else 0

private theorem choose_step (x : ℂ) (k : ℕ) :
    (k + 1 : ℂ) * Ring.choose x (k + 1) = (x - (k : ℂ)) * Ring.choose x k := by
  have h := Ring.choose_smul_choose x (by omega : k ≤ k + 1)
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul, mul_comm] using h

private theorem coefficient_step_zero (α : ℂ) (r : ℕ) :
    (r + 1 : ℂ) * coefficient α (r + 1) 0 = (α - (r : ℂ)) * coefficient α r 0 := by
  simpa [coefficient] using choose_step α r

private theorem coefficient_step_succ (α : ℂ) (r j : ℕ) (hj : j ≤ r) :
    (r + 1 : ℂ) * coefficient α (r + 1) (j + 1) =
      coefficient α r j + (α - (r : ℂ) - (j + 1 : ℂ)) * coefficient α r (j + 1) := by
  by_cases top : j = r
  · subst j
    have hFactorial : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have hSucc : (r + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    simp only [coefficient, le_refl, ite_true, Nat.sub_self, Ring.choose_zero_right,
      Nat.not_succ_le_self, ite_false, mul_zero, add_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · have hNext : j + 1 ≤ r := by omega
    let k := r - (j + 1)
    have split : r - j = k + 1 := by omega
    have count : (r : ℂ) = (k : ℂ) + (j : ℂ) + 1 := by
      exact_mod_cast (show r = k + j + 1 by omega)
    have pascal := Ring.choose_succ_succ (α - (j + 1 : ℂ)) k
    have step := choose_step (α - (j + 1 : ℂ)) k
    rw [show α - (j + 1 : ℂ) + 1 = α - (j : ℂ) by ring] at pascal
    have hFactorial : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hSucc : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    simp only [coefficient, if_pos hj, if_pos hNext, if_pos (show j + 1 ≤ r + 1 by omega),
      show r + 1 - (j + 1) = k + 1 by omega, show r - (j + 1) = k by rfl, split,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [pascal, count]
    field_simp
    linear_combination step

private theorem sum_step {W : Type*} [AddCommGroup W] [Module ℂ W]
    (α : ℂ) (r : ℕ) (F : ℕ → W) :
    (r + 1 : ℂ) • (∑ j ∈ Finset.range (r + 2), coefficient α (r + 1) j • F j) =
      (∑ j ∈ Finset.range (r + 1), coefficient α r j • F (j + 1)) +
      ∑ j ∈ Finset.range (r + 1), (coefficient α r j * (α - (r : ℂ) - (j : ℂ))) • F j := by
  let g := fun j : ℕ => (coefficient α r j * (α - (r : ℂ) - (j : ℂ))) • F j
  have top : g (r + 1) = 0 := by simp [g, coefficient]
  have shift : (∑ j ∈ Finset.range (r + 1), g (j + 1)) + g 0 =
      ∑ j ∈ Finset.range (r + 1), g j := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ, top, add_zero]
  calc
    _ = (∑ j ∈ Finset.range (r + 1),
          ((r + 1 : ℂ) * coefficient α (r + 1) (j + 1)) • F (j + 1)) +
        ((r + 1 : ℂ) * coefficient α (r + 1) 0) • F 0 := by
      rw [Finset.smul_sum, Finset.sum_range_succ']
      simp only [smul_smul]
    _ = (∑ j ∈ Finset.range (r + 1), (coefficient α r j • F (j + 1) + g (j + 1))) + g 0 := by
      rw [coefficient_step_zero]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [coefficient_step_succ α r j (by have := Finset.mem_range.mp hj; omega), add_smul]
        simp only [g, Nat.cast_add, Nat.cast_one, mul_comm]
      · simp [g, mul_comm]
    _ = _ := by rw [Finset.sum_add_distrib, add_assoc, shift]

-- The mode recurrence uses only the weight shift of the source and the
-- Ward commutator on the target, so it applies to both native carriers.
private theorem dividedAd_modes_of_ward {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Module.End ℂ V) (T : Module.End ℂ W)
    (mode : ℤ → V →ₗ[ℂ] Module.End ℂ W) (a : V) (d m : ℤ)
    (ward : ∀ (j : ℕ) (q : ℤ),
      T * mode q ((S ^ j) a) - mode q ((S ^ j) a) * T =
        mode q (S ((S ^ j) a)) + (2 * ((d : ℂ) - (j : ℂ)) - (q : ℂ) - 2) •
          mode (q + 1) ((S ^ j) a)) (r : ℕ) :
    (r.factorial : ℂ)⁻¹ • (LieAlgebra.ad ℂ (Module.End ℂ W) T ^ r) (mode m a) =
      ∑ j ∈ Finset.range (r + 1),
        ((j.factorial : ℂ)⁻¹ * integerBinomial (2 * d - m - (j : ℤ) - 2) (r - j)) •
          mode (m + (r : ℤ) - (j : ℤ)) ((S ^ j) a) := by
  let α : ℂ := 2 * (d : ℂ) - (m : ℂ) - 2
  have expansion (n : ℕ) :
      dividedAd T n (mode m a) =
        ∑ j ∈ Finset.range (n + 1), coefficient α n j •
          mode (m + (n : ℤ) - (j : ℤ)) ((S ^ j) a) := by
    induction n with
    | zero => simp [dividedAd, coefficient]
    | succ n ih =>
      let next := fun j : ℕ =>
        mode (m + ((n + 1 : ℕ) : ℤ) - (j : ℤ)) ((S ^ j) a)
      have modeStep (j : ℕ) :
          LieAlgebra.ad ℂ (Module.End ℂ W) T
            (mode (m + (n : ℤ) - (j : ℤ)) ((S ^ j) a)) =
            next (j + 1) + (α - (n : ℂ) - (j : ℂ)) • next j := by
        rw [LieAlgebra.ad_apply, Ring.lie_def,
          ward j]
        have hScalar : 2 * ((d : ℂ) - (j : ℂ)) -
            ((m + (n : ℤ) - (j : ℤ) : ℤ) : ℂ) - 2 = α - (n : ℂ) - (j : ℂ) := by
          dsimp only [α]
          push_cast <;> ring
        dsimp only [next]
        rw [pow_succ' S j, Module.End.mul_apply,
          show m + ((n + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = m + (n : ℤ) - (j : ℤ) by omega,
          show m + ((n + 1 : ℕ) : ℤ) - (j : ℤ) = m + (n : ℤ) - (j : ℤ) + 1 by omega,
          hScalar]
      apply smul_right_injective (Module.End ℂ W)
        (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      change (n + 1 : ℂ) • dividedAd T (n + 1) (mode m a) =
        (n + 1 : ℂ) • ∑ j ∈ Finset.range (n + 2), coefficient α (n + 1) j • next j
      rw [dividedAd_succ, ih, map_sum]
      simp only [map_smul]
      calc
        _ = ∑ j ∈ Finset.range (n + 1), coefficient α n j •
              (next (j + 1) + (α - (n : ℂ) - (j : ℂ)) • next j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [modeStep]
        _ = (∑ j ∈ Finset.range (n + 1), coefficient α n j • next (j + 1)) +
            ∑ j ∈ Finset.range (n + 1),
              (coefficient α n j * (α - (n : ℂ) - (j : ℂ))) • next j := by
          simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        _ = _ := (sum_step α n next).symm
  change dividedAd T r (mode m a) = _
  rw [expansion]
  apply Finset.sum_congr rfl
  intro j hj
  have hArg : ((2 * d - m - (j : ℤ) - 2 : ℤ) : ℂ) = α - (j : ℂ) := by
    dsimp only [α]
    push_cast <;> ring
  have hChoose : ((Ring.choose (2 * d - m - (j : ℤ) - 2) (r - j) : ℤ) : ℂ) =
      Ring.choose (α - (j : ℂ)) (r - j) := by
    rw [← hArg]
    exact Ring.map_choose (Int.castRingHom ℂ) _ _
  rw [coefficient, if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [integerBinomial, hChoose]
  simp only [div_eq_mul_inv, mul_comm]

/-- Every divided power of the adjoint action on an actual homogeneous
source mode, with integer binomial coefficients and a finite range at
each order. The mode index is the normalized index of `Y`. -/
theorem sourceLOne_dividedAd_modes (a : Carrier lattice) (d : ℤ)
    (ha : L₀ a = (d : ℂ) • a) (m : ℤ) (r : ℕ) :
    (r.factorial : ℂ)⁻¹ • (adL₁ ^ r) ((Y lattice a)[[m]]) =
      ∑ j ∈ Finset.range (r + 1),
        ((j.factorial : ℂ)⁻¹ * ((Ring.choose (2 * d - m - (j : ℤ) - 2) (r - j) : ℤ) : ℂ)) •
          ((Y lattice ((L₁ ^ j) a))[[m + (r : ℤ) - (j : ℤ)]]) := by
  let mode (q : ℤ) : Carrier lattice →ₗ[ℂ] Module.End ℂ (Carrier lattice) :=
    (LinearMap.proj q).comp (VertexOperator.ncoeff.comp (Y lattice))
  exact dividedAd_modes_of_ward L₁ L₁ mode a d m
    (fun j q => sourceLOne_mode_commutator _ _ (sourceLOne_pow_weight a (d : ℂ) ha j) q) r

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSourceMobius
