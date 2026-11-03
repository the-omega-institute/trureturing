/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorSameRLeftCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorSameRLeftCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed left-nested covariance with the original full clearing and numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFinalLaurentFiber
import D5.S3.VertexAlgebra.Sectors.LatticeSectorMiddleCommonNumerator
import D5.S3.VertexAlgebra.FormalSeries.SupportedFinalCovariance

/-!
Original canonical fields and original all-integer Borcherds only. The imported
suppliers retain Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution.

The old k,a,P are never enlarged. The original-state cutoffs Acore (u on t),
Bcore (v on t), and U (u on v) occur only in a temporary extra multiplier.
The y^Bcore factor is essential: every expanded Barg is >= Bcore independently
of the old k. The extra y monomial is removed by signed translation and the
extra positive factor by a genuine x-supported inverse. No substitution on
raw L or K, energy selector, new sewing law, or uniform descendant cutoff.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorSameRLeftCovariance
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open LatticeSectorSecondCollisionSlice LatticeSectorMiddleCommonNumerator
open LatticeSectorFinalLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedChannelSeries SupportedThreeFieldCollision SupportedMiddleCollision
open SupportedCollisionSlice ThreeFieldFinalLaurentFiber ThreeFieldPolynomialCovariance
open SupportedFinalCovariance
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- The literal ORIGINAL middle multiplier; no extra core cutoffs. -/
def middlePolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  variablePolynomial 0 ^ k * (variablePolynomial 0 - variablePolynomial 1) ^ k *
    variablePolynomial 1 ^ k * (variablePolynomial 0 + variablePolynomial 2) ^ a 0 *
    (variablePolynomial 1 + variablePolynomial 2) ^ a 1 * variablePolynomial 2 ^ a 2

/-- SAME original full R after the final collision; this is not enlarged. -/
def finalPolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
    (variablePolynomial 0 + variablePolynomial 1) ^ k *
    (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ a 0 *
    (variablePolynomial 1 + variablePolynomial 2) ^ a 1 * variablePolynomial 2 ^ a 2

private theorem pair_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (X Y : T) (A : ℕ) :
    (X + Y) ^ A = ∑ h ∈ Finset.range (A + 1),
      (A.choose h : ℂ) • (X ^ h * Y ^ (A - h)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro h hh
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

private theorem difference_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (X Y : T) (k : ℕ) :
    (X - Y) ^ k = ∑ p ∈ Finset.range (k + 1),
      (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • (X ^ (k - p) * Y ^ p) := by
  rw [show X - Y = -Y + X by ring, pair_expansion]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [neg_pow]
  ring

private theorem monomial_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (A B C : ℕ) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ A * variablePolynomial 1 ^ B *
      variablePolynomial 2 ^ C) F ![x, y, z] = F ![x - A, y - B, z - C] := by
  have single : variablePolynomial 0 ^ A * variablePolynomial 1 ^ B *
      variablePolynomial 2 ^ C = AddMonoidAlgebra.single
        (A • Pi.single 0 1 + B • Pi.single 1 1 + C • Pi.single 2 1 : Exponent 3) 1 := by
    simp [variablePolynomial, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single]
  rw [single, polynomialAction, AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • F (![x, y, z] -
    (A • Pi.single 0 1 + B • Pi.single 1 1 + C • Pi.single 2 1)) = _
  rw [one_smul]
  congr 1
  funext i
  fin_cases i <;> simp [nsmul_eq_mul, Pi.single_apply, Matrix.vecHead, Matrix.vecTail]

private theorem xy_shift_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (A B : ℕ) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ A * variablePolynomial 1 ^ B)
      F ![x, y, z] = F ![x - A, y - B, z] := by
  have h := monomial_action F A B 0 x y z
  simpa only [pow_zero, mul_one, Nat.cast_zero, sub_zero] using h

private theorem xy_iterate_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (N A B C : ℕ) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ N *
      (variablePolynomial 0 + variablePolynomial 1) ^ A *
      variablePolynomial 1 ^ B * variablePolynomial 2 ^ C) F ![x, y, z] =
      clearIterate N A B (fun x y => F ![x, y, z - C]) x y := by
  classical
  rw [pair_expansion]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, clearIterate]
  apply Finset.sum_congr rfl
  intro h hh
  have hhA : h ≤ A := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun v : V => (A.choose h : ℂ) • v)
  have regroup : (variablePolynomial (0 : Fin 3)) ^ N *
      (variablePolynomial 0 ^ h * variablePolynomial 1 ^ (A - h)) *
      variablePolynomial 1 ^ B * variablePolynomial 2 ^ C =
      variablePolynomial 0 ^ (N + h) * variablePolynomial 1 ^ (B + (A - h)) *
        variablePolynomial 2 ^ C := by
    simp only [pow_add]
    ring
  rw [regroup, monomial_action]
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hhA] <;> omega

private theorem xz_iterate_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (N A B C : ℕ) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ N *
      (variablePolynomial 0 + variablePolynomial 2) ^ A *
      variablePolynomial 1 ^ B * variablePolynomial 2 ^ C) F ![x, y, z] =
      clearIterate N A C (fun x z => F ![x, y - B, z]) x z := by
  classical
  rw [pair_expansion]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, clearIterate]
  apply Finset.sum_congr rfl
  intro h hh
  have hhA : h ≤ A := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun v : V => (A.choose h : ℂ) • v)
  have regroup : (variablePolynomial (0 : Fin 3)) ^ N *
      (variablePolynomial 0 ^ h * variablePolynomial 2 ^ (A - h)) *
      variablePolynomial 1 ^ B * variablePolynomial 2 ^ C =
      variablePolynomial 0 ^ (N + h) * variablePolynomial 1 ^ B *
        variablePolynomial 2 ^ (C + (A - h)) := by
    simp only [pow_add]
    ring
  rw [regroup, monomial_action]
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hhA] <;> omega

private theorem xy_clear_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (k A B C : ℕ) (x y z : ℤ) :
    polynomialAction ((variablePolynomial 0 - variablePolynomial 1) ^ k *
      variablePolynomial 0 ^ A * variablePolynomial 1 ^ B * variablePolynomial 2 ^ C)
      F ![x, y, z] =
      clear k (fun s b => F ![s - A, b - B, z - C]) x y := by
  classical
  rw [difference_expansion]
  simp only [Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, clear]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply congrArg (fun v : V => (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • v)
  have regroup : ((variablePolynomial (0 : Fin 3)) ^ (k - p) * variablePolynomial 1 ^ p) *
      variablePolynomial 0 ^ A * variablePolynomial 1 ^ B * variablePolynomial 2 ^ C =
      variablePolynomial 0 ^ (A + (k - p)) * variablePolynomial 1 ^ (B + p) *
        variablePolynomial 2 ^ C := by
    simp only [pow_add]
    ring
  rw [regroup, monomial_action]
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hpk] <;> omega

/-- This is a finite identity in the Laurent polynomial ring. It changes no
raw channel and makes no convergence or substitution claim. -/
private theorem middle_expansion (k : ℕ) (a : Fin 3 → ℕ) (Acore Bcore : ℕ) :
    (variablePolynomial 0 ^ Acore * variablePolynomial 1 ^ Bcore) * middlePolynomial k a =
      ∑ h0 ∈ Finset.range (a 0 + 1), ∑ h1 ∈ Finset.range (a 1 + 1),
        ((a 0).choose h0 : ℂ) • (((a 1).choose h1 : ℂ) •
          ((variablePolynomial 0 - variablePolynomial 1) ^ k *
            variablePolynomial 0 ^ (Acore + k + h0) *
            variablePolynomial 1 ^ (Bcore + k + h1) *
            variablePolynomial 2 ^ ((a 0 - h0) + (a 1 - h1) + a 2))) := by
  unfold middlePolynomial
  rw [pair_expansion (variablePolynomial 0) (variablePolynomial 2),
    pair_expansion (variablePolynomial 1) (variablePolynomial 2)]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h0 hh0
  apply Finset.sum_congr rfl
  intro h1 hh1
  simp only [pow_add, Algebra.smul_def]
  ring

private theorem final_expansion (k : ℕ) (a : Fin 3 → ℕ) (Acore Bcore : ℕ) :
    (((variablePolynomial 0 + variablePolynomial 1) ^ Acore *
      variablePolynomial 1 ^ Bcore) * finalPolynomial k a) =
      ∑ h0 ∈ Finset.range (a 0 + 1), ∑ h1 ∈ Finset.range (a 1 + 1),
        ((a 0).choose h0 : ℂ) • (((a 1).choose h1 : ℂ) •
          (variablePolynomial 0 ^ k *
            (variablePolynomial 0 + variablePolynomial 1) ^ (Acore + k + h0) *
            variablePolynomial 1 ^ (Bcore + k + h1) *
            variablePolynomial 2 ^ ((a 0 - h0) + (a 1 - h1) + a 2))) := by
  unfold finalPolynomial
  rw [pair_expansion (variablePolynomial 0 + variablePolynomial 1) (variablePolynomial 2),
    pair_expansion (variablePolynomial 1) (variablePolynomial 2)]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h0 hh0
  apply Finset.sum_congr rfl
  intro h1 hh1
  simp only [pow_add, Algebra.smul_def]
  ring

private theorem middle_action_is_actual (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (s b z : ℤ) :
    polynomialAction (middlePolynomial k a)
      (fun e => middleIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) ![s, b, z] =
      clearedMiddleSlice D α β γ δ u v t w k a b s z := by
  classical
  have expanded : middlePolynomial k a =
      ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • (((a 1).choose h : ℂ) •
          (variablePolynomial 0 ^ (2 * k - p) *
            (variablePolynomial 0 + variablePolynomial 2) ^ a 0 *
            variablePolynomial 1 ^ (k + p + h) *
            variablePolynomial 2 ^ (a 2 + a 1 - h))) := by
    unfold middlePolynomial
    rw [difference_expansion, pair_expansion (variablePolynomial 1) (variablePolynomial 2)]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
    apply Finset.sum_congr rfl
    intro h hh
    have hhC : h ≤ a 1 := by simpa using Finset.mem_range.mp hh
    rw [show 2 * k - p = k + (k - p) by omega,
      show a 2 + a 1 - h = a 2 + (a 1 - h) by omega]
    simp only [pow_add, Algebra.smul_def]
    ring
  rw [expanded]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, clearedMiddleSlice]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun v : Oscillator D =>
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • (((a 1).choose h : ℂ) • v))
  rw [xz_iterate_action]
  apply congrArg (fun F : ℤ → ℤ → Oscillator D =>
    clearIterate (2 * k - p) (a 0) (a 2 + a 1 - h) F s z)
  funext x z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  congr 1 <;> omega

/-- Expanded ACTUAL M, with BOTH original-state monomial shifts. Every
Aarg>=Acore and Barg>=Bcore; k and a remain the original witnesses. -/
private theorem shifted_middle_expansion (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (Acore Bcore : ℕ) (s b z : ℤ) :
    clearedMiddleSlice D α β γ δ u v t w k a (b - Bcore) (s - Acore) z =
      ∑ h0 ∈ Finset.range (a 0 + 1), ∑ h1 ∈ Finset.range (a 1 + 1),
        ((a 0).choose h0 : ℂ) • (((a 1).choose h1 : ℂ) •
          clear k (fun s b => middleIterate D α β γ δ u v t w
            (s - (Acore + k + h0 : ℕ)) (b - (Bcore + k + h1 : ℕ))
            (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))) s b) := by
  let F : Distribution 3 (Oscillator D) := fun e =>
    middleIterate D α β γ δ u v t w (e 0) (e 1) (e 2)
  have shifted : polynomialAction
      ((variablePolynomial 0 ^ Acore * variablePolynomial 1 ^ Bcore) * middlePolynomial k a)
      F ![s, b, z] = clearedMiddleSlice D α β γ δ u v t w k a
        (b - Bcore) (s - Acore) z := by
    rw [map_mul, Module.End.mul_apply]
    rw [xy_shift_action]
    exact middle_action_is_actual D α β γ δ u v t w k a (s - Acore) (b - Bcore) z
  rw [← shifted, middle_expansion]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro h0 hh0
  apply Finset.sum_congr rfl
  intro h1 hh1
  simp only [xy_clear_action, F, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  rfl

private theorem final_action_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (k : ℕ) (a : Fin 3 → ℕ) (Acore Bcore : ℕ) (x y z : ℤ) :
    polynomialAction (((variablePolynomial 0 + variablePolynomial 1) ^ Acore *
      variablePolynomial 1 ^ Bcore) * finalPolynomial k a) F ![x, y, z] =
      ∑ h0 ∈ Finset.range (a 0 + 1), ∑ h1 ∈ Finset.range (a 1 + 1),
        ((a 0).choose h0 : ℂ) • (((a 1).choose h1 : ℂ) •
          clearIterate k (Acore + k + h0) (Bcore + k + h1)
            (fun x y => F ![x, y, z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ)]) x y) := by
  rw [final_expansion]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro h0 hh0
  apply Finset.sum_congr rfl
  intro h1 hh1
  rw [xy_iterate_action]

private theorem original_left_collision (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k A B : ℕ)
    (hA : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n t = 0)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n t = 0)
    (x y z : ℤ) :
    clearIterate k A B (fun s q => leftNested D α β γ δ u v t w s q z) x y =
      ∑ i ∈ Finset.range (y.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) •
          middleIterate D α β γ δ u v t w (x - A - k + i) (y - B - i) z := by
  classical
  let L : Oscillator D →ₗ[ℂ] Oscillator D :=
    { toFun := fun state => canonical D ((α + β) + γ) δ state (-z - 1) w
      map_add' := by
        intro r s
        simp only [map_add, Pi.add_apply, LinearMap.add_apply]
      map_smul' := by
        intro c r
        simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply] }
  have bor := iterate_borcherds D α β γ u v t k A B hA x y
  have mapped := congrArg L bor.2
  rw [map_finsum L bor.1] at mapped
  simp only [map_smul] at mapped
  have left : L (clearIterate k A B (iterate D α β γ u v t) x y) =
      clearIterate k A B (fun s q => leftNested D α β γ δ u v t w s q z) x y := by
    simp only [clearIterate, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro h hh
    rfl
  rw [left] at mapped
  have eq : clearIterate k A B
      (fun s q => leftNested D α β γ δ u v t w s q z) x y =
      ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) •
        L (product D α β γ u v t (x - A - k + i) (y - B - i)) := by
    exact mapped
  rw [eq]
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) •
        L (product D α β γ u v t (x - A - k + i) (y - B - i))) =
      ∑ i ∈ Finset.range (y.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) •
          L (product D α β γ u v t (x - A - k + i) (y - B - i)) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have hyi : y < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    have hz := hB (-(y - B - i) - 1) (by omega)
    simp only [product, hz, map_zero, smul_zero]
  rw [finiteSum]
  apply Finset.sum_congr rfl
  intro i hi
  have evaluation (state : Oscillator D) :
      L state = canonical D ((α + β) + γ) δ state (-z - 1) w := rfl
  rw [evaluation]
  apply congrArg (fun state : Oscillator D =>
    (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) • state)
  change canonical D ((α + β) + γ) δ
      (product D α β γ u v t (x - A - k + i) (y - B - i)) (-z - 1) w =
    canonical D (α + (β + γ)) δ
      (product D α β γ u v t (x - A - k + i) (y - B - i)) (-z - 1) w
  exact congrArg (fun c : Charge D => canonical D c δ
    (product D α β γ u v t (x - A - k + i) (y - B - i)) (-z - 1) w)
    (add_assoc α β γ)


/-- The actual finite covariance increment. The real original hA and hB
kill every tail. Only finite sums are interchanged; the same y.toNat fiber is
used before and after signed_transform_clear. The original Borcherds supplier
maps its actual finite finsum through the fixed outer canonical mode. -/
private theorem actual_extra_covariance (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (Acore Bcore : ℕ)
    (hA : ∀ n : ℤ, (Acore : ℤ) ≤ n → canonical D α γ u n t = 0)
    (hB : ∀ n : ℤ, (Bcore : ℤ) ≤ n → canonical D β γ v n t = 0)
    (x y z : ℤ) :
    (∑ i ∈ Finset.range (y.toNat + 1),
      (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
        clearedMiddleSlice D α β γ δ u v t w k a
          (y - i - Bcore) (x + i - Acore) z) =
      polynomialAction (((variablePolynomial 0 + variablePolynomial 1) ^ Acore *
        variablePolynomial 1 ^ Bcore) * finalPolynomial k a)
        (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) ![x, y, z] := by
  classical
  have term (h0 h1 : ℕ) :
      (∑ i ∈ Finset.range (y.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
          clear k (fun s b => middleIterate D α β γ δ u v t w
            (s - (Acore + k + h0 : ℕ)) (b - (Bcore + k + h1 : ℕ))
            (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))) (x + i) (y - i)) =
      clearIterate k (Acore + k + h0) (Bcore + k + h1)
        (fun x y => leftNested D α β γ δ u v t w x y
          (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))) x y := by
    let F : ℤ → ℤ → Oscillator D := fun s b =>
      middleIterate D α β γ δ u v t w
        (s - (Acore + k + h0 : ℕ)) (b - (Bcore + k + h1 : ℕ))
        (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))
    have lower (s b : ℤ) (hb : b < -(0 : ℤ)) : F s b = 0 := by
      dsimp only [F]
      unfold middleIterate iterate
      rw [hB (-(b - (Bcore + k + h1 : ℕ)) - 1) (by omega)]
      simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
    have transformed := signed_transform_clear F k 0 lower (-x - 1) x y
    have boundA (n : ℤ) (hn : ((Acore + k + h0 : ℕ) : ℤ) ≤ n) :
        canonical D α γ u n t = 0 := hA n (by omega)
    have boundB (n : ℤ) (hn : ((Bcore + k + h1 : ℕ) : ℤ) ≤ n) :
        canonical D β γ v n t = 0 := hB n (by omega)
    have original := original_left_collision D α β γ δ u v t w k
      (Acore + k + h0) (Bcore + k + h1) boundA boundB x y
      (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))
    have transformedEq :
        (∑ i ∈ Finset.range (y.toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
            clear k F (x + i) (y - i)) =
        ∑ i ∈ Finset.range (y.toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial (-x - 1 + k) i) •
            F (x - k + i) (y - i) := by
      simpa only [Nat.cast_zero, add_zero] using transformed
    refine transformedEq.trans ?_
    rw [original]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show -x - 1 + k = (k : ℤ) - x - 1 by omega]
    apply congrArg (fun v : Oscillator D =>
      (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - x - 1) i) • v)
    dsimp only [F]
    congr 1 <;> omega
  simp_rw [shifted_middle_expansion, Finset.smul_sum]
  rw [final_action_expansion]
  calc
    _ = ∑ h0 ∈ Finset.range (a 0 + 1), ∑ h1 ∈ Finset.range (a 1 + 1),
        ((a 0).choose h0 : ℂ) • (((a 1).choose h1 : ℂ) •
          (∑ i ∈ Finset.range (y.toNat + 1),
            (((-1 : ℂ) ^ i) * integerBinomial (-x - 1) i) •
              clear k (fun s b => middleIterate D α β γ δ u v t w
                (s - (Acore + k + h0 : ℕ)) (b - (Bcore + k + h1 : ℕ))
                (z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ))) (x + i) (y - i))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h0 hh0
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h1 hh1
      rw [Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h0 hh0
      apply Finset.sum_congr rfl
      intro h1 hh1
      rw [term]
      rfl

private theorem extra_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (A B : ℕ) (x y z : ℤ) :
    polynomialAction ((variablePolynomial 0 + variablePolynomial 1) ^ A *
      variablePolynomial 1 ^ B) F ![x, y, z] =
      ∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) •
        F ![x - h, y - B - A + h, z] := by
  have h := xy_iterate_action F 0 A B 0 x y z
  simpa only [pow_zero, one_mul, mul_one, Nat.cast_zero, sub_zero, clearIterate] using h

private theorem final_native_extra {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (A B : ℕ) :
    finalCollision ((MvPowerSeries.X 0 ^ A * MvPowerSeries.X 1 ^ B) *
      MvPowerSeries.subst (middleArguments R) P) =
      (((MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ A * MvPowerSeries.X 1 ^ B) *
        MvPowerSeries.subst (triangularArguments R) P) := by
  have legal : MvPowerSeries.HasSubst (finalArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [finalArguments]
  have combined := final_middle_substitution P
  unfold finalCollision at combined ⊢
  rw [MvPowerSeries.subst_mul legal, MvPowerSeries.subst_mul legal,
    MvPowerSeries.subst_pow legal, MvPowerSeries.subst_pow legal,
    MvPowerSeries.subst_X legal, MvPowerSeries.subst_X legal, combined]
  rfl

/-- Actual M=Rmiddle L supplies the native Q. Original-state Jacobi supplies
the other side. SAME k,a,P,R survive cancellation of the TEMPORARY extra
factor. No raw K/R/common-P equality is a premise of this inference. -/
private theorem sameR_from_actual_middle (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (P : MvPowerSeries (Fin 3) (Oscillator D))
    (common : ∀ b s z : ℤ, clearedMiddleSlice D α β γ δ u v t w k a b s z =
      signedExtend (MvPowerSeries.subst (middleArguments (Oscillator D)) P) ![s, b, z])
    (U Acore Bcore : ℕ)
    (hU : ∀ n : ℤ, (U : ℤ) ≤ n → canonical D α β u n v = 0)
    (hA : ∀ n : ℤ, (Acore : ℤ) ≤ n → canonical D α γ u n t = 0)
    (hB : ∀ n : ℤ, (Bcore : ℤ) ≤ n → canonical D β γ v n t = 0)
    (x y z : ℤ) :
    polynomialAction (finalPolynomial k a)
      (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) ![x, y, z] =
      signedExtend (MvPowerSeries.subst (triangularArguments (Oscillator D)) P) ![x, y, z] := by
  classical
  let K : Distribution 3 (Oscillator D) := fun e =>
    leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)
  let Pm := MvPowerSeries.subst (middleArguments (Oscillator D)) P
  let Ptri := MvPowerSeries.subst (triangularArguments (Oscillator D)) P
  let Q : MvPowerSeries (Fin 3) (Oscillator D) :=
    (MvPowerSeries.X 0 ^ Acore * MvPowerSeries.X 1 ^ Bcore) * Pm
  let G : ℤ → ℤ → ℤ → Oscillator D := fun x y z =>
    polynomialAction (finalPolynomial k a) K ![x, y, z]
  let H : ℤ → ℤ → ℤ → Oscillator D := fun x y z => signedExtend Ptri ![x, y, z]
  have nativeQ (b s z : ℤ) :
      clearedMiddleSlice D α β γ δ u v t w k a (b - Bcore) (s - Acore) z =
        signedExtend Q ![s, b, z] := by
    dsimp only [Q]
    rw [mul_assoc, signed_X_pow_mul, signed_X_pow_mul]
    have index : (![s, b, z] : Exponent 3) - Acore • Pi.single 0 1 -
        Bcore • Pi.single 1 1 = ![s - Acore, b - Bcore, z] := by
      funext i
      fin_cases i <;> simp [nsmul_eq_mul, Pi.single_apply, Matrix.vecHead, Matrix.vecTail]
    rw [index]
    exact common _ _ _
  have lowerK (x y z : ℤ) (hx : x < -(U : ℤ)) : K ![x, y, z] = 0 := by
    dsimp only [K, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    unfold leftNested
    rw [hU (-x - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  have lowerG (x y z : ℤ) (hx : x < -(U : ℤ)) : G x y z = 0 := by
    dsimp only [G]
    have expanded := final_action_expansion K k a 0 0 x y z
    simp only [pow_zero, one_mul, mul_one] at expanded
    rw [expanded]
    apply Finset.sum_eq_zero
    intro h0 hh0
    apply Finset.sum_eq_zero
    intro h1 hh1
    have zero : clearIterate k (0 + k + h0) (0 + k + h1)
        (fun x y => K ![x, y, z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ)]) x y = 0 := by
      unfold clearIterate
      apply Finset.sum_eq_zero
      intro h hh
      change ((0 + k + h0).choose h : ℂ) • K
        ![x - k - h, y - (0 + k + h1 : ℕ) - (0 + k + h0 : ℕ) + h,
          z - ((a 0 - h0) + (a 1 - h1) + a 2 : ℕ)] = 0
      rw [lowerK _ _ _ (by omega), smul_zero]
    rw [zero, smul_zero, smul_zero]
  have lowerH (x y z : ℤ) (hx : x < -(U : ℤ)) : H x y z = 0 := by
    dsimp only [H]
    apply if_neg
    intro h
    have := h 0
    change 0 ≤ x at this
    omega
  have extra (x y z : ℤ) :
      (∑ h ∈ Finset.range (Acore + 1), (Acore.choose h : ℂ) •
        G (x - h) (y - Bcore - Acore + h) z) =
      ∑ h ∈ Finset.range (Acore + 1), (Acore.choose h : ℂ) •
        H (x - h) (y - Bcore - Acore + h) z := by
    have native := signed_final_transform
      (fun b s z => clearedMiddleSlice D α β γ δ u v t w k a
        (b - Bcore) (s - Acore) z) Q nativeQ x y z
    have actual := actual_extra_covariance D α β γ δ u v t w k a Acore Bcore hA hB x y z
    have withExtra : polynomialAction
        (((variablePolynomial 0 + variablePolynomial 1) ^ Acore *
          variablePolynomial 1 ^ Bcore) * finalPolynomial k a) K ![x, y, z] =
        signedExtend (finalCollision Q) ![x, y, z] := actual.symm.trans native
    change polynomialAction
      (((variablePolynomial 0 + variablePolynomial 1) ^ Acore *
        variablePolynomial 1 ^ Bcore) * finalPolynomial k a) K ![x, y, z] =
      signedExtend (finalCollision Q) ![x, y, z] at withExtra
    have actionExtra := extra_action (polynomialAction (finalPolynomial k a) K)
      Acore Bcore x y z
    have actionMul := congrFun
      (congrArg (fun L : Module.End ℂ (Distribution 3 (Oscillator D)) => L K)
        (map_mul (polynomialAction (V := Oscillator D))
          ((variablePolynomial 0 + variablePolynomial 1) ^ Acore * variablePolynomial 1 ^ Bcore)
          (finalPolynomial k a))) ![x, y, z]
    have translated :
        (∑ h ∈ Finset.range (Acore + 1), (Acore.choose h : ℂ) •
          G (x - h) (y - Bcore - Acore + h) z) =
        signedExtend (finalCollision Q) ![x, y, z] :=
      actionExtra.symm.trans (actionMul.symm.trans withExtra)
    rw [translated]
    have multiplyQ : finalCollision Q =
        (((MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ Acore *
          MvPowerSeries.X 1 ^ Bcore) * Ptri) := final_native_extra P Acore Bcore
    rw [multiplyQ]
    simpa only [H] using (signed_extra_mul Ptri Acore Bcore x y z)
  exact remove_supported_extra G H Acore Bcore U lowerG lowerH extra x y z

/-- The literal final polynomial acts on the actual canonical left-nested
channel as the triangular substitution of the original common numerator.
The original k, a, P, truncation and all six signed product laws are retained. -/
theorem actual_three_field_same_R_left_covariance
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let states : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c states i)
          (labelledFields D c states j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        ∀ e : Exponent 3,
          polynomialAction (finalPolynomial k a)
            (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
            signedExtend (MvPowerSeries.subst (triangularArguments (Oscillator D)) P) e := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_middle_common_numerator D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, common⟩ := rest δ w
  obtain ⟨U, hU⟩ := canonical_truncation D α β u v
  obtain ⟨A, hA⟩ := canonical_truncation D α γ u t
  obtain ⟨B, hB⟩ := canonical_truncation D β γ v t
  refine ⟨a, P, truncation, six, ?_⟩
  intro e
  have target := sameR_from_actual_middle D α β γ δ u v t w k a P common
    U.toNat A.toNat B.toNat
    (fun n hn => hU n (by omega)) (fun n hn => hA n (by omega))
    (fun n hn => hB n (by omega)) (e 0) (e 1) (e 2)
  have index : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [index] using target

#print axioms actual_three_field_same_R_left_covariance
end
end D5.S3.VertexAlgebra.LatticeSectorSameRLeftCovariance
