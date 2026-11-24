/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterRootDimensions
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterDiagonalMultiplicity

/-! The native Monster string alphabet and Euler exponents in total degree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open Finset MonsterPositiveStringPresentation PowerSeries WeightedFreeAlgebraEulerSeries
open ActualLeechOrbifoldMonsterDenominator
  (integerDiagonalDenominator)
open MonsterPositiveCocycle (imaginaryRoot realRoot)
open RealRootBracket (monsterSimpleMomentum positiveRoot)

open private low_dimensions from
  D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldHeckeExpansion

attribute [local instance] realCartanStateAddCommGroup realCartanShellAddCommGroup
  realCartanCyclesAddCommGroup

/-- The actual positive real simple root is one-dimensional. -/
theorem monsterPositiveRealGrade_finrank :
    Module.finrank ℝ (realMomentumGrade (monsterNativeMomentum realRoot)) = 1 := by
  rw [monsterNativeMomentum_realRoot]
  have hp : positiveRoot ≠ 0 := by
    intro h
    have hz := congrFun h (0 : Fin 2)
    norm_num [positiveRoot] at hz
  rw [realMomentumGrade_finrank_of_ne_zero _ hp]
  simpa [positiveRoot] using low_dimensions.1

theorem monsterPositiveRealGrade_span
    (x : realMomentumGrade (monsterNativeMomentum realRoot)) :
    ∃ r : ℝ, (r • monsterRealPositiveGenerator none : momentumRealLie) = x.val := by
  revert x
  have hdim := monsterPositiveRealGrade_finrank
  rw [monsterNativeMomentum_realRoot] at hdim ⊢
  intro x
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hdim monsterRealSimpleE_ne_zero x
  exact ⟨r, congrArg Subtype.val hr⟩

abbrev MonsterStringToken := StringToken monsterRealOrder

/-- Every token in a string of order `n` has total degree `n+1`. -/
def monsterStringDegree (w : MonsterStringToken) : ℕ := (monsterRealOrder w.1 : ℕ) + 1

theorem monsterStringDegree_pos (w : MonsterStringToken) : 0 < monsterStringDegree w := by
  simp [monsterStringDegree]

theorem monsterStringDegree_eq_coordinates (w : MonsterStringToken) :
    (monsterStringDegree w : ℤ) =
      (tokenWeight monsterRealOrder w).1 + (tokenWeight monsterRealOrder w).2 := by
  rw [tokenWeight_coordinates]
  simp [monsterStringDegree]
  omega

private abbrev SimpleDimension (n : ℕ+) :=
  Module.finrank ℝ (realMomentumGrade (monsterSimpleMomentum n))

private def tokenEquiv : MonsterStringToken ≃ Σ n : ℕ+, Fin (SimpleDimension n) × Fin (n : ℕ) :=
  (Equiv.sigmaAssoc (fun (n : ℕ+) (_ : Fin (SimpleDimension n)) => Fin (n : ℕ))).trans
    (Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _)

private theorem tokenEquiv_degree (w : MonsterStringToken) :
    monsterStringDegree w = ((tokenEquiv w).1 : ℕ) + 1 := rfl

theorem finite_monsterStringDegree_cutoff (d : ℕ) :
    Finite {w : MonsterStringToken // monsterStringDegree w ≤ d} := by
  let f : {n : ℕ+ // (n : ℕ) + 1 ≤ d} → Fin (d + 1) :=
    fun n => ⟨n.1, by have := n.property; omega⟩
  let : Finite {n : ℕ+ // (n : ℕ) + 1 ≤ d} :=
    Finite.of_injective f fun _ _ h => Subtype.ext (Subtype.ext (congrArg Fin.val h))
  let e := (Equiv.subtypeEquiv (p := fun w => monsterStringDegree w ≤ d)
      tokenEquiv (fun w => by rw [tokenEquiv_degree])).trans
    (Equiv.subtypeSigmaEquiv (fun n : ℕ+ => Fin (SimpleDimension n) × Fin (n : ℕ))
      (fun n => (n : ℕ) + 1 ≤ d))
  exact Finite.of_injective e e.injective

/-- The exact number of actual string tokens in degree `d`. -/
theorem monsterString_letterCount (d : ℕ) :
    letterCount monsterStringDegree d =
      if 2 ≤ d then
        (d - 1) * ActualLeechOrbifoldMonsterDenominator.multiplicity 1 (d - 1)
      else 0 := by
  by_cases hd : 2 ≤ d
  · let n : ℕ+ := ⟨d - 1, by omega⟩
    let e : {w : MonsterStringToken // monsterStringDegree w = d} ≃
        Fin (SimpleDimension n) × Fin (n : ℕ) :=
      (Equiv.subtypeEquiv tokenEquiv (fun w => by
        rw [tokenEquiv_degree]
        constructor
        · intro h
          apply Subtype.ext
          change ((tokenEquiv w).1 : ℕ) = d - 1
          omega
        · intro h
          have hv := congrArg (fun x : ℕ+ => (x : ℕ)) h
          change ((tokenEquiv w).1 : ℕ) = d - 1 at hv
          omega)).trans (Equiv.sigmaSubtype n)
    have hdim :
        SimpleDimension n = ActualLeechOrbifoldMonsterDenominator.multiplicity 1 (d - 1) := by
      change Module.finrank ℝ (realMomentumGrade (monsterSimpleMomentum (d - 1))) = _
      rw [← monsterNativeMomentum_imaginaryRoot]
      exact monsterImaginaryGrade_finrank 1 (d - 1) (by decide)
    rw [letterCount, Nat.card_congr e, Nat.card_prod, Nat.card_fin, Nat.card_fin,
      ite_eq_left hd, hdim, mul_comm]
    rfl
  · let : IsEmpty {w : MonsterStringToken // monsterStringDegree w = d} := ⟨fun w => by
      have h := w.property
      have hn := (monsterRealOrder w.val.1).property
      change (monsterRealOrder w.val.1 : ℕ) + 1 = d at h
      have hge : 2 ≤ (monsterRealOrder w.val.1 : ℕ) + 1 :=
        Nat.succ_le_succ (Nat.succ_le_of_lt hn)
      exact hd (h ▸ hge)⟩
    simp [letterCount, hd]

private theorem integerDiagonalDenominator_eq_letters :
    integerDiagonalDenominator = 1 - letterSeries ℤ monsterStringDegree := by
  unfold integerDiagonalDenominator
  congr 1
  ext d
  rw [coeff_X_pow_mul', letterSeries]
  simp only [coeff_mk, monsterString_letterCount]
  by_cases hd : 2 ≤ d
  · simp only [ite_eq_left hd, Nat.cast_mul]
    have h : d - 2 + 1 = d - 1 := by omega
    have hcast : ((d - 2 : ℕ) : ℤ) + 1 = ((d - 1 : ℕ) : ℤ) := by exact_mod_cast h
    rw [h, hcast]
  · simp [hd]

/-- The independently proved integral Monster denominator, with factors grouped
by total degree, is the finite denominator for the actual string alphabet. -/
theorem monsterNative_truncatedEulerDenominator (N : ℕ) :
    trunc (N + 1) (truncatedEulerDenominator ℤ monsterNativeImaginaryMultiplicity N) =
      trunc (N + 1) (1 - letterSeries ℤ monsterStringDegree) := by
  rw [monsterNative_truncatedEulerDenominator_eq_diagonal, integerDiagonalDenominator_eq_letters]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
