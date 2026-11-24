/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRealRootStrings
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterRealRootStrings
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Exact real-root Serre relations and string lengths in the actual relative BRST algebra. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootLocalNilpotence
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNullMomentum
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
For the actual relative ghost-one classes at momentum `(1,-n)`, the first lowering
and the `n`th raising land in nonzero null momenta. The swapped `sl₂` triple gives
the intervening nonvanishing powers and the lowering coefficients.

proof_shape: monster_real_root_serre, monster_ad_pow_eq_zero_iff,
  monster_string_finrank: content
admission_basis: escape-witness
escape_witness: Momentum determines the two vanishing endpoints. The Cartan eigenvalues
separate the nonzero powers of the real-root adjoint between them.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RealRootBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeBracket (MomentumH1 momentumBracket momentumBracket_incl)
open RelativeCohomology (GradedCycles GradedCohomology ghostOne_eq_zero_of_nonzero_null)

open private ad_pow_incl_mem from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootLocalNilpotence
open private rootCycle root_norms incl_injective from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "raise" => LieAlgebra.ad ℂ MomentumH1 positiveRootClass

local instance (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Momentum) : AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

/-- The momentum `(1,-n)` of the imaginary simple-root family for `n ≥ 1`. -/
def monsterSimpleMomentum (n : ℕ) : Momentum :=
  fun (i : Fin 2) => if i = 0 then 1 else -(n : ℤ)

private theorem monsterSimpleMomentum_zero (n : ℕ) :
    monsterSimpleMomentum n (0 : Fin 2) = 1 := by
  simp [monsterSimpleMomentum]

private theorem monsterSimpleMomentum_one (n : ℕ) :
    monsterSimpleMomentum n (1 : Fin 2) = -(n : ℤ) := by
  simp [monsterSimpleMomentum]

private theorem incl_eq_zero_of_nonzero_null (p : Momentum) (hp : p ≠ 0)
    (hnull : p (0 : Fin 2) * p (1 : Fin 2) = 0) (x : H p) : incl p x = 0 := by
  rw [ghostOne_eq_zero_of_nonzero_null p hp hnull x, map_zero]

/-- The normalized actual root classes form an `sl₂` triple in `MomentumH1`. -/
theorem normalized_real_root_isSl2Triple :
    IsSl2Triple (cartanClass (fun _ => 1)) positiveRootClass (-negativeRootClass) := by
  obtain ⟨hef, hhe, hhf⟩ := normalized_real_root_triple
  refine ⟨?_, hef, ?_, ?_⟩
  · rw [← opposite_root_lie_brackets.2.2.2.1, ← lie_skew]
    exact neg_ne_zero.mpr opposite_root_lie_brackets.2.2.2.2
  · simpa only [two_smul] using hhe
  · simpa only [neg_smul, two_smul] using hhf

/-- Lowering a class at `(1,-n)` reaches the nonzero null momentum `(0,-n-1)`. -/
theorem lie_negativeRootClass_neg_monsterSimple (n : ℕ) (x : H (monsterSimpleMomentum n)) :
    ⁅-negativeRootClass, incl (monsterSimpleMomentum n) x⁆ = 0 := by
  let p : Momentum := -positiveRoot + monsterSimpleMomentum n
  have hp₀ : p (0 : Fin 2) = 0 := by
    change -(positiveRoot (0 : Fin 2)) + monsterSimpleMomentum n (0 : Fin 2) = 0
    simp only [positiveRoot, monsterSimpleMomentum_zero, neg_add_cancel]
  have hp₁ : p (1 : Fin 2) = -1 - (n : ℤ) := by
    change -(positiveRoot (1 : Fin 2)) + monsterSimpleMomentum n (1 : Fin 2) = _
    simp only [positiveRoot, monsterSimpleMomentum_one, sub_eq_add_neg]
  have hp : p ≠ 0 := by
    intro hz
    have hz₁ := congrFun hz (1 : Fin 2)
    change p (1 : Fin 2) = 0 at hz₁
    rw [hp₁] at hz₁
    omega
  have hnull : p (0 : Fin 2) * p (1 : Fin 2) = 0 := by rw [hp₀, zero_mul]
  let u : H (-positiveRoot) := Submodule.Quotient.mk (rootCycle (-positiveRoot) root_norms.2)
  rw [neg_lie]
  change -(momentumBracket (incl (-positiveRoot) u) (incl (monsterSimpleMomentum n) x)) = 0
  rw [momentumBracket_incl, incl_eq_zero_of_nonzero_null p hp hnull, neg_zero]

/-- The normalized Cartan class acts on momentum `(1,-n)` by the scalar `1-n`. -/
theorem lie_cartanClass_monsterSimple (n : ℕ) (x : H (monsterSimpleMomentum n)) :
    ⁅cartanClass (fun _ => 1), incl (monsterSimpleMomentum n) x⁆ =
      (1 - (n : ℂ)) • incl (monsterSimpleMomentum n) x := by
  rw [lie_cartanClass_incl]
  simp only [one_mul, monsterSimpleMomentum_one, monsterSimpleMomentum_zero,
    Int.cast_neg, Int.cast_natCast, Int.cast_one, sub_eq_add_neg, add_comm]

/-- The native real-simple-root Serre relation at `(1,-n)`. The `n`th power
of the positive-root adjoint reaches `(n+1,0)`. -/
theorem monster_real_root_serre (n : ℕ) (x : H (monsterSimpleMomentum n)) :
    (raise ^ n) (incl (monsterSimpleMomentum n) x) = 0 := by
  let p : Momentum := monsterSimpleMomentum n + n • positiveRoot
  have hp₀ : p (0 : Fin 2) = (n : ℤ) + 1 := by
    change monsterSimpleMomentum n (0 : Fin 2) + n • positiveRoot (0 : Fin 2) = _
    simp only [monsterSimpleMomentum_zero, positiveRoot, Int.nsmul_eq_mul, mul_one, add_comm]
  have hp₁ : p (1 : Fin 2) = 0 := by
    change monsterSimpleMomentum n (1 : Fin 2) + n • positiveRoot (1 : Fin 2) = 0
    simp only [monsterSimpleMomentum_one, positiveRoot, Int.nsmul_eq_mul, mul_one, neg_add_cancel]
  have hp : p ≠ 0 := by
    intro hz
    have hz₀ := congrFun hz (0 : Fin 2)
    change p (0 : Fin 2) = 0 at hz₀
    rw [hp₀] at hz₀
    omega
  have hnull : p (0 : Fin 2) * p (1 : Fin 2) = 0 := by rw [hp₁, mul_zero]
  let u : H positiveRoot := Submodule.Quotient.mk (rootCycle positiveRoot root_norms.1)
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp
    (ad_pow_incl_mem positiveRoot (monsterSimpleMomentum n) u x n)
  change incl p y = (raise ^ n) (incl (monsterSimpleMomentum n) x) at hy
  exact hy.symm.trans (incl_eq_zero_of_nonzero_null p hp hnull y)

set_option maxHeartbeats 1000000 in
private theorem monster_primitive (n : ℕ) (hn : 1 ≤ n) (x : H (monsterSimpleMomentum n))
    (hx : x ≠ 0) : IsSl2Triple.HasPrimitiveVectorWith normalized_real_root_isSl2Triple.symm
      (incl (monsterSimpleMomentum n) x) ((n - 1 : ℕ) : ℂ) := by
  refine ⟨?_, ?_, lie_negativeRootClass_neg_monsterSimple n x⟩
  · intro hz
    exact hx (incl_injective (monsterSimpleMomentum n)
      (hz.trans ((incl (monsterSimpleMomentum n)).map_zero).symm))
  · rw [neg_lie, lie_cartanClass_monsterSimple, ← neg_smul, neg_sub,
      Nat.cast_sub hn, Nat.cast_one]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Every power strictly below the Serre exponent survives on a nonzero class. -/
theorem monster_ad_pow_ne_zero (n : ℕ) (hn : 1 ≤ n) (x : H (monsterSimpleMomentum n))
    (hx : x ≠ 0) (k : ℕ) (hk : k < n) :
    (raise ^ k) (incl (monsterSimpleMomentum n) x) ≠ 0 :=
  (monster_primitive n hn x hx).pow_toEnd_f_ne_zero_of_eq_nat
    (n := n - 1) rfl (by omega : k ≤ n - 1)

/-- The first vanishing power on a nonzero class at `(1,-n)` is exactly `n`. -/
theorem monster_ad_pow_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) (x : H (monsterSimpleMomentum n))
    (hx : x ≠ 0) (k : ℕ) : (raise ^ k) (incl (monsterSimpleMomentum n) x) = 0 ↔ n ≤ k := by
  constructor
  · intro hz
    by_contra! hk
    exact monster_ad_pow_ne_zero n hn x hx k hk hz
  · intro hk
    rw [show k = (k - n) + n by omega, pow_add, Module.End.mul_apply,
      monster_real_root_serre, map_zero]

set_option maxHeartbeats 1000000 in
/-- The `k`th raised vector has Cartan weight `1-n+2k`. -/
theorem lie_cartanClass_monster_ad_pow (n : ℕ) (hn : 1 ≤ n)
    (x : H (monsterSimpleMomentum n)) (k : ℕ) :
    ⁅cartanClass (fun _ => 1), (raise ^ k) (incl (monsterSimpleMomentum n) x)⁆ =
      (1 - (n : ℂ) + 2 * (k : ℂ)) • (raise ^ k) (incl (monsterSimpleMomentum n) x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hw := (monster_primitive n hn x hx).lie_h_pow_toEnd_f k
  rw [neg_lie, neg_eq_iff_eq_neg, ← neg_smul, Nat.cast_sub hn, Nat.cast_one] at hw
  rw [show -((n : ℂ) - 1 - 2 * (k : ℂ)) = 1 - (n : ℂ) + 2 * (k : ℂ) by ring] at hw
  exact hw

set_option maxHeartbeats 1000000 in
/-- With unscaled raising powers `v_k`, lowering sends `v_(k+1)` to
`(k+1)(n-1-k) v_k`. -/
theorem lie_negativeRootClass_neg_monster_ad_pow_succ (n : ℕ) (hn : 1 ≤ n)
    (x : H (monsterSimpleMomentum n)) (k : ℕ) :
    ⁅-negativeRootClass, (raise ^ (k + 1)) (incl (monsterSimpleMomentum n) x)⁆ =
      (((k : ℂ) + 1) * ((n : ℂ) - 1 - (k : ℂ))) •
        (raise ^ k) (incl (monsterSimpleMomentum n) x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hl := (monster_primitive n hn x hx).lie_e_pow_succ_toEnd_f k
  rw [Nat.cast_sub hn, Nat.cast_one] at hl
  exact hl

set_option synthInstance.maxHeartbeats 80000 in
/-- The surviving powers in a nonzero string are independent by their Cartan weights. -/
theorem monster_string_linearIndependent (n : ℕ) (hn : 1 ≤ n)
    (x : H (monsterSimpleMomentum n)) (hx : x ≠ 0) :
    LinearIndependent ℂ (fun i : Fin n => (raise ^ i.val) (incl (monsterSimpleMomentum n) x)) := by
  let weights : Fin n → ℂ := fun i => 1 - (n : ℂ) + 2 * (i.val : ℂ)
  refine (LieAlgebra.ad ℂ MomentumH1 (cartanClass (fun _ => 1))).eigenvectors_linearIndependent'
    weights ?_ _ ?_
  · intro i j hij
    apply Fin.ext
    apply Nat.cast_injective (R := ℂ)
    change 1 - (n : ℂ) + 2 * (i.val : ℂ) = 1 - (n : ℂ) + 2 * (j.val : ℂ) at hij
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (add_left_cancel hij)
  · intro i
    exact Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (lie_cartanClass_monster_ad_pow n hn x i.val),
        monster_ad_pow_ne_zero n hn x hx i.val i.isLt⟩

/-- The cyclic string spanned by all raising powers on a nonzero class has dimension `n`. -/
theorem monster_string_finrank (n : ℕ) (hn : 1 ≤ n) (x : H (monsterSimpleMomentum n))
    (hx : x ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun k : ℕ => (raise ^ k) (incl (monsterSimpleMomentum n) x)))) = n := by
  have hspan : Submodule.span ℂ (Set.range (fun k : ℕ =>
      (raise ^ k) (incl (monsterSimpleMomentum n) x))) =
      Submodule.span ℂ (Set.range (fun i : Fin n =>
        (raise ^ i.val) (incl (monsterSimpleMomentum n) x))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      by_cases hk : k < n
      · exact Submodule.subset_span ⟨(⟨k, hk⟩ : Fin n), rfl⟩
      · dsimp only
        rw [(monster_ad_pow_eq_zero_iff n hn x hx k).2 (by omega : n ≤ k)]
        exact Submodule.zero_mem _
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [hspan, finrank_span_eq_card (monster_string_linearIndependent n hn x hx), Fintype.card_fin]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RealRootBracket
