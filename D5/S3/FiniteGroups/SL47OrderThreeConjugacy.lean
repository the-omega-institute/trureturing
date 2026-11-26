import D5.S3.FiniteGroups.ExtremalC48GroupStep
import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.Algebra.Group.Conj

/-! Element conjugacy at order three in `SL₂(F₄₇)` and its transport to lattice isometries. -/

set_option autoImplicit false

namespace ExtremalC48

open Matrix
open scoped Matrix Pointwise

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def A : SL47 :=
  ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩

private def N : SL47 :=
  ⟨!![3, 20; 23, -3], by rw [Matrix.det_fin_two_of]; decide⟩

private theorem A_order : orderOf A = 3 := by
  refine orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext
    change ((A ^ 3 : SL47) : Matrix (Fin 2) (Fin 2) (ZMod 47)) =
      ((1 : SL47) : Matrix (Fin 2) (Fin 2) (ZMod 47))
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, pow_succ _ 2, pow_two]
    simp only [A, SpecialLinearGroup.coe_mk, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro h
    have h00 := congrArg (fun M : SL47 => M 0 0) h
    change (0 : ZMod 47) = 1 at h00
    exact (by decide : (0 : ZMod 47) ≠ 1) h00

private theorem N_mul_A : N * A = A ^ 2 * N := by
  apply Subtype.ext
  change ((N * A : SL47) : Matrix (Fin 2) (Fin 2) (ZMod 47)) =
    ((A ^ 2 * N : SL47) : Matrix (Fin 2) (Fin 2) (ZMod 47))
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow, pow_two]
  simp only [N, A, SpecialLinearGroup.coe_mk, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem orderThree_isConj_A (x : SL47) (hx : orderOf x = 3) : IsConj x A := by
  classical
  have hp : Nat.Prime 3 := Fact.out
  have hDiv : 3 ∣ Nat.card SL47 := by rw [card_SL47]; decide
  have hNotDiv : ¬ 3 ^ 2 ∣ Nat.card SL47 := by rw [card_SL47]; decide
  have hFactor : (Nat.card SL47).factorization 3 = 1 := by
    have hLower := (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hDiv
    have hUpper : ¬ 2 ≤ (Nat.card SL47).factorization 3 := fun h =>
      hNotDiv ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h)
    omega
  let P := Sylow.ofCard (Subgroup.zpowers x) (p := 3) (by
    rw [Nat.card_zpowers, hx, hFactor, pow_one])
  let Q := Sylow.ofCard (Subgroup.zpowers A) (p := 3) (by
    rw [Nat.card_zpowers, A_order, hFactor, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL47 P Q
  have hPQ : MulAut.conj g • Subgroup.zpowers x = Subgroup.zpowers A :=
    congrArg Sylow.toSubgroup hg
  have hMem := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Subgroup.zpowers x)
    (Subgroup.mem_zpowers x)
  rw [hPQ] at hMem
  change g * x * g⁻¹ ∈ Subgroup.zpowers A at hMem
  have hRange := mem_zpowers_iff_mem_range_orderOf.mp hMem
  rw [A_order] at hRange
  obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp hRange
  have hkLt := Finset.mem_range.mp hk
  have hCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hConj : IsConj x (g * x * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  rcases hCases with rfl | rfl | rfl
  · rw [← hkEq, pow_zero] at hConj
    exact ((orderOf_eq_prime_iff.mp hx).2 (isConj_one_left.mp hConj)).elim
  · rw [← hkEq, pow_one] at hConj
    exact hConj
  · rw [← hkEq] at hConj
    have hSquare : IsConj A (A ^ 2) := isConj_iff.mpr
      ⟨N, mul_inv_eq_iff_eq_mul.mpr N_mul_A⟩
    exact hConj.trans hSquare.symm

/-- Any two elements of order three in `SL₂(F₄₇)` are conjugate. -/
theorem SL47_orderThree_isConj (x y : SL47) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    IsConj x y :=
  (orderThree_isConj_A x hx).trans (orderThree_isConj_A y hy).symm

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality (LatticeData Charge bilinear)

/-- A faithful, exhaustive realization of `SL₂(F₄₇)` by integral lattice isometries
gives a form-preserving conjugator between any two isometries of order three. -/
theorem lattice_orderThree_conjugacy (D : LatticeData)
    (μ : Additive SL47 →+ AddAut (Charge D)) (hFaithful : Function.Injective μ)
    (hPreserves : ∀ s : Additive SL47, ∀ a b, bilinear D (μ s a) (μ s b) = bilinear D a b)
    (hExhaustive : ∀ s : AddAut (Charge D),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) → ∃ k, μ k = s)
    (x y : AddAut (Charge D))
    (hx : ∀ a b, bilinear D (x a) (x b) = bilinear D a b)
    (hy : ∀ a b, bilinear D (y a) (y b) = bilinear D a b)
    (hxOrder : addOrderOf x = 3) (hyOrder : addOrderOf y = 3) :
    ∃ r : AddAut (Charge D),
      (∀ a b, bilinear D (r a) (r b) = bilinear D a b) ∧ ∀ z, r (x z) = y (r z) := by
  obtain ⟨a, ha⟩ := hExhaustive x hx
  obtain ⟨b, hb⟩ := hExhaustive y hy
  have preimageOrder (s : Additive SL47) (hs : addOrderOf (μ s) = 3) : orderOf s.toMul = 3 :=
    calc
      orderOf s.toMul = addOrderOf s := (addOrderOf_ofMul_eq_orderOf s.toMul).symm
      _ = addOrderOf (μ s) := (addOrderOf_injective μ hFaithful s).symm
      _ = 3 := hs
  have haOrder := preimageOrder a (by simpa only [ha] using hxOrder)
  have hbOrder := preimageOrder b (by simpa only [hb] using hyOrder)
  obtain ⟨c, hc⟩ := isConj_iff.mp (SL47_orderThree_isConj a.toMul b.toMul haOrder hbOrder)
  have hab : c * a.toMul = b.toMul * c := mul_inv_eq_iff_eq_mul.mp hc
  have hEq : μ (Additive.ofMul c) + μ a = μ b + μ (Additive.ofMul c) := by
    rw [← map_add, ← map_add]
    exact congrArg (fun t : SL47 => μ (Additive.ofMul t)) hab
  refine ⟨μ (Additive.ofMul c), hPreserves (Additive.ofMul c), fun z => ?_⟩
  rw [← ha, ← hb]
  exact congrArg (fun s : AddAut (Charge D) => s z) hEq

end ExtremalC48
