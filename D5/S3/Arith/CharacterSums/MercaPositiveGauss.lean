/- GID: D5/S3/Arith/CharacterSums/MercaPositiveGauss
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/MercaPositiveGauss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The positive quadratic Gauss sign from the actual rank-one even lattice. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import D5.S3.Analytic.Zeta.PrimeQuadraticLValues
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
Milgram's classical positive phase is specialized to the rank-one lattice with
Gram matrix (2r). Its actual discriminant group is parametrized by residues
modulo r and modulo two. The resulting evaluation fixes the quadratic Gauss sign.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.MercaPositiveGauss
open D5.S3.VertexAlgebra LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDiscriminantWeil Matrix

private abbrev rankOne (r : ℕ) : LatticeData where
  rank := 1
  G := fun _ _ => 2 * (r : ℤ)
  symmetric := by intros; rfl
  even_diagonal := fun _ => ⟨r, by ring⟩

private lemma rankOne_positive (r : ℕ) (hr : 0 < r) :
    (gramReal (rankOne r)).PosDef := by
  have hg : gramReal (rankOne r) = Matrix.of (fun (_ _ : Fin 1) => (2 : ℝ) * r) := by
    ext i j
    change ((2 * (r : ℤ) : ℤ) : ℝ) = 2 * r
    push_cast
    rfl
  rw [hg]
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    rfl
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    have hp : (0 : ℝ) < r := Nat.cast_pos.mpr hr
    have hs := sq_pos_of_ne_zero hx0
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, star_trivial, Matrix.of_apply]
    nlinarith

private def param (r : ℕ) (x : ZMod r × ZMod 2) : Discriminant (rankOne r) :=
  classOf (rankOne r) (fun _ => 2 * (x.1.val : ℤ) + (r : ℤ) * x.2.val)

private lemma param_injective (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    Function.Injective (param r) := by
  intro x y hxy
  obtain ⟨v, hv⟩ := (Submodule.Quotient.eq (gramRange (rankOne r))).mp hxy
  have hv0 : 2 * (r : ℤ) * v 0 =
      (2 * (x.1.val : ℤ) + (r : ℤ) * x.2.val) -
        (2 * (y.1.val : ℤ) + (r : ℤ) * y.2.val) := by
    simpa [gramMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one] using
      congrFun hv (0 : Fin 1)
  have h1 : x.1 = y.1 := by
    have hc := congrArg (fun z : ℤ => (z : ZMod r)) hv0
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, mul_zero, add_zero, ZMod.natCast_zmod_val] at hc
    apply mul_left_cancel₀ (Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega)))
    linear_combination -hc
  have hr2 : (r : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod r 2, show r % 2 = 1 by omega]
    rfl
  have h2 : x.2 = y.2 := by
    have hc := congrArg (fun z : ℤ => (z : ZMod 2)) hv0
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat, Int.cast_natCast, hr2,
      show (2 : ZMod 2) = 0 by decide, zero_mul, mul_zero, zero_add, one_mul,
      ZMod.natCast_zmod_val] at hc
    exact sub_eq_zero.mp hc.symm
  exact Prod.ext h1 h2

private def paramEquiv (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    ZMod r × ZMod 2 ≃ Discriminant (rankOne r) := by
  letI : Fact (gramReal (rankOne r)).PosDef := ⟨rankOne_positive r (Fact.out : r.Prime).pos⟩
  letI : Finite (Discriminant (rankOne r)) :=
    @discriminantFinite (rankOne r) ⟨rankOne_positive r (Fact.out : r.Prime).pos⟩
  letI : Fintype (Discriminant (rankOne r)) := Fintype.ofFinite _
  apply Equiv.ofBijective (param r)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨param_injective r hr, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
    (dual_lattice_realization (rankOne r) (rankOne_positive r (Fact.out : r.Prime).pos)).2.1]
  change r * 2 = (Matrix.det (fun (_ _ : Fin 1) => 2 * (r : ℤ))).natAbs
  rw [Matrix.det_fin_one]
  simp [Int.natAbs_mul, Nat.mul_comm]

private lemma pair_rankOne (r : ℕ) (v : ℤ) :
    pairRaw (rankOne r) (fun _ => v) (fun _ => v) =
      (v : ℚ) ^ 2 / (2 * r) := by
  have hg : gramRat (rankOne r) = Matrix.of (fun (_ _ : Fin 1) => (2 : ℚ) * r) := by
    ext i j
    change ((2 * (r : ℤ) : ℤ) : ℚ) = 2 * r
    push_cast
    rfl
  simp only [pairRaw, dualVector, inverseRat, hg, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one, Matrix.inv_subsingleton, Matrix.diagonal_apply, Matrix.of_apply,
    ite_true, Ring.inverse_eq_inv]
  ring

private lemma parameter_quadratic (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (y : ZMod r) (e : ZMod 2) :
    quadraticClass (rankOne r) (param r (y, e)) =
      (((y.val : ℚ) ^ 2 / r : ℚ) : QmodZ) + ((e.val : ℚ) ^ 2 / 4 : ℚ) := by
  rw [param, quadraticClass_mk (rankOne r)
    (rankOne_positive r (Fact.out : r.Prime).pos), pair_rankOne]
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  have hr4 : r = 4 * (r / 4) + 1 := by omega
  have hrat : ((2 * (y.val : ℤ) + (r : ℤ) * e.val : ℤ) : ℚ) ^ 2 /
      (2 * r) / 2 = (y.val : ℚ) ^ 2 / r + (e.val : ℚ) ^ 2 / 4 +
        (((y.val : ℤ) * e.val + (r / 4 : ℕ) * (e.val : ℤ) ^ 2 : ℤ) : ℚ) := by
    have hc : (r : ℚ) = 4 * (r / 4 : ℕ) + 1 := by exact_mod_cast hr4
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
    field_simp [hrQ]
    rw [hc]
    ring
  rw [hrat, AddCircle.coe_add, AddCircle.coe_add]
  have hz (z : ℤ) : ((z : ℚ) : QmodZ) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨z, by simp⟩
  rw [hz, add_zero]

private lemma parameter_phase (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)
    (y : ZMod r) (e : ZMod 2) :
    phase (quadraticClass (rankOne r) (param r (y, e))) =
      ZMod.stdAddChar (y ^ 2) * if e = 0 then 1 else Complex.I := by
  rw [parameter_quadratic r hr, phase.map_add_eq_mul]
  have hy : phase (((y.val : ℚ) ^ 2 / r : ℚ) : QmodZ) =
      ZMod.stdAddChar (y ^ 2) := by
    rw [phase_mk]
    have hyc : y ^ 2 = ((y.val : ℤ) ^ 2 : ℤ) := by simp
    rw [hyc, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hy]
  congr 1
  by_cases he : e = 0
  · subst e
    norm_num [phase_mk, ZMod.val]
  · have he1 : e = 1 := by fin_cases e <;> norm_num at *
    subst e
    norm_num only [show (1 : ZMod 2).val = 1 by decide, phase_mk,
      show (1 : ZMod 2) ≠ 0 by decide, ite_false, Nat.cast_one, one_pow]
    convert Complex.exp_pi_div_two_mul_I using 1 <;> congr 1 <;> norm_num <;> ring

private lemma milgram_square_sum (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    (1 + Complex.I) * (∑ y : ZMod r, ZMod.stdAddChar (y ^ 2)) =
      (Real.sqrt (2 * (r : ℝ)) : ℂ) *
        Complex.exp (Real.pi * Complex.I / 4) := by
  let D := rankOne r
  have hD := rankOne_positive r (Fact.out : r.Prime).pos
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Finite (Discriminant D) := @discriminantFinite D ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hm := milgram D hD
  have hcard : Nat.card (Discriminant D) = 2 * r := by
    rw [(dual_lattice_realization D hD).2.1]
    change (Matrix.det (fun (_ _ : Fin 1) => 2 * (r : ℤ))).natAbs = 2 * r
    rw [Matrix.det_fin_one]
    simp [Int.natAbs_mul]
  have hrho : rho D = (Real.sqrt (2 * (r : ℝ)) : ℂ) := by
    rw [rho, hcard, Nat.cast_mul, Nat.cast_ofNat]
  have hsum : (∑ a : Discriminant D, phase (quadraticClass D a)) =
      (1 + Complex.I) * ∑ y : ZMod r, ZMod.stdAddChar (y ^ 2) := by
    rw [← Equiv.sum_comp (paramEquiv r hr)]
    change (∑ x : ZMod r × ZMod 2,
      phase (quadraticClass (rankOne r) (param r x))) = _
    rw [Fintype.sum_prod_type]
    simp_rw [parameter_phase r hr]
    simp only [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
      Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), ite_true,
      if_neg (by decide : (1 : ZMod 2) ≠ 0), mul_one]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hn : rho D ≠ 0 := by
    rw [hrho]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr (Fact.out : r.Prime).pos))).ne'
  change (rho D)⁻¹ * (∑ a : Discriminant D, phase (quadraticClass D a)) = _ at hm
  rw [hsum, show D.rank = 1 by rfl, Nat.cast_one, mul_one] at hm
  have he := congrArg (fun z : ℂ => rho D * z) hm
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, hrho] at he
  exact he

/-- The positive square-root evaluation comes from Milgram's positive analytic
phase, so it fixes the sign left undetermined by the squared Gauss identity. -/
theorem square_sum (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    (∑ y : ZMod r, ZMod.stdAddChar (y ^ 2)) = (Real.sqrt r : ℂ) := by
  have hm := milgram_square_sum r hr
  have hp : Complex.exp (Real.pi * Complex.I / 4) =
      (Real.sqrt 2 : ℂ) / 2 * (1 + Complex.I) := by
    rw [show (Real.pi : ℂ) * Complex.I / 4 =
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      ← Complex.cos_add_sin_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    ring
  rw [hp, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul] at hm
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hrhs : (Real.sqrt 2 : ℂ) * (Real.sqrt r : ℂ) *
      ((Real.sqrt 2 : ℂ) / 2 * (1 + Complex.I)) =
      (1 + Complex.I) * (Real.sqrt r : ℂ) := by
    linear_combination ((Real.sqrt r : ℂ) * (1 + Complex.I) / 2) * hs
  rw [hrhs] at hm
  apply mul_left_cancel₀ (show (1 + Complex.I : ℂ) ≠ 0 by
    intro h; have hi := congrArg Complex.re h; norm_num at hi)
  exact hm

private lemma square_sum_eq_gauss (r : ℕ) [Fact r.Prime] (hr : r ≠ 2) :
    (∑ y : ZMod r, ZMod.stdAddChar (y ^ 2)) =
      gaussSum (D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter r)
        ZMod.stdAddChar := by
  classical
  let ψ : AddChar (ZMod r) ℂ := ZMod.stdAddChar
  have hψ : ψ ≠ 1 := by
    intro h
    have he : ψ (1 : ZMod r) = ψ 0 := by rw [h]; rfl
    have hz := ZMod.injective_stdAddChar he
    exact one_ne_zero hz
  have htotal : ∑ a : ZMod r, ψ a = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have hf (a : ZMod r) :
      (∑ y : ZMod r, if y ^ 2 = a then ψ a else 0) =
        ((quadraticChar (ZMod r) a : ℂ) + 1) * ψ a := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := quadraticChar_card_sqrts ((ZMod.ringChar_zmod_n r).substr hr) a
    simp only [Set.toFinset_setOf] at hc
    exact_mod_cast hc
  calc
    _ = ∑ y : ZMod r, ∑ a : ZMod r, if y ^ 2 = a then ψ a else 0 := by simp [ψ]
    _ = ∑ a : ZMod r, ∑ y : ZMod r, if y ^ 2 = a then ψ a else 0 :=
      Finset.sum_comm
    _ = ∑ a : ZMod r, ((quadraticChar (ZMod r) a : ℂ) + 1) * ψ a := by simp_rw [hf]
    _ = _ := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib, htotal, add_zero,
        gaussSum, D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter,
        MulChar.ringHomComp_apply, ψ]
      rfl

/-- The standard Gauss sum of the genuine Legendre character has positive sign. -/
theorem prime_gauss_sum (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    gaussSum (D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter r)
      ZMod.stdAddChar = (Real.sqrt r : ℂ) := by
  rw [← square_sum_eq_gauss r (by omega), square_sum r hr]

end D5.S3.Arith.CharacterSums.MercaPositiveGauss
