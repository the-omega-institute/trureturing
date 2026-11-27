/- GID: D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicIntegralLattice
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Integral lattice saturation and exact trace determinants of cubic orders. -/

import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Int.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open scoped Polynomial
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice
open Matrix Algebra Finset

/-- The discriminant of an integral lattice kills the quotient by that lattice,
without a power basis or multiplicative closure hypothesis on the lattice. -/
theorem discr_smul_mem_integral_span
    {L ι : Type*} [Field L] [Algebra ℚ L] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ L) (hint : ∀ i, IsIntegral ℤ (b i))
    {z : L} (hz : IsIntegral ℤ z) :
    Algebra.discr ℚ b • z ∈ Submodule.span ℤ (Set.range b) := by
  classical
  let _ := Module.Finite.of_basis b
  have hinv : IsUnit (traceMatrix ℚ b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis ℚ b
  have H :
    (traceMatrix ℚ b).det • (traceMatrix ℚ b) *ᵥ (b.equivFun z) =
      (traceMatrix ℚ b).det • fun i => trace ℚ L (z * b i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix ℚ b) fun i => trace ℚ L (z * b i)
  suffices h : ∀ i, ((traceMatrix ℚ b).det • b.equivFun z) i ∈ (⊥ : Subalgebra ℤ ℚ) by
    rw [← b.sum_repr (Algebra.discr ℚ b • z)]
    refine Submodule.sum_mem _ fun i _ => ?_
    specialize h i
    rw [← discr_def, Pi.smul_apply, mem_bot] at h
    obtain ⟨r, hr⟩ := h
    rw [Module.Basis.equivFun_apply] at hr
    rw [map_smul, Finsupp.smul_apply, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro i
  rw [← H, ← mulVec_smul] at cramer
  replace cramer := congr((mulVec (traceMatrix ℚ b)⁻¹) $cramer)
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv,
    one_mulVec, one_mulVec] at cramer
  rw [← congr($cramer i), cramer_apply, det_apply]
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, ite_true]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul (hint _)))
  · simp only [updateCol_apply, hji, ite_false]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace ((hint _).mul (hint _)))

/-- Two Eisenstein generators for the same monogenic order remove the two
denominator primes; a coprime clearing scalar then gives global membership. -/
theorem mem_of_two_eisenstein_denominators
    {L : Type*} [Field L] [Algebra ℚ L]
    (a b : PowerBasis ℚ L) {p q e : ℤ} {m n : ℕ}
    (hp : Prime p) (hq : Prime q) (ha : IsIntegral ℤ a.gen) (hb : IsIntegral ℤ b.gen)
    (hpa : (minpoly ℤ a.gen).IsEisensteinAt (Ideal.span {p}))
    (hqb : (minpoly ℤ b.gen).IsEisensteinAt (Ideal.span {q}))
    (hab : adjoin ℤ ({a.gen} : Set L) = adjoin ℤ ({b.gen} : Set L))
    (M : Submodule ℤ L) (hM : (adjoin ℤ ({a.gen} : Set L)).toSubmodule ≤ M)
    (hcop : IsCoprime e (p^m * q^n))
    {z : L} (hz : IsIntegral ℤ z) (hden : (p^m * q^n) • z ∈ M)
    (hclear : ∀ w ∈ M, e • w ∈ adjoin ℤ ({a.gen} : Set L)) :
    z ∈ M := by
  have h := hclear _ hden
  have hpq : p^m • (q^n • (e • z)) ∈ adjoin ℤ ({a.gen} : Set L) := by
    simpa only [smul_smul, mul_assoc, mul_comm, mul_left_comm] using h
  have hqz := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    hp ha ((hz.smul e).smul (q^n)) hpq hpa
  rw [hab] at hqz
  have he := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    hq hb (hz.smul e) hqz hqb
  rw [← hab] at he
  have hEz : e • z ∈ M := hM he
  obtain ⟨u, v, huv⟩ := hcop
  have hsum := M.add_mem (M.smul_mem u hEz) (M.smul_mem v hden)
  rw [smul_smul, smul_smul, ← add_smul, huv, one_smul] at hsum
  exact hsum

/-- Translation by the scalar one does not change a generated integral order. -/
theorem adjoin_sub_one {R L : Type*} [CommRing R] [CommRing L] [Algebra R L] (x : L) :
    adjoin R ({x - 1} : Set L) = adjoin R ({x} : Set L) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (adjoin R ({x} : Set L)).sub_mem (subset_adjoin rfl) (one_mem _)
  · apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h := (adjoin R ({x-1} : Set L)).add_mem (subset_adjoin (Set.mem_singleton (x-1))) (one_mem _)
    change x ∈ adjoin R ({x-1} : Set L)
    simpa only [sub_add_cancel] using h

/-- An integral monic Eisenstein equation is already the minimal polynomial. -/
theorem eq_minpoly_of_eisenstein {L : Type*} [Field L] [Algebra ℚ L]
    {x : L} {f : ℤ[X]} {p : ℤ} (hp : Prime p) (hmon : f.Monic)
    (hdeg : 0 < f.natDegree) (hei : f.IsEisensteinAt (Ideal.span {p}))
    (hroot : Polynomial.aeval x f = 0) :
    f = minpoly ℤ x := by
  have hprime : (Ideal.span ({p} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hirr : Irreducible f := hei.irreducible hprime hmon.isPrimitive hdeg
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hint : IsIntegral ℤ x := ⟨f, hmon, hroot⟩
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  refine Polynomial.eq_of_monic_of_associated hmon (minpoly.monic hint) ?_
  exact mul_one (minpoly ℤ x) ▸ hg.symm ▸ Associated.mul_left _
    (associated_one_iff_isUnit.2 <| (hirr.isUnit_or_isUnit hg).resolve_left <| minpoly.not_isUnit ℤ x)

/-- Exact membership in the integral lattice, once the proposed basis has
discriminant supported on the same two primes as its Eisenstein witnesses. -/
theorem integral_span_of_two_eisenstein
    {L ι : Type*} [Field L] [Algebra ℚ L] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι ℚ L) (hint : ∀ i, IsIntegral ℤ (B i))
    (a b : PowerBasis ℚ L) {p q e : ℤ} {m n : ℕ}
    (hp : Prime p) (hq : Prime q) (ha : IsIntegral ℤ a.gen) (hb : IsIntegral ℤ b.gen)
    (hpa : (minpoly ℤ a.gen).IsEisensteinAt (Ideal.span {p}))
    (hqb : (minpoly ℤ b.gen).IsEisensteinAt (Ideal.span {q}))
    (hab : adjoin ℤ ({a.gen} : Set L) = adjoin ℤ ({b.gen} : Set L))
    (M : Submodule ℤ L) (hM : (adjoin ℤ ({a.gen} : Set L)).toSubmodule ≤ M)
    (hBM : Submodule.span ℤ (Set.range B) ≤ M)
    (hcop : IsCoprime e (p^m * q^n))
    (hdisc : Algebra.discr ℚ B = ((p^m * q^n : ℤ) : ℚ))
    (hclear : ∀ w ∈ M, e • w ∈ adjoin ℤ ({a.gen} : Set L))
    {z : L} (hz : IsIntegral ℤ z) :
    z ∈ M := by
  apply mem_of_two_eisenstein_denominators a b hp hq ha hb hpa hqb hab M hM hcop hz _ hclear
  have hh := discr_smul_mem_integral_span B hint hz
  rw [hdisc, Int.cast_smul_eq_zsmul] at hh
  exact hBM hh

theorem intermediate_adjoin_sub_one {L : Type*} [Field L] [Algebra ℚ L] (x : L) :
    IntermediateField.adjoin ℚ ({x - 1} : Set L) =
      IntermediateField.adjoin ℚ ({x} : Set L) := by
  apply le_antisymm <;> rw [IntermediateField.adjoin_simple_le_iff]
  · exact (IntermediateField.adjoin ℚ ({x} : Set L)).sub_mem
      (IntermediateField.mem_adjoin_simple_self ℚ x) (one_mem _)
  · have h := (IntermediateField.adjoin ℚ ({x-1} : Set L)).add_mem
       (IntermediateField.mem_adjoin_simple_self ℚ (x-1)) (one_mem _)
    simpa only [sub_add_cancel] using h

/-- In a simple number field a monic companion and its integral translate
provide both prime-saturation witnesses for the same monogenic order. -/
theorem integral_span_of_eisenstein_translate
    {L ι : Type*} [Field L] [Algebra ℚ L] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι ℚ L) (hint : ∀ i, IsIntegral ℤ (B i))
    (x : L) (hxgen : IntermediateField.adjoin ℚ ({x} : Set L) = ⊤)
    {f : ℤ[X]} (hmon : f.Monic) (hdeg : 0 < f.natDegree)
    (hroot : Polynomial.aeval x f = 0)
    {p q e : ℤ} {m n : ℕ} (hp : Prime p) (hq : Prime q)
    (hpa : f.IsEisensteinAt (Ideal.span {p}))
    (hqb : (f.comp (Polynomial.X + Polynomial.C 1)).IsEisensteinAt (Ideal.span {q}))
    (M : Submodule ℤ L) (hM : (adjoin ℤ ({x} : Set L)).toSubmodule ≤ M)
    (hBM : Submodule.span ℤ (Set.range B) ≤ M)
    (hcop : IsCoprime e (p^m * q^n))
    (hdisc : Algebra.discr ℚ B = ((p^m * q^n : ℤ) : ℚ))
    (hclear : ∀ w ∈ M, e • w ∈ adjoin ℤ ({x} : Set L))
    {z : L} (hz : IsIntegral ℤ z) :
    z ∈ M := by
  let g := f.comp (Polynomial.X + Polynomial.C 1)
  have hgmon : g.Monic := hmon.comp (Polynomial.monic_X_add_C 1) fun h => by simp at h
  have hgdeg : 0 < g.natDegree := by
    simpa [g, Polynomial.natDegree_comp] using hdeg
  have hgroot : Polynomial.aeval (x-1) g = 0 := by
    dsimp only [g]
    rw [Polynomial.aeval_comp]
    simpa using hroot
  have hx : IsIntegral ℤ x := ⟨f, hmon, hroot⟩
  have hy : IsIntegral ℤ (x-1) := ⟨g, hgmon, hgroot⟩
  let a := PowerBasis.ofAdjoinSimpleEqTop (hx.tower_top (A := ℚ)) hxgen
  let b := PowerBasis.ofAdjoinSimpleEqTop (hy.tower_top (A := ℚ))
    ((intermediate_adjoin_sub_one x).trans hxgen)
  have hagen : a.gen = x := by simp [a]
  have hbgen : b.gen = x-1 := by simp [b]
  have haex : (minpoly ℤ x).IsEisensteinAt (Ideal.span {p}) :=
    (eq_minpoly_of_eisenstein hp hmon hdeg hpa hroot) ▸ hpa
  have hbex : (minpoly ℤ (x-1)).IsEisensteinAt (Ideal.span {q}) :=
    (eq_minpoly_of_eisenstein hq hgmon hgdeg hqb hgroot) ▸ hqb
  apply integral_span_of_two_eisenstein B hint a b hp hq
    (hagen ▸ hx) (hbgen ▸ hy) (hagen ▸ haex) (hbgen ▸ hbex)
    ?_ M ?_ hBM hcop hdisc ?_ hz
  · rw [hagen, hbgen, adjoin_sub_one]
  · simpa only [hagen] using hM
  · simpa only [hagen] using hclear

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

/-- The integral multiplication table of the scaled power basis. -/
theorem scaled_basis_products {R : Type*} [CommRing R] (A B C x : R)
    (hx : A*x^3+B*x^2+C*x+A=0) :
    let α := A*x
    let β := A*x^2+B*x
    α^2 = A*β-B*α ∧ α*β = -C*α-A^2 ∧ β^2 = -C*β-A*α-B*A := by
  dsimp
  constructor
  · ring
  constructor
  · linear_combination A*hx
  · linear_combination (A*x+B)*hx

/-- The companion numerator in the actual integral scaled basis. -/
theorem companion_numerator {R : Type*} [CommRing R] (A D x : R) :
    let α := A*x
    let β := A*x^2-3*D*x
    (α-D)^2 = A*β+D*α+D^2 := by
  dsimp
  ring

/-- The square of the companion can be obtained with no new denominator. -/
theorem companion_square {F : Type*} [Field F] (P E y : F)
    (hP : P ≠ 0) (hy : y^3-3*P^2*y+E*P^2=0) :
    let θ := y^2/P
    θ^2 = 3*P*θ-E*y := by
  dsimp
  field_simp
  linear_combination y*hy

/-- Two exact integer-linear expressions for the two candidates to enlarge
the scaled order; the coefficients are in the image of the base ring. -/
theorem enlarged_lattice_generators {R : Type*} [CommRing R]
    (A D P α β θ ω k l m n r s : R)
    (hP : ∀ z : R, P*z=0 → z=0)
    (hθ : P*θ=A*β+D*α+D^2)
    (hω : P*ω=β+k*α+l)
    (hk : A*k=D+P*m) (hl : A*l=D^2+P*n) (hBez : r*A+s*P=1) :
    θ=A*ω-m*α-n ∧ ω=r*θ+(r*m+s*k)*α+s*β+(r*n+s*l) := by
  have hθω : θ=A*ω-m*α-n := by
    apply sub_eq_zero.mp
    apply hP
    linear_combination hθ-A*hω-α*hk-hl
  exact ⟨hθω, by linear_combination -r*hθω+s*hω-ω*hBez⟩


end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

open Algebra Matrix

/-- The table trace Gram is the genuine algebra trace Gram of a scaled
basis, not merely an auxiliary matrix. No separability hypothesis is needed
for this computation. -/
theorem traceMatrix_scaled {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (b : Module.Basis (Fin 3) K L) (A B C : K) (α β : L)
    (hb0 : b 0 = 1) (hb1 : b 1 = α) (hb2 : b 2 = β)
    (ha2 : α*α = A • β - B • α)
    (hab : α*β = (-C) • α - algebraMap K L (A^2))
    (hb2p : β*β = (-C) • β - A • α - algebraMap K L (B*A)) :
    traceMatrix K b = !![3, -B, -2*C;
                         -B, B^2-2*A*C, B*C-3*A^2;
                         -2*C, B*C-3*A^2, 2*C^2-2*A*B] := by
  have hrepr (u v w : K) (i : Fin 3) :
      b.repr (u • b 0 + v • b 1 + w • b 2) i =
        u*(if i=0 then 1 else 0)+v*(if i=1 then 1 else 0)+w*(if i=2 then 1 else 0) := by
    simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hreprα (i j : Fin 3) : b.repr (α * b j) i =
      (!![0, 0, -A^2; 1, -B, -C; 0, A, 0] : Matrix (Fin 3) (Fin 3) K) i j := by
    have he0 : α * b 0 = (0:K) • b 0 + (1:K) • b 1 + (0:K) • b 2 := by simp [hb0,hb1]
    have he1 : α * b 1 = (0:K) • b 0 + (-B) • b 1 + A • b 2 := by
      rw [hb1,ha2]
      simp [hb2,sub_eq_add_neg,add_comm]
    have he2 : α * b 2 = (-(A^2)) • b 0 + (-C) • b 1 + (0:K) • b 2 := by
      rw [hb2,hab]
      simp [hb0,hb1,Algebra.smul_def,sub_eq_add_neg,add_comm]
    fin_cases j <;>
      first | (change b.repr (α * b 0) i = _; rw [he0,hrepr]; fin_cases i <;> simp)
            | (change b.repr (α * b 1) i = _; rw [he1,hrepr]; fin_cases i <;> simp)
            | (change b.repr (α * b 2) i = _; rw [he2,hrepr]; fin_cases i <;> simp)
  have hreprβ (i j : Fin 3) : b.repr (β * b j) i =
      (!![0, -A^2, -(B*A); 0, -C, -A; 1, 0, -C] : Matrix (Fin 3) (Fin 3) K) i j := by
    have he0 : β * b 0 = (0:K) • b 0 + (0:K) • b 1 + (1:K) • b 2 := by simp [hb0,hb2]
    have he1 : β * b 1 = (-(A^2)) • b 0 + (-C) • b 1 + (0:K) • b 2 := by
      rw [hb1,mul_comm,hab]
      simp [hb0,Algebra.smul_def,sub_eq_add_neg,add_comm]
    have he2 : β * b 2 = (-(B*A)) • b 0 + (-A) • b 1 + (-C) • b 2 := by
      rw [hb2,hb2p]
      simp [hb0,hb1,Algebra.smul_def,sub_eq_add_neg]
      ring
    fin_cases j <;>
      first | (change b.repr (β * b 0) i = _; rw [he0,hrepr]; fin_cases i <;> simp)
            | (change b.repr (β * b 1) i = _; rw [he1,hrepr]; fin_cases i <;> simp)
            | (change b.repr (β * b 2) i = _; rw [he2,hrepr]; fin_cases i <;> simp)
  have htr1 : trace K L (1:L) = 3 := by
    simpa using trace_algebraMap_of_basis b (1:K)
  have htrα : trace K L α = -B := by
    rw [trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_three]
    simp only [diag, leftMulMatrix_eq_repr_mul, hreprα]
    simp
  have htrβ : trace K L β = -2*C := by
    rw [trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_three]
    simp only [diag, leftMulMatrix_eq_repr_mul, hreprβ]
    simp
    ring
  have htrcast (u : K) : trace K L (algebraMap K L u) = 3*u := by
    simpa [three_nsmul, two_mul, add_assoc, add_comm] using trace_algebraMap_of_basis b u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceMatrix_apply, hb0,hb1,hb2, ha2, hab, hb2p, htr1,htrα,htrβ, mul_comm β α] <;>
    first | (rw [← map_pow (algebraMap K L), htrcast]; ring)
          | (rw [← map_mul (algebraMap K L), htrcast]; ring)
          | ring

/-- Under the native norm equation, the actual old basis trace
determinant is the known binary-cubic discriminant. -/
theorem traceMatrix_det_scaled_native {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (b : Module.Basis (Fin 3) K L) (A D P : K) (α β : L)
    (hb0 : b 0 = 1) (hb1 : b 1 = α) (hb2 : b 2 = β)
    (ha2 : α*α = A • β - (-3*D) • α)
    (hab : α*β = (-(3*(D-A))) • α - algebraMap K L (A^2))
    (hb2p : β*β = (-(3*(D-A))) • β - A • α - algebraMap K L ((-3*D)*A))
    (hn : A^2-A*D+D^2=P^2) :
    (traceMatrix K b).det = 81*P^4 := by
  rw [traceMatrix_scaled b A (-3*D) (3*(D-A)) α β hb0 hb1 hb2 ha2 hab hb2p,
    Matrix.det_fin_three]
  simp
  linear_combination (81*(A^2-A*D+D^2+P^2))*hn

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

/-- The enlarged four-generator lattice becomes a sublattice of the
companion power order after multiplying by AE. -/
theorem clear_enlarged_lattice {L : Type*} [CommRing L]
    (A D E P a b c d : ℤ) (α β θ : L)
    (hβ : (A:L)*β = (P:L)*θ - (D:L)*α - (D:L)^2)
    (hα : (E:L)*α = 3*(P:L)*θ - θ^2 + (E:L)*(D:L)) :
    ((A*E : ℤ) : L) * ((a:L) + (b:L)*α + (c:L)*β + (d:L)*θ) ∈
      Algebra.adjoin ℤ ({θ} : Set L) := by
  let S := Algebra.adjoin ℤ ({θ} : Set L)
  have hθ : θ ∈ S := Algebra.subset_adjoin (Set.mem_singleton θ)
  have hcast (n : ℤ) : (n:L) ∈ S := S.intCast_mem n
  have hEα : (E:L)*α ∈ S := by
    rw [hα]
    exact S.add_mem (S.sub_mem
      (S.mul_mem (S.mul_mem (show (3:L) ∈ S by simpa only [Int.cast_ofNat] using hcast 3) (hcast P)) hθ)
      (S.pow_mem hθ 2)) (S.mul_mem (hcast E) (hcast D))
  have hAEβ : (A:L)*(E:L)*β ∈ S := by
    rw [show (A:L)*(E:L)*β =
      ((E:L)*(P:L))*θ - (D:L)*((E:L)*α) - (E:L)*(D:L)^2 by
      linear_combination (E:L)*hβ]
    exact S.sub_mem (S.sub_mem (S.mul_mem (S.mul_mem (hcast E) (hcast P)) hθ)
      (S.mul_mem (hcast D) hEα)) (S.mul_mem (hcast E) (S.pow_mem (hcast D) 2))
  rw [show ((A*E : ℤ) : L) * ((a:L)+(b:L)*α+(c:L)*β+(d:L)*θ) =
    (((A:L)*(E:L))*(a:L) + ((A:L)*(b:L))*((E:L)*α)) +
    (c:L)*((A:L)*(E:L)*β) + ((A:L)*(E:L)*(d:L))*θ by push_cast; ring]
  exact S.add_mem (S.add_mem (S.add_mem
    (S.mul_mem (S.mul_mem (hcast A) (hcast E)) (hcast a))
    (S.mul_mem (S.mul_mem (hcast A) (hcast b)) hEα))
    (S.mul_mem (hcast c) hAEβ))
    (S.mul_mem (S.mul_mem (S.mul_mem (hcast A) (hcast E)) (hcast d)) hθ)

/-- Integer-span form of the clearing assertion, for direct use with
the two-prime global saturation lemma. -/
theorem clear_span_enlarged {L : Type*} [CommRing L]
    (A D E P : ℤ) (α β θ : L)
    (hβ : (A:L)*β = (P:L)*θ - (D:L)*α - (D:L)^2)
    (hα : (E:L)*α = 3*(P:L)*θ - θ^2 + (E:L)*(D:L))
    (z : L) (hz : z ∈ Submodule.span ℤ (Set.range (![1,α,β,θ] : Fin 4 → L))) :
    (A*E) • z ∈ Algebra.adjoin ℤ ({θ} : Set L) := by
  let S := Algebra.adjoin ℤ ({θ} : Set L)
  refine Submodule.span_induction (p := fun w _ => (A*E) • w ∈ S) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨i,rfl⟩
    fin_cases i
    · simpa [Algebra.smul_def, eq_intCast] using clear_enlarged_lattice A D E P 1 0 0 0 α β θ hβ hα
    · simpa [Algebra.smul_def, eq_intCast] using clear_enlarged_lattice A D E P 0 1 0 0 α β θ hβ hα
    · simpa [Algebra.smul_def, eq_intCast] using clear_enlarged_lattice A D E P 0 0 1 0 α β θ hβ hα
    · simpa [Algebra.smul_def, eq_intCast] using clear_enlarged_lattice A D E P 0 0 0 1 α β θ hβ hα
  · rw [smul_zero]
    exact S.zero_mem
  · intro x y hx hy h₁ h₂
    rw [smul_add]
    exact S.add_mem h₁ h₂
  · intro n x hx h₁
    rw [smul_comm]
    exact S.toSubmodule.smul_mem n h₁

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

/-- An integral monic cubic equation puts the entire monogenic order in
any integer lattice containing the three initial powers. -/
theorem adjoin_le_of_monic_cubic {L : Type*} [CommRing L]
    (θ : L) (a b c : ℤ)
    (hc : θ^3 = (a:L)*θ^2+(b:L)*θ+(c:L))
    (M : Submodule ℤ L) (h0 : 1 ∈ M) (h1 : θ ∈ M) (h2 : θ^2 ∈ M) :
    (Algebra.adjoin ℤ ({θ} : Set L)).toSubmodule ≤ M := by
  rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.span_le]
  rintro x ⟨n, rfl⟩
  have hstep (n : ℕ) : θ^(n+3) = a • θ^(n+2) + b • θ^(n+1) + c • θ^n := by
    simp only [Algebra.smul_def, eq_intCast]
    rw [pow_add θ n 3, hc, pow_add θ n 2, pow_add θ n 1]
    ring
  have hp (n : ℕ) : θ^n ∈ M ∧ θ^(n+1) ∈ M ∧ θ^(n+2) ∈ M := by
    induction n with
    | zero => simpa using And.intro h0 (And.intro h1 h2)
    | succ n hn =>
      refine ⟨hn.2.1,hn.2.2,?_⟩
      change θ^(n+3) ∈ M
      rw [hstep]
      exact M.add_mem (M.add_mem (M.smul_mem a hn.2.2) (M.smul_mem b hn.2.1))
        (M.smul_mem c hn.1)
  exact (hp n).1

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice
open Algebra Matrix

/-- Scaling the third primitive lattice vector by 1/P divides the
actual trace determinant by P², even with a shear in the first two vectors. -/
theorem trace_det_single_denominator {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (α β : L) (P k l : K) :
    (traceMatrix K (![1, α, P⁻¹ • (β + k • α + algebraMap K L l)] : Fin 3 → L)).det =
      P⁻¹ ^ 2 * (traceMatrix K (![1, α, β] : Fin 3 → L)).det := by
  let T : Matrix (Fin 3) (Fin 3) K := !![1,0,0; 0,1,0; l/P,k/P,1/P]
  let v : Fin 3 → L := ![1,α,β]
  have hv : T.map (algebraMap K L) *ᵥ v = ![1, α, P⁻¹ • (β+k • α+algebraMap K L l)] := by
    funext i
    fin_cases i <;> simp [T,v,mulVec,dotProduct,Fin.sum_univ_three,Algebra.smul_def,div_eq_mul_inv]
    ring
  have hd : T.det = P⁻¹ := by
    simp [T, Matrix.det_fin_three]
  rw [← hv, traceMatrix_of_matrix_mulVec, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hd]
  dsimp [v]
  ring

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

/-- The old two nontrivial basis elements are integral, witnessed by
explicit monic cubics. -/
theorem scaled_basis_integral {L : Type*} [CommRing L] (A B C : ℤ) (x : L)
    (hx : (A:L)*x^3+(B:L)*x^2+(C:L)*x+(A:L)=0) :
    IsIntegral ℤ ((A:L)*x) ∧ IsIntegral ℤ ((A:L)*x^2+(B:L)*x) := by
  let α := (A:L)*x
  let β := (A:L)*x^2+(B:L)*x
  have htable := scaled_basis_products (A:L) (B:L) (C:L) x hx
  have hal : α^3+(B:L)*α^2+((A*C:ℤ):L)*α+((A^3:ℤ):L)=0 := by
    dsimp [α]
    push_cast
    linear_combination (A:L)^2 * hx
  have hbe : β^3+((2*C:ℤ):L)*β^2+((A*B+C^2:ℤ):L)*β
      + ((A*B*C-A^3:ℤ):L)=0 := by
    have hab : α*β = -(C:L)*α-(A:L)^2 := htable.2.1
    have hbb : β^2 = -(C:L)*β-(A:L)*α-(B:L)*(A:L) := htable.2.2
    push_cast
    linear_combination (β+(C:L))*hbb-(A:L)*hab
  constructor
  · let f : Cubic ℤ := ⟨1,B,A*C,A^3⟩
    refine ⟨f.toPoly, Cubic.monic_of_a_eq_one rfl, ?_⟩
    change Polynomial.aeval α f.toPoly = 0
    simpa only [f,Cubic.toPoly,map_add,map_mul,map_pow,Polynomial.aeval_C,
      Polynomial.aeval_X, eq_intCast, map_intCast, map_ofNat, map_sub, Int.cast_one, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, one_mul] using hal
  · let f : Cubic ℤ := ⟨1,2*C,A*B+C^2,A*B*C-A^3⟩
    refine ⟨f.toPoly, Cubic.monic_of_a_eq_one rfl, ?_⟩
    change Polynomial.aeval β f.toPoly = 0
    simpa only [f,Cubic.toPoly,map_add,map_mul,map_pow,Polynomial.aeval_C,
      Polynomial.aeval_X, eq_intCast, map_intCast, map_ofNat, map_sub, Int.cast_one, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, one_mul] using hbe

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

open Matrix

/-- The two triangular basis changes are valid over the fraction field
when their diagonal factors are nonzero. -/
theorem triangular_basis {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis (Fin 3) K L) (a u v w : K) (ha : a ≠ 0) (hw : w ≠ 0) :
    ∃ b' : Module.Basis (Fin 3) K L,
      b' 0 = b 0 ∧ b' 1 = a • b 1 ∧ b' 2 = u • b 0 + v • b 1 + w • b 2 := by
  let T : Matrix (Fin 3) (Fin 3) K := !![1,0,u; 0,a,v; 0,0,w]
  have hd : IsUnit T.det := by simp [T, Matrix.det_fin_three, ha, hw]
  let b' := b.map (T.toLinearEquiv b hd)
  refine ⟨b', ?_, ?_, ?_⟩
  all_goals simp [b', Matrix.toLinearEquiv_apply, Matrix.toLin_self, Fin.sum_univ_three, T]

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

/-- The explicit inverse generators yield exact equality of integer spans,
not just rational spanning or a determinant comparison. -/
theorem enlarged_spans_eq {L : Type*} [CommRing L]
    (α β θ ω : L) (A m n r u v w P k l : ℤ)
    (hθ : θ = (A:L)*ω-(m:L)*α-(n:L))
    (hω : ω = (r:L)*θ+(u:L)*α+(v:L)*β+(w:L))
    (hβ : β = (P:L)*ω-(k:L)*α-(l:L)) :
    Submodule.span ℤ (Set.range (![1,α,β,θ] : Fin 4 → L)) =
    Submodule.span ℤ (Set.range (![1,α,ω] : Fin 3 → L)) := by
  let M := Submodule.span ℤ (Set.range (![1,α,β,θ] : Fin 4 → L))
  let N := Submodule.span ℤ (Set.range (![1,α,ω] : Fin 3 → L))
  have hM (i : Fin 4) : (![1,α,β,θ] : Fin 4 → L) i ∈ M :=
    Submodule.subset_span ⟨i,rfl⟩
  have hN (i : Fin 3) : (![1,α,ω] : Fin 3 → L) i ∈ N :=
    Submodule.subset_span ⟨i,rfl⟩
  have h0M : 1 ∈ M := hM 0
  have h1M : α ∈ M := hM 1
  have h2M : β ∈ M := hM 2
  have h3M : θ ∈ M := hM 3
  have h0N : 1 ∈ N := hN 0
  have h1N : α ∈ N := hN 1
  have h2N : ω ∈ N := hN 2
  have hcast (S : Submodule ℤ L) (hh : (1:L) ∈ S) (z : ℤ) : (z:L) ∈ S := by
    simpa [Algebra.smul_def,eq_intCast] using S.smul_mem z hh
  have hsm (S : Submodule ℤ L) (z : ℤ) {x : L} (hx : x ∈ S) : (z:L)*x ∈ S := by
    simpa [Algebra.smul_def,eq_intCast] using S.smul_mem z hx
  have hωM : ω ∈ M := by
    rw [hω]
    exact M.add_mem (M.add_mem (M.add_mem (hsm M r h3M) (hsm M u h1M))
      (hsm M v h2M)) (hcast M h0M w)
  have hθN : θ ∈ N := by
    rw [hθ]
    exact N.sub_mem (N.sub_mem (hsm N A h2N) (hsm N m h1N)) (hcast N h0N n)
  have hβN : β ∈ N := by
    rw [hβ]
    exact N.sub_mem (N.sub_mem (hsm N P h2N) (hsm N k h1N)) (hcast N h0N l)
  change M = N
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    fin_cases i
    · exact h0N
    · exact h1N
    · exact hβN
    · exact hθN
  · apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    fin_cases i
    · exact h0M
    · exact h1M
    · exact hωM

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

namespace D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice

open Module NumberField
open scoped NumberField

/-- A tuple spanning precisely the integral elements gives an integral
basis. This interface takes the maximal-lattice result as a hypothesis. -/
noncomputable def integralBasisOfSpan
    {L : Type*} [Field L] [NumberField L] {ι : Type*}
    (b : ι → L) (hc : ∀ i, IsIntegral ℤ (b i))
    (hli : LinearIndependent ℚ b)
    (hs : ∀ x : L, IsIntegral ℤ x → x ∈ Submodule.span ℤ (Set.range b)) :
    Basis ι ℤ (𝓞 L) := by
  let c := RingOfIntegers.restrict b hc
  let f : (𝓞 L) →ₗ[ℤ] L := (IsScalarTower.toAlgHom ℤ (𝓞 L) L).toLinearMap
  have hf : f ∘ c = b := rfl
  have hli' : LinearIndependent ℤ c := by
    apply LinearIndependent.of_comp f
    rw [hf]
    exact hli.restrict_scalars' ℤ
  apply Basis.mk hli'
  intro x _
  have hmap : Submodule.map f (Submodule.span ℤ (Set.range c)) =
      Submodule.span ℤ (Set.range b) := by
    rw [Submodule.map_span, ← Set.range_comp, hf]
  have hm : f x ∈ Submodule.map f (Submodule.span ℤ (Set.range c)) := by
    rw [hmap]
    exact hs _ (RingOfIntegers.isIntegral_coe x)
  obtain ⟨y,hy,heq⟩ := Submodule.mem_map.mp hm
  have hxy : y = x := RingOfIntegers.coe_injective heq
  exact hxy ▸ hy

@[simp] theorem integralBasisOfSpan_coe
    {L : Type*} [Field L] [NumberField L] {ι : Type*}
    (b : ι → L) (hc : ∀ i, IsIntegral ℤ (b i))
    (hli : LinearIndependent ℚ b)
    (hs : ∀ x : L, IsIntegral ℤ x → x ∈ Submodule.span ℤ (Set.range b)) (i : ι) :
    (integralBasisOfSpan b hc hli hs i : L) = b i := by
  unfold integralBasisOfSpan
  rw [Basis.mk_apply]
  rfl

/-- Discriminant transport from any chosen integral basis. -/
theorem discr_eq_of_integralBasis
    {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Basis ι ℤ (𝓞 L)) :
    Algebra.discr ℚ (fun i => (B i : L)) = (NumberField.discr L : ℚ) := by
  have h := Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) (Rₘ := ℚ) L B
  rw [NumberField.discr_eq_discr L B] at h
  have hf : ⇑(B.localizationLocalization ℚ (nonZeroDivisors ℤ) L) =
      (fun i => (B i : L)) := by
    funext i
    exact Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) L B i
  rw [hf] at h
  exact h

/-- An explicit maximal integral span identifies its rational trace
determinant with the signed number-field discriminant. -/
theorem discr_eq_of_integral_span
    {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → L) (hc : ∀ i, IsIntegral ℤ (b i))
    (hli : LinearIndependent ℚ b)
    (hs : ∀ x : L, IsIntegral ℤ x → x ∈ Submodule.span ℤ (Set.range b)) :
    Algebra.discr ℚ b = (NumberField.discr L : ℚ) := by
  simpa only [integralBasisOfSpan_coe] using
    discr_eq_of_integralBasis (integralBasisOfSpan b hc hli hs)

/-- Equality with the integral closure includes tuple integrality. -/
theorem discr_eq_of_span_eq_integralClosure
    {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → L) (hli : LinearIndependent ℚ b)
    (hs : Submodule.span ℤ (Set.range b) = (integralClosure ℤ L).toSubmodule) :
    Algebra.discr ℚ b = (NumberField.discr L : ℚ) := by
  refine discr_eq_of_integral_span b ?_ hli ?_
  · intro i
    change b i ∈ (integralClosure ℤ L).toSubmodule
    rw [← hs]
    exact Submodule.subset_span (Set.mem_range_self i)
  · intro x hx
    rw [hs]
    exact hx

end D5.S3.Factorization.QuadraticIdeals.CubicIntegralLattice
