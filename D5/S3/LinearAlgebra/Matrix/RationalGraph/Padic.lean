/- GID: D5/S3/LinearAlgebra/Matrix/RationalGraph/Padic
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-power matrix congruences over the p-adic integers -/

import OmegaBuild.Commands
import Mathlib.NumberTheory.Padics.RingHoms
import D5.S3.LinearAlgebra.Matrix.RationalGraph.CRT

/-! Omega original.

# Prime-power matrix congruences over the p-adic integers

Reduction to the same finite residue ring identifies the p-adic congruence
index with the corresponding integer index. If the congruence modulo `p ^ l`
comes from clearing a denominator `p ^ l * c` with `p ∤ c`, membership is
equivalent to integrality of the original rational matrix product over `ℤ_[p]`.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators Padic

namespace Omega.RationalMatrixGraph.Padic

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-- Coordinatewise reduction of a p-adic integer vector modulo `p ^ l`. -/
def reduceVecPow {n : Type*} (l : ℕ) : (n → ℤ_[p]) →+ (n → ZMod (p ^ l)) where
  toFun v i := PadicInt.toZModPow l (v i)
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

theorem reduceVecPow_surj {n : Type*} (l : ℕ) :
    Function.Surjective (reduceVecPow p (n := n) l) := by
  intro v
  choose a ha using fun i : n => ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) l) (v i)
  exact ⟨a, funext ha⟩

/-- The p-adic integer vectors whose image under `A` vanishes modulo `p ^ l`. -/
def localKernel {n : Type*} [Fintype n] (l : ℕ) (A : Matrix n n ℤ) :
    AddSubgroup (n → ℤ_[p]) :=
  ((CRT.reduceMatrix (p ^ l) A).mulVecLin.toAddMonoidHom.comp
    (reduceVecPow p l)).ker

/-- Both indices count the image of the same matrix over `ZMod (p ^ l)`. -/
theorem localKernel_index {n : Type*} [Fintype n] (l : ℕ) (A : Matrix n n ℤ) :
    (localKernel p l A).index = (CRT.graphKernel (p ^ l) A).index := by
  rw [CRT.kernel_card]
  let f := (CRT.reduceMatrix (p ^ l) A).mulVecLin.toAddMonoidHom
  let g := f.comp (reduceVecPow p l)
  have hr : g.range = f.range := by
    change (f.comp (reduceVecPow p l)).range = f.range
    rw [AddMonoidHom.range_comp, AddMonoidHom.range_eq_top.mpr (reduceVecPow_surj p l),
      AddSubgroup.map_top]
  change Nat.card ((n → ℤ_[p]) ⧸ g.ker) = Nat.card f.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hr]

theorem localKernel_mem {n : Type*} [Fintype n] (l : ℕ) (A : Matrix n n ℤ)
    (v : n → ℤ_[p]) :
    v ∈ localKernel p l A ↔ ∀ i, (p : ℤ_[p]) ^ l ∣ (A.map (Int.castRingHom ℤ_[p]) *ᵥ v) i := by
  unfold localKernel
  rw [AddMonoidHom.mem_ker]
  let f := PadicInt.toZModPow (p := p) l
  let B := A.map (Int.castRingHom ℤ_[p])
  have hM : B.map f = CRT.reduceMatrix (p ^ l) A := by
    ext i j
    exact map_intCast f _
  have hs (i : n) :
      ((CRT.reduceMatrix (p ^ l) A).mulVecLin.toAddMonoidHom.comp
        (reduceVecPow p l)) v i = f ((B *ᵥ v) i) := by
    change (CRT.reduceMatrix (p ^ l) A *ᵥ (f ∘ v)) i = _
    rw [← hM, ← RingHom.map_mulVec]
  constructor
  · intro hv i
    have he := congrFun hv i
    rw [hs] at he
    change PadicInt.toZModPow l ((B *ᵥ v) i) = 0 at he
    rwa [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at he
  · intro hv
    ext i
    rw [hs]
    change PadicInt.toZModPow l ((B *ᵥ v) i) = 0
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hv i

/-- The integer congruence index factors over the prime powers dividing `D`. -/
theorem global_index {n : Type*} [Fintype n] (D : ℕ) (hD : D ≠ 0) (A : Matrix n n ℤ) :
    (CRT.graphKernel D A).index =
      ∏ q : D.primeFactors, (localKernel q.val (D.factorization q.val) A
        (hp := ⟨Nat.prime_of_mem_primeFactors q.property⟩)).index := by
  classical
  simp_rw [localKernel_index]
  let d : D.primeFactors → ℕ := fun q => q.val ^ (D.factorization q.val)
  have hd : (∏ i, d i) = D := (Nat.prod_primeFactors_coe_pow_factorization hD).symm
  have hc : Pairwise (Function.onFun Nat.Coprime d) :=
    D.pairwise_coprime_pow_primeFactors_factorization
  simpa only [d, hd] using CRT.index_prod d hc A

/-- A cleared congruence at `p` is equivalent to integrality of the unscaled
rational matrix product in the p-adic field. -/
theorem localKernel_unscaled {n : Type*} [Fintype n] (D c l : ℕ) (hc : ¬p ∣ c)
    (hDc : D = p ^ l * c) (A : Matrix n n ℤ) (E : Matrix n n ℚ)
    (hA : ∀ i j, (A i j : ℚ) = (D : ℚ) * E i j) (v : n → ℤ_[p]) :
    v ∈ localKernel p l A ↔
      ∀ i, ∃ a : ℤ_[p], (a : ℚ_[p]) =
        ((E.map (algebraMap ℚ ℚ_[p])) *ᵥ (fun j => (v j : ℚ_[p]))) i := by
  rw [localKernel_mem]
  apply forall_congr'
  intro i
  let b := ((A.map (Int.castRingHom ℤ_[p])) *ᵥ v) i
  let e := ((E.map (algebraMap ℚ ℚ_[p])) *ᵥ (fun j => (v j : ℚ_[p]))) i
  change (p : ℤ_[p]) ^ l ∣ b ↔ ∃ a : ℤ_[p], (a : ℚ_[p]) = e
  have hb : (b : ℚ_[p]) = (D : ℚ_[p]) * e := by
    unfold b e
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    change (PadicInt.Coe.ringHom (p := p)) (∑ j : n, (A i j : ℤ_[p]) * v j) = _
    rw [map_sum]
    simp only [map_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hh := congrArg (fun q : ℚ => (q : ℚ_[p])) (hA i j)
    push_cast at hh
    change (A i j : ℚ_[p]) * (v j : ℚ_[p]) =
      (D : ℚ_[p]) * ((E i j : ℚ_[p]) * (v j : ℚ_[p]))
    rw [hh, mul_assoc]
  have hunit : IsUnit (c : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hc))
  let u := hunit.unit
  have hu : (u : ℤ_[p]) = (c : ℤ_[p]) := hunit.unit_spec
  have hD : (D : ℚ_[p]) = (p : ℚ_[p]) ^ l * (c : ℚ_[p]) := by
    exact_mod_cast hDc
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(↑u⁻¹ : ℤ_[p]) * a, ?_⟩
    have he : (a : ℚ_[p]) = (c : ℚ_[p]) * e := by
      apply mul_left_cancel₀ (pow_ne_zero _ hp0)
      rw [ha, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hD, mul_assoc] at hb
      exact hb
    have hu' : ((u : ℤ_[p]) : ℚ_[p]) = (c : ℚ_[p]) := by
      rw [hu, PadicInt.coe_natCast]
    rw [PadicInt.coe_mul, he, ← hu', ← mul_assoc, ← PadicInt.coe_mul, Units.inv_mul,
      PadicInt.coe_one, one_mul]
  · rintro ⟨a, ha⟩
    refine ⟨(c : ℤ_[p]) * a, PadicInt.coe_inj.mp ?_⟩
    rw [hb, hD, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      PadicInt.coe_natCast, ha, mul_assoc]

end

end Omega.RationalMatrixGraph.Padic
