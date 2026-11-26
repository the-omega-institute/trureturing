/- GID: D5/S1/Eigenstructure/BinaryCubicCompanion
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/BinaryCubicCompanion
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Companion bases for binary cubic characteristic polynomials with constant term one. -/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-! Companion bases for the two cubic polynomials with trace zero and constant term one. -/

namespace D5.S1.Eigenstructure.BinaryCubicCompanion

open Module Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem eq_of_add_eq_zero {x y : V} (h : x + y = 0) : x = y :=
  (add_eq_zero_iff_eq_neg.mp h).trans (ZModModule.neg_eq_self y)

private theorem independent_three (x y z : V)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hxyz : x + y + z ≠ 0) :
    LinearIndependent (ZMod 2) ![x, y, z] := by
  have hxy' : x + y ≠ 0 := fun h => hxy (eq_of_add_eq_zero h)
  have hxz' : x + z ≠ 0 := fun h => hxz (eq_of_add_eq_zero h)
  have hyz' : y + z ≠ 0 := fun h => hyz (eq_of_add_eq_zero h)
  rw [Fintype.linearIndependent_iff]
  intro a h j
  rw [Fin.sum_univ_three] at h
  rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary (a 0) with ha | ha <;>
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary (a 1) with hb | hb <;>
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary (a 2) with hc | hc <;>
    fin_cases j <;> simp_all

private theorem vector_outside_kernels (f g : Module.End (ZMod 2) V) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ v, f v ≠ 0 ∧ g v ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra! h
    exact hg (LinearMap.ext h)
  by_cases hxg : g x = 0
  · by_cases hyf : f y = 0
    · exact ⟨x + y, by simpa [hyf] using hx, by simpa [hxg] using hy⟩
    · exact ⟨y, hyf, hy⟩
  · exact ⟨x, hx, hxg⟩

private theorem cyclic_basis [FiniteDimensional (ZMod 2) V]
    (hdim : finrank (ZMod 2) V = 3) (f : Module.End (ZMod 2) V)
    (a : ZMod 2) (v : V) (hv : v ≠ 0) (hfix : f v ≠ v)
    (hsum : v + f v + f (f v) ≠ 0) (hrec : f (f (f v)) = a • f v + v) :
    ∃ b : Basis (Fin 3) (ZMod 2) V,
      f (b 0) = b 1 ∧ f (b 1) = b 2 ∧ f (b 2) = b 0 + a • b 1 := by
  have hthird : f (f (f v)) ≠ f v := by
    rw [hrec]
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary a with rfl | rfl
    · simpa using Ne.symm hfix
    · simpa using hv
  have hthird0 : f (f (f v)) ≠ 0 := by
    rw [hrec]
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary a with rfl | rfl
    · simpa using hv
    · simpa using fun h : f v + v = 0 => hfix (eq_of_add_eq_zero h)
  have hsecond0 : f (f v) ≠ 0 := by
    intro h
    exact hthird0 (by rw [h, map_zero])
  have hfirst0 : f v ≠ 0 := by
    intro h
    exact hsecond0 (by rw [h, map_zero])
  have hsecond : v ≠ f (f v) := fun h => hthird (congrArg f h).symm
  have hsteps : f v ≠ f (f v) :=
    fun h => hthird ((congrArg f h).symm.trans h.symm)
  have hli := independent_three v (f v) (f (f v)) hv hfirst0 hsecond0 hfix.symm hsecond hsteps hsum
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  refine ⟨b, ?_, ?_, ?_⟩
  · simp [b]
  · simp [b]
  · simpa [b, add_comm] using hrec

/-- The characteristic polynomials X cubed plus one and X cubed plus X
plus one each determine an ordered companion basis over the binary field. -/
theorem exists_basis [FiniteDimensional (ZMod 2) V]
    (hdim : finrank (ZMod 2) V = 3) (f : Module.End (ZMod 2) V)
    (a : ZMod 2) (hf : f.charpoly = X ^ 3 + C a * X + 1) :
    ∃ b : Basis (Fin 3) (ZMod 2) V,
      f (b 0) = b 1 ∧ f (b 1) = b 2 ∧ f (b 2) = b 0 + a • b 1 := by
  have hch := LinearMap.aeval_self_charpoly f
  rw [hf] at hch
  have hpow : f ^ 3 = a • f + 1 := by
    apply (add_eq_zero_iff_eq_neg.mp ?_).trans (ZModModule.neg_eq_self _)
    simpa [aeval_add, aeval_mul, aeval_X_pow, Algebra.smul_def, add_assoc] using hch
  have hrec (v : V) : f (f (f v)) = a • f v + v := by
    simpa [pow_succ, Module.End.mul_apply] using congrFun (congrArg DFunLike.coe hpow) v
  have hne : f ≠ 1 := by
    intro he
    have hc : (X ^ 3 + C a * X + 1 : (ZMod 2)[X]) = (X - 1) ^ 3 := by
      rw [← hf, he, LinearMap.charpoly_one, hdim]
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary a with rfl | rfl
    · have h := congrArg (fun p : (ZMod 2)[X] => p.derivative.eval 1) hc
      norm_num [derivative_pow] at h
      exact (by decide : (3 : ZMod 2) ≠ 0) h
    · have h := congrArg (fun p : (ZMod 2)[X] => p.eval 1) hc
      norm_num at h
      exact (by decide : (3 : ZMod 2) ≠ 0) h
  have hquad : f ^ 2 + f + 1 ≠ 0 := by
    rcases D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary a with rfl | rfl
    · have heig : f.HasEigenvalue 1 :=
        (Module.End.hasEigenvalue_iff_isRoot_charpoly f 1).mpr (by
          norm_num [IsRoot, hf]
          decide)
      obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
      have hvfix : f v = v := by simpa using hv.apply_eq_smul
      intro he
      have hz := congrFun (congrArg DFunLike.coe he) v
      exact hv.2 (by simpa [pow_succ, Module.End.mul_apply, hvfix, ZModModule.add_self] using hz)
    · have hnonzero : f ≠ 0 := by
        intro he
        have h := congrArg (fun p : (ZMod 2)[X] => p.eval 0) hf
        norm_num [he, hdim] at h
      intro he
      apply hnonzero
      have hmul : (f + 1) * (f ^ 2 + f + 1) = f ^ 3 + 1 := by
        calc
          _ = (f ^ 3 + 1) + (f ^ 2 + f) + (f ^ 2 + f) := by noncomm_ring
          _ = _ := by rw [add_assoc, ZModModule.add_self, add_zero]
      rw [he, mul_zero, hpow, one_smul, add_assoc, ZModModule.add_self, add_zero] at hmul
      exact hmul.symm
  obtain ⟨v, hvfix, hvsum⟩ := vector_outside_kernels (f - 1) (f ^ 2 + f + 1)
    (sub_ne_zero.mpr hne) hquad
  have hv : v ≠ 0 := by
    intro he
    exact hvfix (by rw [he, map_zero])
  apply cyclic_basis hdim f a v hv
  · exact sub_ne_zero.mp (show f v - v ≠ 0 from hvfix)
  · simpa [pow_succ, Module.End.mul_apply, add_comm, add_left_comm] using hvsum
  · exact hrec v

end D5.S1.Eigenstructure.BinaryCubicCompanion
