/- GID: D5/S1/Eigenstructure/BinaryCubicRepeatedRoot
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/BinaryCubicRepeatedRoot
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The two binary cubic normal forms with characteristic polynomial X cubed plus X. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! The repeated-root cubic has a zero line and a two-dimensional primary space at one. -/

namespace D5.S1.Eigenstructure.BinaryCubicRepeatedRoot

open Module Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "F₂" => ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]

private theorem finrank_ker_eq_one (f : Module.End F₂ V) (hf : f.charpoly = X ^ 3 + X) :
    finrank F₂ f.ker = 1 := by
  have hq : (X ^ 2 + 1 : F₂[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : F₂[X] => p.eval 0) h
    simp at h0
  have hroot : rootMultiplicity 0 f.charpoly = 1 := by
    rw [hf, show (X ^ 3 + X : F₂[X]) = X * (X ^ 2 + 1) by ring,
      rootMultiplicity_mul (mul_ne_zero X_ne_zero hq),
      rootMultiplicity_eq_zero (p := X ^ 2 + 1) (x := (0 : F₂)) (by simp [IsRoot]), add_zero]
    simpa using (rootMultiplicity_X_sub_C_self (x := (0 : F₂)))
  have hspace : f.eigenspace 0 = f.ker := by
    ext x
    simp [LinearMap.mem_ker]
  have hle := LinearMap.finrank_eigenspace_le f 0
  rw [hspace, hroot] at hle
  have hev : f.HasEigenvalue 0 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f 0).mpr (by simp [hf, IsRoot])
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hvker : v ∈ f.ker :=
    LinearMap.mem_ker.mpr (by simpa using hv.apply_eq_smul)
  have hn : Nontrivial f.ker :=
    ⟨⟨⟨v, hvker⟩, 0, fun h => hv.2 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < finrank F₂ f.ker := (Module.finrank_pos_iff_of_free F₂ f.ker).mpr hn
  omega

omit [FiniteDimensional F₂ V] in
private theorem involution_basis (f : Module.End F₂ V) (hdim : finrank F₂ V = 2)
    (hsq : f ^ 2 = 1) (hne : f ≠ 1) :
    ∃ b : Basis (Fin 2) F₂ V, f (b 0) = b 0 ∧ f (b 1) = b 0 + b 1 := by
  let n : Module.End F₂ V := f - 1
  have hnz : n ≠ 0 := sub_ne_zero.mpr hne
  have hnil : n ^ 2 = 0 := by
    calc
      n ^ 2 = f ^ 2 + 1 - (f + f) := by dsimp [n]; noncomm_ring
      _ = 0 := by rw [hsq, ZModModule.add_self, ZModModule.add_self, sub_zero]
  obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
    by_contra! H
    exact hnz (LinearMap.ext H)
  have hnv : n (n v) = 0 := by
    simpa [pow_two, Module.End.mul_apply] using congrFun (congrArg DFunLike.coe hnil) v
  have hli : LinearIndependent F₂ ![n v, v] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have he : a 0 • n v + a 1 • v = 0 := by simpa [Fin.sum_univ_two] using ha
    have h1 : a 1 = 0 := by
      have hh : a 1 • n v = 0 := by
        simpa [hnv] using congrArg n he
      exact (smul_eq_zero.mp hh).resolve_right hv
    have h0 : a 0 = 0 := by
      rw [h1, zero_smul, add_zero] at he
      exact (smul_eq_zero.mp he).resolve_right hv
    fin_cases j <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hnv' : f (n v) = n v :=
    sub_eq_zero.mp (show f (n v) - n v = 0 from hnv)
  have hv' : f v = n v + v := by
    change f v = f v - v + v
    abel
  exact ⟨b, by simpa [b] using hnv', by simpa [b] using hv'⟩

/-- A binary endomorphism with characteristic polynomial X cubed plus X
has a two-dimensional block at one and a zero line. Idempotence
distinguishes the scalar block from the length-two block. -/
theorem exists_basis (f : Module.End F₂ V) (hdim : finrank F₂ V = 3)
    (hf : f.charpoly = X ^ 3 + X) :
    ∃ b : Basis (Fin 3) F₂ V, f (b 0) = b 0 ∧ f (b 2) = 0 ∧
      ((f ^ 2 = f ∧ f (b 1) = b 1) ∨ (f ^ 2 ≠ f ∧ f (b 1) = b 0 + b 1)) := by
  have hch := LinearMap.aeval_self_charpoly f
  rw [hf] at hch
  have hcube : f ^ 3 = f := by
    apply (add_eq_zero_iff_eq_neg.mp ?_).trans (ZModModule.neg_eq_self f)
    simpa [aeval_add, aeval_X_pow] using hch
  have hproj : IsIdempotentElem (f ^ 2) := by
    calc
      f ^ 2 * f ^ 2 = f ^ 3 * f := by noncomm_ring
      _ = f ^ 2 := by rw [hcube, pow_two]
  have hker : LinearMap.ker (f ^ 2) = f.ker := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      calc
        f x = (f ^ 3) x := by rw [hcube]
        _ = f ((f ^ 2) x) := by
          rw [show f ^ 3 = f * f ^ 2 by noncomm_ring, Module.End.mul_apply]
        _ = 0 := by simp [hx]
    · intro hx
      simp [pow_two, Module.End.mul_apply, hx]
  let Q := LinearMap.range (f ^ 2)
  have hcompl : IsCompl Q f.ker := by
    simpa [Q, hker] using LinearMap.IsIdempotentElem.isCompl hproj
  have hkdim := finrank_ker_eq_one f hf
  have hqdim : finrank F₂ Q = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker (f ^ 2)
    rw [hker, hkdim, hdim] at h
    exact Nat.add_right_cancel h
  have hpres (x : V) (hx : x ∈ Q) : f x ∈ Q := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨f y, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    rw [show f ^ 2 * f = f * f ^ 2 by noncomm_ring]
  let g : Module.End F₂ Q := f.restrict hpres
  have hsq : g ^ 2 = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change f (f x.val) = x.val
    simpa [pow_two, Module.End.mul_apply] using
      (LinearMap.IsIdempotentElem.mem_range_iff hproj).mp x.property
  have hiff : f ^ 2 = f ↔ g = 1 := by
    constructor
    · intro he
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change f x.val = x.val
      have hh := (LinearMap.IsIdempotentElem.mem_range_iff hproj).mp x.property
      rwa [he] at hh
    · intro he
      apply LinearMap.ext
      intro x
      let y : Q := ⟨f x, f x, by
        have hh := congrFun (congrArg DFunLike.coe hcube) x
        simpa [pow_succ, Module.End.mul_apply] using hh⟩
      have hy : g y = y := by rw [he]; rfl
      have hy' := congrArg (fun z : Q => z.val) hy
      change f (f x) = f x at hy' ⊢
      exact hy'
  have hQ : ∃ b : Basis (Fin 2) F₂ Q, g (b 0) = b 0 ∧
      ((f ^ 2 = f ∧ g (b 1) = b 1) ∨ (f ^ 2 ≠ f ∧ g (b 1) = b 0 + b 1)) := by
    by_cases he : f ^ 2 = f
    · let b := Module.finBasisOfFinrankEq F₂ Q hqdim
      have hg := hiff.mp he
      exact ⟨b, by rw [hg]; rfl, Or.inl ⟨he, by rw [hg]; rfl⟩⟩
    · obtain ⟨b, h0, h1⟩ := involution_basis g hqdim hsq (fun hg => he (hiff.mpr hg))
      exact ⟨b, h0, Or.inr ⟨he, h1⟩⟩
  obtain ⟨q, hq0, hq1⟩ := hQ
  let k := Module.finBasisOfFinrankEq F₂ f.ker hkdim
  let b : Basis (Fin 3) F₂ V :=
    ((q.prod k).map (Q.prodEquivOfIsCompl f.ker hcompl)).reindex finSumFinEquiv
  have hs0 : (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 0 = Sum.inl 0 := rfl
  have hs1 : (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 1 = Sum.inl 1 := rfl
  have hs2 : (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 2 = Sum.inr 0 := rfl
  have hb0 : b 0 = (q 0 : V) := by simp [b, hs0]
  have hb1 : b 1 = (q 1 : V) := by simp [b, hs1]
  have hb2 : b 2 = (k 0 : V) := by simp [b, hs2]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb0]
    exact congrArg Subtype.val hq0
  · rw [hb2]
    exact (k 0).property
  · rcases hq1 with ⟨he, h⟩ | ⟨he, h⟩
    · exact Or.inl ⟨he, by rw [hb1]; exact congrArg Subtype.val h⟩
    · exact Or.inr ⟨he, by rw [hb0, hb1]; exact congrArg Subtype.val h⟩

end D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
