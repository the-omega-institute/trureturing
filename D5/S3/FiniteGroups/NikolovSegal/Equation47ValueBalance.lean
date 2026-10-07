/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueBalance
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueNormalization
import Mathlib.Data.List.Count

set_option autoImplicit false

/-! The actual matching pairs of VALUE variables in the normalized system
of Part I Proposition 9.1, printed p.224.  Constants (including all scalar
cycle parameters) and automorphism exponents do not count as variables. -/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u v

def signedVariables {S : Type u} [Group S] {V : Type v}
    (W : List (Letter V S)) : List (V × Bool) :=
  W.filterMap (fun l => match l with
    | .var x _ neg => some (x,neg)
    | .constant _ => none)

private theorem variables_append {S : Type u} [Group S] {V : Type v}
    (A B : List (Letter V S)) :
    signedVariables (A++B) = signedVariables A ++ signedVariables B := by
  simp [signedVariables]

private theorem variables_twist {S : Type u} [Group S] {V : Type v}
    (g : MulAut S) (W : List (Letter V S)) :
    signedVariables (twist g W) = signedVariables W := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    cases l with
    | var x g' neg =>
      change (x,neg) :: signedVariables (twist g W) = (x,neg) :: signedVariables W
      rw [ih]
    | constant s => exact ih

private theorem variables_inverse {S : Type u} [Group S] {V : Type v}
    (W : List (Letter V S)) :
    signedVariables (inverseWord W) =
      (signedVariables W).reverse.map (fun p => (p.1,!p.2)) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    rw [show inverseWord (l::W) = inverseWord W ++ [match l with
      | .var x g neg => .var x g (!neg)
      | .constant s => .constant s⁻¹] by
        simp only [inverseWord,List.reverse_cons,List.map_append,List.map_singleton]
        rfl]
    rw [variables_append,ih]
    cases l <;> simp [signedVariables,List.reverse_cons]

variable {S I : Type u} [Group S] [Finite I] [DecidableEq I] {m : ℕ}

private theorem variables_boundary (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (j : Fin m) (a : I) (n : ℕ) :
    signedVariables (boundaryWord tau alpha j a n) =
      ((List.range n).map (fun k => ((j,(tau j)^[k+1] a),false))).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [boundaryWord,variables_append,variables_twist,ih]
    simp only [signedVariables,List.filterMap_cons,List.filterMap_nil,
      List.range_succ,List.map_append,List.map_singleton,List.reverse_append,
      List.reverse_singleton,List.singleton_append]

/-- The actual nonbase coordinates of ONE actual permutation cycle,
in increasing cyclic order. -/
noncomputable def tailPoints (tau : Equiv.Perm I) (a : I) : List I :=
  (List.range (Function.minimalPeriod tau a-1)).map (fun n => tau^[n+1] a)

private theorem tailPoints_nodup (tau : Equiv.Perm I) (a : I) :
    (tailPoints tau a).Nodup := by
  rw [tailPoints,List.nodup_map_iff_inj_on List.nodup_range]
  intro n hn k hk heq
  simp only [List.mem_range] at hn hk
  have hh := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (by omega : n+1 < Function.minimalPeriod tau a)
    (by omega : k+1 < Function.minimalPeriod tau a)).mp heq
  omega

private theorem mem_tailPoints (tau : Equiv.Perm I) (a w : I) :
    w ∈ tailPoints tau a ↔ cycleClass tau w = cycleClass tau a ∧ w ≠ a := by
  constructor
  · rintro hw
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hw
    have hn' : n < Function.minimalPeriod tau a-1 := List.mem_range.mp hn
    constructor
    · apply Quotient.sound
      change tau.SameCycle (tau^[n+1] a) a
      simpa only [Equiv.Perm.coe_pow] using
        (Equiv.Perm.SameCycle.refl tau a).pow_left (n := n+1)
    · intro hh
      have hz := (show Function.IsPeriodicPt tau (n+1) a from hh).eq_zero_of_lt_minimalPeriod
        (by omega)
      omega
  · rintro ⟨hc,hwa⟩
    have hsame : tau.SameCycle a w := Quotient.exact hc.symm
    obtain ⟨n,hn⟩ := hsame.exists_nat_pow_eq
    have hn' : tau^[n] a = w := by simpa only [Equiv.Perm.coe_pow] using hn
    have hp : a ∈ Function.periodicPts tau := by
      apply Function.mk_mem_periodicPts (orderOf_pos tau)
      change tau^[orderOf tau] a = a
      rw [← Equiv.Perm.coe_pow,pow_orderOf_eq_one]
      rfl
    let e := Function.minimalPeriod tau a
    have he : 0 < e := Function.minimalPeriod_pos_of_mem_periodicPts hp
    let k := n % e
    have hk : k < e := Nat.mod_lt n he
    have hkw : tau^[k] a = w := by
      dsimp [k,e]
      rw [Function.iterate_mod_minimalPeriod_eq,hn']
    have hkpos : 0 < k := by
      by_contra h
      have hz : k = 0 := by omega
      rw [hz] at hkw
      exact hwa hkw.symm
    apply List.mem_map.mpr
    refine ⟨k-1,List.mem_range.mpr (by dsimp [e] at hk; omega),?_⟩
    simpa only [Nat.sub_add_cancel hkpos] using hkw

/-- The exact signed variable block after (50): a positive singleton at a
nonbase coordinate; the entire negative cyclic block at its base. -/
theorem normalizedFactorWord_variables (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (a : I) :
    signedVariables (normalizedFactorWord tau alpha u j a) =
      if a = base (tau j) a then
        (tailPoints (tau j) a).map (fun w => ((j,w),true))
      else [((j,a),false)] := by
  by_cases ha : a = base (tau j) a
  · rw [normalizedFactorWord,if_pos ha,baseValueWord]
    simp only [← ha,
      variables_append,variables_inverse,variables_twist,variables_boundary]
    simp only [signedVariables,List.filterMap_cons,List.filterMap_nil,
      List.reverse_reverse,List.map_map,List.nil_append,tailPoints]
    rfl
  · simp [normalizedFactorWord,ha,signedVariables]

private theorem factor_variables_nodup (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (a : I) :
    (signedVariables (normalizedFactorWord tau alpha u j a)).Nodup := by
  rw [normalizedFactorWord_variables]
  split
  · apply (tailPoints_nodup _ _).map
    intro v w h
    exact congrArg (fun p => p.1.2) h
  · simp

private theorem factor_variable_mem (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (a : I)
    (e : Arc m I) (neg : Bool) :
    (e,neg) ∈ signedVariables (normalizedFactorWord tau alpha u j a) ↔
      j = e.1 ∧ e.2 ≠ base (tau e.1) e.2 ∧
        a = (if neg then base (tau e.1) e.2 else e.2) := by
  rw [normalizedFactorWord_variables]
  by_cases ha : a = base (tau j) a
  · rw [if_pos ha]
    simp only [List.mem_map]
    constructor
    · rintro ⟨w,hw,hwe⟩
      have hj : j = e.1 := congrArg (fun p => p.1.1) hwe
      have hwv : w = e.2 := congrArg (fun p => p.1.2) hwe
      have hneg : true = neg := congrArg Prod.snd hwe
      rw [hwv] at hw
      obtain ⟨hc,hne⟩ := (mem_tailPoints _ _ _).mp hw
      have hb : base (tau j) e.2 = a := by
        unfold base
        rw [hc]
        exact ha.symm
      refine ⟨hj,?_,?_⟩ <;> rw [← hj]
      · simpa only [hb] using hne
      · rw [← hneg,if_pos rfl,hb]
    · rintro ⟨hj,he,hae⟩
      rw [← hj] at he hae
      cases neg
      · simp only [Bool.false_eq_true,↓reduceIte] at hae
        exact False.elim (he (hae.symm.trans (ha.trans
          (congrArg (base (tau j)) hae)) ))
      · simp only [↓reduceIte] at hae
        refine ⟨e.2,(mem_tailPoints _ _ _).mpr ⟨?_,?_⟩,?_⟩
        · rw [hae]
          exact (Quotient.out_eq (cycleClass (tau j) e.2)).symm
        · simpa only [hae] using he
        · exact Prod.ext (Prod.ext hj rfl) rfl
  · rw [if_neg ha]
    simp only [List.mem_singleton]
    constructor
    · intro h
      have hj : e.1 = j := congrArg (fun p => p.1.1) h
      have hw : e.2 = a := congrArg (fun p => p.1.2) h
      have hn : neg = false := congrArg Prod.snd h
      exact ⟨hj.symm,by simpa only [hj,hw] using ha,by simp [hn,hw]⟩
    · rintro ⟨hj,he,hae⟩
      rw [← hj] at he hae
      cases neg
      · simp only [Bool.false_eq_true,↓reduceIte] at hae
        exact Prod.ext (Prod.ext hj.symm hae.symm) rfl
      · simp only [↓reduceIte] at hae
        have hb : base (tau j) (base (tau j) e.2) = base (tau j) e.2 := by
          change (cycleClass (tau j) (base (tau j) e.2)).out = _
          rw [show cycleClass (tau j) (base (tau j) e.2) = cycleClass (tau j) e.2
            from Quotient.out_eq _]
          rfl
        exact False.elim (ha (by rw [hae,hb]))

private theorem factor_variable_count (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (a : I)
    (e : Arc m I) (neg : Bool) :
    (signedVariables (normalizedFactorWord tau alpha u j a)).count (e,neg) =
      if j = e.1 ∧ e.2 ≠ base (tau e.1) e.2 ∧
        a = (if neg then base (tau e.1) e.2 else e.2) then 1 else 0 := by
  by_cases h : j = e.1 ∧ e.2 ≠ base (tau e.1) e.2 ∧
    a = (if neg then base (tau e.1) e.2 else e.2)
  · rw [if_pos h]
    exact List.count_eq_one_of_mem (factor_variables_nodup tau alpha u j a)
      ((factor_variable_mem tau alpha u j a e neg).mpr h)
  · rw [if_neg h]
    exact List.count_eq_zero.mpr (fun he => h
      ((factor_variable_mem tau alpha u j a e neg).mp he))

/-- A nonbase VALUE variable occurs positively exactly at its actual
coordinate and negatively exactly at its actual cycle base.  Base variables
do not occur.  This derives the genuine star links used in Proposition 9.1. -/
theorem normalizedVertexWord_variable_count (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (a : I)
    (e : Arc m I) (neg : Bool) :
    (signedVariables (normalizedVertexWord tau alpha u a)).count (e,neg) =
      if e.2 ≠ base (tau e.1) e.2 ∧
        a = (if neg then base (tau e.1) e.2 else e.2) then 1 else 0 := by
  simp only [normalizedVertexWord,signedVariables,List.filterMap_flatten,
    List.map_ofFn,List.count_flatten]
  change (List.ofFn (fun j =>
    (signedVariables (normalizedFactorWord tau alpha u j a)).count (e,neg))).sum = _
  simp only [factor_variable_count,List.sum_ofFn]
  simp [Finset.sum_ite_irrel,ite_and]

/-- Exactly one positive AND one negative occurrence per true nonbase VALUE
variable across the normalized equations.  Their total number is the accepted
mn - sum c(tau_j) count, before the n-1 linked substitutions. -/
theorem normalized_system_balance [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (e : Arc m I) (neg : Bool) :
    (∑ a : I, (signedVariables (normalizedVertexWord tau alpha u a)).count (e,neg)) =
      if e.2 ≠ base (tau e.1) e.2 then 1 else 0 := by
  simp only [normalizedVertexWord_variable_count]
  simp [ite_and,Finset.sum_ite_irrel]

end NikolovSegal.Equation47ValueNormalization
