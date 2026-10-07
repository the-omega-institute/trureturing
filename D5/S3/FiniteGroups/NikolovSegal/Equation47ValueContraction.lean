/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueContraction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueLinks
import Mathlib.Tactic.Group

set_option autoImplicit false

/-! Actual automorphism-bearing linked substitution (l -> 1), Part I p.225.
This operates on the normalized VALUE words, not on commutator witnesses.
All other coordinate equations and all unused variables are retained. -/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u v

variable {S : Type u} [Group S] {V : Type v} [DecidableEq V] [BEq V] [LawfulBEq V]

/-- Literal replacement of ONE variable, retaining every automorphism and
sign at its actual occurrence. -/
def replaceValueVariable (W : List (Letter V S)) (x : V)
    (R : List (Letter V S)) : List (Letter V S) :=
  W.flatMap (fun l => match l with
    | .var y g neg => if y = x then
        if neg then inverseWord (twist g R) else twist g R
      else [l]
    | .constant _ => [l])

private theorem variable_value (z : V → S) (x : V) (g : MulAut S) (neg : Bool) :
    wordValue [.var x g neg] z = if neg then (g (z x))⁻¹ else g (z x) :=
  value_var z x g neg

theorem replaceValueVariable_value (W : List (Letter V S)) (x : V)
    (R : List (Letter V S)) (z : V → S) :
    wordValue (replaceValueVariable W x R) z =
      wordValue W (Function.update z x (wordValue R z)) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    rw [show replaceValueVariable (l::W) x R =
        (match l with
          | .var y g neg => if y = x then
              if neg then inverseWord (twist g R) else twist g R
            else [l]
          | .constant _ => [l]) ++ replaceValueVariable W x R from rfl,
      value_append,ih]
    cases l with
    | constant s =>
      rw [show .constant s::W = [.constant s]++W from rfl,value_append]
      simp only [value_constant]
    | var y g neg =>
      rw [show wordValue (.var y g neg :: W)
          (Function.update z x (wordValue R z)) =
        wordValue [.var y g neg] (Function.update z x (wordValue R z)) *
          wordValue W (Function.update z x (wordValue R z)) by
            rw [show .var y g neg :: W = [.var y g neg] ++ W from rfl,value_append]]
      congr 1
      by_cases h : y = x
      · subst y
        simp only [if_pos rfl,variable_value,Function.update_self]
        cases neg <;> simp [value_inverse,value_twist]
      · simp only [if_neg h,variable_value,Function.update_of_ne h]

private theorem value_avoids_update (W : List (Letter V S)) (x : V)
    (h : avoids W x) (z : V → S) (s : S) :
    wordValue W (Function.update z x s) = wordValue W z := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    have ht : avoids W x := fun g neg hn => h g neg (by simp [hn])
    rw [show l::W = [l]++W from rfl,value_append,value_append,ih ht]
    congr 1
    cases l with
    | constant s => rfl
    | var y g neg =>
      have hy : y ≠ x := by
        intro hh
        subst y
        exact h g neg (by simp)
      simp [Function.update_of_ne hy]

private def keyList (W : List (Letter V S)) : List V :=
  (signedVariables W).map Prod.fst

private theorem key_count (W : List (Letter V S)) (x : V) :
    (keyList W).count x = (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) := by
  have h : ∀ L : List (V × Bool), (L.map Prod.fst).count x =
      L.count (x,false) + L.count (x,true) := by
    intro L
    induction L with
    | nil => simp
    | cons p L ih =>
      rcases p with ⟨y,neg⟩
      cases neg <;> by_cases heq : y = x
      all_goals simp [heq,ih] <;> omega
  exact h _

private theorem variable_in_keys (W : List (Letter V S)) (x : V)
    (g : MulAut S) (neg : Bool) (h : .var x g neg ∈ W) : x ∈ keyList W := by
  apply List.mem_map.mpr
  refine ⟨(x,neg),?_,rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨.var x g neg,h,rfl⟩

private theorem split_unique_variable (W : List (Letter V S)) (x : V) (neg : Bool)
    (hcount : (signedVariables W).count (x,neg) = 1)
    (hother : (signedVariables W).count (x,!neg) = 0) :
    ∃ (g : MulAut S) (C D : List (Letter V S)),
      W = C ++ [.var x g neg] ++ D ∧ avoids C x ∧ avoids D x := by
  have hmem : (x,neg) ∈ signedVariables W := List.count_pos_iff.mp (by omega)
  obtain ⟨l,hl,hvar⟩ := List.mem_filterMap.mp hmem
  cases l with
  | constant s => simp [signedVariables] at hvar
  | var y g sign =>
    have hh : (y,sign) = (x,neg) := Option.some.inj hvar
    have hy : y = x := congrArg Prod.fst hh
    have hs : sign = neg := congrArg Prod.snd hh
    subst y
    subst sign
    obtain ⟨C,D,hW⟩ := List.mem_iff_append.mp hl
    have hW' : W = C ++ [.var x g neg] ++ D := by
      simpa only [List.singleton_append,List.append_assoc] using hW
    have hkeys : (keyList W).count x = 1 := by
      rw [key_count]
      cases neg <;> simp_all
    rw [hW'] at hkeys
    have hc : (keyList C).count x = 0 ∧ (keyList D).count x = 0 := by
      simp only [keyList,signedVariables,List.filterMap_append,List.map_append,
        List.filterMap_cons,List.filterMap_nil,List.map_cons,List.map_nil,
        List.count_append,List.count_singleton_self] at hkeys
      change (keyList C).count x + 1 + (keyList D).count x = 1 at hkeys
      omega
    refine ⟨g,C,D,?_,?_,?_⟩
    · exact hW'
    · intro g neg h
      exact (List.count_eq_zero.mp hc.1) (variable_in_keys C x g neg h)
    · intro g neg h
      exact (List.count_eq_zero.mp hc.2) (variable_in_keys D x g neg h)

/-- Solve the linked equation with its genuine occurrence automorphism.
Both signs lead to the printed ordered DC splice in the OTHER equation. -/
def valueSolutionWord (g : MulAut S) (neg : Bool)
    (C D : List (Letter V S)) (target : S) : List (Letter V S) :=
  twist g.symm (if neg then D ++ [.constant target⁻¹] ++ C
    else inverseWord C ++ [.constant target] ++ inverseWord D)

private theorem solution_solves (x : V) (g : MulAut S) (neg : Bool)
    (C D : List (Letter V S)) (hC : avoids C x) (hD : avoids D x)
    (target : S) (z : V → S) :
    wordValue (C ++ [.var x g neg] ++ D)
      (Function.update z x (wordValue (valueSolutionWord g neg C D target) z)) = target := by
  simp only [value_append,value_avoids_update C x hC,value_avoids_update D x hD,
    value_var,Function.update_self,valueSolutionWord,value_twist]
  cases neg <;>
    simp only [Bool.false_eq_true,↓reduceIte,value_append,value_constant,
      value_inverse,map_mul,map_inv,MulEquiv.apply_symm_apply] <;> group

private theorem solution_unique (x : V) (g : MulAut S) (neg : Bool)
    (C D : List (Letter V S)) (target : S) (z : V → S)
    (hz : wordValue (C ++ [.var x g neg] ++ D) z = target) :
    wordValue (valueSolutionWord g neg C D target) z = z x := by
  rw [value_append,value_append,value_var] at hz
  simp only [valueSolutionWord,value_twist]
  cases neg <;>
    simp only [Bool.false_eq_true,↓reduceIte] at hz ⊢ <;>
    simp only [value_append,value_constant,value_inverse] <;>
    rw [← hz] <;>
    simp only [map_mul,map_inv,MulEquiv.symm_apply_apply] <;> group

variable {I : Type u} [Finite I] [DecidableEq I] {m : ℕ}

/-- A genuine normalized cycle-star link supplies the actual leaf
substitution, without assuming decompositions or solvability.  The leaf
equation is removed, all other equations are replaced literally, and every
unused variable assignment is retained.  The equivalence is for arbitrary
target constants and the same fixed scalar cycle parameters. -/
theorem actual_value_link_contraction
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (a : I)
    (ha : a ≠ base (tau j) a) (leaf : I)
    (hleaf : leaf = a ∨ leaf = base (tau j) a) (kappa : I → S) :
    ∃ R : List (Letter (Arc m I) S),
      ∀ z : Arc m I → S,
        (∀ e, e ≠ (j,a) →
          Function.update z (j,a) (wordValue R z) e = z e) ∧
        wordValue (normalizedVertexWord tau alpha u leaf)
          (Function.update z (j,a) (wordValue R z)) = kappa leaf ∧
        (∀ v, wordValue
          (replaceValueVariable (normalizedVertexWord tau alpha u v) (j,a) R) z =
          wordValue (normalizedVertexWord tau alpha u v)
            (Function.update z (j,a) (wordValue R z))) ∧
        ((∃ c : Arc m I → S,
          (∀ e, e ≠ (j,a) → c e = z e) ∧
          ∀ v, wordValue (normalizedVertexWord tau alpha u v) c = kappa v) ↔
          ∀ v, v ≠ leaf → wordValue
            (replaceValueVariable (normalizedVertexWord tau alpha u v) (j,a) R) z =
              kappa v) := by
  let neg : Bool := decide (leaf ≠ a)
  have hleafneg : leaf = (if neg then base (tau j) a else a) := by
    rcases hleaf with h | h
    · simp [neg,h]
    · simp [neg,h,Ne.symm ha]
  have hleafother : leaf ≠ (if !neg then base (tau j) a else a) := by
    rcases hleaf with h | h
    · simp [neg,h,ha]
    · simp [neg,h,Ne.symm ha]
  have hc : (signedVariables (normalizedVertexWord tau alpha u leaf)).count
      ((j,a),neg) = 1 := by
    rw [normalizedVertexWord_variable_count]
    simp [ha,hleafneg]
  have ho : (signedVariables (normalizedVertexWord tau alpha u leaf)).count
      ((j,a),!neg) = 0 := by
    rw [normalizedVertexWord_variable_count]
    exact if_neg (fun h => hleafother h.2)
  obtain ⟨g,C,D,hW,hC,hD⟩ := split_unique_variable _ (j,a) neg hc ho
  let R := valueSolutionWord g neg C D (kappa leaf)
  refine ⟨R,?_⟩
  intro z
  refine ⟨fun e he => Function.update_of_ne he _ _,?_,
    fun v => replaceValueVariable_value _ _ _ _,?_⟩
  · rw [hW]
    exact solution_solves (j,a) g neg C D hC hD _ z
  constructor
  · rintro ⟨c,hcz,hc⟩ v hv
    rw [replaceValueVariable_value]
    have hzleaf : wordValue (C ++ [.var (j,a) g neg] ++ D) c = kappa leaf := by
      rw [← hW]
      exact hc leaf
    have hRc : wordValue R c = c (j,a) := solution_unique _ _ _ _ _ _ _ hzleaf
    have hR : wordValue R z = wordValue R c := by
      have hupdate : Function.update z (j,a) (c (j,a)) = c := by
        funext e
        by_cases he : e = (j,a)
        · subst e
          simp
        · rw [Function.update_of_ne he,hcz e he]
      have hCz := value_avoids_update C (j,a) hC z (c (j,a))
      have hDz := value_avoids_update D (j,a) hD z (c (j,a))
      rw [hupdate] at hCz hDz
      dsimp [R,valueSolutionWord]
      cases neg <;> simp only [Bool.false_eq_true,↓reduceIte,
        value_twist,value_append,value_constant,value_inverse,hCz,hDz]
    rw [hR,hRc]
    have heq : Function.update z (j,a) (c (j,a)) = c := by
      funext e
      by_cases he : e = (j,a)
      · subst e
        simp
      · rw [Function.update_of_ne he,hcz e he]
    rw [heq]
    exact hc v
  · intro hz
    refine ⟨Function.update z (j,a) (wordValue R z),
      fun e he => Function.update_of_ne he _ _,?_⟩
    intro v
    by_cases hv : v = leaf
    · subst v
      rw [hW]
      exact solution_solves (j,a) g neg C D hC hD _ z
    · rw [← replaceValueVariable_value]
      exact hz v hv

/-- Consume the constructed link substitution on the unchanged actual
corrected q-powered commutator equations.  The right side contains the
literal remaining equations, not an off-representative coverage predicate.
No scalar theorem is used for this reversible elimination step. -/
theorem corrected_normalized_link_reconstruction [Fintype I] {q : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (u : ∀ j, ActualCycle (sigma j ^ q) → S)
    (j : Fin m) (a : I) (ha : a ≠ base (sigma j ^ q) a)
    (leaf : I) (hleaf : leaf = a ∨ leaf = base (sigma j ^ q) a) :
    ∀ kappa : I → S, ∃ R : List (Letter (Arc m I) S),
      (∃ c : Fin m → I → S,
        (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
        ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v) ↔
      (∃ z : Arc m I → S, ∀ v, v ≠ leaf → wordValue
        (replaceValueVariable (normalizedVertexWord (fun j => sigma j ^ q)
          (fun j i => correctedCycleComponent beta sigma y j i q) u v) (j,a) R) z =
            kappa v) := by
  intro kappa
  obtain ⟨R,hR⟩ := actual_value_link_contraction (fun j => sigma j ^ q)
    (fun j i => correctedCycleComponent beta sigma y j i q) u j a ha leaf hleaf kappa
  refine ⟨R,?_⟩
  rw [← corrected_normalized_system_iff k sigma beta hcoord y u kappa]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,(hR z).2.2.2.mp ⟨z,fun _ _ => rfl,hz⟩⟩
  · rintro ⟨z,hz⟩
    obtain ⟨c,hcz,hc⟩ := (hR z).2.2.2.mpr hz
    exact ⟨c,hc⟩

/-- These are precisely the keys with a matching pair in the proved
normalized system, by normalized_system_balance. -/
abbrev FreeValueVariable (tau : Fin m → Equiv.Perm I) :=
  {e : Arc m I // e.2 ≠ base (tau e.1) e.2}

private theorem free_value_card [Fintype I] (tau : Fin m → Equiv.Perm I) :
    Nat.card (FreeValueVariable tau) =
      ∑ j : Fin m, Nat.card (NonbaseValueCoordinate (tau j)) := by
  let f : FreeValueVariable tau ≃ (j : Fin m) × NonbaseValueCoordinate (tau j) :=
    { toFun := fun e => ⟨e.val.1,⟨e.val.2,e.prop⟩⟩
      invFun := fun e => ⟨(e.1,e.2.val),e.2.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f,Nat.card_sigma]

/-- The budget now counts the actual signed variable support of the literal
normalized system, not the witness keys of actualResidualWord. -/
theorem normalized_actual_variable_card [Fintype I]
    (tau : Fin m → Equiv.Perm I) :
    Nat.card (FreeValueVariable tau) +
      (∑ j : Fin m, actualCycleCount (tau j)) = m * Fintype.card I := by
  rw [free_value_card]
  exact cycle_value_free_coordinate_count tau

/-- The literal normalized VALUE system has enough initial matching pairs
for the paper's n-1 links and D extractions.  Construction and colour control
of the whole contraction/extraction sequence remain separate obligations. -/
theorem normalized_typeII_initial_pair_budget [Fintype I] {D : ℕ}
    (tau : Fin m → Equiv.Perm I) (hn : 2 ≤ Fintype.card I)
    (htype : (4+2*D) * Fintype.card I ≤
      ∑ j : Fin m, (Fintype.card I - actualFixedCount (tau j))) :
    Fintype.card I + 2*D + 1 + (Fintype.card I - 1) ≤
      Nat.card (FreeValueVariable tau) := by
  rw [free_value_card]
  have h := typeII_free_coordinate_budget tau hn htype
  omega

end NikolovSegal.Equation47ValueNormalization
