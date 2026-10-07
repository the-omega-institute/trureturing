/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueElimination
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized value elimination, balance and component colour bounds. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueForest
import D5.S3.FiniteGroups.NikolovSegal.Equation47Colours
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Part I p.225: literal repeated linked substitutions in the normalized
VALUE system.  The recursive extension runs backwards through the displayed
substitutions, so every automorphism and every noncommutative factor order is
retained.  Scalar cycle parameters and the global correction are fixed inputs.
-/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u v
variable {S : Type u} [Group S] {V : Type v}
  [DecidableEq V] [BEq V] [LawfulBEq V]

@[simp] theorem variables_append (A B : List (Letter V S)) :
    signedVariables (A++B) = signedVariables A ++ signedVariables B := by
  simp only [signedVariables,List.filterMap_append]

@[simp] theorem variables_var (x : V) (g : MulAut S) (s : Bool)
    (W : List (Letter V S)) :
    signedVariables (.var x g s :: W) = (x,s)::signedVariables W := rfl

@[simp] private theorem variables_constant (a : S) (W : List (Letter V S)) :
    signedVariables (.constant a :: W) = signedVariables W := rfl

@[simp] theorem variables_nil : signedVariables ([] : List (Letter V S)) = [] := rfl

theorem count_twist (g : MulAut S) (W : List (Letter V S))
    (x : V) (s : Bool) :
    (signedVariables (twist g W)).count (x,s) = (signedVariables W).count (x,s) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    cases l with
    | var y h neg =>
      change ((y,neg)::signedVariables (twist g W)).count (x,s) =
        ((y,neg)::signedVariables W).count (x,s)
      simp only [List.count_cons,ih]
    | constant a => exact ih

theorem count_inverse (W : List (Letter V S)) (x : V) (s : Bool) :
    (signedVariables (inverseWord W)).count (x,s) =
      (signedVariables W).count (x,!s) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    rw [show inverseWord (l::W) = inverseWord W ++ [match l with
      | .var y g neg => .var y g (!neg)
      | .constant a => .constant a⁻¹] by
        simp only [inverseWord,List.reverse_cons,List.map_append,List.map_singleton]
        rfl, variables_append,List.count_append,ih]
    cases l with
    | constant a => simp only [variables_constant,variables_nil,List.count_nil,Nat.add_zero]
    | var y g neg =>
      cases neg <;> cases s <;> by_cases hy : y = x <;>
        simp [hy,Nat.add_comm]

theorem avoids_of_counts (W : List (Letter V S)) (x : V)
    (h : ∀ s, (signedVariables W).count (x,s) = 0) : avoids W x := by
  intro g s hs
  have hm : (x,s) ∈ signedVariables W :=
    List.mem_filterMap.mpr ⟨.var x g s,hs,rfl⟩
  exact (List.count_eq_zero.mp (h s)) hm

theorem counts_of_avoids (W : List (Letter V S)) (x : V)
    (h : avoids W x) (s : Bool) : (signedVariables W).count (x,s) = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  obtain ⟨l,hl,he⟩ := List.mem_filterMap.mp hm
  cases l with
  | constant a => simp at he
  | var y g neg =>
    have hh : (y,neg) = (x,s) := Option.some.inj he
    have hy : y = x := congrArg Prod.fst hh
    subst y
    exact h g neg hl

private theorem avoids_update (W : List (Letter V S)) (x : V)
    (h : avoids W x) (z : V → S) (a : S) :
    wordValue W (Function.update z x a) = wordValue W z := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    have ht : avoids W x := fun g s hn => h g s (by simp [hn])
    rw [show l::W = [l]++W from rfl,value_append,value_append,ih ht]
    congr 1
    cases l with
    | constant b => rfl
    | var y g s =>
      have hy : y ≠ x := by
        intro he; subst y; exact h g s (by simp)
      simp [Function.update_of_ne hy]

structure Cut (V : Type v) (S : Type u) [Group S] where
  aut : MulAut S
  negative : Bool
  before : List (Letter V S)
  after : List (Letter V S)

private def ValidCut (W : List (Letter V S)) (x : V) (c : Cut V S) : Prop :=
  W = c.before ++ [.var x c.aut c.negative] ++ c.after ∧
    avoids c.before x ∧ avoids c.after x

private theorem exists_cut (W : List (Letter V S)) (x : V)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) : ∃ c : Cut V S, ValidCut W x c := by
  let keys := (signedVariables W).map Prod.fst
  have hkeys : keys.count x = 1 := by
    have hh : ∀ L : List (V × Bool), (L.map Prod.fst).count x =
        L.count (x,false) + L.count (x,true) := by
      intro L
      induction L with
      | nil => simp
      | cons p L ih =>
        rcases p with ⟨y,s⟩
        cases s <;> by_cases hy : y = x <;> simp [hy,ih] <;> omega
    exact (hh _).trans hc
  have hm : x ∈ keys := List.count_pos_iff.mp (by omega)
  obtain ⟨p,hp,hpx⟩ := List.mem_map.mp hm
  obtain ⟨l,hl,he⟩ := List.mem_filterMap.mp hp
  cases l with
  | constant a => simp at he
  | var y g s =>
    have hy : y = x := by
      have hh : (y,s) = p := Option.some.inj he
      exact (congrArg Prod.fst hh).trans hpx
    subst y
    obtain ⟨C,D,hW⟩ := List.mem_iff_append.mp hl
    have hW' : W = C ++ [.var x g s] ++ D := by
      simpa only [List.singleton_append,List.append_assoc] using hW
    have hzero : (signedVariables C).count (x,false) +
        (signedVariables C).count (x,true) = 0 ∧
        (signedVariables D).count (x,false) +
        (signedVariables D).count (x,true) = 0 := by
      rw [hW'] at hc
      cases s <;> simp at hc <;> omega
    refine ⟨⟨g,s,C,D⟩,hW',?_,?_⟩
    · change avoids C x
      apply avoids_of_counts
      intro s; cases s <;> omega
    · change avoids D x
      apply avoids_of_counts
      intro s; cases s <;> omega

noncomputable def cut (W : List (Letter V S)) (x : V) : Cut V S := by
  classical
  exact if h : ∃ c : Cut V S, ValidCut W x c then Classical.choose h
    else ⟨1,false,[],[]⟩

theorem cut_spec (W : List (Letter V S)) (x : V)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) : ValidCut W x (cut W x) := by
  have h := exists_cut W x hc
  simp only [cut,dif_pos h]
  exact Classical.choose_spec h

noncomputable def linkSolution (W : List (Letter V S)) (x : V)
    (t : S) : List (Letter V S) :=
  valueSolutionWord (cut W x).aut (cut W x).negative
    (cut W x).before (cut W x).after t

private theorem link_solves (W : List (Letter V S)) (x : V) (t : S)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) (z : V → S) :
    wordValue W (Function.update z x (wordValue (linkSolution W x t) z)) = t := by
  obtain ⟨hW,hC,hD⟩ := cut_spec W x hc
  unfold linkSolution
  generalize hcut : cut W x = c at hW hC hD ⊢
  rcases c with ⟨g,neg,C,D⟩
  change W = C ++ [.var x g neg] ++ D at hW
  change avoids C x at hC
  change avoids D x at hD
  rw [hW]
  simp only [value_append,avoids_update _ x hC,avoids_update _ x hD,
    value_var,Function.update_self,valueSolutionWord,value_twist]
  cases neg <;>
    simp only [Bool.false_eq_true,↓reduceIte,value_append,value_constant,
      value_inverse,map_mul,map_inv,MulEquiv.apply_symm_apply] <;> group

private theorem link_unique (W : List (Letter V S)) (x : V) (t : S)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) (z : V → S)
    (hz : wordValue W z = t) : wordValue (linkSolution W x t) z = z x := by
  obtain ⟨hW,hC,hD⟩ := cut_spec W x hc
  unfold linkSolution
  generalize hcut : cut W x = c at hW hC hD ⊢
  rcases c with ⟨g,neg,C,D⟩
  change W = C ++ [.var x g neg] ++ D at hW
  rw [hW,value_append,value_append,value_var] at hz
  simp only [valueSolutionWord,value_twist]
  cases neg <;>
    simp only [Bool.false_eq_true,↓reduceIte] at hz ⊢ <;>
    simp only [value_append,value_constant,value_inverse] <;>
    rw [← hz] <;>
    simp only [map_mul,map_inv,MulEquiv.symm_apply_apply] <;> group

theorem solution_count (W : List (Letter V S)) (x y : V) (t : S)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) (hy : y ≠ x) (s : Bool) :
    (signedVariables (linkSolution W x t)).count (y,s) =
      (signedVariables W).count (y,if (cut W x).negative then s else !s) := by
  obtain ⟨hW,hC,hD⟩ := cut_spec W x hc
  unfold linkSolution
  generalize hcut : cut W x = c at hW hC hD ⊢
  rcases c with ⟨g,neg,C,D⟩
  change W = C ++ [.var x g neg] ++ D at hW
  rw [hW]
  unfold valueSolutionWord
  rw [count_twist]
  cases neg <;> simp [count_inverse,hy,Ne.symm hy] <;> omega

theorem replace_count_other (W R : List (Letter V S)) (x y : V)
    (hy : y ≠ x) (s : Bool) :
    (signedVariables (replaceValueVariable W x R)).count (y,s) =
      (signedVariables W).count (y,s) +
      (signedVariables W).count (x,false) * (signedVariables R).count (y,s) +
      (signedVariables W).count (x,true) * (signedVariables R).count (y,!s) := by
  induction W with
  | nil => simp [replaceValueVariable]
  | cons l W ih =>
    rw [show replaceValueVariable (l::W) x R =
      (match l with
        | .var w g neg => if w = x then
            if neg then inverseWord (twist g R) else twist g R
          else [l]
        | .constant a => [l]) ++ replaceValueVariable W x R by cases l <;> rfl,
      variables_append,List.count_append,ih]
    cases l with
    | constant a => simp
    | var w g neg =>
      by_cases hw : w = x
      · subst w
        cases neg <;> cases s <;>
          simp [count_twist,count_inverse,hy,Ne.symm hy,Nat.add_mul] <;> ring
      · cases neg <;> cases s <;> by_cases hwy : w = y <;>
          simp [hw,hwy,hy,Ne.symm hy] <;> ring

variable {I : Type u} [Finite I] [DecidableEq I] {m : ℕ}

def Ready (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I))
    (W : I → List (Letter (Arc m I) S)) : Prop :=
  ∀ p ∈ L, ∀ v s, (signedVariables (W v)).count (p.2,s) =
    if p.2.2 ≠ base (tau p.2.1) p.2.2 ∧
      v = (if s then base (tau p.2.1) p.2.2 else p.2.2) then 1 else 0

theorem leaf_count (tau : Fin m → Equiv.Perm I)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (p : I × Arc m I) (hL : ValueLeafOrder tau (p::L))
    (hW : Ready tau (p::L) W) :
    (signedVariables (W p.1)).count (p.2,false) +
      (signedVariables (W p.1)).count (p.2,true) = 1 := by
  have hp := hL.1 p (by simp)
  rw [hW p (by simp),hW p (by simp)]
  rcases hp.2 with h | h <;> simp [h,hp.1,Ne.symm hp.1]

theorem ready_next (tau : Fin m → Equiv.Perm I)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (p : I × Arc m I) (hL : ValueLeafOrder tau (p::L))
    (hW : Ready tau (p::L) W) (t : S) :
    Ready tau L (fun v => replaceValueVariable (W v) p.2
      (linkSolution (W p.1) p.2 t)) := by
  have hc := leaf_count tau L W p hL hW
  intro a ha v s
  have hnot := (List.pairwise_cons.mp hL.2).1 a ha
  have hne : a.2 ≠ p.2 := by
    intro he; exact hnot (he ▸ (hL.1 p (by simp)).2)
  have hz : ∀ s, (signedVariables (W p.1)).count (a.2,s) = 0 := by
    intro s
    rw [hW a (by simp [ha])]
    apply if_neg
    rintro ⟨_,hh⟩
    cases s <;> exact hnot (by simp_all [valueIncident])
  rw [replace_count_other _ _ _ _ hne s,solution_count _ _ _ _ hc hne,
    solution_count _ _ _ _ hc hne,hz,hz]
  simpa using hW a (by simp [ha]) v s

/-- Literal successive substitutions of actual nonbase VALUE labels. -/
noncomputable def contractValueSystem (kappa : I → S) :
    List (I × Arc m I) → (I → List (Letter (Arc m I) S)) →
      (I → List (Letter (Arc m I) S))
  | [], W => W
  | p::L, W => contractValueSystem kappa L (fun v =>
      replaceValueVariable (W v) p.2 (linkSolution (W p.1) p.2 (kappa p.1)))

/-- Back substitution constructs all selected VALUE coordinates, retaining
every off-tree parameter from the supplied assignment. -/
noncomputable def extendValueSystem (kappa : I → S) :
    List (I × Arc m I) → (I → List (Letter (Arc m I) S)) →
      (Arc m I → S) → (Arc m I → S)
  | [], W, z => z
  | p::L, W, z =>
    let R := linkSolution (W p.1) p.2 (kappa p.1)
    let a := extendValueSystem kappa L
      (fun v => replaceValueVariable (W v) p.2 R) z
    Function.update a p.2 (wordValue R a)

/-- Every ordered residual is identified with the reconstructed actual
normalized equation, by evaluation of the literal substitutions. -/
theorem contractValueSystem_value (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (z : Arc m I → S) (v : I) :
    wordValue (contractValueSystem kappa L W v) z =
      wordValue (W v) (extendValueSystem kappa L W z) := by
  induction L generalizing W with
  | nil => rfl
  | cons p L ih =>
    rw [contractValueSystem,ih,replaceValueVariable_value]
    rfl

theorem extendValueSystem_unused (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (z : Arc m I → S) (e : Arc m I) (he : ∀ p ∈ L, e ≠ p.2) :
    extendValueSystem kappa L W z e = z e := by
  induction L generalizing W with
  | nil => rfl
  | cons p L ih =>
    rw [extendValueSystem,Function.update_of_ne (he p (by simp))]
    exact ih _ (fun a ha => he a (by simp [ha]))

private theorem extend_solves (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W) (z : Arc m I → S) :
    ∀ p ∈ L, wordValue (W p.1) (extendValueSystem kappa L W z) = kappa p.1 := by
  induction L generalizing W with
  | nil => simp
  | cons p L ih =>
    have hc := leaf_count tau L W p hL hW
    have ht : ValueLeafOrder tau L :=
      ⟨fun a ha => hL.1 a (by simp [ha]),hL.2.of_cons⟩
    have hr := ready_next tau L W p hL hW (kappa p.1)
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      exact link_solves _ _ _ hc _
    · rw [extendValueSystem,← replaceValueVariable_value]
      exact ih _ ht hr a ha

private theorem extend_fixed (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W) (z : Arc m I → S)
    (hz : ∀ p ∈ L, wordValue (W p.1) z = kappa p.1) :
    extendValueSystem kappa L W z = z := by
  induction L generalizing W with
  | nil => rfl
  | cons p L ih =>
    have hc := leaf_count tau L W p hL hW
    have hu := link_unique _ _ _ hc z (hz p (by simp))
    have ht : ValueLeafOrder tau L :=
      ⟨fun a ha => hL.1 a (by simp [ha]),hL.2.of_cons⟩
    have hr := ready_next tau L W p hL hW (kappa p.1)
    have hnext : ∀ a ∈ L, wordValue (replaceValueVariable (W a.1) p.2
        (linkSolution (W p.1) p.2 (kappa p.1))) z = kappa a.1 := by
      intro a ha
      rw [replaceValueVariable_value,hu,Function.update_eq_self]
      exact hz a (by simp [ha])
    rw [extendValueSystem,ih _ ht hr hnext,hu,Function.update_eq_self]

/-- The full actual VALUE forest has been contracted, not just one link.
Every off-root equation is solved for EVERY assignment of unused variables;
root equations are the literal ordered residuals, with all scalar cycle
parameters still freely prescribed. -/
theorem normalized_value_forest_reconstruction
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) :
    (∀ z : Arc m I → S,
      (∀ e, (∀ p ∈ L, e ≠ p.2) →
        extendValueSystem kappa L (normalizedVertexWord tau alpha u) z e = z e) ∧
      (∀ v, v ≠ r v → wordValue (normalizedVertexWord tau alpha u v)
        (extendValueSystem kappa L (normalizedVertexWord tau alpha u) z) = kappa v) ∧
      (∀ v, wordValue (contractValueSystem kappa L
        (normalizedVertexWord tau alpha u) v) z =
        wordValue (normalizedVertexWord tau alpha u v)
          (extendValueSystem kappa L (normalizedVertexWord tau alpha u) z))) ∧
    ((∃ z : Arc m I → S, ∀ v,
      wordValue (normalizedVertexWord tau alpha u v) z = kappa v) ↔
     ∃ z : Arc m I → S, ∀ v, v = r v →
      wordValue (contractValueSystem kappa L
        (normalizedVertexWord tau alpha u) v) z = kappa v) := by
  have hW : Ready tau L (normalizedVertexWord tau alpha u) := by
    intro p hp v s
    exact normalizedVertexWord_variable_count tau alpha u v p.2 s
  constructor
  · intro z
    refine ⟨fun e he => extendValueSystem_unused _ _ _ _ _ he,?_,
      fun v => contractValueSystem_value _ _ _ _ v⟩
    intro v hv
    obtain ⟨p,hp,hpv⟩ := (hroots v).mpr hv
    rw [← hpv]
    exact extend_solves tau kappa L _ hL hW z p hp
  · constructor
    · rintro ⟨z,hz⟩
      refine ⟨z,?_⟩
      intro v hv
      rw [contractValueSystem_value,extend_fixed tau kappa L _ hL hW z
        (fun p hp => hz p.1)]
      exact hz v
    · rintro ⟨z,hz⟩
      refine ⟨extendValueSystem kappa L (normalizedVertexWord tau alpha u) z,?_⟩
      intro v
      by_cases hv : v = r v
      · rw [← contractValueSystem_value]
        exact hz v hv
      · obtain ⟨p,hp,hpv⟩ := (hroots v).mpr hv
        rw [← hpv]
        exact extend_solves tau kappa L _ hL hW z p hp

/-- Actual corrected-action reconstruction after ALL normalized forest
links, on EACH true powered component.  The SAME y precedes every target,
and the true scalar cycle parameters u remain arbitrary.  No extraction or
coverage hypothesis is introduced by this reversible reduction. -/
theorem corrected_value_forest_reconstruction [Fintype I] {q : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (r : I → I)
    (hr : ∀ v, (qPowerGraph sigma q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph sigma q).Reachable v w → r v = r w) :
    ∃ L : List (I × Arc m I), ValueLeafOrder (fun j => sigma j ^ q) L ∧
      (∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) ∧
      ∀ (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S),
      (∃ c : Fin m → I → S,
        (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
        ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v) ↔
      (∃ z : Arc m I → S, ∀ v, v = r v → wordValue
        (contractValueSystem kappa L (normalizedVertexWord (fun j => sigma j ^ q)
          (fun j i => correctedCycleComponent beta sigma y j i q) u) v) z = kappa v) := by
  have hgraph : qPowerGraph (fun j => sigma j ^ q) 1 = qPowerGraph sigma q := by
    ext v w
    simp only [qPowerGraph,pow_one]
  obtain ⟨F,L,hF,hacyc,hreach,hL,hroots,hedges⟩ :=
    exists_value_leafOrder (fun j => sigma j ^ q) r
      (by simpa only [hgraph] using hr) (by simpa only [hgraph] using hconst)
  refine ⟨L,hL,hroots,?_⟩
  intro u kappa
  rw [← corrected_normalized_system_iff k sigma beta hcoord y u kappa]
  exact (normalized_value_forest_reconstruction _ _ _ _ L hL r hroots).2


end NikolovSegal.Equation47ValueNormalization
