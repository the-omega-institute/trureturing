/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueSequenceBalance
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueSequenceBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized value elimination, balance and component colour bounds. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueElimination

set_option autoImplicit false
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u v
variable {S : Type u} [Group S] {V : Type v}
variable {I : Type u} [Finite I] [DecidableEq I] {m : ℕ}

theorem cut_count (W : List (Letter (Arc m I) S)) (x : Arc m I)
    (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) (s : Bool) :
    (signedVariables W).count (x,s) = if s = (cut W x).negative then 1 else 0 := by
  obtain ⟨hW,hC,hD⟩ := cut_spec W x hc
  generalize hcut : cut W x = c at hW hC hD ⊢
  rcases c with ⟨g,neg,C,D⟩
  change W = C ++ [.var x g neg] ++ D at hW
  change avoids C x at hC
  change avoids D x at hD
  rw [hW]
  simp only [variables_append,variables_var,variables_nil,List.count_append,
    List.count_cons,List.count_nil,counts_of_avoids _ _ hC,counts_of_avoids _ _ hD]
  cases s <;> cases neg <;> simp

private theorem solution_avoids (W : List (Letter (Arc m I) S)) (x : Arc m I)
    (t : S) (hc : (signedVariables W).count (x,false) +
      (signedVariables W).count (x,true) = 1) : avoids (linkSolution W x t) x := by
  obtain ⟨hW,hC,hD⟩ := cut_spec W x hc
  unfold linkSolution
  generalize hcut : cut W x = c at hW hC hD ⊢
  rcases c with ⟨g,neg,C,D⟩
  change avoids C x at hC
  change avoids D x at hD
  apply avoids_of_counts
  intro s
  unfold valueSolutionWord
  rw [count_twist]
  cases neg <;> simp [count_inverse,counts_of_avoids _ _ hC,counts_of_avoids _ _ hD]

private theorem replace_count_self (W R : List (Letter (Arc m I) S))
    (x : Arc m I) (hR : avoids R x) (s : Bool) :
    (signedVariables (replaceValueVariable W x R)).count (x,s) = 0 := by
  induction W with
  | nil => rfl
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
        cases neg <;> simp [count_inverse,count_twist,counts_of_avoids _ _ hR]
      · cases neg <;> cases s <;> simp [hw]

def SystemBalance (A : Finset I)
    (W : I → List (Letter (Arc m I) S)) (B : Finset (Arc m I)) : Prop :=
  ∀ e s, ∑ v ∈ A, (signedVariables (W v)).count (e,s) = if e ∈ B then 1 else 0

theorem balance_next (A : Finset I)
    (W : I → List (Letter (Arc m I) S)) (B : Finset (Arc m I))
    (leaf : I) (x : Arc m I) (t : S) (hleaf : leaf ∈ A)
    (hc : (signedVariables (W leaf)).count (x,false) +
      (signedVariables (W leaf)).count (x,true) = 1)
    (hbal : SystemBalance A W B) :
    SystemBalance (A.erase leaf)
      (fun v => replaceValueVariable (W v) x (linkSolution (W leaf) x t)) (B.erase x) := by
  have hx : x ∈ B := by
    by_contra h
    have hf := hbal x false
    have ht := hbal x true
    simp only [if_neg h] at hf ht
    have hf' := Finset.single_le_sum (fun v (_ : v ∈ A) =>
      Nat.zero_le ((signedVariables (W v)).count (x,false))) hleaf
    have ht' := Finset.single_le_sum (fun v (_ : v ∈ A) =>
      Nat.zero_le ((signedVariables (W v)).count (x,true))) hleaf
    omega
  have hs : ∀ s, (∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,s)) +
      (signedVariables (W leaf)).count (x,s) = 1 := by
    intro s
    rw [Finset.sum_erase_add _ _ hleaf,hbal x s,if_pos hx]
  intro e s
  by_cases he : e = x
  · subst e
    simp only [Finset.mem_erase,ne_eq,not_true_eq_false,false_and,ite_false]
    apply Finset.sum_eq_zero
    intro v hv
    exact replace_count_self _ _ _ (solution_avoids _ _ _ hc) s
  · have hformula : (∑ v ∈ A.erase leaf,
        (signedVariables (replaceValueVariable (W v) x
          (linkSolution (W leaf) x t))).count (e,s)) =
        (∑ v ∈ A.erase leaf, (signedVariables (W v)).count (e,s)) +
        (∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,false)) *
          (signedVariables (linkSolution (W leaf) x t)).count (e,s) +
        (∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,true)) *
          (signedVariables (linkSolution (W leaf) x t)).count (e,!s) := by
      simp_rw [replace_count_other _ _ _ _ he]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
        ← Finset.sum_mul,← Finset.sum_mul]
    rw [hformula,solution_count _ _ _ _ hc he,solution_count _ _ _ _ hc he]
    have hf := hs false
    have ht := hs true
    rw [cut_count _ _ hc false] at hf
    rw [cut_count _ _ hc true] at ht
    cases hn : (cut (W leaf) x).negative
    · simp only [hn,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,Bool.not_not] at hf ht ⊢
      have hzero : ∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,false) = 0 := by omega
      have hone : ∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,true) = 1 := by omega
      simp only [hzero,hone,Nat.zero_mul,Nat.one_mul,Nat.add_zero]
      rw [Finset.sum_erase_add _ _ hleaf,hbal e s]
      simp [he]
    · simp only [hn,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte] at hf ht ⊢
      have hone : ∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,false) = 1 := by omega
      have hzero : ∑ v ∈ A.erase leaf, (signedVariables (W v)).count (x,true) = 0 := by omega
      simp only [hzero,hone,Nat.zero_mul,Nat.one_mul,Nat.add_zero]
      rw [Finset.sum_erase_add _ _ hleaf,hbal e s]
      simp [he]

def remainingVertices : Finset I → List (I × Arc m I) → Finset I
  | A, [] => A
  | A, p::L => remainingVertices (A.erase p.1) L

theorem mem_remaining (A : Finset I) (L : List (I × Arc m I)) (v : I) :
    v ∈ remainingVertices A L ↔ v ∈ A ∧ ∀ p ∈ L, v ≠ p.1 := by
  induction L generalizing A with
  | nil => simp [remainingVertices]
  | cons p L ih => simp only [remainingVertices,ih,Finset.mem_erase,List.mem_cons]
                   aesop

private def remainingVariables : Finset (Arc m I) → List (I × Arc m I) → Finset (Arc m I)
  | B, [] => B
  | B, p::L => remainingVariables (B.erase p.2) L

private theorem mem_remaining_variables (B : Finset (Arc m I))
    (L : List (I × Arc m I)) (e : Arc m I) :
    e ∈ remainingVariables B L ↔ e ∈ B ∧ ∀ p ∈ L, e ≠ p.2 := by
  induction L generalizing B with
  | nil => simp [remainingVariables]
  | cons p L ih => simp only [remainingVariables,ih,Finset.mem_erase,List.mem_cons]
                   aesop

private theorem sequence_balance (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W)
    (A : Finset I) (B : Finset (Arc m I))
    (hA : ∀ p ∈ L, p.1 ∈ A) (hbal : SystemBalance A W B) :
    SystemBalance (remainingVertices A L) (contractValueSystem kappa L W)
      (remainingVariables B L) := by
  induction L generalizing W A B with
  | nil => exact hbal
  | cons p L ih =>
    have hc := leaf_count tau L W p hL hW
    have ht : ValueLeafOrder tau L :=
      ⟨fun a ha => hL.1 a (by simp [ha]),hL.2.of_cons⟩
    have hr := ready_next tau L W p hL hW (kappa p.1)
    have hA' : ∀ a ∈ L, a.1 ∈ A.erase p.1 := by
      intro a ha
      apply Finset.mem_erase.mpr
      refine ⟨?_,hA a (by simp [ha])⟩
      intro he
      have hn := (List.pairwise_cons.mp hL.2).1 a ha
      exact hn (he ▸ (hL.1 a (by simp [ha])).2)
    exact ih _ ht hr _ _ hA'
      (balance_next A W B p.1 p.2 (kappa p.1) (hA p (by simp)) hc hbal)

/-- Exact signed balance after EVERY forest contraction: each surviving
actual nonbase VALUE appears once with each sign among the root residuals;
each contracted variable and each cycle-base variable appears zero times.
The count is independent of all targets and scalar cycle parameters. -/
theorem normalized_value_forest_balance [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (e : Arc m I) (s : Bool) :
    (∑ v ∈ Finset.univ.filter (fun v => v = r v),
      (signedVariables (contractValueSystem kappa L
        (normalizedVertexWord tau alpha u) v)).count (e,s)) =
    if e.2 ≠ base (tau e.1) e.2 ∧ (∀ p ∈ L, e ≠ p.2) then 1 else 0 := by
  classical
  let B := Finset.univ.filter (fun e : Arc m I => e.2 ≠ base (tau e.1) e.2)
  have hW : Ready tau L (normalizedVertexWord tau alpha u) := by
    intro p hp v s
    exact normalizedVertexWord_variable_count tau alpha u v p.2 s
  have hbal : SystemBalance Finset.univ (normalizedVertexWord tau alpha u) B := by
    intro e s
    simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using
      normalized_system_balance tau alpha u e s
  have hh := sequence_balance tau kappa L _ hL hW Finset.univ B (by simp) hbal e s
  have hremain : remainingVertices Finset.univ L =
      Finset.univ.filter (fun v => v = r v) := by
    ext v
    rw [mem_remaining]
    simp only [Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · intro hv
      by_contra hn
      obtain ⟨p,hp,he⟩ := (hroots v).mpr hn
      exact hv p hp he.symm
    · intro hv p hp he
      have hn := (hroots v).mp ⟨p,hp,he.symm⟩
      exact hn hv
  rw [hremain] at hh
  change (∑ v ∈ Finset.univ.filter (fun v => v = r v),
    (signedVariables (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) v)).count (e,s)) =
      (if e ∈ remainingVariables B L then 1 else 0) at hh
  simp only [mem_remaining_variables] at hh
  simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using hh


def LocalWords (r : I → I) (W : I → List (Letter (Arc m I) S)) : Prop :=
  ∀ v e s, 0 < (signedVariables (W v)).count (e,s) → r e.2 = r v

theorem local_next (r : I → I)
    (W : I → List (Letter (Arc m I) S)) (leaf : I) (x : Arc m I) (t : S)
    (hc : (signedVariables (W leaf)).count (x,false) +
      (signedVariables (W leaf)).count (x,true) = 1)
    (hloc : LocalWords r W) :
    LocalWords r (fun v => replaceValueVariable (W v) x (linkSolution (W leaf) x t)) := by
  have hxl : r x.2 = r leaf := hloc leaf x (cut (W leaf) x).negative (by
    rw [cut_count _ _ hc]
    simp)
  intro v e s hpos
  by_contra hne
  by_cases he : e = x
  · subst e
    rw [replace_count_self _ _ _ (solution_avoids _ _ _ hc)] at hpos
    omega
  · have hz : (signedVariables (W v)).count (e,s) = 0 := by
      by_contra h
      exact hne (hloc v e s (by omega))
    rw [replace_count_other _ _ _ _ he,hz] at hpos
    by_cases hv : r leaf = r v
    · have hR : ∀ s, (signedVariables (linkSolution (W leaf) x t)).count (e,s) = 0 := by
        intro s
        rw [solution_count _ _ _ _ hc he]
        by_contra h
        have hh := hloc leaf e (if (cut (W leaf) x).negative then s else !s) (by omega)
        exact hne (hh.trans hv)
      rw [hR s,hR (!s)] at hpos
      simp at hpos
    · have hX : ∀ s, (signedVariables (W v)).count (x,s) = 0 := by
        intro s
        by_contra h
        have hh := hloc v x s (by omega)
        exact hv (hxl.symm.trans hh)
      rw [hX false,hX true] at hpos
      simp at hpos

private theorem sequence_local (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W) (r : I → I)
    (hloc : LocalWords r W) : LocalWords r (contractValueSystem kappa L W) := by
  induction L generalizing W with
  | nil => exact hloc
  | cons p L ih =>
    have hc := leaf_count tau L W p hL hW
    have ht : ValueLeafOrder tau L :=
      ⟨fun a ha => hL.1 a (by simp [ha]),hL.2.of_cons⟩
    have hr := ready_next tau L W p hL hW (kappa p.1)
    exact ih _ ht hr (local_next r W p.1 p.2 (kappa p.1) hc hloc)

theorem root_base (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (e : Arc m I) : r e.2 = r (base (tau e.1) e.2) := by
  by_cases he : e.2 = base (tau e.1) e.2
  · exact congrArg r he
  · apply hconst
    rw [← valueLinkGraph_reachable]
    exact (show (valueLinkGraph tau).Adj e.2 (base (tau e.1) e.2) from
      ⟨he,e.1,Or.inl rfl⟩).reachable

theorem normalized_local (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (u : ∀ j, ActualCycle (tau j) → S)
    (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w) :
    LocalWords r (normalizedVertexWord tau alpha u) := by
  intro v e s hpos
  rw [normalizedVertexWord_variable_count] at hpos
  have hh : e.2 ≠ base (tau e.1) e.2 ∧
      v = (if s then base (tau e.1) e.2 else e.2) := by
    by_contra h
    simp [h] at hpos
  rw [hh.2]
  cases s
  · rfl
  · exact root_base tau r hconst e

/-- EACH genuine component residual is balanced separately.  The support is
exactly its surviving nonbase VALUE labels; no pair is split between roots.
This uses actual component locality, not original-action transitivity. -/
theorem normalized_value_residual_sign_count [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root) (e : Arc m I) (s : Bool) :
    (signedVariables (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root)).count (e,s) =
      if e.2 ≠ base (tau e.1) e.2 ∧ (∀ p ∈ L, e ≠ p.2) ∧ r e.2 = root
      then 1 else 0 := by
  classical
  have hW : Ready tau L (normalizedVertexWord tau alpha u) := by
    intro p hp v s
    exact normalizedVertexWord_variable_count tau alpha u v p.2 s
  have hloc := sequence_local tau kappa L _ hL hW r (normalized_local tau alpha u r hconst)
  by_cases he : r e.2 = root
  · have hsingle : (∑ v ∈ Finset.univ.filter (fun v => v = r v),
        (signedVariables (contractValueSystem kappa L
          (normalizedVertexWord tau alpha u) v)).count (e,s)) =
        (signedVariables (contractValueSystem kappa L
          (normalizedVertexWord tau alpha u) root)).count (e,s) := by
      apply Finset.sum_eq_single root
      · intro v hv hvne
        have hvroot : v = r v := (Finset.mem_filter.mp hv).2
        by_contra hn
        have hh := hloc v e s (by omega)
        exact hvne (hvroot.trans (hh.symm.trans he))
      · intro h
        exact False.elim (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot⟩))
    rw [← hsingle,normalized_value_forest_balance tau alpha u kappa L hL r hroots]
    simp [he]
  · have hz : (signedVariables (contractValueSystem kappa L
        (normalizedVertexWord tau alpha u) root)).count (e,s) = 0 := by
      by_contra hn
      have hh := hloc root e s (by omega)
      exact he (hh.trans hroot.symm)
    simp [hz,he]

theorem forest_labels_nodup (tau : Fin m → Equiv.Perm I)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L) :
    (L.map Prod.fst).Nodup ∧ (L.map Prod.snd).Nodup := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have ht : ValueLeafOrder tau L :=
      ⟨fun a ha => hL.1 a (by simp [ha]),hL.2.of_cons⟩
    obtain ⟨hv,he⟩ := ih ht
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨⟨?_,hv⟩,⟨?_,he⟩⟩
    · intro hm
      obtain ⟨a,ha,hap⟩ := List.mem_map.mp hm
      exact (List.pairwise_cons.mp hL.2).1 a ha (hap ▸ (hL.1 a (by simp [ha])).2)
    · intro hm
      obtain ⟨a,ha,hap⟩ := List.mem_map.mp hm
      exact (List.pairwise_cons.mp hL.2).1 a ha (hap.symm ▸ (hL.1 p (by simp)).2)

/-- The actual surviving support of ONE component, ready for Lemma8.3.
Its equality with the root word's support is proved from exact signed counts.
-/
noncomputable def valueResidualSupport [Fintype I]
    (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I))
    (r : I → I) (root : I) : Finset (Arc m I) :=
  Finset.univ.filter (fun e => e.2 ≠ base (tau e.1) e.2 ∧
    (∀ p ∈ L, e ≠ p.2) ∧ r e.2 = root)

theorem normalized_value_residual_support [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root) :
    ((signedVariables (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root)).map Prod.fst).toFinset =
      valueResidualSupport tau L r root := by
  classical
  ext e
  simp only [List.mem_toFinset,List.mem_map,valueResidualSupport,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨x,s⟩,hx,he⟩
    change x = e at he
    subst x
    have hc : 0 < (signedVariables (contractValueSystem kappa L
        (normalizedVertexWord tau alpha u) root)).count (e,s) := List.count_pos_iff.mpr hx
    rw [normalized_value_residual_sign_count tau alpha u kappa L hL r hroots hconst root hroot] at hc
    by_contra h
    rw [if_neg h] at hc
    omega
  · intro he
    refine ⟨(e,false),List.count_pos_iff.mp ?_,rfl⟩
    rw [normalized_value_residual_sign_count tau alpha u kappa L hL r hroots hconst root hroot]
    rw [if_pos he]
    exact Nat.zero_lt_one

/-- On a connected powered component, the real residual has exactly
mn-sum(cycles)-(n-1) matching pairs, as printed on p.225.  No witness-variable
word or assumed extraction certificate is used in this count. -/
theorem normalized_connected_residual_pair_count [Fintype I]
    (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I))
    (hL : ValueLeafOrder tau L) (root : I)
    (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ root) :
    (valueResidualSupport tau L (fun _ => root) root).card +
      (Fintype.card I - 1) = Nat.card (FreeValueVariable tau) := by
  classical
  let B := Finset.univ.filter (fun e : Arc m I => e.2 ≠ base (tau e.1) e.2)
  let E := (L.map Prod.snd).toFinset
  have hsubset : E ⊆ B := by
    intro e he
    obtain ⟨p,hp,hpe⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [hpe] using (hL.1 p hp).1
  have hsupport : valueResidualSupport tau L (fun _ => root) root = B \ E := by
    ext e
    simp only [valueResidualSupport,B,E,Finset.mem_filter,Finset.mem_univ,
      true_and,Finset.mem_sdiff,List.mem_toFinset,List.mem_map,and_true]
    constructor
    · rintro ⟨he,hu⟩
      refine ⟨he,?_⟩
      rintro ⟨p,hp,hpe⟩
      exact hu p hp hpe.symm
    · rintro ⟨he,hu⟩
      refine ⟨he,?_⟩
      intro p hp hpe
      exact hu ⟨p,hp,hpe.symm⟩
  have hvertices : (L.map Prod.fst).toFinset = Finset.univ.erase root := by
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_erase,
      Finset.mem_univ,and_true]
    exact hroots v
  have hnodup := forest_labels_nodup tau L hL
  have hlength : L.length = Fintype.card I - 1 := by
    have hh := congrArg Finset.card hvertices
    rw [List.toFinset_card_of_nodup hnodup.1,List.length_map,
      Finset.card_erase_of_mem (Finset.mem_univ root),Finset.card_univ] at hh
    exact hh
  have hE : E.card = Fintype.card I - 1 := by
    change (L.map Prod.snd).toFinset.card = Fintype.card I - 1
    rw [List.toFinset_card_of_nodup hnodup.2,List.length_map,hlength]
  have hB : B.card = Nat.card (FreeValueVariable tau) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  rw [hsupport,← hE,Finset.card_sdiff_add_card_eq_card hsubset,hB]

/-- The actual normalized residual, AFTER its n-1 constructed links, meets
the numerical support bound needed by Proposition8.4.  The colour bound and
quantitative extraction construction are still separate unproved steps. -/
theorem normalized_connected_typeII_residual_budget [Fintype I] {D : ℕ}
    (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I))
    (hL : ValueLeafOrder tau L) (root : I)
    (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ root)
    (hn : 2 ≤ Fintype.card I)
    (htype : (4+2*D) * Fintype.card I ≤
      ∑ j : Fin m, (Fintype.card I - actualFixedCount (tau j))) :
    Fintype.card I + 2*D + 1 ≤
      (valueResidualSupport tau L (fun _ => root) root).card := by
  have hc := normalized_connected_residual_pair_count tau L hL root hroots
  have hb := normalized_typeII_initial_pair_budget tau hn htype
  omega



/-! The component-weight colour proof below applies to this exact postorder
recursion.  It does not import the paper's growing-root invariant as a premise. -/

end NikolovSegal.Equation47ValueNormalization
