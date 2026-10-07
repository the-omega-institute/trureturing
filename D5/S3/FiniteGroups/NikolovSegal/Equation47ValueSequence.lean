/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueSequence
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized value elimination, balance and component colour bounds. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueSequenceBalance

set_option autoImplicit false
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u v
variable {S : Type u} [Group S] {V : Type v}
variable {I : Type u} [Finite I] [DecidableEq I] {m : ℕ}

open Equation47Colours List

@[simp] private theorem colours_append (A B : List (Letter (Arc m I) S)) :
    wordColours (A++B) = wordColours A ++ wordColours B := by
  simp [wordColours,signedVariables]

@[simp] private theorem colours_twist (g : MulAut S) (W : List (Letter (Arc m I) S)) :
    wordColours (twist g W) = wordColours W := by
  induction W with
  | nil => rfl
  | cons l W ih => cases l <;> simp_all [wordColours,signedVariables,twist]

@[simp] private theorem colours_inverse (W : List (Letter (Arc m I) S)) :
    wordColours (inverseWord W) = (wordColours W).reverse.map (fun p => (p.1,!p.2)) := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    rw [show inverseWord (l::W) = inverseWord W ++ [match l with
      | .var y g neg => .var y g (!neg)
      | .constant a => .constant a⁻¹] by
        simp only [inverseWord,List.reverse_cons,List.map_append,List.map_singleton]; cases l <;> rfl,
      colours_append,ih]
    cases l <;> simp [wordColours,signedVariables,List.reverse_cons]

private theorem replace_avoids_eq (W R : List (Letter (Arc m I) S))
    (x : Arc m I) (h : avoids W x) : replaceValueVariable W x R = W := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    have ht : avoids W x := fun g s hn => h g s (by simp [hn])
    cases l with
    | constant a => simpa [replaceValueVariable] using congrArg (List.cons (.constant a)) (ih ht)
    | var y g s =>
      have hy : y ≠ x := by intro he; subst y; exact h g s (by simp)
      simpa [replaceValueVariable,hy] using congrArg (List.cons (.var y g s)) (ih ht)

@[simp] private theorem colours_var (x : Arc m I) (g : MulAut S) (s : Bool) :
    wordColours [.var x g s] = [(x.1,s)] := rfl

@[simp] private theorem colours_constant (a : S) :
    wordColours ([.constant a] : List (Letter (Arc m I) S)) = [] := rfl

private theorem link_colour_bound (U W : List (Letter (Arc m I) S)) (x : Arc m I) (t : S)
    (hU : (signedVariables U).count (x,false) + (signedVariables U).count (x,true) = 1)
    (hW : (signedVariables W).count (x,false) + (signedVariables W).count (x,true) = 1)
    (hop : (signedVariables W).count (x,(cut U x).negative) = 0) :
    signedRank (wordColours (replaceValueVariable W x (linkSolution U x t))) ≤
      signedRank (wordColours W) + signedRank (wordColours U) := by
  obtain ⟨hUw,hC,hD⟩ := cut_spec U x hU
  obtain ⟨hWw,hA,hB⟩ := cut_spec W x hW
  have hs : (cut W x).negative = !(cut U x).negative := by
    rw [cut_count W x hW] at hop
    cases hws : (cut W x).negative <;> cases hus : (cut U x).negative <;>
      simp only [hws,hus,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        Bool.true_eq_false,↓reduceIte] at hop ⊢ <;> omega
  unfold linkSolution
  generalize hcU : cut U x = cU at hUw hC hD hs ⊢
  generalize hcW : cut W x = cW at hWw hA hB hs
  rcases cU with ⟨gU,negU,C,D⟩
  rcases cW with ⟨gW,negW,A,B⟩
  change U = C ++ [.var x gU negU] ++ D at hUw
  change W = A ++ [.var x gW negW] ++ B at hWw
  change avoids C x at hC
  change avoids D x at hD
  change avoids A x at hA
  change avoids B x at hB
  change negW = !negU at hs
  subst negW
  rw [hWw]
  have hrepl : replaceValueVariable
      (A ++ [.var x gW (!negU)] ++ B) x (valueSolutionWord gU negU C D t) =
      A ++ (if !negU then inverseWord (twist gW (valueSolutionWord gU negU C D t))
        else twist gW (valueSolutionWord gU negU C D t)) ++ B := by
    simp only [replaceValueVariable,List.flatMap_append]
    change replaceValueVariable A x _ ++ _ ++ replaceValueVariable B x _ = _
    rw [replace_avoids_eq A _ x hA,replace_avoids_eq B _ x hB]
    simp [replaceValueVariable]
  rw [hrepl,hUw]
  have hk := signedRank_link (wordColours A) (wordColours B) (wordColours C) (wordColours D) x.1 (!negU)
  cases negU <;>
    simpa only [valueSolutionWord,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      ↓reduceIte,colours_append,colours_twist,colours_inverse,colours_var,colours_constant,
      List.reverse_append,List.reverse_nil,List.map_append,List.map_nil,List.nil_append,
      List.append_nil,List.map_reverse,List.reverse_reverse,List.map_map,Function.comp_def,
      Bool.not_not,Prod.eta,List.map_id',List.map_id,List.map_id_fun,List.append_assoc] using hk


private theorem colour_next (A : Finset I)
    (W : I → List (Letter (Arc m I) S)) (B : Finset (Arc m I))
    (leaf : I) (x : Arc m I) (t : S) (hleaf : leaf ∈ A)
    (hc : (signedVariables (W leaf)).count (x,false) +
      (signedVariables (W leaf)).count (x,true) = 1)
    (hbal : SystemBalance A W B) :
    (∑ v ∈ A.erase leaf, signedRank (wordColours
      (replaceValueVariable (W v) x (linkSolution (W leaf) x t)))) ≤
    ∑ v ∈ A, signedRank (wordColours (W v)) := by
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
  let f := fun v => (signedVariables (W v)).count (x,false) +
    (signedVariables (W v)).count (x,true)
  have hsum : ∑ v ∈ A.erase leaf, f v = 1 := by
    dsimp [f]
    rw [Finset.sum_add_distrib]
    have hf := hs false
    have ht := hs true
    omega
  have hsame : ∑ v ∈ A.erase leaf,
      (signedVariables (W v)).count (x,(cut (W leaf) x).negative) = 0 := by
    have hh := hs (cut (W leaf) x).negative
    rw [cut_count _ _ hc,if_pos rfl] at hh
    omega
  have hstep : ∀ v ∈ A.erase leaf,
      signedRank (wordColours (replaceValueVariable (W v) x (linkSolution (W leaf) x t))) ≤
      signedRank (wordColours (W v)) + f v * signedRank (wordColours (W leaf)) := by
    intro v hv
    have hle : f v ≤ 1 := by
      have hh := Finset.single_le_sum (fun w (_ : w ∈ A.erase leaf) => Nat.zero_le (f w)) hv
      omega
    by_cases hf : f v = 0
    · have ha : avoids (W v) x := by
        apply avoids_of_counts
        intro s; cases s <;> dsimp [f] at hf <;> omega
      rw [replace_avoids_eq _ _ _ ha,hf]
      simp
    · have hone : f v = 1 := by omega
      have hop : (signedVariables (W v)).count (x,(cut (W leaf) x).negative) = 0 := by
        have hh := Finset.single_le_sum (fun w (_ : w ∈ A.erase leaf) =>
          Nat.zero_le ((signedVariables (W w)).count (x,(cut (W leaf) x).negative))) hv
        omega
      rw [hone,Nat.one_mul]
      exact link_colour_bound _ _ _ _ hc hone hop
  calc
    _ ≤ ∑ v ∈ A.erase leaf,
        (signedRank (wordColours (W v)) + f v * signedRank (wordColours (W leaf))) :=
      Finset.sum_le_sum hstep
    _ = (∑ v ∈ A.erase leaf, signedRank (wordColours (W v))) +
        signedRank (wordColours (W leaf)) := by
      rw [Finset.sum_add_distrib,← Finset.sum_mul,hsum,Nat.one_mul]
    _ = _ := Finset.sum_erase_add _ _ hleaf

private theorem sequence_colour_sum (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W)
    (A : Finset I) (B : Finset (Arc m I))
    (hA : ∀ p ∈ L, p.1 ∈ A) (hbal : SystemBalance A W B) :
    (∑ v ∈ remainingVertices A L,
      signedRank (wordColours (contractValueSystem kappa L W v))) ≤
    (∑ v ∈ A, signedRank (wordColours (W v))) := by
  induction L generalizing W A B with
  | nil => exact Nat.le_refl _
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
    exact (ih _ ht hr _ _ hA'
      (balance_next A W B p.1 p.2 (kappa p.1) (hA p (by simp)) hc hbal)).trans
      (colour_next A W B p.1 p.2 (kappa p.1) (hA p (by simp)) hc hbal)

/-- The final actual VALUE residual has the printed L_n colour bound for
this complete connected coordinate system.  The proof uses additive
subtree weights of the accepted postorder, not a silently assumed p225
untouched-equation invariant.  All targets and cycle scalars are arbitrary. -/
theorem normalized_connected_residual_colour [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (root : I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ root) :
    colourType (wordColours (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root)) <+
      colourBound m (Fintype.card I) := by
  classical
  let B := Finset.univ.filter (fun e : Arc m I => e.2 ≠ base (tau e.1) e.2)
  have hW : Ready tau L (normalizedVertexWord tau alpha u) := by
    intro p hp v s
    exact normalizedVertexWord_variable_count tau alpha u v p.2 s
  have hbal : SystemBalance Finset.univ (normalizedVertexWord tau alpha u) B := by
    intro e s
    simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using
      normalized_system_balance tau alpha u e s
  have hh := sequence_colour_sum tau kappa L _ hL hW Finset.univ B (by simp) hbal
  have hremain : remainingVertices Finset.univ L = {root} := by
    ext v
    rw [mem_remaining]
    simp only [Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hv
      by_contra hn
      obtain ⟨p,hp,he⟩ := (hroots v).mpr hn
      exact hv p hp he.symm
    · intro hv p hp he
      subst v
      exact (hroots root).mp ⟨p,hp,he.symm⟩ rfl
  rw [hremain,Finset.sum_singleton] at hh
  apply (signedRank_iff _).mp
  apply hh.trans
  calc
    _ ≤ ∑ v : I, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v hv
      apply (signedRank_iff _).mpr
      simpa [colourBound] using normalized_initial_colour_bound tau alpha u v
    _ = _ := by simp


private theorem component_balance (A : Finset I)
    (W : I → List (Letter (Arc m I) S)) (B : Finset (Arc m I))
    (r : I → I) (root : I) (hloc : LocalWords r W) (hbal : SystemBalance A W B) :
    SystemBalance (A.filter (fun v => r v = root)) W
      (B.filter (fun e => r e.2 = root)) := by
  classical
  intro e s
  by_cases he : r e.2 = root
  · have hh : (∑ v ∈ A.filter (fun v => r v = root),
        (signedVariables (W v)).count (e,s)) =
        ∑ v ∈ A, (signedVariables (W v)).count (e,s) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvroot : r v = root
      · simp [hvroot]
      · have hz : (signedVariables (W v)).count (e,s) = 0 := by
          by_contra hn
          exact hvroot ((hloc v e s (by omega)).symm.trans he)
        simp [hvroot,hz]
    rw [hh,hbal e s]
    simp [he]
  · have hz : (∑ v ∈ A.filter (fun v => r v = root),
        (signedVariables (W v)).count (e,s)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hvroot := (Finset.mem_filter.mp hv).2
      by_contra hn
      exact he ((hloc v e s (by omega)).trans hvroot)
    rw [hz]
    simp [he]

private theorem component_colour_next (A : Finset I)
    (W : I → List (Letter (Arc m I) S)) (B : Finset (Arc m I))
    (leaf : I) (x : Arc m I) (t : S) (hleaf : leaf ∈ A)
    (hc : (signedVariables (W leaf)).count (x,false) +
      (signedVariables (W leaf)).count (x,true) = 1)
    (hbal : SystemBalance A W B) (r : I → I) (root : I) (hloc : LocalWords r W) :
    (∑ v ∈ (A.erase leaf).filter (fun v => r v = root), signedRank (wordColours
      (replaceValueVariable (W v) x (linkSolution (W leaf) x t)))) ≤
      ∑ v ∈ A.filter (fun v => r v = root), signedRank (wordColours (W v)) := by
  classical
  have heq : (A.erase leaf).filter (fun v => r v = root) =
      (A.filter (fun v => r v = root)).erase leaf := by ext v; simp; tauto
  rw [heq]
  by_cases hroot : r leaf = root
  · exact colour_next _ W _ leaf x t (by simp [hleaf,hroot]) hc
      (component_balance A W B r root hloc hbal)
  · have hxl : r x.2 = r leaf := hloc leaf x (cut (W leaf) x).negative (by
      rw [cut_count _ _ hc]; simp)
    have hout : leaf ∉ A.filter (fun v => r v = root) := by simp [hroot]
    rw [Finset.erase_eq_of_notMem hout]
    apply Finset.sum_le_sum
    intro v hv
    have ha : avoids (W v) x := by
      apply avoids_of_counts
      intro s
      by_contra hn
      have hh := hloc v x s (by omega)
      exact hroot (hxl.symm.trans (hh.trans (Finset.mem_filter.mp hv).2))
    rw [replace_avoids_eq _ _ _ ha]

private theorem sequence_colour_component (tau : Fin m → Equiv.Perm I) (kappa : I → S)
    (L : List (I × Arc m I)) (W : I → List (Letter (Arc m I) S))
    (hL : ValueLeafOrder tau L) (hW : Ready tau L W)
    (A : Finset I) (B : Finset (Arc m I))
    (hA : ∀ p ∈ L, p.1 ∈ A) (hbal : SystemBalance A W B)
    (r : I → I) (root : I) (hloc : LocalWords r W) :
    (∑ v ∈ (remainingVertices A L).filter (fun v => r v = root),
      signedRank (wordColours (contractValueSystem kappa L W v))) ≤
      ∑ v ∈ A.filter (fun v => r v = root), signedRank (wordColours (W v)) := by
  induction L generalizing W A B with
  | nil => exact Nat.le_refl _
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
    exact (ih _ ht hr _ _ hA'
      (balance_next A W B p.1 p.2 (kappa p.1) (hA p (by simp)) hc hbal)
      (local_next r W p.1 p.2 (kappa p.1) hc hloc)).trans
      (component_colour_next A W B p.1 p.2 (kappa p.1) (hA p (by simp)) hc hbal r root hloc)

/-- Each TRUE component receives its own component-size L_n bound through
all postorder contractions, including steps in other powered components.
The scalar cycle parameters, targets and genuine automorphisms are arbitrary. -/
theorem normalized_component_residual_colour [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root) :
    colourType (wordColours (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root)) <+
      colourBound m (Finset.univ.filter (fun v : I => r v = root)).card := by
  classical
  let B := Finset.univ.filter (fun e : Arc m I => e.2 ≠ base (tau e.1) e.2)
  have hW : Ready tau L (normalizedVertexWord tau alpha u) := by
    intro p hp v s
    exact normalizedVertexWord_variable_count tau alpha u v p.2 s
  have hbal : SystemBalance Finset.univ (normalizedVertexWord tau alpha u) B := by
    intro e s
    simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using
      normalized_system_balance tau alpha u e s
  have hh := sequence_colour_component tau kappa L _ hL hW Finset.univ B (by simp)
    hbal r root (normalized_local tau alpha u r hconst)
  have hremain : (remainingVertices Finset.univ L).filter (fun v => r v = root) = {root} := by
    ext v
    simp only [Finset.mem_filter,mem_remaining,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨hv,hrv⟩
      have hvroot : v = r v := by
        by_contra hn
        obtain ⟨p,hp,he⟩ := (hroots v).mpr hn
        exact hv p hp he.symm
      exact hvroot.trans hrv
    · intro hv
      subst v
      refine ⟨?_,hroot.symm⟩
      intro p hp he
      exact ((hroots root).mp ⟨p,hp,he.symm⟩) hroot
  rw [hremain,Finset.sum_singleton] at hh
  apply (signedRank_iff _).mp
  apply hh.trans
  calc
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : I => r v = root), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v hv
      apply (signedRank_iff _).mpr
      simpa [colourBound] using normalized_initial_colour_bound tau alpha u v
    _ = _ := by simp


/-- The exact n-1-link count localizes to EVERY true component of the
actual VALUE forest, even when powered transitivity fails globally. -/
theorem normalized_component_residual_pair_count [Fintype I]
    (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root) :
    (valueResidualSupport tau L r root).card +
      ((Finset.univ.filter (fun v : I => r v = root)).card - 1) =
      (Finset.univ.filter (fun e : Arc m I =>
        e.2 ≠ base (tau e.1) e.2 ∧ r e.2 = root)).card := by
  classical
  let A := Finset.univ.filter (fun v : I => r v = root)
  let B := Finset.univ.filter (fun e : Arc m I =>
    e.2 ≠ base (tau e.1) e.2 ∧ r e.2 = root)
  let K := L.filter (fun p => r p.1 = root)
  let E := (K.map Prod.snd).toFinset
  have hinc : ∀ p ∈ L, r p.2.2 = r p.1 := by
    intro p hp
    rcases (hL.1 p hp).2 with hs | hs
    · exact congrArg r hs.symm
    · rw [hs]; exact root_base tau r hconst p.2
  have hK : ValueLeafOrder tau K :=
    ⟨fun p hp => hL.1 p (List.mem_of_mem_filter hp),hL.2.filter _⟩
  have hsubset : E ⊆ B := by
    intro e he
    obtain ⟨p,hp,hpe⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    obtain ⟨hpL,hpr⟩ := List.mem_filter.mp hp
    simp only [decide_eq_true_eq] at hpr
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
    subst e
    exact ⟨(hL.1 p hpL).1,(hinc p hpL).trans hpr⟩
  have hsupport : valueResidualSupport tau L r root = B \ E := by
    ext e
    simp only [valueResidualSupport,B,E,K,Finset.mem_filter,Finset.mem_univ,
      true_and,Finset.mem_sdiff,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨he,hu,hr⟩
      refine ⟨⟨he,hr⟩,?_⟩
      rintro ⟨p,⟨hp,hpr⟩,hpe⟩
      exact hu p hp hpe.symm
    · rintro ⟨⟨he,hr⟩,hu⟩
      refine ⟨he,?_,hr⟩
      intro p hp hpe
      apply hu
      refine ⟨p,⟨hp,?_⟩,hpe.symm⟩
      exact (hinc p hp).symm.trans (hpe ▸ hr)
  have hvertices : (K.map Prod.fst).toFinset = A.erase root := by
    ext v
    simp only [K,A,List.mem_toFinset,List.mem_map,List.mem_filter,
      decide_eq_true_eq,Finset.mem_erase,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨p,⟨hp,hpr⟩,hpv⟩
      subst v
      refine ⟨?_,hpr⟩
      intro h
      have hn := (hroots p.1).mp ⟨p,hp,rfl⟩
      rw [h] at hn
      exact hn hroot
    · rintro ⟨hv,hvr⟩
      have hn : v ≠ r v := by simpa only [hvr] using hv
      obtain ⟨p,hp,hpv⟩ := (hroots v).mpr hn
      exact ⟨p,⟨hp,by simpa only [hpv] using hvr⟩,hpv⟩
  have hnodup := forest_labels_nodup tau K hK
  have hlength : K.length = A.card-1 := by
    have hh := congrArg Finset.card hvertices
    rw [List.toFinset_card_of_nodup hnodup.1,List.length_map,
      Finset.card_erase_of_mem (show root ∈ A from by
        simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]; exact hroot.symm)] at hh
    exact hh
  have hE : E.card = A.card-1 := by
    rw [List.toFinset_card_of_nodup hnodup.2,List.length_map,hlength]
  change _ + (A.card-1) = B.card
  rw [hsupport,← hE,Finset.card_sdiff_add_card_eq_card hsubset]

end NikolovSegal.Equation47ValueNormalization
