/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueLinks
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueLinks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueBalance

set_option autoImplicit false

/-! Initial colour bound and the actual links of the normalized VALUE
system, Part I pp.224--225.  Connectivity is that of the permutations being
normalized (sigma^q in the consumer), not the original transitive tuple. -/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
open List
universe u

/-- The paper's colour type: contract consecutive equal NEGATIVE colours,
then forget the signs.  Positive repetitions are not contracted. -/
def colourTypeFrom {m : ℕ} (previous : Option (Fin m)) :
    List (Fin m × Bool) → List (Fin m)
  | [] => []
  | (j,negative)::W =>
    if negative && decide (previous = some j) then colourTypeFrom (some j) W
    else j :: colourTypeFrom (if negative then some j else none) W

def colourType {m : ℕ} (W : List (Fin m × Bool)) : List (Fin m) :=
  colourTypeFrom none W

private theorem colour_state_sublist {m : ℕ} (p : Option (Fin m))
    (W : List (Fin m × Bool)) : colourTypeFrom p W <+ colourType W := by
  cases W with
  | nil => exact List.Sublist.refl _
  | cons l W =>
    rcases l with ⟨j,neg⟩
    cases neg
    · simp [colourType,colourTypeFrom]
    · simp only [colourType,colourTypeFrom,Bool.true_and,decide_eq_true_eq,
        Option.noConfusion,↓reduceIte]
      by_cases hp : p = some j
      · simp only [if_pos hp]
        exact List.Sublist.cons _ (List.Sublist.refl _)
      · simp [hp]

private theorem colour_append {m : ℕ} (A B : List (Fin m × Bool))
    (p : Option (Fin m)) :
    colourTypeFrom p (A++B) <+ colourTypeFrom p A ++ colourType B := by
  induction A generalizing p with
  | nil => exact colour_state_sublist p B
  | cons l A ih =>
    rcases l with ⟨j,neg⟩
    simp only [List.cons_append,colourTypeFrom]
    split
    · exact ih (some j)
    · exact List.Sublist.cons_cons _ (ih (if neg then some j else none))

private theorem negative_run_state {m : ℕ} {A : Type u}
    (j : Fin m) (L : List A) :
    colourTypeFrom (some j) (L.map (fun _ => (j,true))) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons,colourTypeFrom,Bool.true_and,decide_true,↓reduceIte]
    exact ih

private theorem negative_run_bound {m : ℕ} {A : Type u}
    (j : Fin m) (L : List A) :
    colourType (L.map (fun _ => (j,true))) <+ [j] := by
  cases L with
  | nil => exact List.nil_sublist _
  | cons a L =>
    simp only [colourType,List.map_cons,colourTypeFrom,Bool.true_and,
      decide_eq_true_eq,Option.noConfusion,↓reduceIte]
    rw [negative_run_state]
    simp

private theorem blocks_colour_bound {m : ℕ}
    (f : Fin m → List (Fin m × Bool))
    (hf : ∀ j, colourType (f j) <+ [j]) (J : List (Fin m)) :
    colourType (J.flatMap f) <+ J := by
  induction J with
  | nil => exact List.Sublist.refl _
  | cons j J ih =>
    change colourType (f j ++ J.flatMap f) <+ j::J
    exact (colour_append (f j) (J.flatMap f) none).trans ((hf j).append ih)

variable {S I : Type u} [Group S] [Finite I] [DecidableEq I] {m : ℕ}

def wordColours (W : List (Letter (Arc m I) S)) : List (Fin m × Bool) :=
  (signedVariables W).map (fun p => (p.1.1,p.2))

/-- The REAL initial normalized equations satisfy the printed L_1 bound.
All scalar parameters disappear only from the syntactic variable projection;
they remain present in the evaluated words. -/
theorem normalized_initial_colour_bound (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (a : I) :
    colourType (wordColours (normalizedVertexWord tau alpha u a)) <+
      List.ofFn (fun j : Fin m => j) := by
  let f := fun j => wordColours (normalizedFactorWord tau alpha u j a)
  have hf : ∀ j, colourType (f j) <+ [j] := by
    intro j
    dsimp [f,wordColours]
    rw [normalizedFactorWord_variables]
    split
    · simp only [List.map_map]
      exact negative_run_bound j _
    · simp [colourType,colourTypeFrom]
  have h := blocks_colour_bound f hf (List.ofFn (fun j : Fin m => j))
  convert h using 1
  simp [wordColours,normalizedVertexWord,signedVariables,List.map_flatten,
    List.flatMap, List.map_ofFn,List.map_map,f,Function.comp_def]

/-- Actual link graph after substituting cycle bases: a free VALUE is the
edge from its coordinate to its genuine cycle base. -/
noncomputable def valueLinkGraph (tau : Fin m → Equiv.Perm I) : SimpleGraph I where
  Adj v w := v ≠ w ∧ ∃ j, base (tau j) v = w ∨ base (tau j) w = v
  symm := ⟨fun v w h => ⟨h.1.symm,by
    obtain ⟨j,hj⟩ := h.2
    exact ⟨j,hj.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem link_to_base (tau : Fin m → Equiv.Perm I) (j : Fin m) (v : I) :
    (valueLinkGraph tau).Reachable v (base (tau j) v) := by
  by_cases h : v = base (tau j) v
  · rw [← h]
  · exact (show (valueLinkGraph tau).Adj v (base (tau j) v) from
      ⟨h,j,Or.inl rfl⟩).reachable

private theorem link_reachable_same_cycle (tau : Fin m → Equiv.Perm I)
    (j : Fin m) {v w : I} (h : (tau j).SameCycle v w) :
    (valueLinkGraph tau).Reachable v w := by
  have hb : base (tau j) v = base (tau j) w := by
    apply congrArg Quotient.out
    exact Quotient.sound h
  exact (link_to_base tau j v).trans (hb ▸ (link_to_base tau j w).symm)

private theorem perm_reachable_iterate (tau : Fin m → Equiv.Perm I)
    (j : Fin m) (v : I) (n : ℕ) :
    (qPowerGraph tau 1).Reachable v ((tau j)^[n] v) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    apply ih.trans
    by_cases heq : (tau j)^[n] v = tau j ((tau j)^[n] v)
    · rw [← heq]
    · exact (show (qPowerGraph tau 1).Adj ((tau j)^[n] v)
        (tau j ((tau j)^[n] v)) from ⟨heq,j,Or.inl (by simp)⟩).reachable

private theorem perm_reachable_same_cycle (tau : Fin m → Equiv.Perm I)
    (j : Fin m) {v w : I} (h : (tau j).SameCycle v w) :
    (qPowerGraph tau 1).Reachable v w := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hnv : (tau j)^[n] v = w := by simpa only [Equiv.Perm.coe_pow] using hn
  rw [← hnv]
  exact perm_reachable_iterate tau j v n

private theorem reachable_of_adj_reachable {G H : SimpleGraph I}
    (h : ∀ v w, G.Adj v w → H.Reachable v w) {v w : I}
    (hvw : G.Reachable v w) : H.Reachable v w := by
  obtain ⟨p⟩ := hvw
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih => exact (h _ _ hadj).trans ih

/-- The normalized VALUE graph has EXACTLY the true permutation-action
components.  For tau=sigma^q these are powered components; original
transitivity is never used to collapse them. -/
theorem valueLinkGraph_reachable (tau : Fin m → Equiv.Perm I) :
    (valueLinkGraph tau).Reachable = (qPowerGraph tau 1).Reachable := by
  funext v w
  apply propext
  constructor
  · apply reachable_of_adj_reachable
    intro a b h
    obtain ⟨j,hj | hj⟩ := h.2
    · apply perm_reachable_same_cycle tau j
      rw [← hj]
      exact (show (tau j).SameCycle (base (tau j) a) a from
        Quotient.exact (Quotient.out_eq (cycleClass (tau j) a))).symm
    · apply perm_reachable_same_cycle tau j
      rw [← hj]
      exact Quotient.exact (Quotient.out_eq (cycleClass (tau j) b))
  · apply reachable_of_adj_reachable
    intro a b h
    obtain ⟨j,hj | hj⟩ := h.2
    · apply link_reachable_same_cycle tau j
      rw [pow_one] at hj
      rw [← hj]
      exact (Equiv.Perm.SameCycle.refl _ _).apply_right
    · apply link_reachable_same_cycle tau j
      rw [pow_one] at hj
      rw [← hj]
      exact (Equiv.Perm.SameCycle.refl _ _).apply_left

/-- The actual stars admit a spanning forest in EACH true component, with
the same components as the corrected action's permutations. -/
theorem valueLinkGraph_spanningForest [Fintype I]
    (tau : Fin m → Equiv.Perm I) :
    ∃ F : SimpleGraph I, F ≤ valueLinkGraph tau ∧ F.IsAcyclic ∧
      F.Reachable = (qPowerGraph tau 1).Reachable := by
  obtain ⟨F,hF,hacyc,hreach⟩ := (valueLinkGraph tau).exists_isAcyclic_reachable_eq_le
  exact ⟨F,hF,hacyc,hreach.trans (valueLinkGraph_reachable tau)⟩

end NikolovSegal.Equation47ValueNormalization
