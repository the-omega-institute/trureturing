/- GID: D5/S3/FiniteGroups/NikolovSegal/BalancedCrossing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/BalancedCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.List.Count
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NikolovSegal.BalancedCrossing
universe u
variable {V : Type u} [DecidableEq V]
abbrev Word (V : Type u) := List (V × Bool)

def Balanced (W : Word V) : Prop :=
  W.Nodup ∧ ∀ x, W.count (x,false) = W.count (x,true)

def support (W : Word V) : Finset V := (W.map Prod.fst).toFinset

def flip (p : V × Bool) : V × Bool := (p.1,!p.2)

@[simp] theorem flip_flip (p : V × Bool) : flip (flip p) = p := by
  cases p; simp [flip]

theorem balanced_mate {W : Word V} (h : Balanced W) {p : V × Bool}
    (hp : p ∈ W) : flip p ∈ W := by
  rcases p with ⟨x,s⟩
  have hc := h.2 x
  have hp := List.count_pos_iff.mpr hp
  cases s <;> simp only [flip,Bool.not_false,Bool.not_true,Prod.fst,Prod.snd] <;>
    apply List.count_pos_iff.mp <;> omega

theorem balanced_step {W R : Word V} (h : Balanced W)
    (hs : FreeGroup.Red.Step W R) : Balanced R := by
  rcases hs with @⟨A,B,x,s⟩
  refine ⟨h.1.sublist (FreeGroup.Red.Step.sublist FreeGroup.Red.Step.not),?_⟩
  intro y
  have hc := h.2 y
  cases s <;> by_cases he : y = x <;>
    simp [List.count_append,List.count_cons,he] at hc ⊢ <;> omega

theorem balanced_red {W R : Word V} (h : Balanced W)
    (hr : FreeGroup.Red W R) : Balanced R := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact balanced_step ih hs

theorem balanced_of_counts {W : Word V}
    (h : ∀ x s, W.count (x,s) = if x ∈ support W then 1 else 0) : Balanced W := by
  refine ⟨List.nodup_iff_count_le_one.mpr ?_,?_⟩
  · rintro ⟨x,s⟩
    rw [h x s]; split_ifs <;> omega
  · intro x; rw [h x false,h x true]

theorem balanced_count {W : Word V} (h : Balanced W) (x : V) (s : Bool) :
    W.count (x,s) = if x ∈ support W then 1 else 0 := by
  by_cases hx : x ∈ support W
  · rw [if_pos hx]
    apply List.count_eq_one_of_mem h.1
    have hm : ∃ t, (x,t) ∈ W := by
      simpa [support,List.mem_map,Prod.exists] using hx
    obtain ⟨t,ht⟩ := hm
    cases s <;> cases t <;> first | exact ht | simpa [flip] using balanced_mate h ht
  · rw [if_neg hx]
    apply List.count_eq_zero.mpr
    intro hp
    apply hx
    simp only [support,List.mem_toFinset,List.mem_map]
    exact ⟨(x,s),hp,rfl⟩

theorem balanced_length {W : Word V} (h : Balanced W) : W.length = 2 * (support W).card := by
  have he : W.toFinset = (support W) ×ˢ (Finset.univ : Finset Bool) := by
    ext p
    rcases p with ⟨x,s⟩
    simp only [List.mem_toFinset,Finset.mem_product,Finset.mem_univ,and_true]
    rw [← List.count_pos_iff,balanced_count h]
    split_ifs <;> simp_all
  rw [← List.toFinset_card_of_nodup h.1,he,Finset.card_product]
  simp [Nat.mul_comm]

/-- A literal alternating pair, with signs retained in the word itself. -/
def Crossing (W : Word V) : Prop :=
  ∃ (x y : V) (sx sy : Bool) (A B C D E : Word V), x ≠ y ∧
    W = A ++ [(x,!sx)] ++ B ++ [(y,!sy)] ++ C ++ [(x,sx)] ++ D ++ [(y,sy)] ++ E

/-- The genuinely missing combinatorics of Lemma 8.1, first on reduced words. -/
theorem reduced_crossing {W : Word V} (hb : Balanced W)
    (hr : FreeGroup.IsReduced W) (hne : W ≠ []) : Crossing W := by
  classical
  have hex : ∃ n : ℕ, ∃ (A B C : Word V) (x : V) (s : Bool),
      W = A ++ [(x,s)] ++ B ++ [(x,!s)] ++ C ∧ B.length = n := by
    cases W with
    | nil => exact False.elim (hne rfl)
    | cons p T =>
      have hm := balanced_mate hb (List.mem_cons_self)
      have hp : flip p ≠ p := by cases p with | mk x s => cases s <;> simp [flip]
      have ht : flip p ∈ T := (List.mem_cons.mp hm).resolve_left hp
      obtain ⟨B,C,he⟩ := List.mem_iff_append.mp ht
      refine ⟨B.length,[],B,C,p.1,p.2,?_,rfl⟩
      simpa [he,flip,List.append_assoc] using (rfl : p::T = p::T)
  let n := Nat.find hex
  obtain ⟨A,B,C,x,s,hW,hB⟩ := Nat.find_spec hex
  have hmin : ∀ (A' B' C' : Word V) (y : V) (t : Bool),
      W = A' ++ [(y,t)] ++ B' ++ [(y,!t)] ++ C' → n ≤ B'.length := by
    intro A' B' C' y t he
    exact Nat.find_min' hex ⟨A',B',C',y,t,he,rfl⟩
  have hBn : B ≠ [] := by
    intro he
    subst B
    have hs : FreeGroup.Red.Step W (A++C) := by
      rw [hW]; simpa [List.append_assoc] using
        (@FreeGroup.Red.Step.not V A C x s)
    exact hr.not_step hs
  cases B with
  | nil => exact False.elim (hBn rfl)
  | cons p T =>
    have hpW : p ∈ W := by rw [hW]; simp
    have hmate := balanced_mate hb hpW
    have hpKey : p.1 ≠ x := by
      intro he
      rcases p with ⟨y,t⟩
      dsimp at he; subst y
      have hc := List.nodup_iff_count_le_one.mp hb.1 (x,t)
      cases s <;> cases t <;> simp [hW,List.count_append,List.count_cons] at hc <;> omega
    have hnotT : flip p ∉ T := by
      intro hm
      obtain ⟨U,Q,hT⟩ := List.mem_iff_append.mp hm
      have he : W = (A ++ [(x,s)]) ++ [(p.1,p.2)] ++ U ++ [(p.1,!p.2)] ++
          (Q ++ [(x,!s)] ++ C) := by
        rw [hW,hT]; cases p; simp [flip,List.append_assoc]
      have hh := hmin (A++[(x,s)]) U (Q++[(x,!s)]++C) p.1 p.2 he
      have hl : U.length < n := by
        change (p::T).length = n at hB
        rw [hT] at hB
        simp only [List.length_cons,List.length_append] at hB
        omega
      omega
    have hpSelf : flip p ≠ p := by cases p with | mk y t => cases t <;> simp [flip]
    have hmAC : flip p ∈ A ∨ flip p ∈ C := by
      rw [hW] at hmate
      simp only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hmate
      rcases hmate with ((((hA | hx) | (hp | hT)) | hxi) | hC)
      · exact Or.inl hA
      · have := congrArg Prod.fst hx; exact False.elim (hpKey this)
      · exact False.elim (hpSelf hp)
      · exact False.elim (hnotT hT)
      · have := congrArg Prod.fst hxi; exact False.elim (hpKey this)
      · exact Or.inr hC
    rcases hmAC with hmA | hmC
    · obtain ⟨U,Q,hA⟩ := List.mem_iff_append.mp hmA
      refine ⟨p.1,x,p.2,!s,U,Q,[],T,C,hpKey,?_⟩
      rw [hW,hA]; cases p; simp [flip,List.append_assoc]
    · obtain ⟨U,Q,hC⟩ := List.mem_iff_append.mp hmC
      refine ⟨x,p.1,!s,!p.2,A,[],T,U,Q,Ne.symm hpKey,?_⟩
      rw [hW,hC]; cases p; simp [flip,List.append_assoc]

end NikolovSegal.BalancedCrossing
