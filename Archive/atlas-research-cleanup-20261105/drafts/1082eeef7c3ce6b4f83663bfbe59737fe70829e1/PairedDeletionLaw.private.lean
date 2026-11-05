import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Permutation
/- Exact fibres of two labelled deletions on fixed-support oriented cycles.
   The quotient identifies rotations and preserves orientation. The classification
   applies to support size at least three, including the at-least-four range. -/

import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

universe u
variable {α : Type u} [DecidableEq α]

private theorem mem_support (C : Cycle α) (x : α) :
    x ∈ C.toFinset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with
  | _ l => exact List.mem_toFinset

private theorem rooted {C : Cycle α} {r : α} (hr : r ∈ C) :
    ∃ L : List α, C = (r :: L : List α) := by
  induction C using Quotient.inductionOn with
  | _ W =>
    obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp (Cycle.mem_coe_iff.mp hr)
    refine ⟨Q ++ P, Cycle.coe_eq_coe.mpr ⟨P.length, ?_⟩⟩
    simpa only [List.cons_append] using List.rotate_append_length_eq P (r :: Q)

def erase (x : α) (L : List α) : List α :=
  L.filter (fun y => decide (y ≠ x))

private theorem erase_eq_self {x : α} {L : List α} (hx : x ∉ L) :
    erase x L = L := by
  unfold erase
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  intro h
  exact hx (h ▸ hy)

private theorem erase_cons (x y : α) (L : List α) :
    erase x (y :: L) = if y = x then erase x L else y :: erase x L := by
  by_cases h : y = x <;> simp [erase, h]

private theorem opposite_tails
    {L K : List α} {a b : α}
    (hL : (a :: L).Nodup) (hK : (b :: K).Nodup) (hab : a ≠ b)
    (hA : erase a (a :: L) = erase a (b :: K))
    (hB : erase b (a :: L) = erase b (b :: K)) :
    ∃ R : List α, L = b :: R ∧ K = a :: R := by
  have haL : a ∉ L := (List.nodup_cons.mp hL).1
  have hbK : b ∉ K := (List.nodup_cons.mp hK).1
  have hfirst : L = b :: erase a K := by
    rw [erase_cons, if_pos rfl, erase_eq_self haL,
      erase_cons, if_neg (Ne.symm hab)] at hA
    exact hA
  let R : List α := erase a K
  have hLR : L = b :: R := hfirst
  have hbR : b ∉ R := by
    have hn : (b :: R).Nodup := hLR ▸ (List.nodup_cons.mp hL).2
    exact (List.nodup_cons.mp hn).1
  have hsecond : a :: erase b L = K := by
    rw [erase_cons, if_neg hab, erase_cons, if_pos rfl, erase_eq_self hbK] at hB
    exact hB
  have hLerase : erase b L = R := by
    rw [hLR, erase_cons, if_pos rfl, erase_eq_self hbR]
  have hKR : K = a :: R := by
    rw [hLerase] at hsecond
    exact hsecond.symm
  exact ⟨R, hLR, hKR⟩

/- The two possible rooted words obtained by swapping an adjacent a,b pair. -/
def adjacentSwapAt (r a b : α) (C D : Cycle α) : Prop :=
  ∃ P Q : List α,
    (C = (r :: P ++ [a,b] ++ Q : List α) ∧
      D = (r :: P ++ [b,a] ++ Q : List α)) ∨
    (C = (r :: P ++ [b,a] ++ Q : List α) ∧
      D = (r :: P ++ [a,b] ++ Q : List α))

/- Cyclic adjacency of the deleted labels in one rooted representative. -/
def cyclicAdjacentAt (r a b : α) (C : Cycle α) : Prop :=
  ∃ P Q : List α,
    C = (r :: P ++ [a,b] ++ Q : List α) ∨
    C = (r :: P ++ [b,a] ++ Q : List α)

private theorem adjacent_perm_forward {r a b : α} {P Q : List α} :
    (r :: P ++ [a,b] ++ Q).Perm (r :: P ++ [b,a] ++ Q) := by
  have h := (List.Perm.swap b a Q).append_left P
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h.cons r

private theorem adjacent_perm_reverse {r a b : α} {P Q : List α} :
    (r :: P ++ [b,a] ++ Q).Perm (r :: P ++ [a,b] ++ Q) := by
  simpa using
    (adjacent_perm_forward (r := r) (a := b) (b := a) (P := P) (Q := Q))

private theorem adjacent_swap_delete_forward
    {r a b : α} {P Q : List α} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b) :
    delete a (r :: P ++ [a,b] ++ Q : Cycle α) =
        delete a (r :: P ++ [b,a] ++ Q : Cycle α) ∧
    delete b (r :: P ++ [a,b] ++ Q : Cycle α) =
        delete b (r :: P ++ [b,a] ++ Q : Cycle α) := by
  constructor
  · change (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α) =
      (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α)
    simp [erase, hra, hrb, hab, Ne.symm hab]
  · change (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α) =
      (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α)
    simp [erase, hra, hrb, hab, Ne.symm hab]

private theorem adjacent_swap_delete_reverse
    {r a b : α} {P Q : List α} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b) :
    delete a (r :: P ++ [b,a] ++ Q : Cycle α) =
        delete a (r :: P ++ [a,b] ++ Q : Cycle α) ∧
    delete b (r :: P ++ [b,a] ++ Q : Cycle α) =
        delete b (r :: P ++ [a,b] ++ Q : Cycle α) := by
  simpa [and_comm] using
    (adjacent_swap_delete_forward (r := r) (a := b) (b := a) (P := P) (Q := Q)
      hrb hra hab.symm)

private theorem adjacent_swap_ne_forward
    {r a b : α} {P Q : List α} (hab : a ≠ b)
    (hN : (r :: P ++ [a,b] ++ Q).Nodup) :
    (r :: P ++ [b,a] ++ Q : Cycle α) ≠ (r :: P ++ [a,b] ++ Q : Cycle α) := by
  intro h
  have ht := anchored_coe_injective hN h.symm
  have hblock : [a,b] ++ Q = [b,a] ++ Q := by
    simpa [List.append_assoc] using congrArg (List.drop P.length) ht
  have hab' : a = b := by
    simpa using congrArg List.head? hblock
  exact hab hab'

private theorem adjacent_swap_ne_reverse
    {r a b : α} {P Q : List α} (hab : a ≠ b)
    (hN : (r :: P ++ [b,a] ++ Q).Nodup) :
    (r :: P ++ [a,b] ++ Q : Cycle α) ≠ (r :: P ++ [b,a] ++ Q : Cycle α) := by
  exact adjacent_swap_ne_forward hab.symm hN

/-
  The central list classification.  The proof follows the first-list
  structural split.  Equality of an erasure preserves a head outside the
  erased pair; equal heads recurse on the tails.  Equal a/b heads are fixed by
  the other erasure and nodup.  Opposite heads force the displayed adjacent
  block by the two erasure equations.
-/
theorem erase_pair_classification
    {L K : List α} {a b : α}
    (hL : L.Nodup) (hK : K.Nodup)
    (haL : a ∈ L) (hbL : b ∈ L)
    (haK : a ∈ K) (hbK : b ∈ K) (hab : a ≠ b)
    (hA : erase a L = erase a K)
    (hB : erase b L = erase b K) :
    L = K ∨ ∃ P Q : List α,
      (L = P ++ [a,b] ++ Q ∧ K = P ++ [b,a] ++ Q) ∨
      (L = P ++ [b,a] ++ Q ∧ K = P ++ [a,b] ++ Q) := by
  induction L generalizing K with
  | nil => exact False.elim (by simpa using haL)
  | cons x L ih =>
    cases K with
    | nil => exact False.elim (by simpa using haK)
    | cons y K =>
      have hL' : (x :: L).Nodup := hL
      have hK' : (y :: K).Nodup := hK
      by_cases hxa : x = a
      · subst x
        by_cases hya : y = a
        · subst y
          have haL' : a ∉ L := (List.nodup_cons.mp hL').1
          have haK' : a ∉ K := (List.nodup_cons.mp hK').1
          have htail : erase a L = erase a K := by
            simpa [erase] using hA
          have hLK : L = K := by
            simpa [erase_eq_self haL', erase_eq_self haK'] using htail
          exact Or.inl (by simpa [hLK])
        · by_cases hyb : y = b
          · subst y
            obtain ⟨R, hLR, hKR⟩ := opposite_tails hL' hK' hab hA hB
            exact Or.inr ⟨[], R, Or.inl ⟨by simpa [hLR], by simpa [hKR]⟩⟩
          · have hhead : a = y := by
              have h := hB
              simp only [erase, List.filter_cons, decide_eq_true hab,
                decide_eq_true hyb, ↓reduceIte] at h
              have hh := congrArg List.head? h
              simpa using hh
            exact (hya hhead.symm).elim
      · by_cases hxb : x = b
        · subst x
          by_cases hya : y = a
          · subst y
            obtain ⟨R, hLR, hKR⟩ := opposite_tails hL' hK' hab.symm hB hA
            exact Or.inr ⟨[], R, Or.inr ⟨by simpa [hLR], by simpa [hKR]⟩⟩
          · by_cases hyb : y = b
            · subst y
              have hbL' : b ∉ L := (List.nodup_cons.mp hL').1
              have hbK' : b ∉ K := (List.nodup_cons.mp hK').1
              have htail : erase b L = erase b K := by
                simpa [erase] using hB
              have hLK : L = K := by
                simpa [erase_eq_self hbL', erase_eq_self hbK'] using htail
              exact Or.inl (by simpa [hLK])
            · have hhead : b = y := by
                have h := hA
                simp only [erase, List.filter_cons, decide_eq_true (Ne.symm hab),
                  decide_eq_true hya, ↓reduceIte] at h
                have hh := congrArg List.head? h
                simpa using hh
              exact (hyb hhead.symm).elim
        · by_cases hya : y = a
          · subst y
            have hhead : x = a := by
              have h := hB
              simp only [erase, List.filter_cons, decide_eq_true hxb,
                decide_eq_true hab, ↓reduceIte] at h
              have hh := congrArg List.head? h
              simpa using hh
            exact (hxa hhead).elim
          · by_cases hyb : y = b
            · subst y
              have hhead : x = b := by
                have h := hA
                simp only [erase, List.filter_cons, decide_eq_true hxa,
                  decide_eq_true (Ne.symm hab), ↓reduceIte] at h
                have hh := congrArg List.head? h
                simpa using hh
              exact (hxb hhead).elim
            · have hheadA : x :: erase a L = y :: erase a K := by
                simpa [erase, hxa, hya] using hA
              have hheadB : x :: erase b L = y :: erase b K := by
                simpa [erase, hxb, hyb] using hB
              have hxy : x = y := by
                have hh := congrArg List.head? hheadA
                simpa using hh
              subst y
              have hAtail : erase a L = erase a K :=
                (List.cons.inj hheadA).2
              have hBtail : erase b L = erase b K :=
                (List.cons.inj hheadB).2
              have haLt : a ∈ L := by simpa [Ne.symm hxa] using haL
              have hbLt : b ∈ L := by simpa [Ne.symm hxb] using hbL
              have haKt : a ∈ K := by simpa [Ne.symm hxa] using haK
              have hbKt : b ∈ K := by simpa [Ne.symm hxb] using hbK
              rcases ih hL.tail hK.tail haLt hbLt haKt hbKt hAtail hBtail with
                hEq | ⟨P, Q, hSwap⟩
              · exact Or.inl (by simpa [hEq])
              · rcases hSwap with hSwap | hSwap
                · exact Or.inr ⟨x :: P, Q, Or.inl ⟨
                    by simpa [List.cons_append] using congrArg (List.cons x) hSwap.1,
                    by simpa [List.cons_append] using congrArg (List.cons x) hSwap.2⟩⟩
                · exact Or.inr ⟨x :: P, Q, Or.inr ⟨
                    by simpa [List.cons_append] using congrArg (List.cons x) hSwap.1,
                    by simpa [List.cons_append] using congrArg (List.cons x) hSwap.2⟩⟩

private theorem map_swap_fixed {a b : α} {W : List α}
    (hW : ∀ x ∈ W, x ≠ a ∧ x ≠ b) :
    W.map (Equiv.swap a b) = W := by
  induction W with
  | nil => rfl
  | cons x W ih =>
    have hx := hW x (by simp)
    have htail : ∀ y ∈ W, y ≠ a ∧ y ≠ b := by
      intro y hy
      exact hW y (by simp [hy])
    simp only [List.map_cons]
    rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2, ih htail]

private theorem map_adjacent_forward
    {r a b : α} {P Q : List α} (hra : r ≠ a) (hrb : r ≠ b)
    (hab : a ≠ b) (hN : (r :: P ++ [a,b] ++ Q).Nodup) :
    (r :: P ++ [b,a] ++ Q : Cycle α) =
      Cycle.map (Equiv.swap a b) (r :: P ++ [a,b] ++ Q : Cycle α) := by
  have htail : (P ++ [a,b] ++ Q).Nodup := (List.nodup_cons.mp hN).2
  have htail' : (P ++ ([a,b] ++ Q)).Nodup := by
    simpa [List.append_assoc] using htail
  have hparts := List.nodup_append'.mp htail'
  have hblock := List.nodup_append'.mp hparts.2.1
  have hP : ∀ x ∈ P, x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro hxa
      subst x
      exact (List.disjoint_iff_ne.mp hparts.2.2) _ hx a (by simp) rfl
    · intro hxb
      subst x
      exact (List.disjoint_iff_ne.mp hparts.2.2) _ hx b (by simp) rfl
  have hQ : ∀ x ∈ Q, x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro hxa
      subst x
      exact (List.disjoint_iff_ne.mp hblock.2.2) a (by simp) _ hx rfl
    · intro hxb
      subst x
      exact (List.disjoint_iff_ne.mp hblock.2.2) b (by simp) _ hx rfl
  change (r :: P ++ [b,a] ++ Q : Cycle α) =
    Cycle.map (Equiv.swap a b) (r :: P ++ [a,b] ++ Q : Cycle α)
  rw [Cycle.map_coe]
  simp only [List.map_cons, List.map_append, List.map_nil]
  rw [Equiv.swap_apply_of_ne_of_ne hra hrb, map_swap_fixed hP]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [map_swap_fixed hQ]

private theorem map_adjacent_reverse
    {r a b : α} {P Q : List α} (hra : r ≠ a) (hrb : r ≠ b)
    (hab : a ≠ b) (hN : (r :: P ++ [b,a] ++ Q).Nodup) :
    (r :: P ++ [a,b] ++ Q : Cycle α) =
      Cycle.map (Equiv.swap a b) (r :: P ++ [b,a] ++ Q : Cycle α) := by
  have h := map_adjacent_forward (r := r) (a := b) (b := a) (P := P) (Q := Q)
    hrb hra hab.symm hN
  simpa [Equiv.swap_comm] using h

/- The nontrivial rooted swap is unique for one fixed nodup source. -/
theorem adjacentSwapAt_unique
    {r a b : α} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    {C D E : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup) (hE : E.Nodup)
    (hCD : adjacentSwapAt r a b C D)
    (hCE : adjacentSwapAt r a b C E) : D = E := by
  rcases hCD with ⟨P, Q, hCD | hCD⟩
  · have hN : (r :: P ++ [a,b] ++ Q).Nodup := by
      apply Cycle.nodup_coe_iff.mp
      rw [← hCD.1]
      exact hC
    have hmapD : D = Cycle.map (Equiv.swap a b) C := by
      calc
        D = (r :: P ++ [b,a] ++ Q : List α) := hCD.2
        _ = Cycle.map (Equiv.swap a b) (r :: P ++ [a,b] ++ Q : List α) :=
          map_adjacent_forward hra hrb hab hN
        _ = Cycle.map (Equiv.swap a b) C := by rw [hCD.1]
    rcases hCE with ⟨P', Q', hCE | hCE⟩
    · have hN' : (r :: P' ++ [a,b] ++ Q').Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCE.1]
        exact hC
      have hmapE : E = Cycle.map (Equiv.swap a b) C := by
        calc
          E = (r :: P' ++ [b,a] ++ Q' : List α) := hCE.2
          _ = Cycle.map (Equiv.swap a b) (r :: P' ++ [a,b] ++ Q' : List α) :=
            map_adjacent_forward hra hrb hab hN'
          _ = Cycle.map (Equiv.swap a b) C := by rw [hCE.1]
      exact hmapD.trans hmapE.symm
    · have hN' : (r :: P' ++ [b,a] ++ Q').Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCE.1]
        exact hC
      have hmapE : E = Cycle.map (Equiv.swap a b) C := by
        calc
          E = (r :: P' ++ [a,b] ++ Q' : List α) := hCE.2
          _ = Cycle.map (Equiv.swap a b) (r :: P' ++ [b,a] ++ Q' : List α) :=
            map_adjacent_reverse hra hrb hab hN'
          _ = Cycle.map (Equiv.swap a b) C := by rw [hCE.1]
      exact hmapD.trans hmapE.symm
  · have hN : (r :: P ++ [b,a] ++ Q).Nodup := by
      apply Cycle.nodup_coe_iff.mp
      rw [← hCD.1]
      exact hC
    have hmapD : D = Cycle.map (Equiv.swap a b) C := by
      calc
        D = (r :: P ++ [a,b] ++ Q : List α) := hCD.2
        _ = Cycle.map (Equiv.swap a b) (r :: P ++ [b,a] ++ Q : List α) :=
          map_adjacent_reverse hra hrb hab hN
        _ = Cycle.map (Equiv.swap a b) C := by rw [hCD.1]
    rcases hCE with ⟨P', Q', hCE | hCE⟩
    · have hN' : (r :: P' ++ [a,b] ++ Q').Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCE.1]
        exact hC
      have hmapE : E = Cycle.map (Equiv.swap a b) C := by
        calc
          E = (r :: P' ++ [b,a] ++ Q' : List α) := hCE.2
          _ = Cycle.map (Equiv.swap a b) (r :: P' ++ [a,b] ++ Q' : List α) :=
            map_adjacent_forward hra hrb hab hN'
          _ = Cycle.map (Equiv.swap a b) C := by rw [hCE.1]
      exact hmapD.trans hmapE.symm
    · have hN' : (r :: P' ++ [b,a] ++ Q').Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCE.1]
        exact hC
      have hmapE : E = Cycle.map (Equiv.swap a b) C := by
        calc
          E = (r :: P' ++ [a,b] ++ Q' : List α) := hCE.2
          _ = Cycle.map (Equiv.swap a b) (r :: P' ++ [b,a] ++ Q' : List α) :=
            map_adjacent_reverse hra hrb hab hN'
          _ = Cycle.map (Equiv.swap a b) C := by rw [hCE.1]
      exact hmapD.trans hmapE.symm

/- Exact two-deletion classification after fixing a root outside the pair. -/
theorem paired_fiber_iff_at_root
    {A : Finset α} {r a b : α}
    (hrA : r ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    {C D : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) :
    (delete a C = delete a D ∧ delete b C = delete b D) ↔
      C = D ∨ adjacentSwapAt r a b C D := by
  obtain ⟨L, hCL⟩ := rooted ((mem_support C r).mp (sC.symm ▸ hrA))
  obtain ⟨K, hDK⟩ := rooted ((mem_support D r).mp (sD.symm ▸ hrA))
  subst C
  subst D
  have hnL : (r :: L).Nodup := Cycle.nodup_coe_iff.mp hC
  have hnK : (r :: K).Nodup := Cycle.nodup_coe_iff.mp hD
  have haL : a ∈ L := by
    have hfin : a ∈ (r :: L : Cycle α).toFinset := by simpa [sC] using ha
    have h := (mem_support (r :: L : Cycle α) a).mp hfin
    simpa [Ne.symm hra] using h
  have hbL : b ∈ L := by
    have hfin : b ∈ (r :: L : Cycle α).toFinset := by simpa [sC] using hb
    have h := (mem_support (r :: L : Cycle α) b).mp hfin
    simpa [Ne.symm hrb] using h
  have haK : a ∈ K := by
    have hfin : a ∈ (r :: K : Cycle α).toFinset := by simpa [sD] using ha
    have h := (mem_support (r :: K : Cycle α) a).mp hfin
    simpa [Ne.symm hra] using h
  have hbK : b ∈ K := by
    have hfin : b ∈ (r :: K : Cycle α).toFinset := by simpa [sD] using hb
    have h := (mem_support (r :: K : Cycle α) b).mp hfin
    simpa [Ne.symm hrb] using h
  constructor
  · rintro ⟨hA, hB⟩
    have hna : (r :: erase a L).Nodup := by
      simpa [erase, hra] using (hnL.filter (fun y => decide (y ≠ a)))
    have hnb : (r :: erase b L).Nodup := by
      simpa [erase, hrb] using (hnL.filter (fun y => decide (y ≠ b)))
    have hnaK : (r :: erase a K).Nodup := by
      simpa [erase, hra] using (hnK.filter (fun y => decide (y ≠ a)))
    have hnbK : (r :: erase b K).Nodup := by
      simpa [erase, hrb] using (hnK.filter (fun y => decide (y ≠ b)))
    have hA' : (r :: erase a L : Cycle α) = (r :: erase a K : Cycle α) := by
      change (((r :: L).filter (fun y => decide (y ≠ a))) : Cycle α) =
        (((r :: K).filter (fun y => decide (y ≠ a))) : Cycle α) at hA
      simpa only [erase, List.filter_cons, decide_eq_true hra, ↓reduceIte] using hA
    have hB' : (r :: erase b L : Cycle α) = (r :: erase b K : Cycle α) := by
      change (((r :: L).filter (fun y => decide (y ≠ b))) : Cycle α) =
        (((r :: K).filter (fun y => decide (y ≠ b))) : Cycle α) at hB
      simpa only [erase, List.filter_cons, decide_eq_true hrb, ↓reduceIte] using hB
    have hEraseA := anchored_coe_injective hna hA'
    have hEraseB := anchored_coe_injective hnb hB'
    rcases erase_pair_classification (L := L) (K := K) hnL.tail hnK.tail
      haL hbL haK hbK hab hEraseA hEraseB with hEq | ⟨P, Q, hSwap⟩
    · exact Or.inl (by simpa [hEq])
    · exact Or.inr ⟨P, Q, by
        rcases hSwap with h | h
        · left
          exact ⟨by simpa [List.cons_append] using congrArg (fun l : List α => (r :: l : Cycle α)) h.1,
            by simpa [List.cons_append] using congrArg (fun l : List α => (r :: l : Cycle α)) h.2⟩
        · right
          exact ⟨by simpa [List.cons_append] using congrArg (fun l : List α => (r :: l : Cycle α)) h.1,
            by simpa [List.cons_append] using congrArg (fun l : List α => (r :: l : Cycle α)) h.2⟩⟩
  · intro h
    rcases h with hEq | hSwap
    · exact ⟨congrArg (delete a) hEq, congrArg (delete b) hEq⟩
    · rcases hSwap with ⟨P, Q, hForms⟩
      rcases hForms with hForms | hForms
      · have hObs := adjacent_swap_delete_forward hra hrb hab (P := P) (Q := Q)
        simpa only [hForms.1, hForms.2] using hObs
      · have hObs := adjacent_swap_delete_reverse hra hrb hab (P := P) (Q := Q)
        simpa only [hForms.1, hForms.2] using hObs

/- The existential-root form of the classification. -/
theorem paired_fiber_iff
    {A : Finset α} (hA : 3 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C D : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) :
    (delete a C = delete a D ∧ delete b C = delete b D) ↔
      C = D ∨ ∃ r ∈ A, r ≠ a ∧ r ≠ b ∧ adjacentSwapAt r a b C D := by
  have hex : ∃ r ∈ A, r ∉ ({a,b} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({a,b} : Finset α) := by
      intro r hr
      by_contra hr'
      exact hn ⟨r, hr, hr'⟩
    have hc := Finset.card_le_card hs
    have ht : ({a,b} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  constructor
  · intro h
    obtain ⟨r, hrA, hr⟩ := hex
    have hroot := (paired_fiber_iff_at_root hrA ha hb (by
      intro e; exact hr (by simp [e])) (by
      intro e; exact hr (by simp [e])) hab hC hD sC sD).mp h
    rcases hroot with hEq | hSwap
    · exact Or.inl hEq
    · exact Or.inr ⟨r, hrA, by intro e; exact hr (by simp [e]),
        by intro e; exact hr (by simp [e]), hSwap⟩
  · intro h
    rcases h with hEq | ⟨r, hrA, hra, hrb, hSwap⟩
    · subst D
      exact ⟨rfl, rfl⟩
    · exact (paired_fiber_iff_at_root hrA ha hb hra hrb hab hC hD sC sD).mpr
        (Or.inr hSwap)

/- Any two non-central members of one fixed pair fibre are equal. -/
theorem pair_fiber_at_most_two
    {A : Finset α} (hA : 3 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C D E : Cycle α}
    (hC : C.Nodup) (hD : D.Nodup) (hE : E.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A) (sE : E.toFinset = A)
    (hDobs : delete a C = delete a D ∧ delete b C = delete b D)
    (hEobs : delete a C = delete a E ∧ delete b C = delete b E)
    (hDC : D ≠ C) (hEC : E ≠ C) : D = E := by
  obtain ⟨r, hrA, hr⟩ : ∃ r ∈ A, r ∉ ({a,b} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({a,b} : Finset α) := by
      intro r hrA
      by_contra hr'
      exact hn ⟨r, hrA, hr'⟩
    have hc := Finset.card_le_card hs
    have ht : ({a,b} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have hra : r ≠ a := by intro e; exact hr (by simp [e])
  have hrb : r ≠ b := by intro e; exact hr (by simp [e])
  have hCD := (paired_fiber_iff_at_root hrA ha hb hra hrb hab hC hD sC sD).mp hDobs
  have hCE := (paired_fiber_iff_at_root hrA ha hb hra hrb hab hC hE sC sE).mp hEobs
  rcases hCD with hEq | hCD
  · exact (hDC hEq.symm).elim
  rcases hCE with hEq | hCE
  · exact (hEC hEq.symm).elim
  exact adjacentSwapAt_unique hra hrb hab hC hD hE hCD hCE

/- Exact existence of a nontrivial alternative: precisely cyclic adjacency. -/
theorem exists_nontrivial_alternative_iff_cyclicAdjacent
    {A : Finset α} (hA : 3 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {C : Cycle α} (hC : C.Nodup) (sC : C.toFinset = A) :
    (∃ D : Cycle α, D.Nodup ∧ D.toFinset = A ∧ D ≠ C ∧
      delete a C = delete a D ∧ delete b C = delete b D) ↔
      ∃ r ∈ A, r ≠ a ∧ r ≠ b ∧ cyclicAdjacentAt r a b C := by
  have hex : ∃ r ∈ A, r ∉ ({a,b} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({a,b} : Finset α) := by
      intro r hr
      by_contra hr'
      exact hn ⟨r, hr, hr'⟩
    have hc := Finset.card_le_card hs
    have ht : ({a,b} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  constructor
  · rintro ⟨D, hD, sD, hDC, hAobs, hBobs⟩
    obtain ⟨r, hrA, hr⟩ := hex
    have hroot := (paired_fiber_iff_at_root hrA ha hb (by
      intro e; exact hr (by simp [e])) (by
      intro e; exact hr (by simp [e])) hab hC hD sC sD).mp
      ⟨hAobs, hBobs⟩
    rcases hroot with hEq | hSwap
    · exact (hDC hEq.symm).elim
    · rcases hSwap with ⟨P, Q, hForms⟩
      rcases hForms with h | h
      · exact ⟨r, hrA, by intro e; exact hr (by simp [e]),
          by intro e; exact hr (by simp [e]), ⟨P, Q, Or.inl h.1⟩⟩
      · exact ⟨r, hrA, by intro e; exact hr (by simp [e]),
          by intro e; exact hr (by simp [e]), ⟨P, Q, Or.inr h.1⟩⟩
  · rintro ⟨r, hrA, hra, hrb, hAdj⟩
    rcases hAdj with ⟨P, Q, hCform | hCform⟩
    · let D : Cycle α := (r :: P ++ [b,a] ++ Q : List α)
      have hSrcN : (r :: P ++ [a,b] ++ Q).Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCform]
        exact hC
      have hDstN : D.Nodup := by
        apply Cycle.nodup_coe_iff.mpr
        exact (adjacent_perm_forward (r := r) (a := a) (b := b)
          (P := P) (Q := Q)).nodup_iff.mp hSrcN
      have hDstS : D.toFinset = A := by
        change (r :: P ++ [b,a] ++ Q : List α).toFinset = A
        rw [hCform] at sC
        exact (List.toFinset_eq_of_perm _ _
          (adjacent_perm_forward (r := r) (a := a) (b := b) (P := P) (Q := Q))).symm.trans sC
      have hObs := adjacent_swap_delete_forward hra hrb hab (P := P) (Q := Q)
      have hNe : D ≠ C := by
        intro h
        apply adjacent_swap_ne_forward hab hSrcN
        exact h.trans hCform
      exact ⟨D, hDstN, hDstS, hNe, by simpa only [hCform] using hObs.1,
        by simpa only [hCform] using hObs.2⟩
    · let D : Cycle α := (r :: P ++ [a,b] ++ Q : List α)
      have hSrcN : (r :: P ++ [b,a] ++ Q).Nodup := by
        apply Cycle.nodup_coe_iff.mp
        rw [← hCform]
        exact hC
      have hDstN : D.Nodup := by
        apply Cycle.nodup_coe_iff.mpr
        exact (adjacent_perm_reverse (r := r) (a := a) (b := b)
          (P := P) (Q := Q)).nodup_iff.mp hSrcN
      have hDstS : D.toFinset = A := by
        change (r :: P ++ [a,b] ++ Q : List α).toFinset = A
        rw [hCform] at sC
        exact (List.toFinset_eq_of_perm _ _
          (adjacent_perm_reverse (r := r) (a := a) (b := b) (P := P) (Q := Q))).symm.trans sC
      have hObs := adjacent_swap_delete_reverse hra hrb hab (P := P) (Q := Q)
      have hNe : D ≠ C := by
        intro h
        apply adjacent_swap_ne_reverse hab hSrcN
        exact h.trans hCform
      exact ⟨D, hDstN, hDstS, hNe, by simpa only [hCform] using hObs.1,
        by simpa only [hCform] using hObs.2⟩

end D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionLaw

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
open scoped BigOperators

universe u v
variable {α : Type u} [DecidableEq α]

/-- The complete carrier of nodup oriented cycles on the fixed support. -/
abbrev FixedCycles (A : Finset α) := {C : Cycle α // C.Nodup ∧ C.toFinset = A}

/-- Each paired channel observes two deletions of the same original. -/
def paired (a b : α) (C : Cycle α) : Cycle α × Cycle α :=
  (delete a C, delete b C)

private theorem block_positions {x y : α} {P Q : List α}
    (h : (P ++ [x,y] ++ Q).Nodup) (hxy : x ≠ y) :
    (P ++ [x,y] ++ Q).idxOf x = P.length ∧
    (P ++ [x,y] ++ Q).idxOf y = P.length + 1 := by
  have hd := (List.nodup_append'.mp (show (P ++ ([x,y] ++ Q)).Nodup by
    simpa only [List.append_assoc] using h)).2.2
  have hx : x ∉ P := by
    intro hx
    exact (List.disjoint_iff_ne.mp hd) x hx x (by simp) rfl
  have hy : y ∉ P := by
    intro hy
    exact (List.disjoint_iff_ne.mp hd) y hy y (by simp) rfl
  constructor <;>
    simp [List.append_assoc, List.idxOf_append_of_notMem hx,
      List.idxOf_append_of_notMem hy, hxy]

private theorem adjacent_positions {r x y : α} {W : List α}
    (hW : (r :: W).Nodup) (hxy : x ≠ y)
    (h : cyclicAdjacentAt r x y (r :: W : Cycle α)) :
    W.idxOf x + 1 = W.idxOf y ∨ W.idxOf y + 1 = W.idxOf x := by
  rcases h with ⟨P,Q,h | h⟩
  · have he := anchored_coe_injective hW h
    have ht : W = P ++ [x,y] ++ Q := by simpa only [List.append_eq, List.append_assoc] using he
    rw [ht]
    have hn : (P ++ [x,y] ++ Q).Nodup := ht ▸ hW.tail
    have hp := block_positions hn hxy
    exact Or.inl (by omega)
  · have he := anchored_coe_injective hW h
    have ht : W = P ++ [y,x] ++ Q := by simpa only [List.append_eq, List.append_assoc] using he
    rw [ht]
    have hn : (P ++ [y,x] ++ Q).Nodup := ht ▸ hW.tail
    have hp := block_positions hn hxy.symm
    exact Or.inr (by omega)

private theorem third_position {a b c : α} {P Q : List α}
    (hac : a ≠ c) (hbc : b ≠ c) :
    (P ++ [a,b] ++ Q).idxOf c = (P ++ [b,a] ++ Q).idxOf c := by
  by_cases hc : c ∈ P
  · simp only [List.append_assoc, List.idxOf_append_of_mem hc]
  · simp [List.append_assoc, List.idxOf_append_of_notMem hc, hac, hbc]

/-- With a common cut outside the three labels, a nontrivial a,b swap
cannot have a nontrivial b,c fibre at both ends. The fourth label supplies
that cut, so the argument includes wrap-around and support size four. -/
theorem swap_has_leaf {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {C D E H : Cycle α}
    (nC : C.Nodup) (nD : D.Nodup) (nE : E.Nodup) (nH : H.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A)
    (sE : E.toFinset = A) (sH : H.toFinset = A)
    (hCD : paired a b C = paired a b D) (hDC : D ≠ C)
    (hCE : paired b c C = paired b c E) (hEC : E ≠ C)
    (hDH : paired b c D = paired b c H) (hHD : H ≠ D) : False := by
  obtain ⟨r,hrA,hr⟩ : ∃ r ∈ A, r ∉ ({a,b,c} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({a,b,c} : Finset α) := by
      intro r hrA
      by_contra hr
      exact hn ⟨r,hrA,hr⟩
    have := Finset.card_le_card hs
    have : ({a,b,c} : Finset α).card ≤ 3 := Finset.card_le_three
    omega
  have hra : r ≠ a := by intro h; exact hr (by simp [h])
  have hrb : r ≠ b := by intro h; exact hr (by simp [h])
  have hrc : r ≠ c := by intro h; exact hr (by simp [h])
  have ab := (paired_fiber_iff_at_root hrA ha hb hra hrb hab nC nD sC sD).mp
    (Prod.mk.inj hCD)
  have bcC := (paired_fiber_iff_at_root hrA hb hc hrb hrc hbc nC nE sC sE).mp
    (Prod.mk.inj hCE)
  have bcD := (paired_fiber_iff_at_root hrA hb hc hrb hrc hbc nD nH sD sH).mp
    (Prod.mk.inj hDH)
  rcases ab with he | hs
  · exact hDC he.symm
  rcases bcC with he | hsC
  · exact hEC he.symm
  rcases bcD with he | hsD
  · exact hHD he.symm
  have adjC : cyclicAdjacentAt r b c C := by
    rcases hsC with ⟨P,Q,h | h⟩
    · exact ⟨P,Q,Or.inl h.1⟩
    · exact ⟨P,Q,Or.inr h.1⟩
  have adjD : cyclicAdjacentAt r b c D := by
    rcases hsD with ⟨P,Q,h | h⟩
    · exact ⟨P,Q,Or.inl h.1⟩
    · exact ⟨P,Q,Or.inr h.1⟩
  rcases hs with ⟨P,Q,h | h⟩
  · have nW : (r :: P ++ [a,b] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.1 ▸ nC)
    have nV : (r :: P ++ [b,a] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.2 ▸ nD)
    have pC := adjacent_positions nW hbc (h.1 ▸ adjC)
    have pD := adjacent_positions nV hbc (h.2 ▸ adjD)
    have pW := block_positions nW.tail hab
    have pV := block_positions nV.tail hab.symm
    have pT := third_position (P := P) (Q := Q) hac hbc
    simp only [List.append_eq, List.append_assoc] at pC pD pW pV pT
    rcases pC with hC | hC <;> rcases pD with hD | hD <;> omega
  · have nW : (r :: P ++ [b,a] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.1 ▸ nC)
    have nV : (r :: P ++ [a,b] ++ Q).Nodup :=
      Cycle.nodup_coe_iff.mp (h.2 ▸ nD)
    have pC := adjacent_positions nW hbc (h.1 ▸ adjC)
    have pD := adjacent_positions nV hbc (h.2 ▸ adjD)
    have pW := block_positions nW.tail hab.symm
    have pV := block_positions nV.tail hab
    have pT := third_position (P := P) (Q := Q) hac hbc
    simp only [List.append_eq, List.append_assoc] at pC pD pW pV pT
    rcases pC with hC | hC <;> rcases pD with hD | hD <;> omega

/-- Every fixed-support cycle occurs among the permutations of A.toList;
therefore this is the full finite carrier, for arbitrary ambient labels. -/
theorem fixedCycles_finite (A : Finset α) :
    {C : Cycle α | C.Nodup ∧ C.toFinset = A}.Finite := by
  classical
  let S : Finset (Cycle α) := A.toList.permutations.toFinset.image (fun L : List α => (L : Cycle α))
  apply (Set.toFinite (↑S : Set (Cycle α))).subset
  intro C hC
  change C ∈ S
  induction C using Quotient.inductionOn with
  | _ L =>
    have hn : L.Nodup := Cycle.nodup_coe_iff.mp hC.1
    have hs : L.toFinset = A := hC.2
    have hp : L.Perm A.toList := List.perm_of_nodup_nodup_toFinset_eq
      hn A.nodup_toList (by simpa using hs)
    exact Finset.mem_image.mpr ⟨L, by simpa using List.mem_permutations.mpr hp, rfl⟩

/-- Every finite support has an actual legal original. -/
theorem fixedCycles_nonempty (A : Finset α) : Nonempty (FixedCycles A) := by
  refine ⟨⟨(A.toList : Cycle α), ?_⟩⟩
  constructor
  · exact Cycle.nodup_coe_iff.mpr A.nodup_toList
  · simp

noncomputable instance fixedCyclesFintype (A : Finset α) : Fintype (FixedCycles A) :=
  (fixedCycles_finite A).fintype

/-- Signed mass of one output fibre. Output values need no chosen real encoding. -/
noncomputable def pushforward {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (w : ι → ℝ) (y : Y) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => f i = y), w i

private theorem singleton_mass {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (w : ι → ℝ) (i : ι)
    (hs : ∀ j, f j = f i → j = i) : pushforward f w (f i) = w i := by
  classical
  have he : Finset.univ.filter (fun j => f j = f i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hs j, fun h => h ▸ rfl⟩
  simp only [pushforward, he, Finset.sum_singleton]

/-- For any finite injectively realized family of legal cycles, the two separate
paired laws have zero common signed kernel. No adjacency, forest or desired
injectivity conclusion is a hypothesis. Families may omit swap partners. -/
theorem signed_kernel {ι : Type v} [Fintype ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A)
    (w : ι → ℝ)
    (hF : ∀ y, pushforward (fun i => paired a b (X i)) w y = 0)
    (hG : ∀ y, pushforward (fun i => paired b c (X i)) w y = 0) :
    w = 0 := by
  classical
  let F := fun i => paired a b (X i)
  let G := fun i => paired b c (X i)
  have hleaf (i j k : ι) (hij : F j = F i) (hne : j ≠ i)
      (hik : G k = G i) (hk : k ≠ i) : ∀ l, G l = G j → l = j := by
    intro l hl
    by_contra hlj
    exact swap_has_leaf hA ha hb hc hab hbc hac
      (hn i) (hn j) (hn k) (hn l) (hs i) (hs j) (hs k) (hs l)
      hij.symm (fun h => hne (hi h)) hik.symm (fun h => hk (hi h))
      hl.symm (fun h => hlj (hi h))
  funext i
  change w i = 0
  by_cases hfi : ∀ j, F j = F i → j = i
  · exact (singleton_mass F w i hfi).symm.trans (hF (F i))
  · push_neg at hfi
    obtain ⟨j,hij,hji⟩ := hfi
    by_cases hgi : ∀ k, G k = G i → k = i
    · exact (singleton_mass G w i hgi).symm.trans (hG (G i))
    · push_neg at hgi
      obtain ⟨k,hik,hki⟩ := hgi
      have hwj : w j = 0 :=
        (singleton_mass G w j (hleaf i j k hij hji hik hki)).symm.trans (hG (G j))
      have htwo : Finset.univ.filter (fun l => F l = F i) = {i,j} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hl
          by_cases hli : l = i
          · exact Or.inl hli
          · right
            apply hi
            exact pair_fiber_at_most_two (by omega) ha hb hab
              (hn i) (hn l) (hn j) (hs i) (hs l) (hs j)
              (Prod.mk.inj hl.symm) (Prod.mk.inj hij.symm)
              (fun h => hli (hi h)) (fun h => hji (hi h))
        · rintro (rfl | rfl)
          · rfl
          · exact hij
      have he := hF (F i)
      simp only [pushforward] at he
      change (∑ l ∈ Finset.univ.filter (fun l => F l = F i), w l) = 0 at he
      rw [htwo] at he
      simpa [Finset.sum_pair (Ne.symm hji), hwj] using he

/-- The two paired pushforwards identify all real signed weights on a finite
legal realization, hence in particular all probability weights. -/
theorem signed_injective {ι : Type v} [Fintype ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A)
    (μ ν : ι → ℝ)
    (hF : pushforward (fun i => paired a b (X i)) μ =
      pushforward (fun i => paired a b (X i)) ν)
    (hG : pushforward (fun i => paired b c (X i)) μ =
      pushforward (fun i => paired b c (X i)) ν) : μ = ν := by
  have hz := signed_kernel hA ha hb hc hab hbc hac X hi hn hs (μ - ν)
    (fun y => by
      have he := congrFun hF y
      simpa only [pushforward, Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] using he)
    (fun y => by
      have he := congrFun hG y
      simpa only [pushforward, Pi.sub_apply, Finset.sum_sub_distrib, sub_eq_zero] using he)
  exact sub_eq_zero.mp hz

/-- Full fixed-support law injectivity, without restricting the law to a chosen
subfamily. The Fintype instance enumerates every legal oriented cycle. -/
theorem full_signed_injective {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ ν : FixedCycles A → ℝ)
    (hF : pushforward (fun C : FixedCycles A => paired a b C.val) μ =
      pushforward (fun C : FixedCycles A => paired a b C.val) ν)
    (hG : pushforward (fun C : FixedCycles A => paired b c C.val) μ =
      pushforward (fun C : FixedCycles A => paired b c C.val) ν) : μ = ν := by
  exact signed_injective hA ha hb hc hab hbc hac Subtype.val Subtype.val_injective
    (fun C => C.prop.1) (fun C => C.prop.2) μ ν hF hG

/-- Probability-law specialization with nonnegativity and total mass one. -/
theorem full_probability_injective {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (μ ν : FixedCycles A → ℝ)
    (_hμ : (∀ C, 0 ≤ μ C) ∧ ∑ C, μ C = 1)
    (_hν : (∀ C, 0 ≤ ν C) ∧ ∑ C, ν C = 1)
    (hF : pushforward (fun C : FixedCycles A => paired a b C.val) μ =
      pushforward (fun C : FixedCycles A => paired a b C.val) ν)
    (hG : pushforward (fun C : FixedCycles A => paired b c C.val) μ =
      pushforward (fun C : FixedCycles A => paired b c C.val) ν) : μ = ν := by
  exact full_signed_injective hA ha hb hc hab hbc hac μ ν hF hG

end D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
