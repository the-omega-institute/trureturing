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
