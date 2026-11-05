/-
  R1 source candidate: the exact fibres of two labelled circular deletions.

  This source has complete proof terms but has deliberately not been compiled
  in this source-preparation stage.  It uses the stable circular-word APIs
  from DeletionReadoutReconstruction, CyclicInsertionGap, and
  CircularDeletionTransport.  The mathematical statement is the fixed-support
  classification: two equal labelled deletions give either the same oriented
  cycle or the adjacent swap of the two deleted labels.  The stated working
  range is A.card >= 3 (and therefore includes the original A.card >= 4 use).
-/

import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionFiber

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

universe u
variable {α : Type u} [DecidableEq α]

abbrev SupportedCircle (A : Finset α) :=
  D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.SupportedCircle A

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

private theorem opposite_tails
    {L K : List α} {a b : α}
    (hL : (a :: L).Nodup) (hK : (b :: K).Nodup) (hab : a ≠ b)
    (hA : erase a (a :: L) = erase a (b :: K))
    (hB : erase b (a :: L) = erase b (b :: K)) :
    ∃ R : List α, L = b :: R ∧ K = a :: R := by
  have haL : a ∉ L := (List.nodup_cons.mp hL).1
  have hbK : b ∉ K := (List.nodup_cons.mp hK).1
  have hfilterA : L.filter (fun y => decide (y ≠ a)) = L := by
    simpa [erase] using erase_eq_self haL
  have hfilterB : K.filter (fun y => decide (y ≠ b)) = K := by
    simpa [erase] using erase_eq_self hbK
  have hfirst : L = b :: erase a K := by
    have h := hA
    simp only [erase, List.filter_cons, decide_false, Bool.false_eq_true,
      ↓reduceIte, decide_eq_true (Ne.symm hab), List.cons.injEq] at h
    rw [hfilterA] at h
    exact h
  let R : List α := erase a K
  have hLR : L = b :: R := by simpa [R] using hfirst
  have hbR : b ∉ R := by
    have hn : (b :: R).Nodup := hLR ▸ (List.nodup_cons.mp hL).2
    exact (List.nodup_cons.mp hn).1
  have hsecond : a :: erase b L = erase b K := by
    have h := hB
    simp only [erase, List.filter_cons, decide_eq_true hab, ↓reduceIte,
      decide_false, Bool.false_eq_true] at h
    exact h
  have hLerase : erase b L = R := by
    rw [hLR]
    simp only [erase, List.filter_cons, decide_false, Bool.false_eq_true,
      ↓reduceIte, erase_eq_self hbR]
  have hKR : K = a :: R := by
    rw [hLerase, hfilterB] at hsecond
    exact hsecond.symm
  exact ⟨R, hLR, hKR⟩

/- The two possible rooted words obtained by swapping an adjacent a,b pair. -/
def adjacentSwapAt (r a b : α) (C D : Cycle α) : Prop :=
  ∃ P Q : List α,
    (C = (r :: P ++ [a,b] ++ Q : List α) ∧
      D = (r :: P ++ [b,a] ++ Q : List α)) ∨
    (C = (r :: P ++ [b,a] ++ Q : List α) ∧
      D = (r :: P ++ [a,b] ++ Q : List α))

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
  | nil => exact (haL rfl).elim
  | cons x L ih =>
    cases K with
    | nil => exact (haK rfl).elim
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
            exact (hyb hhead.symm).elim
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
                  decide_eq_true hyb, ↓reduceIte] at h
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
              have haLt : a ∈ L := by simpa [hxa] using haL
              have hbLt : b ∈ L := by simpa [hxb] using hbL
              have haKt : a ∈ K := by simpa [hxa] using haK
              have hbKt : b ∈ K := by simpa [hxb] using hbK
              rcases ih hL.tail hK.tail haLt hbLt haKt hbKt hab hAtail hBtail with
                hEq | ⟨P, Q, hSwap⟩
              · exact Or.inl (by simpa [hEq])
              · rcases hSwap with hSwap | hSwap
                · exact Or.inr ⟨x :: P, Q, Or.inl ⟨
                    by simpa [List.cons_append] using hSwap.1,
                    by simpa [List.cons_append] using hSwap.2⟩⟩
                · exact Or.inr ⟨x :: P, Q, Or.inr ⟨
                    by simpa [List.cons_append] using hSwap.1,
                    by simpa [List.cons_append] using hSwap.2⟩⟩

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
      exact hparts.2.2 _ hx a (by simp)
    · intro hxb
      subst x
      exact hparts.2.2 _ hx b (by simp)
  have hQ : ∀ x ∈ Q, x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro hxa
      subst x
      exact hblock.2.2 a (by simp) _ hx
    · intro hxb
      subst x
      exact hblock.2.2 b (by simp) _ hx
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
    (hrA : r ∈ A) (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
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
    simpa [hra] using h
  have hbL : b ∈ L := by
    have hfin : b ∈ (r :: L : Cycle α).toFinset := by simpa [sC] using hb
    have h := (mem_support (r :: L : Cycle α) b).mp hfin
    simpa [hrb] using h
  have haK : a ∈ K := by
    have hfin : a ∈ (r :: K : Cycle α).toFinset := by simpa [sD] using ha
    have h := (mem_support (r :: K : Cycle α) a).mp hfin
    simpa [hra] using h
  have hbK : b ∈ K := by
    have hfin : b ∈ (r :: K : Cycle α).toFinset := by simpa [sD] using hb
    have h := (mem_support (r :: K : Cycle α) b).mp hfin
    simpa [hrb] using h
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
      simpa only [List.filter_cons, decide_eq_true hra, ↓reduceIte] using hA
    have hB' : (r :: erase b L : Cycle α) = (r :: erase b K : Cycle α) := by
      change (((r :: L).filter (fun y => decide (y ≠ b))) : Cycle α) =
        (((r :: K).filter (fun y => decide (y ≠ b))) : Cycle α) at hB
      simpa only [List.filter_cons, decide_eq_true hrb, ↓reduceIte] using hB
    have hEraseA := anchored_coe_injective hna hA'
    have hEraseB := anchored_coe_injective hnb hB'
    rcases erase_pair_classification (L := L) (K := K) hnL.tail hnK.tail
      haL hbL haK hbK hab hEraseA hEraseB with hEq | ⟨P, Q, hSwap⟩
    · exact Or.inl (by simpa [hEq])
    · exact Or.inr ⟨P, Q, by
        rcases hSwap with h | h
        · left
          exact ⟨by simpa [List.cons_append] using congrArg (List.cons r) h.1,
            by simpa [List.cons_append] using congrArg (List.cons r) h.2⟩
        · right
          exact ⟨by simpa [List.cons_append] using congrArg (List.cons r) h.1,
            by simpa [List.cons_append] using congrArg (List.cons r) h.2⟩⟩
  · intro h
    rcases h with rfl | h
    · exact ⟨rfl, rfl⟩
    · rcases h with ⟨P, Q, h | h⟩
      · rcases h with ⟨rfl, rfl⟩
        constructor
        · change (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α) =
            (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α)
          simp [erase, hra, hrb, hab, Ne.symm hab]
        · change (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α) =
            (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α)
          simp [erase, hra, hrb, hab, Ne.symm hab]
      · rcases h with ⟨rfl, rfl⟩
        constructor
        · change (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α) =
            (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ a))) : Cycle α)
          simp [erase, hra, hrb, hab, Ne.symm hab]
        · change (((r :: P ++ [b,a] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α) =
            (((r :: P ++ [a,b] ++ Q).filter (fun y => decide (y ≠ b))) : Cycle α)
          simp [erase, hra, hrb, hab, Ne.symm hab]

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
    have hroot := (paired_fiber_iff_at_root hrA (by
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
    · exact (paired_fiber_iff_at_root hrA hra hrb hab hC hD sC sD).mpr
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
  have hCD := (paired_fiber_iff_at_root hrA hra hrb hab hC hD sC sD).mp hDobs
  have hCE := (paired_fiber_iff_at_root hrA hra hrb hab hC hE sC sE).mp hEobs
  rcases hCD with hEq | hCD
  · exact (hDC hEq.symm).elim
  rcases hCE with hEq | hCE
  · exact (hEC hEq.symm).elim
  exact adjacentSwapAt_unique hra hrb hab hC hD hE hCD hCE

end D5.S3.Combinatorics.CircularWords.PairedDeletionFiber
