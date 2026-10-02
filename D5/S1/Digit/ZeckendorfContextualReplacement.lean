/- GID: D5/S1/Digit/ZeckendorfContextualReplacement
   generality: I
   mirror-B: none(waiver:complete-source-residual)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: A fourteen-digit replacement preserves the full partial residual of Fibonacci parity at Fibonacci shifts. -/

import D5.S1.Digit.ZeckendorfRawWindow
import D5.S1.Digit.ZeckendorfCarryBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfContextualReplacement

open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfCarryBarrier
open D5.S1.Digit.GoldenBase4IntervalMachine
open GoldenDesubstitutionZeckendorf

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- The smaller replacement block in MSD order. -/
def B0 : List (Fin 2) := [0,0,0,1,0,0,1,0,1,0,1,0,0,0]

/-- The larger replacement block in MSD order. -/
def B1 : List (Fin 2) := [0,0,0,1,0,1,0,1,0,0,1,0,0,0]

set_option maxHeartbeats 1600000 in
/-- The occurrence lies wholly within the final H digits. Equality includes
all invalid suffixes and the epsilon output, for arbitrary high and low context. -/
theorem contextual_replacement (H : ℕ) (p u : List (Fin 2))
    (hH : 14 ≤ H) (huH : 14 + u.length ≤ H)
    (hlegal : NoAdjacentOnes (p ++ B1 ++ u)) :
    ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B1 ++ u) =
      ZeckendorfRawWindow.residual (Nat.fib H) (p ++ B0 ++ u) := by
  classical
  let C0 : ℕ → List ℕ := fun n => [n+10,n+7,n+5,n+3]
  let C1 : ℕ → List ℕ := fun n => [n+10,n+8,n+6,n+3]
  let A : ℕ → List ℕ := fun j => match j with
    | 0 => [12,10,7,5,3]
    | 1 => [13,8,6,4]
    | 2 => [13,11,7,5]
    | 3 => [14,10,8,6]
    | 4 => [15,9,7]
    | 5 => [15,13,11,9,6]
    | 6 => [16,14,11,9]
    | 7 => [17,15,11,8]
    | 8 => [18,16,11]
    | 9 => [19,17,10]
    | 10 => [20,18]
    | 11 => [21,18,16,14,12]
    | _ => []
  let B : ℕ → List ℕ := fun j => match j with
    | 0 => [12,10,8,6,3]
    | 1 => [13,9,7,4]
    | 2 => [13,11,9,7]
    | 3 => [14,11,9,6]
    | 4 => [15,11,9]
    | 5 => [16,11,8]
    | 6 => [17,11]
    | 7 => [18,10]
    | 8 => [19]
    | 9 => [19,17,15,13,10]
    | 10 => [20,18,16,14]
    | 11 => [21,19,17,14,12]
    | _ => []
  have table_structure (r j : ℕ) (hr : 2 ≤ r) (hj : j < 12) :
      ((A j).map (fun i => r+i)).IsZeckendorfRep ∧
      ((B j).map (fun i => r+i)).IsZeckendorfRep ∧
      (∀ k ∈ (A j).map (fun i => r+i), r+j+1 ≤ k ∧ k ≤ r+j+12) ∧
      (∀ k ∈ (B j).map (fun i => r+i), r+j+1 ≤ k ∧ k ≤ r+j+12) ∧
      (A j).length % 2 = (B j).length % 2 := by
    interval_cases j <;>
      norm_num [A, B, List.IsZeckendorfRep, List.isChain_cons_cons] <;> omega
  have table_values (r j : ℕ) (hj : j < 12) :
      ((C0 (r+j)).map Nat.fib).sum + Nat.fib (r+12) =
        (((A j).map (fun i => r+i)).map Nat.fib).sum ∧
      ((C1 (r+j)).map Nat.fib).sum + Nat.fib (r+12) =
        (((B j).map (fun i => r+i)).map Nat.fib).sum := by
    have linear (i : ℕ) (hi : 1 ≤ i) : Nat.fib (r+i) =
        Nat.fib i * Nat.fib (r+1) + Nat.fib (i-1) * Nat.fib r := by
      have h := Nat.fib_add r (i-1)
      have he : r + (i-1) + 1 = r+i := by omega
      rw [he, Nat.sub_add_cancel hi] at h
      simpa [Nat.mul_comm, Nat.add_comm] using h
    have f2 := linear 2 (by omega)
    have f3 := linear 3 (by omega)
    have f4 := linear 4 (by omega)
    have f5 := linear 5 (by omega)
    have f6 := linear 6 (by omega)
    have f7 := linear 7 (by omega)
    have f8 := linear 8 (by omega)
    have f9 := linear 9 (by omega)
    have f10 := linear 10 (by omega)
    have f11 := linear 11 (by omega)
    have f12 := linear 12 (by omega)
    have f13 := linear 13 (by omega)
    have f14 := linear 14 (by omega)
    have f15 := linear 15 (by omega)
    have f16 := linear 16 (by omega)
    have f17 := linear 17 (by omega)
    have f18 := linear 18 (by omega)
    have f19 := linear 19 (by omega)
    have f20 := linear 20 (by omega)
    have f21 := linear 21 (by omega)
    have f22 := linear 22 (by omega)
    have v1 : Nat.fib 1 = 1 := by decide
    have v2 : Nat.fib 2 = 1 := by decide
    have v3 : Nat.fib 3 = 2 := by decide
    have v4 : Nat.fib 4 = 3 := by decide
    have v5 : Nat.fib 5 = 5 := by decide
    have v6 : Nat.fib 6 = 8 := by decide
    have v7 : Nat.fib 7 = 13 := by decide
    have v8 : Nat.fib 8 = 21 := by decide
    have v9 : Nat.fib 9 = 34 := by decide
    have v10 : Nat.fib 10 = 55 := by decide
    have v11 : Nat.fib 11 = 89 := by decide
    have v12 : Nat.fib 12 = 144 := by decide
    have v13 : Nat.fib 13 = 233 := by decide
    have v14 : Nat.fib 14 = 377 := by decide
    have v15 : Nat.fib 15 = 610 := by decide
    have v16 : Nat.fib 16 = 987 := by decide
    have v17 : Nat.fib 17 = 1597 := by decide
    have v18 : Nat.fib 18 = 2584 := by decide
    have v19 : Nat.fib 19 = 4181 := by decide
    have v20 : Nat.fib 20 = 6765 := by decide
    have v21 : Nat.fib 21 = 10946 := by decide
    have v22 : Nat.fib 22 = 17711 := by decide
    interval_cases j <;>
      norm_num only [C0, C1, A, B, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.map_map, Function.comp_def, Nat.add_zero, Nat.add_assoc] <;>
      simp -failIfUnchanged only [f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22,
        v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, Nat.fib_zero] <;>
      constructor <;> first | trivial | omega | ring
  have concatenate (a b : List ℕ) (ha : a.IsZeckendorfRep) (hb : b.IsZeckendorfRep)
      (hgap : ∀ x ∈ a, ∀ y ∈ b, y+2 ≤ x) : (a ++ b).IsZeckendorfRep := by
    rw [List.IsZeckendorfRep, List.append_assoc, List.isChain_iff_pairwise,
      List.pairwise_append]
    refine ⟨(List.pairwise_append.mp (List.isChain_iff_pairwise.mp ha)).1,
      List.isChain_iff_pairwise.mp hb, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hgap x hx y hy
    · simp only [List.mem_singleton] at hy
      subst y
      exact (List.pairwise_append.mp (List.isChain_iff_pairwise.mp ha)).2.2 x hx 0 (by simp)
  have identify (l : List ℕ) (hl : l.IsZeckendorfRep) (N : ℕ)
      (hv : (l.map Nat.fib).sum = N) : wdigits N = l := (wdigits_unique hl hv).symm
  have core (n : ℕ) (hn : 2 ≤ n) :
      (C0 n).IsZeckendorfRep ∧ (C1 n).IsZeckendorfRep ∧
      (∀ k ∈ C0 n, n+3 ≤ k ∧ k ≤ n+10) ∧
      (∀ k ∈ C1 n, n+3 ≤ k ∧ k ≤ n+10) := by
    norm_num [C0, C1, List.IsZeckendorfRep, List.isChain_cons_cons] <;> omega
  have arithmetic (n : ℕ) (hn : 2 ≤ n) (P T : List ℕ)
      (hP : P.IsZeckendorfRep) (hT : T.IsZeckendorfRep)
      (hp : ∀ k ∈ P, n+14 ≤ k) (ht : ∀ k ∈ T, k < n) :
      parity ((P.map Nat.fib).sum + ((C1 n).map Nat.fib).sum +
          (T.map Nat.fib).sum + Nat.fib H) =
        parity ((P.map Nat.fib).sum + ((C0 n).map Nat.fib).sum +
          (T.map Nat.fib).sum + Nat.fib H) := by
    obtain ⟨hc0, hc1, hb0, hb1⟩ := core n hn
    by_cases hlo : n+13 ≤ H
    · let S := wdigits ((P.map Nat.fib).sum + Nat.fib H)
      have hS : S.IsZeckendorfRep := wdigits_isCanonical _
      have hs : ∀ k ∈ S, n+12 ≤ k := by
        intro k hk
        have h := lower_support_carry_barrier P (n+14) H hP (by omega) hp (by omega) k hk
        simpa [show n+14-2=n+12 by omega] using h
      have hc0T := concatenate (C0 n) T hc0 hT (by
        intro a ha b hb; have := (hb0 a ha).1; have := ht b hb; omega)
      have hc1T := concatenate (C1 n) T hc1 hT (by
        intro a ha b hb; have := (hb1 a ha).1; have := ht b hb; omega)
      have hs0 := concatenate S (C0 n ++ T) hS hc0T (by
        intro a ha b hb
        have ha' := hs a ha
        rcases List.mem_append.mp hb with hb | hb
        · have := (hb0 b hb).2; omega
        · have := ht b hb; omega)
      have hs1 := concatenate S (C1 n ++ T) hS hc1T (by
        intro a ha b hb
        have ha' := hs a ha
        rcases List.mem_append.mp hb with hb | hb
        · have := (hb1 b hb).2; omega
        · have := ht b hb; omega)
      have id0 : wdigits ((P.map Nat.fib).sum + ((C0 n).map Nat.fib).sum +
          (T.map Nat.fib).sum + Nat.fib H) = S ++ (C0 n ++ T) := identify _ hs0 _ (by simp [S, List.map_append]; omega)
      have id1 : wdigits ((P.map Nat.fib).sum + ((C1 n).map Nat.fib).sum +
          (T.map Nat.fib).sum + Nat.fib H) = S ++ (C1 n ++ T) := identify _ hs1 _ (by simp [S, List.map_append]; omega)
      rw [parity, parity, id0, id1]
      simp [List.length_append, C0, C1]
    · by_cases hhi : H ≤ n
      · let S := wdigits (Nat.fib H + (T.map Nat.fib).sum)
        have hS : S.IsZeckendorfRep := wdigits_isCanonical _
        have tsmall : (T.map Nat.fib).sum < Nat.fib n := hT.sum_fib_lt (by
          intro k hk
          rcases List.mem_append.mp (List.mem_of_mem_head? hk) with hk | hk
          · exact ht k hk
          · simp only [List.mem_singleton] at hk; subst k; omega)
        have nsmall : Nat.fib H + (T.map Nat.fib).sum < Nat.fib (n+2) := by
          have := Nat.fib_mono hhi
          have := Nat.fib_lt_fib_succ hn
          rw [Nat.fib_add_two]
          omega
        have hs : ∀ k ∈ S, k ≤ n+1 := by
          intro k hk
          have hterm : Nat.fib k ≤ (S.map Nat.fib).sum :=
            List.le_sum_of_mem (List.mem_map.mpr ⟨k,hk,rfl⟩)
          rw [decode_wdigits] at hterm
          by_contra hnot
          have hmono := Nat.fib_mono (by omega : n+2 ≤ k)
          omega
        have hc0S := concatenate (C0 n) S hc0 hS (by
          intro a ha b hb; have := (hb0 a ha).1; have := hs b hb; omega)
        have hc1S := concatenate (C1 n) S hc1 hS (by
          intro a ha b hb; have := (hb1 a ha).1; have := hs b hb; omega)
        have hp0 := concatenate P (C0 n ++ S) hP hc0S (by
          intro a ha b hb
          have ha' := hp a ha
          rcases List.mem_append.mp hb with hb | hb
          · have := (hb0 b hb).2; omega
          · have := hs b hb; omega)
        have hp1 := concatenate P (C1 n ++ S) hP hc1S (by
          intro a ha b hb
          have ha' := hp a ha
          rcases List.mem_append.mp hb with hb | hb
          · have := (hb1 b hb).2; omega
          · have := hs b hb; omega)
        have id0 : wdigits ((P.map Nat.fib).sum + ((C0 n).map Nat.fib).sum +
            (T.map Nat.fib).sum + Nat.fib H) = P ++ (C0 n ++ S) := identify _ hp0 _ (by simp [S, List.map_append]; omega)
        have id1 : wdigits ((P.map Nat.fib).sum + ((C1 n).map Nat.fib).sum +
            (T.map Nat.fib).sum + Nat.fib H) = P ++ (C1 n ++ S) := identify _ hp1 _ (by simp [S, List.map_append]; omega)
        rw [parity, parity, id0, id1]
        simp [List.length_append, C0, C1]
      · let r := H-12
        let j := n-r
        have hr : 2 ≤ r := by dsimp [r]; omega
        have hj : j < 12 := by dsimp [j,r]; omega
        have hn' : n = r+j := by dsimp [r,j]; omega
        have hH' : H = r+12 := by dsimp [r]; omega
        obtain ⟨ha, hb, haBounds, hbBounds, hpar⟩ := table_structure r j hr hj
        obtain ⟨va,vb⟩ := table_values r j hj
        have haT := concatenate ((A j).map (fun i => r+i)) T ha hT (by
          intro a ha b hb; have := (haBounds a ha).1; have := ht b hb; omega)
        have hbT := concatenate ((B j).map (fun i => r+i)) T hb hT (by
          intro a ha b hb; have := (hbBounds a ha).1; have := ht b hb; omega)
        have hpA := concatenate P ((A j).map (fun i => r+i) ++ T) hP haT (by
          intro a ha b hb
          have ha' := hp a ha
          rcases List.mem_append.mp hb with hb | hb
          · have := (haBounds b hb).2; omega
          · have := ht b hb; omega)
        have hpB := concatenate P ((B j).map (fun i => r+i) ++ T) hP hbT (by
          intro a ha b hb
          have ha' := hp a ha
          rcases List.mem_append.mp hb with hb | hb
          · have := (hbBounds b hb).2; omega
          · have := ht b hb; omega)
        have id0 : wdigits ((P.map Nat.fib).sum + ((C0 n).map Nat.fib).sum +
            (T.map Nat.fib).sum + Nat.fib H) = P ++ ((A j).map (fun i => r+i) ++ T) := identify _ hpA _ (by
          simp only [List.map_append, List.sum_append]
          rw [← va, ← hn', ← hH']; omega)
        have id1 : wdigits ((P.map Nat.fib).sum + ((C1 n).map Nat.fib).sum +
            (T.map Nat.fib).sum + Nat.fib H) = P ++ ((B j).map (fun i => r+i) ++ T) := identify _ hpB _ (by
          simp only [List.map_append, List.sum_append]
          rw [← vb, ← hn', ← hH']; omega)
        rw [parity, parity, id0, id1]
        simp only [List.length_append, List.length_map]
        rw [Nat.add_mod P.length, Nat.add_mod P.length,
          Nat.add_mod (A j).length, Nat.add_mod (B j).length, hpar]
  have support_append (a b : List (Fin 2)) :
      support (a ++ b) = (support a).map (fun k => k+b.length) ++ support b := by
    induction a with
    | nil => simp [support]
    | cons d a ih =>
      by_cases hd : d = 0 <;>
        simp [support, hd, ih, List.length_append, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
  have prefix_canonical (a b : List ℕ) (hc : (a ++ b).IsZeckendorfRep) :
      a.IsZeckendorfRep := by
    unfold List.IsZeckendorfRep at hc ⊢
    exact hc.sublist ((List.sublist_append_left a b).append (List.Sublist.refl [0]))
  have domain (t : List (Fin 2)) :
      NoAdjacentOnes (p ++ B1 ++ t) ↔ NoAdjacentOnes (p ++ B0 ++ t) := by
    simp [NoAdjacentOnes, List.isChain_append, B1, B0]
  funext z
  have hd : NoAdjacentOnes ((p ++ B1 ++ u) ++ z) ↔
      NoAdjacentOnes ((p ++ B0 ++ u) ++ z) := by
    simpa only [List.append_assoc] using domain (u ++ z)
  by_cases hz : NoAdjacentOnes ((p ++ B1 ++ u) ++ z)
  · have hz0 := hd.mp hz
    let t := u ++ z
    let n := t.length+2
    let P := (support p).map (fun k => k+14+t.length)
    let T := support t
    have hpword : NoAdjacentOnes p := by
      have h : NoAdjacentOnes (p ++ (B1 ++ t)) := by
        simpa only [List.append_assoc] using hz
      exact h.left_of_append
    have htword : NoAdjacentOnes t := by
      have h : NoAdjacentOnes (p ++ (B1 ++ t)) := by
        simpa only [List.append_assoc] using hz
      exact h.right_of_append.right_of_append
    have hs1 : support ((p ++ B1 ++ u) ++ z) = P ++ (C1 n ++ T) := by
      simp only [List.append_assoc, support_append, List.map_append, List.map_map]
      norm_num [P,T,t,n,C1,B1,support,support_append,Function.comp_def,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      apply congrArg₂ List.append
      · apply List.map_congr_left
        intro k hk
        omega
      · repeat' apply congrArg₂ List.cons
        all_goals first | omega | rfl
    have hs0 : support ((p ++ B0 ++ u) ++ z) = P ++ (C0 n ++ T) := by
      simp only [List.append_assoc, support_append, List.map_append, List.map_map]
      norm_num [P,T,t,n,C0,B0,support,support_append,Function.comp_def,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      apply congrArg₂ List.append
      · apply List.map_congr_left
        intro k hk
        omega
      · repeat' apply congrArg₂ List.cons
        all_goals first | omega | rfl
    have hP : P.IsZeckendorfRep := by
      have h := (source_word_coordinates _ hz).1
      rw [hs1] at h
      exact prefix_canonical P _ h
    have hT : T.IsZeckendorfRep := (source_word_coordinates t htword).1
    have pbound : ∀ k ∈ P, n+14 ≤ k := by
      intro k hk
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
      have hcan := (source_word_coordinates p hpword).1
      have ha2 := (List.pairwise_append.mp (List.isChain_iff_pairwise.mp hcan)).2.2 a ha 0 (by simp)
      dsimp [n]
      omega
    have tbound : ∀ k ∈ T, k < n := (source_word_coordinates t htword).2.1
    have v1 : value ((p ++ B1 ++ u) ++ z) =
        (P.map Nat.fib).sum + ((C1 n).map Nat.fib).sum + (T.map Nat.fib).sum := by
      unfold value
      rw [← (source_word_coordinates _ hz).2.2.1, hs1]
      simp [value, List.map_append, Nat.add_assoc]
    have v0 : value ((p ++ B0 ++ u) ++ z) =
        (P.map Nat.fib).sum + ((C0 n).map Nat.fib).sum + (T.map Nat.fib).sum := by
      unfold value
      rw [← (source_word_coordinates _ hz0).2.2.1, hs0]
      simp [value, List.map_append, Nat.add_assoc]
    have he := arithmetic n (by dsimp [n]; omega) P T hP hT pbound tbound
    simpa only [ZeckendorfRawWindow.residual, if_pos hz, if_pos hz0, v1, v0] using congrArg some he
  · have hz0 : ¬ NoAdjacentOnes ((p ++ B0 ++ u) ++ z) := fun h => hz (hd.mpr h)
    simp only [ZeckendorfRawWindow.residual, if_neg hz, if_neg hz0]

#print axioms contextual_replacement

end D5.S1.Digit.ZeckendorfContextualReplacement
