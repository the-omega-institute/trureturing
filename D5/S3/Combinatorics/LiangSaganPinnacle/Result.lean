/- GID: D5/S3/Combinatorics/LiangSaganPinnacle/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LiangSaganPinnacle/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/LiangSaganPinnacle/Result.claim; result=D5/S3/Combinatorics/LiangSaganPinnacle/Result.result; claim=D5/S3/Combinatorics/LiangSaganPinnacle/Result.claim
   digest: Ordered pinnacle fibres have pairs without common middle-order upper bounds for every n at least six. -/

/-
admission_basis: open-problem-resolution (#22269; Refuted).
No frozen D5 prerequisites: all imports are pinned Mathlib.
Per declaration: name | proof_shape | escape_witness | consumers.
  Peak | bind-only (definition) | none | pinnacleWord, witness_peak, word_positions
  pinnacleWord | bind-only (definition) | none | Pin, witness_word, word_positions, obstruction
  iota | bind-only (definition) | none | middleLe, iota_max, witness_iota_second
  middleLe | bind-only (definition) | none | claim, obstruction, no_common_upper_bound
  Pin | bind-only (definition) | none | claim, no_common_upper_bound
  claim | bind-only (definition) | none | result
  witness | bind-only (definition) | none | witness_peak, witness_word, witness_iota_max, witness_iota_second
  witness_peak | bind-only | none | witness_word
  witness_word | bind-only | none | no_common_upper_bound
  iota_max | bind-only | none | witness_iota_max, obstruction
  witness_iota_max | bind-only | none | obstruction
  witness_iota_second | bind-only | none | obstruction
  word_positions | bind-only | none | obstruction
  obstruction | content | obstruction | no_common_upper_bound
  sigma | bind-only (definition) | none | no_common_upper_bound, result
  no_common_upper_bound | content | obstruction | result
  result | content | obstruction | settling result
The content is the general-n position obstruction, not finite enumeration.
Utility certified-instance refers only to result using the n=6 fibre;
the family theorem is not a bounded computation.
The obstruction saturates one inversion coordinate, forcing separation of
ordered peaks and a conflicting upper bound on the maximum's coordinate.
All bind-only lemmas are consumed. Classification awaits compiled-term audit.
-/

import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Lattice
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Combinatorics.LiangSaganPinnacle.Result

private def Peak {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : Prop :=
  ∃ l r : Fin n, l.val + 1 = j.val ∧ j.val + 1 = r.val ∧ π l < π j ∧ π r < π j

def pinnacleWord {n : ℕ} (π : Equiv.Perm (Fin n)) : List (Fin n) := by
  classical
  exact ((List.finRange n).filter fun j => decide (Peak π j)).map π

def iota {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w => w < v ∧ π.symm v < π.symm w).card

def middleLe {n : ℕ} (π τ : Equiv.Perm (Fin n)) : Prop := ∀ v, iota π v ≤ iota τ v

def Pin (n : ℕ) (σ : List (Fin n)) := {π : Equiv.Perm (Fin n) // pinnacleWord π = σ}

def claim : Prop := ∀ (n : ℕ) (σ : List (Fin n)),
  ∃ L : DistribLattice (Pin n σ), ∀ x y : Pin n σ, L.le x y ↔ middleLe x.1 y.1

private def witness (k t : ℕ) (ht : t ≤ 1) : Equiv.Perm (Fin (k + 6)) where
  toFun j := ⟨if j.val < t then k+4 else if j.val = t then 0 else
    if j.val = t+1 then k+3 else if j.val = t+2 then 1 else
    if j.val = t+3 then k+5 else if t=0 ∧ j.val=k+5 then k+4 else j.val-t-2,
    by split_ifs <;> omega⟩
  invFun v := ⟨if v.val=0 then t else if v.val=1 then t+2 else
    if v.val=k+3 then t+1 else if v.val=k+5 then t+3 else
    if v.val=k+4 then (if t=0 then k+5 else 0) else v.val+t+2,
    by split_ifs <;> omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv v := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

private lemma witness_peak (k t : ℕ) (ht : t ≤ 1) (j : Fin (k+6)) :
    Peak (witness k t ht) j ↔ j.val=t+1 ∨ j.val=t+3 := by
  constructor
  · rintro ⟨l,r,hl,hr,hL,hR⟩
    change (if _ then _ else _) < (if _ then _ else _) at hL hR
    split_ifs at hL hR <;> omega
  · rintro (hj | hj)
    · refine ⟨⟨t,by omega⟩,⟨t+2,by omega⟩,by omega,by omega,?_,?_⟩ <;>
        change (if _ then _ else _) < (if _ then _ else _)
      all_goals split_ifs <;> omega
    · refine ⟨⟨t+2,by omega⟩,⟨t+4,by omega⟩,by omega,by omega,?_,?_⟩ <;>
        change (if _ then _ else _) < (if _ then _ else _)
      all_goals split_ifs <;> omega

private lemma witness_word (k t : ℕ) (ht : t ≤ 1) :
    pinnacleWord (witness k t ht) = [⟨k+3,by omega⟩,⟨k+5,by omega⟩] := by
  classical
  have hp : (List.finRange (k+6)).filter (fun j => decide (Peak (witness k t ht) j)) =
      [⟨t+1,by omega⟩,⟨t+3,by omega⟩] := by
    apply List.SortedLT.eq_of_mem_iff
      ((List.pairwise_lt_finRange (k+6)).filter _).sortedLT (by simp [List.sortedLT_iff_pairwise]; omega)
    intro j
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_cons, List.mem_singleton]
    rw [witness_peak]
    simp only [Fin.ext_iff]
  rw [pinnacleWord, hp]
  simp only [List.map_cons, List.map_nil]
  simp only [List.cons.injEq]
  refine ⟨?_, ?_, rfl⟩ <;> apply Fin.ext <;> simp [witness] <;> omega

private lemma iota_max {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n)
    (hv : v.val+1=n) : iota π v = n-1-(π.symm v).val := by
  classical
  unfold iota
  calc
    _ = (Finset.Ioi (π.symm v)).card := by
      apply Finset.card_bij (fun w _ => π.symm w)
      · intro w hw
        simpa only [Finset.mem_Ioi] using (Finset.mem_filter.mp hw).2.2
      · intro w hw w' hw' hh
        exact π.symm.injective hh
      · intro j hj
        refine ⟨π j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        have hne : π j ≠ v := by
          intro he
          have := congrArg π.symm he
          simp only [Equiv.symm_apply_apply] at this
          have := Finset.mem_Ioi.mp hj
          omega
        exact ⟨by have := (π j).isLt; have := v.isLt; simp only [ne_eq,Fin.ext_iff] at hne; omega,
          by simpa using Finset.mem_Ioi.mp hj⟩
    _ = _ := Fin.card_Ioi _

private lemma witness_iota_max (k : ℕ) :
    iota (witness k 0 (by omega)) ⟨k+5,by omega⟩ = k+2 := by
  rw [iota_max _ _ (by omega)]
  simp [witness]

private lemma witness_iota_second (k : ℕ) :
    iota (witness k 1 (by omega)) ⟨k+4,by omega⟩ = k+4 := by
  classical
  have he : Finset.univ.filter (fun w : Fin (k+6) =>
      w < ⟨k+4,by omega⟩ ∧ (witness k 1 (by omega)).symm ⟨k+4,by omega⟩ <
        (witness k 1 (by omega)).symm w) = Finset.Iio ⟨k+4,by omega⟩ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw,?_⟩
      change (if _ then _ else _) < (if _ then _ else _)
      split_ifs <;> simp only [Fin.lt_def] at hw <;> omega
  unfold iota
  rw [he]
  exact Fin.card_Iio _

private lemma word_positions {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : Fin n)
    (h : pinnacleWord π = [a,b]) :
    Peak π (π.symm a) ∧ Peak π (π.symm b) ∧ π.symm a < π.symm b := by
  classical
  have he : (List.finRange n).filter (fun j => decide (Peak π j)) = [π.symm a,π.symm b] := by
    have hh := congrArg (List.map π.symm) h
    simpa [pinnacleWord,List.map_map] using hh
  have hpa : π.symm a ∈ (List.finRange n).filter (fun j => decide (Peak π j)) := by rw [he]; simp
  have hpb : π.symm b ∈ (List.finRange n).filter (fun j => decide (Peak π j)) := by rw [he]; simp
  have hord := (List.pairwise_lt_finRange n).filter (fun j => decide (Peak π j))
  rw [he] at hord
  exact ⟨by simpa using hpa,by simpa using hpb,by simpa using hord⟩

private lemma obstruction (k : ℕ) (U : Equiv.Perm (Fin (k+6)))
    (hword : pinnacleWord U = [⟨k+3,by omega⟩,⟨k+5,by omega⟩])
    (hA : middleLe (witness k 0 (by omega)) U)
    (hB : middleLe (witness k 1 (by omega)) U) : False := by
  classical
  let a : Fin (k+6) := ⟨k+3,by omega⟩
  let b : Fin (k+6) := ⟨k+5,by omega⟩
  let c : Fin (k+6) := ⟨k+4,by omega⟩
  have hsat : k+4 ≤ iota U c := (witness_iota_second k) ▸ hB c
  have he : Finset.univ.filter (fun w => w < c ∧ U.symm c < U.symm w) = Finset.Iio c := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hw).2.1
    · simpa [iota,c] using hsat
  have before (w : Fin (k+6)) (hw : w < c) : U.symm c < U.symm w := by
    have := Finset.mem_Iio.mpr hw
    rw [← he] at this
    exact (Finset.mem_filter.mp this).2.2
  obtain ⟨ha,hb,hab⟩ := word_positions U a b hword
  obtain ⟨l,r,hl,hr,hla,hra⟩ := ha
  have hla' : U l < a := by simpa using hla
  have hc : U.symm c < l := by simpa using before (U l) (lt_trans hla' (by simp [a,c]; omega))
  have hq : 2 ≤ (U.symm a).val := by omega
  have hgap : (U.symm a).val+2 ≤ (U.symm b).val := by
    have hne : r ≠ U.symm b := by
      intro h
      rw [h] at hra
      simp only [Equiv.apply_symm_apply] at hra
      have : ¬ b < a := by simp [b,a]; omega
      exact this (by simpa using hra)
    have : r.val ≠ (U.symm b).val := fun h => hne (Fin.ext h)
    have := hab
    omega
  have hh : k+2 ≤ iota U b := (witness_iota_max k) ▸ hA b
  rw [iota_max U b (by simp [b])] at hh
  omega

def sigma (n : ℕ) (hn : 6 ≤ n) : List (Fin n) :=
  [⟨n-3,by omega⟩,⟨n-1,by omega⟩]

theorem no_common_upper_bound (n : ℕ) (hn : 6 ≤ n) :
    ∃ A B : Pin n (sigma n hn), ∀ U : Pin n (sigma n hn),
      ¬ (middleLe A.1 U.1 ∧ middleLe B.1 U.1) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+6 := ⟨n-6,by omega⟩
  have hs : sigma (k+6) hn = [⟨k+3,by omega⟩,⟨k+5,by omega⟩] := by
    simp [sigma, show k+6-3=k+3 by omega, show k+6-1=k+5 by omega]
  refine ⟨⟨witness k 0 (by omega),?_⟩,⟨witness k 1 (by omega),?_⟩,?_⟩
  · rw [hs]; exact witness_word k 0 (by omega)
  · rw [hs]; exact witness_word k 1 (by omega)
  · intro U ⟨hA,hB⟩
    exact obstruction k U.1 (U.2.trans hs) hA hB

theorem result : ¬ claim := by
  intro h
  obtain ⟨L,hL⟩ := h 6 (sigma 6 (by omega))
  obtain ⟨A,B,hAB⟩ := no_common_upper_bound 6 (by omega)
  letI := L
  exact hAB (A ⊔ B) ⟨(hL _ _).mp le_sup_left, (hL _ _).mp le_sup_right⟩

end D5.S3.Combinatorics.LiangSaganPinnacle.Result
