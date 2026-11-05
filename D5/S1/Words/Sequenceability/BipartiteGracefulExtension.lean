/- GID: D5/S1/Words/Sequenceability/BipartiteGracefulExtension
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/BipartiteGracefulExtension
   mirror-E: none(waiver:unbounded-symbolic-proof-no-experimental-artifact)
   anchors: []
   utility: none
   digest: Four-step bipartite graceful paths supply exact two-block attachment lengths. -/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Dist

/-! Exact linear edge inventories for bipartite graceful paths. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S1.Words.Sequenceability.BipartiteGracefulExtension

/-- Ordinary absolute differences of adjacent entries; there is no closing edge. -/
def lengths : List ℕ → List ℕ
  | a :: b :: t => Nat.dist a b :: lengths (b :: t)
  | _ => []

/-- Adjacent labels lie on opposite sides of the split at `s`. -/
def Cross (s a b : ℕ) : Prop := (a ≤ s ∧ s < b) ∨ (b ≤ s ∧ s < a)

/-- The complete auxiliary-path inventory, with its two fixed endpoints. -/
def Auxiliary (s : ℕ) (q : List ℕ) : Prop :=
  q.Perm (List.range (2 * s + 2)) ∧
  q.head? = some (s - 1) ∧ q.getLast? = some (2 * s) ∧
  q.IsChain (Cross s) ∧ (lengths q).Perm (List.range' 1 (2 * s + 1))

/-- Each low label moves by two; each high label moves by six. -/
def embed (s q : ℕ) : ℕ := if q ≤ s then q + 2 else q + 6

/-- Four new labels at each end surround the embedded old path. -/
def extend (s : ℕ) (q : List ℕ) : List ℕ :=
  [s + 3, s + 6, s + 4, s + 5] ++ q.map (embed s) ++
    [0, 2 * s + 9, 1, 2 * s + 8]

private theorem lengths_snoc (q : List ℕ) (a : ℕ) :
    lengths (q ++ [a]) = lengths q ++ (q.getLast?.toList.map (fun b => Nat.dist b a)) := by
  induction q using List.twoStepInduction with
  | nil => simp [lengths]
  | singleton b => simp [lengths]
  | cons_cons b c t _ ih =>
    simpa [lengths] using congrArg (List.cons (Nat.dist b c)) (ih c)

private theorem lengths_prefix (q : List ℕ) (a b c d z : ℕ)
    (hq : q.head? = some z) :
    lengths ([a,b,c,d] ++ q) =
      [Nat.dist a b, Nat.dist b c, Nat.dist c d, Nat.dist d z] ++ lengths q := by
  cases q with
  | nil => simp at hq
  | cons x t => simp only [List.head?_cons, Option.some.injEq] at hq; subst x; rfl

private theorem lengths_map (q : List ℕ) (s : ℕ) (f : ℕ → ℕ) (c : ℕ)
    (hq : q.IsChain (Cross s))
    (hf : ∀ a ∈ q, ∀ b ∈ q, Cross s a b → Nat.dist (f a) (f b) = Nat.dist a b + c) :
    lengths (q.map f) = (lengths q).map (· + c) := by
  revert hq hf
  induction q using List.twoStepInduction with
  | nil => intros; rfl
  | singleton a => intros; rfl
  | cons_cons a b t _ ih =>
    intro hq hf
    have hc := (List.isChain_cons_cons.mp hq)
    simp only [List.map_cons, lengths]
    rw [hf a (by simp) b (by simp) hc.1]
    congr 1
    exact ih b hc.2 (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy]))

private theorem embed_distance (s a b : ℕ) (h : Cross s a b) :
    Nat.dist (embed s a) (embed s b) = Nat.dist a b + 4 := by
  rcases h with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · simp only [embed, ite_eq_left ha, ite_eq_right (by omega : ¬ b ≤ s), Nat.dist]
    omega
  · simp only [embed, ite_eq_left hb, ite_eq_right (by omega : ¬ a ≤ s), Nat.dist]
    omega

private theorem embed_range (s : ℕ) :
    (List.range (2 * s + 2)).map (embed s) =
      List.range' 2 (s + 1) ++ List.range' (s + 7) (s + 1) := by
  have hr : List.range (2 * s + 2) =
      List.range (s + 1) ++ List.range' (s + 1) (s + 1) := by
    simpa [List.range_eq_range', Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (List.range'_append_1 (s := 0) (m := s + 1) (n := s + 1)).symm
  rw [hr, List.map_append]
  congr 1
  · rw [List.range'_eq_map_range]
    apply List.map_congr_left
    intro x hx
    have hx' := List.mem_range.mp hx
    simp [embed, show x ≤ s by omega, Nat.add_comm]
  · have he : (List.range' (s + 1) (s + 1)).map (embed s) =
        (List.range' (s + 1) (s + 1)).map (6 + ·) := by
      apply List.map_congr_left
      intro x hx
      have hx' := List.mem_range'.mp hx
      simp [embed, show ¬ x ≤ s by omega, Nat.add_comm]
    rw [he, List.map_add_range']
    congr 1
    omega

private theorem five_ranges (a b c d e f : ℕ) :
    ((((List.range' a b ++ List.range' (a+b) c) ++ List.range' (a+b+c) d) ++
      List.range' (a+b+c+d) e) ++ List.range' (a+b+c+d+e) f) =
      List.range' a (b+c+d+e+f) := by
  simp only [Nat.add_assoc, List.range'_append_1]

private theorem extension_partition (s : ℕ) :
    ([s+3,s+6,s+4,s+5] ++ List.range' 2 (s+1) ++
      List.range' (s+7) (s+1) ++ [0,2 * s+9,1,2 * s+8]).Perm
      (List.range (2 * s+10)) := by
  have hr : List.range (2 * s+10) =
      [0,1] ++ List.range' 2 (s+1) ++ [s+3,s+4,s+5,s+6] ++
      List.range' (s+7) (s+1) ++ [2 * s+8,2 * s+9] := by
    have h : ((((List.range' 0 2 ++ List.range' 2 (s+1)) ++ List.range' (s+3) 4) ++
        List.range' (s+7) (s+1)) ++ List.range' (2 * s+8) 2) =
        List.range' 0 (2 * s+10) := by
      simpa only [Nat.zero_add,
        show 2+(s+1)=s+3 by omega,
        show s+3+4=s+7 by omega,
        show s+7+(s+1)=2 * s+8 by omega,
        show 2 * s+8+2=2 * s+10 by omega] using five_ranges 0 2 (s+1) 4 (s+1) 2
    have h4 : List.range' (s+3) 4 = [s+3,s+4,s+5,s+6] := by
      simp [List.range', Nat.add_assoc]
    have h2 : List.range' (2 * s+8) 2 = [2 * s+8,2 * s+9] := by
      simp [List.range', Nat.add_assoc]
    have h0 : List.range' 0 2 = [0,1] := rfl
    simpa [List.range_eq_range', h0, h4, h2, List.append_assoc] using h.symm
  rw [hr, List.perm_iff_count]
  intro x
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

private theorem extension_valid (s : ℕ) (hs : 2 ≤ s) (q : List ℕ)
    (hq : Auxiliary s q) : Auxiliary (s+4) (extend s q) := by
  obtain ⟨hv,hh,ht,hc,hd⟩ := hq
  have hmhead : (q.map (embed s)).head? = some (s+1) := by
    simp [List.head?_map, hh, embed, show s-1 ≤ s by omega]
    omega
  have hmtail : (q.map (embed s)).getLast? = some (2 * s+6) := by
    simp [List.getLast?_map, ht, embed, show ¬ 2 * s ≤ s by omega]
  have hmap : (q.map (embed s)).IsChain (Cross (s+4)) := by
    apply List.isChain_map_of_isChain (embed s) _ hc
    intro a b hab
    rcases hab with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · simp only [Cross, embed, ite_eq_left ha, ite_eq_right (by omega : ¬ b ≤ s)]
      omega
    · simp only [Cross, embed, ite_eq_left hb, ite_eq_right (by omega : ¬ a ≤ s)]
      omega
  have hp : [s+3,s+6,s+4,s+5].IsChain (Cross (s+4)) := by
    simp [Cross]
  have hsuf : [0,2 * s+9,1,2 * s+8].IsChain (Cross (s+4)) := by
    simp [Cross]; omega
  have hpc : ([s+3,s+6,s+4,s+5] ++ q.map (embed s)).IsChain (Cross (s+4)) := by
    apply hp.append hmap
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, hmhead,
      Option.mem_def, Option.some.injEq]
    intro x hx y hy
    subst x; subst y
    simp [Cross]
  have hmne : q.map (embed s) ≠ [] := by
    intro hnil
    simp [hnil] at hmhead
  have hend : ([s+3,s+6,s+4,s+5] ++ q.map (embed s)).getLast? =
      some (2 * s+6) := by
    rw [List.getLast?_append_of_ne_nil _ hmne, hmtail]
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hv' := hv.map (embed s)
    rw [embed_range] at hv'
    have hpv := ((List.Perm.refl [s+3,s+6,s+4,s+5]).append hv').append
      (List.Perm.refl [0,2 * s+9,1,2 * s+8])
    have hpart := extension_partition s
    have hsize : 2*(s+4)+2 = 2 * s+10 := by omega
    simpa only [extend, List.append_assoc, hsize] using hpv.trans hpart
  · simp [extend]
  · simp only [extend, List.getLast?_append_cons, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some.injEq]
    omega
  · apply hpc.append hsuf
    simp only [hend, List.head?_cons, Option.mem_def, Option.some.injEq]
    intro x hx y hy
    subst x; subst y
    simp [Cross]; omega
  · have he := lengths_map q s (embed s) 4 hc (fun a _ b _ => embed_distance s a b)
    have hpref := lengths_prefix (q.map (embed s)) (s+3) (s+6) (s+4) (s+5) (s+1) hmhead
    have hl : lengths (extend s q) =
        [3,2,1,4] ++ (lengths q).map (·+4) ++ [2 * s+6,2 * s+9,2 * s+8,2 * s+7] := by
      have hsplit : extend s q =
          ((([s+3,s+6,s+4,s+5] ++ q.map (embed s)) ++ [0]) ++ [2 * s+9]) ++
            [1] ++ [2 * s+8] := by simp [extend, List.append_assoc]
      rw [hsplit]
      simp only [lengths_snoc, List.getLast?_append_cons, List.getLast?_singleton,
        hend, Option.toList_some, List.map_cons, List.map_nil]
      rw [hpref, he]
      simp [Nat.dist, List.append_assoc]
    rw [hl]
    have hd' := hd.map (·+4)
    have hrange : (List.range' 1 (2 * s+1)).map (·+4) = List.range' 5 (2 * s+1) := by
      simpa [Nat.add_comm] using (List.map_add_range' (a := 4) 1 (2 * s+1) 1)
    rw [hrange] at hd'
    have hperm := ((List.Perm.refl [3,2,1,4]).append hd').append
      (List.Perm.refl [2 * s+6,2 * s+9,2 * s+8,2 * s+7])
    apply hperm.trans
    have hr : List.range' 1 (2*(s+4)+1) =
        [1,2,3,4] ++ List.range' 5 (2 * s+1) ++ [2 * s+6,2 * s+7,2 * s+8,2 * s+9] := by
      have h : ((List.range' 1 4 ++ List.range' 5 (2 * s+1)) ++
          List.range' (2 * s+6) 4) = List.range' 1 (2*(s+4)+1) := by
        have hbase := five_ranges 1 4 (2 * s+1) 4 0 0
        simp only [List.range'_zero, List.append_nil, Nat.add_zero] at hbase
        simpa only [Nat.reduceAdd,
          show 5+(2 * s+1)=2 * s+6 by omega,
          show 4+(2 * s+1)+4=2*(s+4)+1 by omega] using hbase
      have h4 : List.range' (2 * s+6) 4 = [2 * s+6,2 * s+7,2 * s+8,2 * s+9] := by
        simp [List.range', Nat.add_assoc]
      simpa [h4, List.range', List.append_assoc] using h.symm
    rw [hr, List.perm_iff_count]
    intro x
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega

private theorem auxiliary_exists (s : ℕ) (hs : 2 ≤ s) : ∃ q, Auxiliary s q := by
  revert hs
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs
    by_cases h6 : 6 ≤ s
    · obtain ⟨q,hq⟩ := ih (s-4) (by omega) (by omega)
      have he := extension_valid (s-4) (by omega) q hq
      have hsub : s-4+4 = s := by omega
      exact ⟨extend (s-4) q, hsub ▸ he⟩
    · have hb : s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨[1,5,0,3,2,4], by unfold Auxiliary Cross; decide⟩
      · exact ⟨[2,5,3,4,0,7,1,6], by unfold Auxiliary Cross; decide⟩
      · exact ⟨[3,6,4,5,1,9,0,7,2,8], by unfold Auxiliary Cross; decide⟩
      · exact ⟨[4,6,5,8,1,9,3,7,2,11,0,10], by unfold Auxiliary Cross; decide⟩

/-- The two orientations of the exact low/high block map. -/
def blockMap (s L : ℕ) (flip : Bool) (q : ℕ) : ℕ :=
  if flip then
    if q ≤ s then L + 3 * s + 1 - q else L + (2 * s+1-q)
  else
    if q ≤ s then L+q else L+s+q

/-- The unchanged vertex following the replaced block. -/
def attachment (s L : ℕ) (flip : Bool) : ℕ :=
  if flip then L+s+1 else L+2 * s

private theorem block_distance (s L a b : ℕ) (flip : Bool)
    (ha : a < 2 * s + 2) (hb : b < 2 * s + 2) (hab : Cross s a b) :
    Nat.dist (blockMap s L flip a) (blockMap s L flip b) = Nat.dist a b + s := by
  cases flip <;> rcases hab with ⟨hal,hbh⟩ | ⟨hbl,hah⟩ <;>
    dsimp only [blockMap] <;>
    split_ifs <;> simp_all only [Nat.dist] <;> omega

/-- Every size at least two supplies the auxiliary path and both exact block
orientations, including the edge to the unchanged next vertex. -/
theorem exists_two_block_attachment (s L : ℕ) (hs : 2 ≤ s) (flip : Bool) :
    ∃ q : List ℕ, Auxiliary s q ∧
      (lengths (q.map (blockMap s L flip) ++ [attachment s L flip])).Perm
        (List.range' s (2 * s+2)) := by
  obtain ⟨q,hq⟩ := auxiliary_exists s hs
  obtain ⟨hv,hh,ht,hc,hd⟩ := hq
  have hb : ∀ a ∈ q, a < 2 * s+2 := by
    intro a ha
    exact List.mem_range.mp (hv.mem_iff.mp ha)
  have he := lengths_map q s (blockMap s L flip) s hc
    (fun a ha b hb' hab => block_distance s L a b flip (hb a ha) (hb b hb') hab)
  have ht' : (q.map (blockMap s L flip)).getLast? =
      some (blockMap s L flip (2 * s)) := by simp [List.getLast?_map, ht]
  have hseam : Nat.dist (blockMap s L flip (2 * s)) (attachment s L flip) = s := by
    cases flip with
    | false =>
      simp [blockMap, attachment, show ¬ 2 * s ≤ s by omega, Nat.dist]
      omega
    | true =>
      simp [blockMap, attachment, show ¬ 2 * s ≤ s by omega, Nat.dist]
  refine ⟨q,⟨hv,hh,ht,hc,hd⟩,?_⟩
  rw [lengths_snoc, ht']
  simp only [Option.toList_some, List.map_cons, List.map_nil, hseam]
  rw [he]
  have hd' := (hd.map (·+s)).append (List.Perm.refl [s])
  have hr : (List.range' 1 (2 * s+1)).map (·+s) = List.range' (s+1) (2 * s+1) := by
    simpa [Nat.add_comm] using (List.map_add_range' (a := s) 1 (2 * s+1) 1)
  rw [hr] at hd'
  apply hd'.trans
  exact List.perm_append_comm.trans (by simp [List.range'])

end D5.S1.Words.Sequenceability.BipartiteGracefulExtension
