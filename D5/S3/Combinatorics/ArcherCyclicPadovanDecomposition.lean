/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanDecomposition
   mirror-E: none(waiver:cyclic-word-arc-decomposition-for-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Circular avoidance forces the low arc to be consecutive and increasing. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanBlocks
import D5.S3.Combinatorics.ArcherCyclicPadovanRotation
import D5.S3.Combinatorics.ArcherCyclicPadovanTriples
import D5.S3.Combinatorics.ArcherCyclicPadovanPatterns
import D5.S3.Combinatorics.ArcherCyclicTetranacciPatterns
import D5.S3.Combinatorics.ArcherCyclicTetranacciInsertion
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition

open ArcherCyclicDefs ArcherCyclicPadovanBlocks ArcherCyclicPadovanSubwords
open ArcherCyclicTetranacciPatterns

theorem low_arc_forced (L R : List ℕ) (hL : L ≠ [])
    (hperm : (1 :: (L ++ 2 :: R)).Perm
      (List.range' 1 (1 :: (L ++ 2 :: R)).length))
    (havoid : ∀ r < (1 :: (L ++ 2 :: R)).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (L ++ 2 :: R)).rotate r)) :
    (∀ x ∈ L, ∀ y ∈ R, y < x) ∧
      R = List.range' 3 R.length ∧
      (∀ r < (1 :: L).length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: L).rotate r)) := by
  let w := 1 :: (L ++ 2 :: R)
  have hnd : w.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have htailnd : (L ++ 2 :: R).Nodup := by simpa [w] using hnd.of_cons
  have hRnd : (2 :: R).Nodup := (List.nodup_append'.mp htailnd).2.1
  have hnot1 : 1 ∉ L ++ 2 :: R := by simpa [w] using (List.nodup_cons.mp hnd).1
  have hsmallL : ∀ x ∈ L, 2 < x := by
    intro x hx
    have hxw : x ∈ w := by simp [w, hx]
    have hxrange := hperm.mem_iff.mp hxw
    have hxlo := List.left_le_of_mem_range' hxrange
    have hx1 : x ≠ 1 := by
      intro heq
      subst x
      exact hnot1 (by simp [hx])
    have hx2 : x ≠ 2 := by
      intro heq
      subst x
      exact (List.nodup_append'.mp htailnd).2.2 hx (by simp)
    omega
  have hsmallR : ∀ x ∈ R, 2 < x := by
    intro x hx
    have hxw : x ∈ w := by simp [w, hx]
    have hxrange := hperm.mem_iff.mp hxw
    have hxlo := List.left_le_of_mem_range' hxrange
    have hx1 : x ≠ 1 := by
      intro heq
      subst x
      exact hnot1 (by simp [hx])
    have hx2 : x ≠ 2 := by
      intro heq
      subst x
      exact (List.nodup_cons.mp hRnd).1 hx
    omega
  have hzero : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (1 :: (L ++ 2 :: R)) := by
    simpa using havoid 0 (by simp)
  have hsep : ∀ x ∈ L, ∀ y ∈ R, y < x := by
    intro x hx y hy
    exact high_arc_above_low_arc L R htailnd hsmallL hzero x y hx hy
  have hRpair : R.Pairwise (· < ·) := by
    rw [List.pairwise_iff_forall_sublist]
    intro a b hab
    have hRnodup : R.Nodup := hRnd.of_cons
    have hne : a ≠ b := by
      have htwo : [a, b].Nodup := hRnodup.sublist hab
      simpa using (List.nodup_cons.mp htwo).1
    by_contra hnot
    have hba : b < a := by omega
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil L hL
    exact (low_arc_has_no_descent L R havoid hsmallR hsep c hc b a hba) hab
  have htail : (L ++ 2 :: R).Perm (List.range' 2 (L.length + 1 + R.length)) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [List.range', List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hperm
  have hrot : (2 :: R ++ L).Perm (List.range' 2 (L.length + 1 + R.length)) :=
    (List.perm_append_comm (l₁ := 2 :: R) (l₂ := L)).trans htail
  have hpermRL : (R ++ L).Perm (List.range' 3 (R.length + L.length)) := by
    apply List.Perm.cons_inv (a := 2)
    simpa [List.range', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrot
  have hRperm : R.Perm (List.range' 3 R.length) :=
    low_block_perm_initial 3 R L hpermRL (fun x hx y hy => hsep y hy x hx)
  have hReq : R = List.range' 3 R.length :=
    hRperm.eq_of_pairwise' (hRpair.imp (fun h => h.le))
      (List.pairwise_le_range' _)
  have hsub : (1 :: L).Sublist w := by
    simp [w]
  have hhered := circular_avoidance_sublist [1, 3, 2, 4] (1 :: L) w hsub
    (by simpa [w] using havoid)
  exact ⟨hsep, hReq, hhered⟩

end D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition

namespace D5.S3.Combinatorics.ArcherCyclicPadovanRecovery

open ArcherCyclicDefs ArcherCyclicPadovanBlocks
open ArcherCyclicPadovanPatterns ArcherCyclicPadovanDecomposition
open ArcherCyclicPadovanSubwords

theorem recover_high_word (L R : List ℕ) (hL : L ≠ [])
    (hperm : (1 :: (L ++ 2 :: R)).Perm
      (List.range' 1 (1 :: (L ++ 2 :: R)).length))
    (havoid : ∀ r < (1 :: (L ++ 2 :: R)).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (L ++ 2 :: R)).rotate r)) :
    ∃ v : List ℕ, v ≠ [] ∧
      (1 :: v).Perm (List.range' 1 (1 :: v).length) ∧
      (∀ r < (1 :: v).length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: v).rotate r)) ∧
      1 :: (L ++ 2 :: R) =
        1 :: (v.map (raiseHigh (R.length + 2)) ++
          2 :: List.range' 3 ((R.length + 2) - 2)) := by
  obtain ⟨_, hR, hhighavoid⟩ := low_arc_forced L R hL hperm havoid
  let m := R.length + 2
  have hmono : StrictMono (raiseHigh m) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [raiseHigh]
    split_ifs <;> omega
  have htail : (L ++ 2 :: R).Perm
      (List.range' 2 (L.length + 1 + R.length)) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [List.range', List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hperm
  have hrot : ((2 :: R) ++ L).Perm
      (List.range' 2 (R.length + 1 + L.length)) := by
    have hcomm : ((2 :: R) ++ L).Perm (L ++ 2 :: R) := List.perm_append_comm
    convert hcomm.trans htail using 1; congr 1; omega
  have hlow : 2 :: R = List.range' 2 (R.length + 1) := by
    have he : List.range' 2 (1 + R.length) = [2] ++ List.range' 3 R.length := by
      rw [← List.range'_append_1]
      rfl
    calc
      2 :: R = 2 :: List.range' 3 R.length := congrArg (2 :: ·) hR
      _ = [2] ++ List.range' 3 R.length := rfl
      _ = List.range' 2 (R.length + 1) := by
        simpa [Nat.add_comm] using he.symm
  have hrange : List.range' 2 (R.length + 1 + L.length) =
      (2 :: R) ++ List.range' (R.length + 3) L.length := by
    rw [hlow, show R.length + 3 = 2 + (R.length + 1) by omega,
      ← List.range'_append_1]
  have hLperm : L.Perm (List.range' (m + 1) L.length) := by
    rw [hrange] at hrot
    have hh : L.Perm (List.range' (R.length + 3) L.length) :=
      (List.perm_append_left_iff (2 :: R)).mp hrot
    simpa [m, Nat.add_assoc] using hh
  let v := L.map (fun z => z - (m - 1))
  have hvlen : v.length = L.length := by simp [v]
  have hmapRange : (List.range' (m + 1) L.length).map
      (fun z => z - (m - 1)) = List.range' 2 L.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range'_1]
      omega
  have hvTail : v.Perm (List.range' 2 v.length) := by
    rw [hvlen, ← hmapRange]
    exact hLperm.map _
  have hvfull : (1 :: v).Perm (List.range' 1 (1 :: v).length) := by
    have hrange : List.range' 1 (1 :: v).length =
        1 :: List.range' 2 v.length := by
      rw [show (1 :: v).length = 1 + v.length by simp [Nat.add_comm],
        ← List.range'_append_1]
      rfl
    rw [hrange]
    exact hvTail.cons 1
  have hLbound (z : ℕ) (hz : z ∈ L) : m + 1 ≤ z :=
    List.left_le_of_mem_range' (hLperm.mem_iff.mp hz)
  have hinverse : v.map (raiseHigh m) = L := by
    change (L.map (fun z => z - (m - 1))).map (raiseHigh m) = L
    rw [List.map_map]
    calc
      L.map (raiseHigh m ∘ fun z => z - (m - 1)) = L.map id := by
        apply List.map_congr_left
        intro z hz
        have hbound := hLbound z hz
        have hnot : ¬ z - (m - 1) < 2 := by omega
        simp only [Function.comp_def, raiseHigh, hnot, ↓reduceIte, id_eq]
        omega
      _ = L := by simp
  have hf1 : raiseHigh m 1 = 1 := by simp [raiseHigh]
  have hmapword : (1 :: v).map (raiseHigh m) = 1 :: L := by
    simp only [List.map_cons, hf1, hinverse]
  have hvavoid : ∀ r < (1 :: v).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: v).rotate r) := by
    intro r hr hpat
    have hpatmap :=
      (contains_map_iff [1, 3, 2, 4] ((1 :: v).rotate r) (raiseHigh m)
        (hmono)).mpr hpat
    have hrotmap : ((1 :: v).rotate r).map (raiseHigh m) =
        (1 :: L).rotate r := by
      rw [List.map_rotate, hmapword]
    rw [hrotmap] at hpatmap
    exact hhighavoid r (by simpa [hvlen] using hr) hpatmap
  refine ⟨v, ?_, hvfull, hvavoid, ?_⟩
  · intro hnil
    have hzero : L.length = 0 := by simpa [hvlen] using congrArg List.length hnil
    exact hL (List.length_eq_zero_iff.mp hzero)
  · rw [hinverse]
    have hm2 : m - 2 = R.length := by dsimp [m]; omega
    rw [hm2, ← hR]

end D5.S3.Combinatorics.ArcherCyclicPadovanRecovery

namespace D5.S3.Combinatorics.ArcherCyclicPadovanDecompositionConverse

open ArcherCyclicDefs ArcherCyclicPadovanRotation
open ArcherCyclicPadovanMinimumRooted ArcherCyclicPadovanSubwords
open ArcherCyclicPadovanTriples

theorem low_arc_sufficient (L R : List ℕ)
    (hnd : (1 :: (L ++ 2 :: R)).Nodup)
    (hLgt : ∀ x ∈ L, 2 < x)
    (hR : R = List.range' 3 R.length)
    (hsep : ∀ x ∈ L, ∀ y ∈ R, y < x)
    (hhigh : ∀ r < (1 :: L).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: L).rotate r)) :
    ∀ r < (1 :: (L ++ 2 :: R)).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (L ++ 2 :: R)).rotate r) := by
  have hremove {u pre middle post : List ℕ}
      (hsub : u.Sublist (pre ++ middle ++ post))
      (hdisj : ∀ x ∈ u, x ∉ middle) :
      u.Sublist (pre ++ post) := by
    have hsub' : u.Sublist (pre ++ (middle ++ post)) := by
      simpa only [List.append_assoc] using hsub
    obtain ⟨u₁, u₂, hu, hpre, hrest⟩ := List.sublist_append_iff.mp hsub'
    have hpost : u₂.Sublist post := by
      apply hrest.of_sublist_append_right
      intro x hx hxm
      exact hdisj x (hu ▸ List.mem_append.mpr (Or.inr hx)) hxm
    rw [hu]
    exact hpre.append hpost
  let K := 2 :: R
  let w := 1 :: (L ++ K)
  have hKpair : K.Pairwise (· < ·) := by
    change (2 :: R).Pairwise (· < ·)
    rw [hR]
    exact List.pairwise_lt_range' (s := 2) (n := R.length + 1)
  have hKmem (z : ℕ) (hz : z ∈ K) : 2 ≤ z := by
    change z ∈ (2 :: R) at hz
    rcases List.mem_cons.mp hz with rfl | hzR
    · omega
    · rw [hR] at hzR
      have hlow := List.left_le_of_mem_range' hzR
      omega
  have hno213 (b c d : ℕ) (h1b : 1 < b) (hbc : b < c) (hcd : c < d)
      (hsub : [c, b, d].Sublist L) : False := by
    have hocc := (circular_1324_iff_minimum_rooted (1 :: L)).mpr
      ⟨0, by simp, 1, b, c, d, L, by simp, h1b, hbc, hcd, hsub⟩
    obtain ⟨r, hr, hpat⟩ := hocc
    exact hhigh r hr hpat
  have split_unique (a : ℕ) (u v u' v' : List ℕ)
      (heq : w = u ++ a :: v) (heq' : w = u' ++ a :: v') :
      u = u' ∧ v = v' := by
    have hnd' : (u ++ a :: v).Nodup := by simpa [← heq, w, K] using hnd
    have hparts := List.nodup_append'.mp hnd'
    have hau : a ∉ u := by
      intro ha
      exact hparts.2.2 ha (by simp)
    have hav : a ∉ v := (List.nodup_cons.mp hparts.2.1).1
    obtain ⟨hu, _, hv⟩ :=
      (List.append_cons_inj_of_notMem hau hav).mp (heq.symm.trans heq')
    exact ⟨hu, hv⟩
  intro r hr hpat
  have hsome : ∃ s < w.length,
      ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate s) := by
    exact ⟨r, by simpa [w, K] using hr, by simpa [w, K] using hpat⟩
  obtain ⟨s, hs, a, b, c, d, t, hroot, hab, hbc, hcd, htriple⟩ :=
    (circular_1324_iff_minimum_rooted w).mp hsome
  have hsplitRoot : ∃ pre post, w = pre ++ a :: post ∧
      t = post ++ pre := by
    have hdrop : w.drop s ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_drop, List.length_nil] at hlen
      omega
    obtain ⟨z, post, hz⟩ := List.exists_cons_of_ne_nil hdrop
    have hrot := List.rotate_eq_drop_append_take (le_of_lt hs)
    rw [hz] at hrot
    rw [hrot] at hroot
    have hza : z = a := by simpa using (congrArg List.head? hroot)
    subst z
    have ht : t = post ++ w.take s := by
      simpa using (congrArg List.tail hroot).symm
    refine ⟨w.take s, post, ?_, ht⟩
    simpa [hz] using (List.take_append_drop s w).symm
  obtain ⟨pre, post, hsplit, htail⟩ := hsplitRoot
  have hamem : a ∈ w := by rw [hsplit]; simp
  by_cases ha1 : a = 1
  · subst a
    have hcanon : w = ([] : List ℕ) ++ 1 :: (L ++ K) := by simp [w]
    obtain ⟨hpre, hpost⟩ :=
      split_unique 1 [] (L ++ K) pre post hcanon hsplit
    subst pre
    subst post
    have ht : t = L ++ K := by simpa using htail
    rw [ht] at htriple
    have hsepK : ∀ x ∈ L, ∀ y ∈ K, y < x := by
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hyR
      · exact hLgt x hx
      · exact hsep x hx y hyR
    have hsubL := triple_213_in_high L K hsepK hKpair c b d hbc hcd htriple
    exact hno213 b c d hab hbc hcd hsubL
  have hatail : a ∈ L ++ K := by
    change a ∈ (1 :: (L ++ K)) at hamem
    rcases List.mem_cons.mp hamem with h | h
    · exact (ha1 h).elim
    · exact h
  rcases List.mem_append.mp hatail with haL | haK
  · obtain ⟨L₁, L₂, hLsplit⟩ := List.mem_iff_append.mp haL
    have hcanon : w = (1 :: L₁) ++ a :: (L₂ ++ K) := by
      simp [w, hLsplit, List.append_assoc]
    obtain ⟨hpre, hpost⟩ :=
      split_unique a (1 :: L₁) (L₂ ++ K) pre post hcanon hsplit
    subst pre
    subst post
    have htriple' : [c, b, d].Sublist (L₂ ++ K ++ (1 :: L₁)) := by
      simpa [htail, List.append_assoc] using htriple
    have hnotK (z : ℕ) (hz : z ∈ [c, b, d]) : z ∉ K := by
      intro hzK
      have hza : a < z := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega
      rcases List.mem_cons.mp hzK with rfl | hzR
      · have := hLgt a haL
        omega
      · have := hsep a haL z hzR
        omega
    have hhighSub : [c, b, d].Sublist (L₂ ++ 1 :: L₁) :=
      hremove htriple' hnotK
    have hword : (1 :: L) = (1 :: L₁) ++ a :: L₂ := by
      simp [hLsplit]
    have hrot : (1 :: L).rotate (1 :: L₁).length =
        a :: (L₂ ++ 1 :: L₁) := by
      rw [hword]
      simp [List.append_assoc, List.rotate_append_length_eq]
    have hindex : (1 :: L₁).length < (1 :: L).length := by
      rw [hword]
      simp
    have hocc := (circular_1324_iff_minimum_rooted (1 :: L)).mpr
      ⟨(1 :: L₁).length, hindex, a, b, c, d, L₂ ++ 1 :: L₁,
        hrot, hab, hbc, hcd, hhighSub⟩
    obtain ⟨r', hr', hpat'⟩ := hocc
    exact hhigh r' hr' hpat'
  · obtain ⟨K₁, K₂, hKsplit⟩ := List.mem_iff_append.mp haK
    have hcanon : w = ((1 :: L) ++ K₁) ++ a :: K₂ := by
      simp [w, hKsplit, List.append_assoc]
    obtain ⟨hpre, hpost⟩ :=
      split_unique a ((1 :: L) ++ K₁) K₂ pre post hcanon hsplit
    subst pre
    subst post
    have hKpair' : (K₁ ++ a :: K₂).Pairwise (· < ·) := by
      simpa [← hKsplit] using hKpair
    have hKparts := List.pairwise_append.mp hKpair'
    have hK₁below : ∀ z ∈ K₁, z < a := by
      intro z hz
      exact hKparts.2.2 z hz a (by simp)
    have hK₂pair : K₂.Pairwise (· < ·) :=
      (List.pairwise_cons.mp hKparts.2.1).2
    have hK₂above : ∀ z ∈ K₂, a < z :=
      (List.pairwise_cons.mp hKparts.2.1).1
    have ha2 : 2 ≤ a := hKmem a haK
    have hK₂memR : ∀ z ∈ K₂, z ∈ R := by
      intro z hz
      have hzK : z ∈ K := by
        rw [hKsplit]
        exact List.mem_append.mpr (Or.inr (by simp [hz]))
      rcases List.mem_cons.mp hzK with hz2 | hzR
      · have := hK₂above z hz
        omega
      · exact hzR
    have hK₂sep : ∀ z ∈ K₂, ∀ y ∈ L, z < y := by
      intro z hz y hy
      exact hsep y hy z (hK₂memR z hz)
    have htriple' : [c, b, d].Sublist ((K₂ ++ 1 :: L) ++ K₁) := by
      simpa [htail, List.append_assoc] using htriple
    have hnotK₁ (z : ℕ) (hz : z ∈ [c, b, d]) : z ∉ K₁ := by
      intro hzK₁
      have hza : a < z := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega
      have := hK₁below z hzK₁
      omega
    have hwithoutK₁ : [c, b, d].Sublist (K₂ ++ 1 :: L) :=
      htriple'.of_sublist_append_left hnotK₁
    have hwithout1 : [c, b, d].Sublist (K₂ ++ L) := by
      apply hremove (middle := [1])
        (by simpa [List.append_assoc] using hwithoutK₁)
      intro z hz hz1
      have hzEq : z = 1 := by simpa using hz1
      have hza : a < z := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega
      omega
    have hsubL := triple_213_after_low K₂ L hK₂pair hK₂sep
      c b d hbc hwithout1
    exact hno213 b c d (by omega) hbc hcd hsubL

end D5.S3.Combinatorics.ArcherCyclicPadovanDecompositionConverse

namespace D5.S3.Combinatorics.ArcherCyclicPadovanInsertTwo

open ArcherCyclicDefs ArcherCyclicPadovanRotation
open ArcherCyclicPadovanMinimumRooted ArcherCyclicPadovanSubwords
open ArcherCyclicPadovanTriples

theorem circular_avoidance_insert_two (R : List ℕ)
    (hnd : (1 :: 2 :: R).Nodup) (hgt : ∀ z ∈ R, 2 < z) :
    (∀ r < (1 :: 2 :: R).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: 2 :: R).rotate r)) ↔
      (∀ r < (1 :: R).length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: R).rotate r)) := by
  have hremove {u pre middle post : List ℕ}
      (hsub : u.Sublist (pre ++ middle ++ post))
      (hdisj : ∀ x ∈ u, x ∉ middle) :
      u.Sublist (pre ++ post) := by
    have hsub' : u.Sublist (pre ++ (middle ++ post)) := by
      simpa only [List.append_assoc] using hsub
    obtain ⟨u₁, u₂, hu, hpre, hrest⟩ := List.sublist_append_iff.mp hsub'
    have hpost : u₂.Sublist post := by
      apply hrest.of_sublist_append_right
      intro x hx hxm
      exact hdisj x (hu ▸ List.mem_append.mpr (Or.inr hx)) hxm
    rw [hu]
    exact hpre.append hpost
  constructor
  · intro h
    have hsub : (1 :: R).Sublist (1 :: 2 :: R) :=
      (List.Sublist.cons 2 (List.Sublist.refl R)).cons_cons 1
    exact circular_avoidance_sublist [1, 3, 2, 4] (1 :: R) (1 :: 2 :: R) hsub h
  · intro hshort
    let w := 1 :: 2 :: R
    have hno213 (b c d : ℕ) (h1b : 1 < b) (hbc : b < c) (hcd : c < d)
        (hsub : [c, b, d].Sublist R) : False := by
      have hocc := (circular_1324_iff_minimum_rooted (1 :: R)).mpr
        ⟨0, by simp, 1, b, c, d, R, by simp, h1b, hbc, hcd, hsub⟩
      obtain ⟨r, hr, hpat⟩ := hocc
      exact hshort r hr hpat
    have split_unique (a : ℕ) (u v u' v' : List ℕ)
        (heq : w = u ++ a :: v) (heq' : w = u' ++ a :: v') :
        u = u' ∧ v = v' := by
      have hnd' : (u ++ a :: v).Nodup := by simpa [← heq, w] using hnd
      have hparts := List.nodup_append'.mp hnd'
      have hau : a ∉ u := by
        intro ha
        exact hparts.2.2 ha (by simp)
      have hav : a ∉ v := (List.nodup_cons.mp hparts.2.1).1
      obtain ⟨hu, _, hv⟩ :=
        (List.append_cons_inj_of_notMem hau hav).mp (heq.symm.trans heq')
      exact ⟨hu, hv⟩
    intro r hr hpat
    have hsome : ∃ s < w.length,
        ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate s) :=
      ⟨r, by simpa [w] using hr, by simpa [w] using hpat⟩
    obtain ⟨s, hs, a, b, c, d, t, hroot, hab, hbc, hcd, htriple⟩ :=
      (circular_1324_iff_minimum_rooted w).mp hsome
    have hsplitRoot : ∃ pre post, w = pre ++ a :: post ∧
        t = post ++ pre := by
      have hdrop : w.drop s ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp only [List.length_drop, List.length_nil] at hlen
        omega
      obtain ⟨z, post, hz⟩ := List.exists_cons_of_ne_nil hdrop
      have hrot := List.rotate_eq_drop_append_take (le_of_lt hs)
      rw [hz] at hrot
      rw [hrot] at hroot
      have hza : z = a := by simpa using (congrArg List.head? hroot)
      subst z
      have ht : t = post ++ w.take s := by
        simpa using (congrArg List.tail hroot).symm
      refine ⟨w.take s, post, ?_, ht⟩
      simpa [hz] using (List.take_append_drop s w).symm
    obtain ⟨pre, post, hsplit, htail⟩ := hsplitRoot
    have hamem : a ∈ w := by rw [hsplit]; simp
    by_cases ha1 : a = 1
    · subst a
      have hcanon : w = ([] : List ℕ) ++ 1 :: (2 :: R) := by simp [w]
      obtain ⟨hpre, hpost⟩ :=
        split_unique 1 [] (2 :: R) pre post hcanon hsplit
      subst pre
      subst post
      have ht : t = 2 :: R := by simpa using htail
      rw [ht] at htriple
      have hpair : ([2] : List ℕ).Pairwise (· < ·) := by simp
      have hsubR := triple_213_after_low [2] R hpair
        (by intro x hx y hy; simp only [List.mem_singleton] at hx; subst x; exact hgt y hy)
        c b d hbc (by simpa using htriple)
      exact hno213 b c d hab hbc hcd hsubR
    by_cases ha2 : a = 2
    · subst a
      have hcanon : w = [1] ++ 2 :: R := by simp [w]
      obtain ⟨hpre, hpost⟩ :=
        split_unique 2 [1] R pre post hcanon hsplit
      subst pre
      subst post
      have ht : t = R ++ [1] := by simpa using htail
      rw [ht] at htriple
      have hsubR : [c, b, d].Sublist R := by
        apply htriple.of_sublist_append_left
        intro z hz hz1
        have hzEq : z = 1 := by simpa using hz1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega
      exact hno213 b c d (by omega) hbc hcd hsubR
    have haR : a ∈ R := by
      change a ∈ (1 :: 2 :: R) at hamem
      rcases List.mem_cons.mp hamem with h1 | htailmem
      · exact (ha1 h1).elim
      rcases List.mem_cons.mp htailmem with h2 | hR
      · exact (ha2 h2).elim
      · exact hR
    obtain ⟨R₁, R₂, hRsplit⟩ := List.mem_iff_append.mp haR
    have hcanon : w = (1 :: 2 :: R₁) ++ a :: R₂ := by
      simp [w, hRsplit]
    obtain ⟨hpre, hpost⟩ :=
      split_unique a (1 :: 2 :: R₁) R₂ pre post hcanon hsplit
    subst pre
    subst post
    have htriple' : [c, b, d].Sublist ((R₂ ++ [1]) ++ [2] ++ R₁) := by
      simpa [htail, List.append_assoc] using htriple
    have hnot2 (z : ℕ) (hz : z ∈ [c, b, d]) : z ∉ [2] := by
      intro hz2
      have hzEq : z = 2 := by simpa using hz2
      have hza : a < z := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega
      have hga := hgt a haR
      omega
    have hshortSub : [c, b, d].Sublist (R₂ ++ 1 :: R₁) := by
      have h := hremove htriple' hnot2
      simpa [List.append_assoc] using h
    have hword : (1 :: R) = (1 :: R₁) ++ a :: R₂ := by
      simp [hRsplit]
    have hrot : (1 :: R).rotate (1 :: R₁).length =
        a :: (R₂ ++ 1 :: R₁) := by
      rw [hword]
      simp [List.append_assoc, List.rotate_append_length_eq]
    have hindex : (1 :: R₁).length < (1 :: R).length := by
      rw [hword]
      simp
    have hocc := (circular_1324_iff_minimum_rooted (1 :: R)).mpr
      ⟨(1 :: R₁).length, hindex, a, b, c, d, R₂ ++ 1 :: R₁,
        hrot, hab, hbc, hcd, hshortSub⟩
    obtain ⟨r', hr', hpat'⟩ := hocc
    exact hshort r' hr' hpat'

end D5.S3.Combinatorics.ArcherCyclicPadovanInsertTwo

namespace D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition

open ArcherCyclicDefs ArcherCyclicPadovanPatterns
open ArcherCyclicPadovanDecompositionConverse

theorem inserted_word_circular_avoid (v : List ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hv : (1 :: v).Perm (List.range' 1 (1 :: v).length))
    (havoid : ∀ r < (1 :: v).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: v).rotate r)) :
    ∀ r < (1 :: (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2))).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4
        ((1 :: (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2))).rotate r) := by
  have hwordPerm :
      (1 :: (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2))).Perm
        (List.range' 1 (v.length + m)) := by
    have hvTail : v.Perm (List.range' 2 v.length) := by
      apply List.Perm.cons_inv (a := 1)
      simpa [List.range', Nat.add_comm] using hv
    have hmapRange : (List.range' 2 v.length).map (raiseHigh m) =
        List.range' (m + 1) v.length := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_range'_1] at hi ⊢
        simp only [raiseHigh]
        split_ifs <;> omega
    have hhigh : (v.map (raiseHigh m)).Perm (List.range' (m + 1) v.length) := by
      rw [← hmapRange]
      exact hvTail.map (raiseHigh m)
    have hlow : 2 :: List.range' 3 (m - 2) = List.range' 2 (m - 1) := by
      have hsub : m - 1 = (m - 2) + 1 := by omega
      rw [hsub]
      rfl
    have hjoin : (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2)).Perm
        (List.range' 2 (m - 1 + v.length)) := by
      have h₁ := hhigh.append_right (2 :: List.range' 3 (m - 2))
      have h₂ : (List.range' (m + 1) v.length ++ 2 :: List.range' 3 (m - 2)).Perm
          ((2 :: List.range' 3 (m - 2)) ++ List.range' (m + 1) v.length) :=
        List.perm_append_comm
      have h₃ : (2 :: List.range' 3 (m - 2)) ++ List.range' (m + 1) v.length =
          List.range' 2 (m - 1 + v.length) := by
        rw [hlow]
        have hstart : 2 + (m - 1) = m + 1 := by omega
        rw [← hstart, List.range'_append_1]
      exact (h₁.trans h₂).trans (h₃ ▸ List.Perm.refl _)
    have hfinal : 1 :: List.range' 2 (m - 1 + v.length) =
        List.range' 1 (v.length + m) := by
      have hlen : v.length + m = (m - 1 + v.length) + 1 := by omega
      rw [hlen]
      rfl
    rw [← hfinal]
    exact hjoin.cons 1
  let f := raiseHigh m
  have hmono : StrictMono (raiseHigh m) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [raiseHigh]
    split_ifs <;> omega
  have hperm := hwordPerm
  have hnd : (1 :: (v.map f ++ 2 :: List.range' 3 (m - 2))).Nodup :=
    hperm.nodup_iff.mpr List.nodup_range'
  have hvTail : v.Perm (List.range' 2 v.length) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [List.range', Nat.add_comm] using hv
  have hhighgt : ∀ x ∈ v.map f, 2 < x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    have hzlow := List.left_le_of_mem_range' (hvTail.mem_iff.mp hz)
    have hz2 : ¬ z < 2 := by omega
    simp only [f, raiseHigh, hz2, ↓reduceIte]
    omega
  have hsep : ∀ x ∈ v.map f, ∀ y ∈ List.range' 3 (m - 2), y < x := by
    intro x hx y hy
    have hxgt := hhighgt x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    have hzlow := List.left_le_of_mem_range' (hvTail.mem_iff.mp hz)
    obtain ⟨j, hj, hyj⟩ := List.mem_range'.mp hy
    have hz2 : ¬ z < 2 := by omega
    simp only [f, raiseHigh, hz2, ↓reduceIte]
    omega
  have hhighavoid : ∀ r < (1 :: v.map f).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: v.map f).rotate r) := by
    intro r hr hocc
    have hf1 : f 1 = 1 := by simp [f, raiseHigh]
    have hmap : (1 :: v.map f).rotate r = ((1 :: v).rotate r).map f := by
      simp [hf1, List.map_rotate]
    rw [hmap] at hocc
    have hraw := (contains_map_iff [1, 3, 2, 4] ((1 :: v).rotate r) f
      (hmono)).mp hocc
    exact havoid r (by simpa using hr) hraw
  exact low_arc_sufficient (v.map f) (List.range' 3 (m - 2))
    hnd hhighgt (by simp) hsep hhighavoid

end D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition

namespace D5.S3.Combinatorics.ArcherCyclicPadovanFrontRecovery

open ArcherCyclicDefs ArcherCyclicPadovanPatterns
open ArcherCyclicPadovanInsertTwo ArcherCyclicTetranacciInsertion

theorem recover_front_word (R : List ℕ)
    (hperm : (1 :: 2 :: R).Perm (List.range' 1 (1 :: 2 :: R).length))
    (hcircle : ∀ r < (1 :: 2 :: R).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: 2 :: R).rotate r)) :
    ∃ s : List ℕ,
      (1 :: s).Perm (List.range' 1 (1 :: s).length) ∧
      (∀ r < (1 :: s).length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r)) ∧
      1 :: 2 :: R = insertWord 1 (1 :: s) := by
  have hmono : StrictMono (raiseHigh 2) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [raiseHigh]
    split_ifs <;> omega
  have htail : (2 :: R).Perm (List.range' 2 (R.length + 1)) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [List.range', Nat.add_assoc, Nat.add_comm] using hperm
  have hR : R.Perm (List.range' 3 R.length) := by
    apply List.Perm.cons_inv (a := 2)
    simpa [List.range', Nat.add_assoc] using htail
  let s := R.map (fun z => z - 1)
  have hslen : s.length = R.length := by simp [s]
  have hmapRange : (List.range' 3 R.length).map (fun z => z - 1) =
      List.range' 2 R.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range'_1]
      omega
  have hsTail : s.Perm (List.range' 2 s.length) := by
    rw [hslen, ← hmapRange]
    exact hR.map _
  have hsperm : (1 :: s).Perm (List.range' 1 (1 :: s).length) := by
    have hrange : List.range' 1 (1 :: s).length =
        1 :: List.range' 2 s.length := by
      rw [show (1 :: s).length = 1 + s.length by simp [Nat.add_comm],
        ← List.range'_append_1]
      rfl
    rw [hrange]
    exact hsTail.cons 1
  have hRgt (z : ℕ) (hz : z ∈ R) : 2 < z :=
    List.left_le_of_mem_range' (hR.mem_iff.mp hz)
  have hinverse : s.map (fun z => 1 + z) = R := by
    change (R.map (fun z => z - 1)).map (fun z => 1 + z) = R
    rw [List.map_map]
    calc
      R.map ((fun z => 1 + z) ∘ fun z => z - 1) = R.map id := by
        apply List.map_congr_left
        intro z hz
        simp only [Function.comp_def, id_eq]
        have := hRgt z hz
        omega
      _ = R := by simp
  have hnd : (1 :: 2 :: R).Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hsmallR := (circular_avoidance_insert_two R hnd hRgt).mp hcircle
  have hsge (z : ℕ) (hz : z ∈ s) : 2 ≤ z :=
    List.left_le_of_mem_range' (hsTail.mem_iff.mp hz)
  have hmapword : (1 :: s).map (raiseHigh 2) = 1 :: R := by
    have hmaptail : s.map (raiseHigh 2) = R := by
      calc
        s.map (raiseHigh 2) = s.map (fun z => 1 + z) := by
          apply List.map_congr_left
          intro z hz
          have hnot : ¬ z < 2 := by have := hsge z hz; omega
          simp only [raiseHigh, hnot, ↓reduceIte]
          omega
        _ = R := hinverse
    simp [hmaptail, raiseHigh]
  have hscircle : ∀ r < (1 :: s).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r) := by
    intro r hr hpat
    have hmap := (contains_map_iff [1, 3, 2, 4] ((1 :: s).rotate r) (raiseHigh 2)
      (hmono)).mpr hpat
    have hrot : ((1 :: s).rotate r).map (raiseHigh 2) =
        (1 :: R).rotate r := by rw [List.map_rotate, hmapword]
    rw [hrot] at hmap
    exact hsmallR r (by simpa [hslen] using hr) hmap
  refine ⟨s, hsperm, hscircle, ?_⟩
  simp [insertWord, hinverse, List.map_cons]

end D5.S3.Combinatorics.ArcherCyclicPadovanFrontRecovery
