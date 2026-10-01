/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanPatterns
   mirror-E: none(waiver:pattern-insertion-for-cyclic-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Pattern tests and monotone relabeling support the cyclic Padovan block decomposition. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanPatterns

open ArcherCyclicDefs

theorem contains_map_iff (ν p : List ℕ) (f : ℕ → ℕ) (hf : StrictMono f) :
    ArrowWilfDefs.Contains ν [] ν.length (p.map f) ↔
      ArrowWilfDefs.Contains ν [] ν.length p := by
  constructor
  · rintro ⟨x, hx, hm, hs, ha⟩
    let y : ℕ → ℕ := fun i => Function.invFun f (x i)
    have hrep (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ ν.length) : f (y i) = x i := by
      apply Function.invFun_eq
      rcases List.mem_map.mp (hm i hi hik) with ⟨a, _, ha⟩
      exact ⟨a, ha⟩
    have hleft (z : ℕ) : Function.invFun f (f z) = z :=
      Function.leftInverse_invFun hf.injective z
    have hsub : (ν.map y).Sublist p := by
      have hs' := hs.map (Function.invFun f)
      simpa [y, List.map_map, Function.comp_def, hleft] using hs'
    refine ⟨y, ?_, ?_, hsub, by simp⟩
    · intro i hi hik
      apply hf.lt_iff_lt.mp
      rw [hrep i hi (by omega), hrep (i + 1) (by omega) (by omega)]
      exact hx i hi hik
    · intro i hi hik
      obtain ⟨a, ha, hfa⟩ := List.mem_map.mp (hm i hi hik)
      have hy : y i = a := by simp [y, ← hfa, hleft]
      simpa [hy] using ha
  · rintro ⟨x, hx, hm, hs, ha⟩
    let y : ℕ → ℕ := fun i => f (x i)
    refine ⟨y, ?_, ?_, ?_, by simp⟩
    · intro i hi hik
      exact hf (hx i hi hik)
    · intro i hi hik
      exact List.mem_map.mpr ⟨x i, hm i hi hik, rfl⟩
    · simpa [y, List.map_map, Function.comp_def] using hs.map f

end D5.S3.Combinatorics.ArcherCyclicPadovanPatterns

namespace D5.S3.Combinatorics.ArcherCyclicPadovanOneLine

open ArcherCyclicDefs

theorem contains_4132_high_one_iff (a : ℕ) (q : List ℕ)
    (ha : 1 < a) (hq : ∀ z ∈ q, 1 < z) :
    ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (a :: 1 :: q) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q ∨
        ∃ c d, [c, d].Sublist q ∧ d < c ∧ c < a := by
  constructor
  · rintro ⟨x, hx, hm, hs, ht⟩
    have h12 : x 1 < x 2 := hx 1 (by omega) (by simp)
    have h23 : x 2 < x 3 := hx 2 (by omega) (by simp)
    have h34 : x 3 < x 4 := hx 3 (by omega) (by simp)
    have h1ge : 1 ≤ x 1 := by
      have hmem := hm 1 (by omega) (by simp)
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h
      · omega
      · omega
      · exact (hq _ h).le
    have h4gt : 1 < x 4 := by omega
    change [x 4, x 1, x 3, x 2].Sublist (a :: 1 :: q) at hs
    rcases List.cons_sublist_cons'.mp hs with htail | ⟨hfirst, htail⟩
    · rcases List.cons_sublist_cons'.mp htail with hqsub | ⟨hfirst1, _⟩
      · left
        refine ⟨x, hx, ?_, hqsub, by simp⟩
        intro i hi hik
        apply hqsub.subset
        have hik' : i ≤ 4 := by simpa using hik
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases hi' with rfl | rfl | rfl | rfl <;> simp
      · omega
    · right
      have hcd : [x 3, x 2].Sublist (1 :: q) :=
        (List.Sublist.cons _ (List.Sublist.refl _)).trans htail
      rcases List.cons_sublist_cons'.mp hcd with hqsub | ⟨hfirst1, _⟩
      · refine ⟨x 3, x 2, hqsub, h23, ?_⟩
        omega
      · omega
  · rintro (hinside | ⟨c, d, hcd, hdc, hca⟩)
    · rcases hinside with ⟨x, hx, hm, hs, ht⟩
      refine ⟨x, hx, ?_, ?_, by simp⟩
      · intro i hi hik
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm i hi hik))
      · exact List.sublist_cons_of_sublist _ (List.sublist_cons_of_sublist _ hs)
    · have hdq : d ∈ q := hcd.subset (by simp)
      have h1d := hq d hdq
      let x : ℕ → ℕ := fun i =>
        if i = 1 then 1 else if i = 2 then d else if i = 3 then c else a
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro i hi hik
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by
          have hik' : i < 4 := by simpa using hik
          omega
        rcases hi' with rfl | rfl | rfl <;> simp [x] <;> omega
      · intro i hi hik
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
          have hik' : i ≤ 4 := by simpa using hik
          omega
        rcases hi' with rfl | rfl | rfl | rfl <;>
          simp [x, hcd.subset (by simp : c ∈ [c, d]), hdq]
      · change [a, 1, c, d].Sublist (a :: 1 :: q)
        exact hcd.cons_cons 1 |>.cons_cons a

end D5.S3.Combinatorics.ArcherCyclicPadovanOneLine

namespace D5.S3.Combinatorics.ArcherCyclicPadovanMiddle

open ArcherCyclicDefs

theorem contains_4132_increasing_middle_iff (mid q : List ℕ)
    (hmid : mid.Pairwise (· < ·))
    (hq : ∀ z ∈ q, z = 1 ∨ z = 2 ∨ ∀ y ∈ mid, y < z) :
    ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (mid ++ q) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q := by
  constructor
  · rintro ⟨x, hx, hm, hs, ht⟩
    have h12 : x 1 < x 2 := hx 1 (by omega) (by simp)
    have h23 : x 2 < x 3 := hx 2 (by omega) (by simp)
    have h34 : x 3 < x 4 := hx 3 (by omega) (by simp)
    change [x 4, x 1, x 3, x 2].Sublist (mid ++ q) at hs
    obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hs
    rcases u with _ | ⟨z, us⟩
    · have hqsub : [x 4, x 1, x 3, x 2].Sublist q := by
        simpa using huv ▸ hv
      refine ⟨x, hx, ?_, hqsub, by simp⟩
      intro i hi hik
      apply hqsub.subset
      have hik' : i ≤ 4 := by simpa using hik
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi' with rfl | rfl | rfl | rfl <;> simp
    · rcases us with _ | ⟨z', us'⟩
      · have hz : z = x 4 := by simpa using (congrArg List.head? huv).symm
        subst z
        have hvEq : [x 1, x 3, x 2] = v := by
          simpa using congrArg List.tail huv
        have hv' : [x 1, x 3, x 2].Sublist q := by simpa [← hvEq] using hv
        have hx4mid : x 4 ∈ mid := hu.subset (by simp)
        have hx1q : x 1 ∈ q := hv'.subset (by simp)
        have hx2q : x 2 ∈ q := hv'.subset (by simp)
        have hx3q : x 3 ∈ q := hv'.subset (by simp)
        have hsmall (i : ℕ) (hi : i = 1 ∨ i = 2 ∨ i = 3)
            (hmem : x i ∈ q) : x i = 1 ∨ x i = 2 := by
          rcases hq (x i) hmem with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have hlt := h (x 4) hx4mid
            rcases hi with rfl | rfl | rfl <;> omega
        have h1 := hsmall 1 (Or.inl rfl) hx1q
        have h2 := hsmall 2 (Or.inr (Or.inl rfl)) hx2q
        have h3 := hsmall 3 (Or.inr (Or.inr rfl)) hx3q
        omega
      · have hfirst : z = x 4 := by simpa using (congrArg List.head? huv).symm
        have hsecond : z' = x 1 := by
          have htail := congrArg List.tail huv
          simpa using (congrArg List.head? htail).symm
        subst z
        subst z'
        have hpair : [x 4, x 1].Sublist mid := by
          exact (List.Sublist.cons_cons (x 4)
            (List.Sublist.cons_cons (x 1) (List.nil_sublist _))).trans hu
        have hlt : x 4 < x 1 := (List.pairwise_iff_forall_sublist.mp hmid) hpair
        omega
  · rintro ⟨x, hx, hm, hs, ht⟩
    refine ⟨x, hx, ?_, List.sublist_append_of_sublist_right hs, by simp⟩
    intro i hi hik
    exact List.mem_append.mpr (Or.inr (hm i hi hik))

theorem descent_tail_in_q (mid q : List ℕ)
    (hmid : mid.Pairwise (· < ·))
    (hmidgt : ∀ z ∈ mid, 2 < z)
    (hq : ∀ z ∈ q, z = 2 ∨ ∀ y ∈ mid, y < z)
    (b c d : ℕ) (hb : 1 ≤ b) (hbd : b < d) (hdc : d < c)
    (htriple : [b, c, d].Sublist (mid ++ 1 :: q)) :
    [c, d].Sublist q := by
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp htriple
  have hcp : 1 < c := by omega
  have hpair_tail (h : [c, d].Sublist (1 :: q)) : [c, d].Sublist q := by
    rcases List.cons_sublist_cons'.mp h with hqsub | ⟨hc1, _⟩
    · exact hqsub
    · omega
  rcases u with _ | ⟨z, us⟩
  · have hvEq : [b, c, d] = v := by simpa using huv
    have htail : [c, d].Sublist (1 :: q) :=
      (List.Sublist.cons _ (List.Sublist.refl _)).trans (by simpa [← hvEq] using hv)
    exact hpair_tail htail
  · have hz : z = b := by simpa using (congrArg List.head? huv).symm
    subst z
    rcases us with _ | ⟨z', us'⟩
    · have hvEq : [c, d] = v := by
        simpa using congrArg List.tail huv
      exact hpair_tail (by simpa [← hvEq] using hv)
    · have hz' : z' = c := by
        have htail := congrArg List.tail huv
        simpa using (congrArg List.head? htail).symm
      subst z'
      have hbc : [b, c].Sublist mid := by
        exact (List.Sublist.cons_cons b
          (List.Sublist.cons_cons c (List.nil_sublist _))).trans hu
      have hbmid : b ∈ mid := hbc.subset (by simp)
      have hcmid : c ∈ mid := hbc.subset (by simp)
      rcases us' with _ | ⟨z'', us''⟩
      · have hvEq : [d] = v := by
          have htail := congrArg List.tail (congrArg List.tail huv)
          simpa using htail
        have hdmem : d ∈ (1 :: q) := hv.subset (by simp [← hvEq])
        rcases List.mem_cons.mp hdmem with hd1 | hdq
        · omega
        · rcases hq d hdq with hd2 | hhigh
          · have hgt := hmidgt b hbmid
            omega
          · have hcd := hhigh c hcmid
            omega
      · have hz'' : z'' = d := by
          have htail := congrArg List.tail (congrArg List.tail huv)
          simpa using (congrArg List.head? htail).symm
        subst z''
        have hcdsub : [c, d].Sublist mid := by
          have hsub : [c, d].Sublist (b :: c :: d :: us'') :=
            List.Sublist.cons _ (List.Sublist.cons_cons c
              (List.Sublist.cons_cons d (List.nil_sublist _)))
          exact hsub.trans hu
        have hcd := (List.pairwise_iff_forall_sublist.mp hmid) hcdsub
        omega

end D5.S3.Combinatorics.ArcherCyclicPadovanMiddle

namespace D5.S3.Combinatorics.ArcherCyclicPadovanBlockPattern

open ArcherCyclicDefs ArcherCyclicPadovanOneLine ArcherCyclicPadovanMiddle

theorem contains_4132_high_middle_iff (a : ℕ) (mid q : List ℕ)
    (ha : 1 < a) (hmid : mid.Pairwise (· < ·))
    (hmidgt : ∀ z ∈ mid, 2 < z)
    (hqgt : ∀ z ∈ q, 1 < z)
    (hq : ∀ z ∈ q, z = 2 ∨ ∀ y ∈ mid, y < z) :
    ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (a :: (mid ++ 1 :: q)) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (a :: 1 :: q) := by
  constructor
  · rintro ⟨x, hx, hm, hs, ht⟩
    have h12 : x 1 < x 2 := hx 1 (by omega) (by simp)
    have h23 : x 2 < x 3 := hx 2 (by omega) (by simp)
    have h34 : x 3 < x 4 := hx 3 (by omega) (by simp)
    change [x 4, x 1, x 3, x 2].Sublist (a :: (mid ++ 1 :: q)) at hs
    rcases List.cons_sublist_cons'.mp hs with htail | ⟨hfirst, htriple⟩
    · have hqmid : ∀ z ∈ (1 :: q),
          z = 1 ∨ z = 2 ∨ ∀ y ∈ mid, y < z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzq
        · exact Or.inl rfl
        · rcases hq z hzq with h2 | hhigh
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr hhigh)
      have hoccTail : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (mid ++ 1 :: q) := by
        refine ⟨x, hx, ?_, htail, by simp⟩
        intro i hi hik
        apply htail.subset
        have hik' : i ≤ 4 := by simpa using hik
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases hi' with rfl | rfl | rfl | rfl <;> simp
      have htailOcc :=
        (contains_4132_increasing_middle_iff mid (1 :: q) hmid hqmid).mp hoccTail
      rcases htailOcc with ⟨y, hy, hym, hys, hyt⟩
      refine ⟨y, hy, ?_, List.sublist_cons_of_sublist a hys, by simp⟩
      intro i hi hik
      exact List.mem_cons_of_mem a (hym i hi hik)
    · have hx1ge : 1 ≤ x 1 := by
        have hmem : x 1 ∈ mid ++ 1 :: q :=
          htriple.subset (by simp)
        rcases List.mem_append.mp hmem with hmidmem | htailmem
        · have hgt := hmidgt (x 1) hmidmem
          omega
        · rcases List.mem_cons.mp htailmem with h1 | hqmem
          · omega
          · exact (hqgt _ hqmem).le
      have hcd := descent_tail_in_q mid q hmid hmidgt hq
        (x 1) (x 3) (x 2) hx1ge h12 h23 htriple
      apply (contains_4132_high_one_iff a q ha hqgt).mpr
      right
      refine ⟨x 3, x 2, hcd, h23, ?_⟩
      omega
  · rintro ⟨x, hx, hm, hs, ht⟩
    have hsub : (a :: 1 :: q).Sublist (a :: (mid ++ 1 :: q)) :=
      (List.sublist_append_right mid (1 :: q)).cons_cons a
    refine ⟨x, hx, ?_, hs.trans hsub, by simp⟩
    intro i hi hik
    exact hsub.subset (hm i hi hik)

end D5.S3.Combinatorics.ArcherCyclicPadovanBlockPattern

namespace D5.S3.Combinatorics.ArcherCyclicPadovanPatterns

/-- Fixes the root label and shifts all other positive labels past a low block. -/
def raiseHigh (m x : ℕ) : ℕ := if x < 2 then x else x + (m - 1)

end D5.S3.Combinatorics.ArcherCyclicPadovanPatterns
