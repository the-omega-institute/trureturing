/- GID: D5/S3/Arith/Congruence/NonsquarefreeAntirun
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/NonsquarefreeAntirun
   mirror-E: none(waiver:universal-bound-with-private-sharpness-example)
   anchors: [mathlib/module/Mathlib.Data.Nat.Squarefree]
   utility: none
   digest: Full nonsquarefree antiruns have at most nine entries. -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.NonsquarefreeAntirun

/-- A strictly increasing list of nonsquarefree natural numbers containing every nonsquarefree
number between any two of its entries. In particular, this is an interval of positions in the
increasing enumeration, rather than an arbitrarily selected subsequence. -/
structure FullNonsquarefreeInterval (l : List ℕ) : Prop where
  increasing : l.Pairwise (· < ·)
  nonsquarefree : ∀ n ∈ l, ¬ Squarefree n
  full : ∀ a ∈ l, ∀ b ∈ l, ∀ n, a ≤ n → n ≤ b → ¬ Squarefree n → n ∈ l

private theorem no_neighbors {l : List ℕ} (hgap : l.IsChain (fun x y => x + 1 < y))
    {n : ℕ} (hn : n ∈ l) (hn1 : n + 1 ∈ l) : False := by
  let : Trans (fun x y : ℕ => x + 1 < y) (fun x y => x + 1 < y)
      (fun x y => x + 1 < y) := ⟨by omega⟩
  have hp := List.pairwise_iff_getElem.mp hgap.pairwise
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hn
  obtain ⟨j, hj, he1⟩ := List.mem_iff_getElem.mp hn1
  rcases lt_trichotomy i j with hij | hij | hij
  · have := hp i j hi hj hij
    omega
  · subst j
    omega
  · have := hp j i hj hi hij
    omega

private theorem not_squarefree_of_four_dvd {n : ℕ} (h : 4 ∣ n) : ¬ Squarefree n := by
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) h

private theorem not_squarefree_of_nine_dvd {n : ℕ} (h : 9 ∣ n) : ¬ Squarefree n := by
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 3 Nat.prime_three) h

/-- An adjacent nonsquarefree pair cannot occur inside a full antirun. -/
private theorem upper_of_pair {l : List ℕ} (hf : FullNonsquarefreeInterval l)
    (hg : l.IsChain (fun x y => x + 1 < y)) {a b k : ℕ} (ha : a ∈ l) (hb : b ∈ l)
    (hak : a ≤ k) (hk : ¬ Squarefree k) (hk1 : ¬ Squarefree (k + 1)) : b ≤ k := by
  by_contra h
  have hkb : k + 1 ≤ b := by omega
  exact no_neighbors hg (hf.full a ha b hb k hak (by omega) hk)
    (hf.full a ha b hb (k + 1) (by omega) hkb hk1)

/-- A full interval of the increasing nonsquarefree sequence whose successive differences
exceed one has at most nine entries. Maximality of the antirun is not needed. -/
theorem antirun_length_le_nine (l : List ℕ) (hfull : FullNonsquarefreeInterval l)
    (hgap : l.IsChain (fun x y => x + 1 < y)) : l.length ≤ 9 := by
  by_contra hlen
  have hten : 10 ≤ l.length := by omega
  let x : Fin 10 → ℕ := fun i => l[i.val]'(by omega)
  have hmem (i : Fin 10) : x i ∈ l := List.getElem_mem _
  have hstep (i : Fin 9) : x i.castSucc + 1 < x i.succ :=
    List.isChain_iff_getElem.mp hgap i.val (by omega)
  have h01 : x 0 + 1 < x 1 := hstep 0
  have h12 : x 1 + 1 < x 2 := hstep 1
  have h23 : x 2 + 1 < x 3 := hstep 2
  have h34 : x 3 + 1 < x 4 := hstep 3
  have h45 : x 4 + 1 < x 5 := hstep 4
  have h56 : x 5 + 1 < x 6 := hstep 5
  have h67 : x 6 + 1 < x 7 := hstep 6
  have h78 : x 7 + 1 < x 8 := hstep 7
  have h89 : x 8 + 1 < x 9 := hstep 8
  let q := x 0 / 36
  have hlo : 36 * q ≤ x 0 := by dsimp [q]; omega
  have hhi : x 0 < 36 * q + 36 := by dsimp [q]; omega
  by_cases hfirst : x 0 ≤ 36 * q + 8
  · have hend := upper_of_pair hfull hgap (hmem 0) (hmem 9) hfirst
      (not_squarefree_of_four_dvd ⟨9 * q + 2, by omega⟩)
      (not_squarefree_of_nine_dvd ⟨4 * q + 1, by omega⟩)
    omega
  · by_cases hsecond : x 0 ≤ 36 * q + 27
    · have hend := upper_of_pair hfull hgap (hmem 0) (hmem 9) hsecond
        (not_squarefree_of_nine_dvd ⟨4 * q + 3, by omega⟩)
        (not_squarefree_of_four_dvd ⟨9 * q + 7, by omega⟩)
      -- Ten separated entries in these nineteen integer positions must fill every other one.
      have hx1 : x 1 = 36 * q + 11 := by omega
      have hforced : 36 * q + 12 ∈ l :=
        hfull.full (x 0) (hmem 0) (x 9) (hmem 9) (36 * q + 12)
          (by omega) (by omega) (not_squarefree_of_four_dvd ⟨9 * q + 3, by omega⟩)
      apply no_neighbors hgap (hmem 1)
      simpa only [hx1, Nat.add_assoc] using hforced
    · have hend := upper_of_pair hfull hgap (hmem 0) (hmem 9) (k := 36 * q + 44)
        (by omega) (not_squarefree_of_four_dvd ⟨9 * q + 11, by omega⟩)
        (not_squarefree_of_nine_dvd ⟨4 * q + 5, by omega⟩)
      omega

/-- The specified nine entries form a full antirun, so the universal bound is sharp. -/
private theorem nine_term_witness :
    let l := [6345, 6348, 6350, 6352, 6354, 6356, 6358, 6360, 6363]
    FullNonsquarefreeInterval l ∧ l.IsChain (fun x y => x + 1 < y) ∧ l.length = 9 := by
  dsimp
  refine ⟨⟨by decide, ?_, ?_⟩, by decide, rfl⟩
  · norm_num
    decide +kernel
  · intro a ha b hb n han hnb hn
    have hab : 6345 ≤ a ∧ b ≤ 6363 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      omega
    have hnlo : 6345 ≤ n := by omega
    have hnhi : n ≤ 6363 := by omega
    interval_cases n <;> norm_num at hn ⊢ <;> exact hn (by decide +kernel)

#print axioms antirun_length_le_nine
#print axioms nine_term_witness

end D5.S3.Arith.Congruence.NonsquarefreeAntirun
