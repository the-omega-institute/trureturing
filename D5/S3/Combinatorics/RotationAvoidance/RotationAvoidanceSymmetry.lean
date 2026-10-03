/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry
   mirror-E: none(waiver:rotation-symmetry-bijections)
   anchors: [mathlib/module/Mathlib.Data.List.Rotate, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Complement and cut-adjusted reversal give the rotation-avoidance orbit bijections. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDefs
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSymmetry

open D5.S3.Combinatorics
open RotationAvoidanceDefs Nonnesting.NonnestingDefs

theorem orbit_wilfEquivalent (k : ℕ) (hk : 1 ≤ k) (q s : List ℕ)
    (hq : q.Perm [1, 2, 3, 4]) (hs : s ∈ orbit q) : WilfEquivalent k q s := by
  classical
  have bounds (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      ∀ value ∈ r, 1 ≤ value ∧ value ≤ 4 := by
    intro value hvalue
    have := hr.mem_iff.mp hvalue
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> omega
  have letters_four (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) : letters r = 4 := by
    have := hr.foldr_eq (f := max) 0
    simpa [letters] using this
  have complement_pattern (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      (complement r).Perm [1, 2, 3, 4] := by
    exact (hr.map (fun value => 5 - value)).trans (by decide)
  have complement_twice (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      complement (complement r) = r := by
    unfold complement
    rw [List.map_map]
    conv_rhs => rw [← List.map_id r]
    apply List.map_congr_left
    intro value hvalue
    have := bounds r hr value hvalue
    dsimp
    omega
  have word_bounds (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
      ∀ value ∈ p, 1 ≤ value ∧ value ≤ n := by
    intro value hvalue
    have := List.mem_range'.mp (hp.mem_iff.mp hvalue)
    omega
  have complement_word (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
      (p.map (fun value => n + 1 - value)).Perm (List.range' 1 n) := by
    have hreverse : (List.range' 1 n).map (fun value => n + 1 - value) =
        (List.range' 1 n).reverse := by
      rw [List.reverse_range', List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro value hvalue
      dsimp
      omega
    exact (hp.map _).trans (hreverse ▸ List.reverse_perm _)
  have word_twice (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
      (p.map (fun value => n + 1 - value)).map (fun value => n + 1 - value) = p := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro value hvalue
    have := word_bounds n p hp value hvalue
    dsimp
    omega
  have reverse_occurrence (r p : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      Occurs r p → Occurs r.reverse p.reverse := by
    have hletters := letters_four r hr
    have hreverse : letters r.reverse = 4 :=
      letters_four r.reverse (List.reverse_perm r |>.trans hr)
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    refine ⟨witness, ?_, ?_, ?_, by simp⟩
    · simpa [hletters, hreverse] using hincreasing
    · simpa [hletters, hreverse] using hmem
    · simpa only [List.map_reverse] using hsub.reverse
  have complement_occurrence (n : ℕ) (r p : List ℕ)
      (hr : r.Perm [1, 2, 3, 4]) (hp : p.Perm (List.range' 1 n)) :
      Occurs r p → Occurs (complement r) (p.map (fun value => n + 1 - value)) := by
    have hletters := letters_four r hr
    have hcomplement := letters_four (complement r) (complement_pattern r hr)
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    let reflected : ℕ → ℕ := fun rank => n + 1 - witness (5 - rank)
    have witness_bounds (rank : ℕ) (hlow : 1 ≤ rank) (hhigh : rank ≤ 4) :
        1 ≤ witness rank ∧ witness rank ≤ n := by
      exact word_bounds n p hp _ (hmem rank hlow (by simpa [hletters] using hhigh))
    refine ⟨reflected, ?_, ?_, ?_, by simp⟩
    · intro rank hlow hhigh
      rw [hcomplement] at hhigh
      have hstep := hincreasing (4 - rank) (by omega) (by rw [hletters]; omega)
      have hindex : 4 - rank + 1 = 5 - rank := by omega
      rw [hindex] at hstep
      have hbound := witness_bounds (5 - rank) (by omega) (by omega)
      dsimp [reflected]
      have hnext : 5 - (rank + 1) = 4 - rank := by omega
      rw [hnext]
      omega
    · intro rank hlow hhigh
      rw [hcomplement] at hhigh
      exact List.mem_map.mpr ⟨witness (5 - rank),
        hmem (5 - rank) (by omega) (by rw [hletters]; omega), rfl⟩
    · have hmapped := hsub.map (fun value => n + 1 - value)
      convert hmapped using 1
      unfold complement
      simp only [List.map_map]
      apply List.map_congr_left
      intro value hvalue
      have := bounds r hr value hvalue
      dsimp [reflected]
      congr 2
      omega
  have complement_counts (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      WilfEquivalent k r (complement r) := by
    intro n hn
    let reflect : List ℕ → List ℕ := List.map (fun value => n + 1 - value)
    have maps (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4])
        (p : List ℕ) (hp : p ∈ rotationAvoiders n k pattern) :
        reflect p ∈ rotationAvoiders n k (complement pattern) := by
      refine ⟨complement_word n p hp.1, ?_⟩
      intro cut hcut hoccurs
      have hrot : (p.rotate cut).Perm (List.range' 1 n) :=
        (List.rotate_perm p cut).trans hp.1
      have hmapped : (reflect p).rotate cut = reflect (p.rotate cut) :=
        (List.map_rotate _ p cut).symm
      rw [hmapped] at hoccurs
      have hback := complement_occurrence n (complement pattern) (reflect (p.rotate cut))
        (complement_pattern pattern hpattern) (complement_word n _ hrot) hoccurs
      rw [complement_twice pattern hpattern, word_twice n _ hrot] at hback
      exact hp.2 cut hcut hback
    apply Set.ncard_congr (fun p _ => reflect p)
    · exact maps r hr
    · intro first second hfirst hsecond heq
      have := congrArg reflect heq
      simpa [reflect, word_twice n first hfirst.1, word_twice n second hsecond.1] using this
    · intro p hp
      have hpreimage := maps (complement r) (complement_pattern r hr) p hp
      rw [complement_twice r hr] at hpreimage
      exact ⟨reflect p, hpreimage, word_twice n p hp.1⟩
  have reverse_counts (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) :
      WilfEquivalent k r r.reverse := by
    intro n hn
    let reflect : List ℕ → List ℕ := fun p => (p.rotate (k - 1)).reverse
    have rotation_identity (p : List ℕ) (hp : p.Perm (List.range' 1 n))
        (cut : ℕ) (hcut : cut < k) :
        (reflect p).rotate cut = (p.rotate (k - 1 - cut)).reverse := by
      have hlength : p.length = n := by simpa using hp.length_eq
      have hsmall : cut < n := lt_of_lt_of_le hcut hn
      dsimp [reflect]
      rw [List.rotate_reverse, List.length_rotate, hlength, Nat.mod_eq_of_lt hsmall,
        List.rotate_rotate]
      have hsum : k - 1 + (n - cut) = n + (k - 1 - cut) := by omega
      rw [hsum, ← List.rotate_rotate, ← hlength, List.rotate_length]
    have involution (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
        reflect (reflect p) = p := by
      have hidentity := rotation_identity p hp (k - 1) (by omega)
      dsimp [reflect]
      rw [hidentity]
      simp
    have maps (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4])
        (p : List ℕ) (hp : p ∈ rotationAvoiders n k pattern) :
        reflect p ∈ rotationAvoiders n k pattern.reverse := by
      refine ⟨(List.reverse_perm _).trans ((List.rotate_perm p _).trans hp.1), ?_⟩
      intro cut hcut hoccurs
      rw [rotation_identity p hp.1 cut hcut] at hoccurs
      have hback := reverse_occurrence pattern.reverse (p.rotate (k - 1 - cut)).reverse
        ((List.reverse_perm pattern).trans hpattern) hoccurs
      simp only [List.reverse_reverse] at hback
      exact hp.2 (k - 1 - cut) (by omega) hback
    apply Set.ncard_congr (fun p _ => reflect p)
    · exact maps r hr
    · intro first second hfirst hsecond heq
      have := congrArg reflect heq
      rwa [involution first hfirst.1, involution second hsecond.1] at this
    · intro p hp
      have hpreimage := maps r.reverse ((List.reverse_perm r).trans hr) p hp
      simp only [List.reverse_reverse] at hpreimage
      exact ⟨reflect p, hpreimage, involution p hp.1⟩
  simp only [orbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · intro n hn
    rfl
  · exact complement_counts q hq
  · exact reverse_counts q hq
  · intro n hn
    exact (reverse_counts q hq n hn).trans
      (complement_counts q.reverse ((List.reverse_perm q).trans hq) n hn)

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSymmetry
