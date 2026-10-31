/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Normalization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Normalization
   mirror-E: none(waiver:physical-ear-normalization)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A legal literal ear moves before a physical negative without changing the old word. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base oldValue newValue negatives actual_values
  source_signs chain_values source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private strip_of_prefix last_nonpositive ear_not_at_end
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
open private insertAt slide_packet find_next_negative
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private ear_perm from D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-- The old physical permutation stays fixed; the new ear can precede a negative. -/
theorem actual_ear_before_negative (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (sigma : List (Fin (a+b+c+d))) (j : ℕ) (hj : j ≤ a+b+c+d)
    (hold : OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma)
    (hnew : OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
      (earWord (a+b+c+d) sigma j)) :
    ∃ j' : ℕ, j ≤ j' ∧ j' < a+b+c+d ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j') ∧
      ∃ n ∈ [d-1,d+c-1,d+c+b-1,a+b+c+d-1],
        ((sigma.drop j').map Fin.val).head? = some n := by
  let k := size a b c d
  let A := seed a b c
  let N := sourceMod a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  let l := sigma.map Fin.val
  have hmod : modulus k = N := by dsimp [k, N, size, modulus, sourceMod]; ring
  have hmod' : modulus (k+1) = 2*N+1 := by dsimp [k,N,size,modulus,sourceMod]; ring
  have hhalf : (2*N+1)/2 = N := by omega
  have hv := actual_values a b c d
  have hfmap (xs : List (Fin k)) : xs.map (actualSource k A) = (xs.map Fin.val).map f := by
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => hv.1 p)
  have hgmap (xs : List (Fin (k+1))) :
      xs.map (actualSource (k+1) (2*A)) = (xs.map Fin.val).map g := by
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => hv.2 p)
  have hfr : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp
  have hperm : l.Perm (List.range k) :=
    (hold.1.map Fin.val).trans (List.Perm.of_eq hfr)
  have hlen : l.length = k := by simpa using hperm.length_eq
  have hmem (i : ℕ) (hi : i ∈ l) : i < k := List.mem_range.mp (hperm.mem_iff.mp hi)
  have holdstrip : InStrip f (N/2) 0 l := by
    apply strip_of_prefix
    intro n
    have he : ((l.take n).map f).sum = ((sigma.take n).map (actualSource k A)).sum := by
      rw [hfmap]
      simp only [l, List.map_take]
    rw [zero_add, he]
    simpa only [hmod, Set.mem_Icc] using hold.2.2 n
  have hearvalues (r : ℕ) : (earWord k sigma r).map Fin.val = insertAt k l r := by
    simp [earWord, insertAt, l, List.map_map, Function.comp_def]
  have hnewstrip : InStrip g N 0 (insertAt k l j) := by
    apply strip_of_prefix
    intro n
    have he : (((insertAt k l j).take n).map g).sum =
        (((earWord k sigma j).take n).map (actualSource (k+1) (2*A))).sum := by
      rw [hgmap]
      simp only [hearvalues, List.map_take]
    rw [zero_add, he]
    simpa only [hmod', hhalf, Set.mem_Icc] using hnew.2.2 n
  have htot := source_totals a b c d ha hb hc hd
  have hfzero : (l.map f).sum = 0 := (hperm.map f).sum_eq.trans htot.1
  have hgzero : (l.map g).sum = -base a b c d 0 := (hperm.map g).sum_eq.trans htot.2.1
  have hApos : 0 < base a b c d 0 := by
    have h := (chain_values a b c d ha hb hc hd).1 0
    omega
  have hearpos : 0 ≤ g k := by change 0 ≤ newValue a b c d (size a b c d); rw [htot.2.2]; omega
  have hlast : ∀ pre n, l = pre ++ [n] → n ∈ negatives a b c d := by
    intro pre n he
    have hn : n ∈ l := by rw [he]; simp
    have hs := source_signs a b c d ha hb hc hd n (hmem n hn)
    have hfnonpos := last_nonpositive f (N/2) pre n (by simpa [← he] using holdstrip)
      (by simpa [← he] using hfzero)
    by_contra hnot
    rw [if_neg hnot] at hs
    change 0 < f n ∧ 0 < g n at hs
    omega
  have hjlt : j < l.length := by
    by_contra h
    have he : j = l.length := by dsimp [k,size] at *; omega
    rw [he] at hnewstrip
    apply ear_not_at_end g N l k (base a b c d 0) hApos hgzero
    simpa [insertAt] using hnewstrip
  have hdrop : l.drop j ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hh
    omega
  have hlastdrop : ∀ pre n, l.drop j = pre ++ [n] → n ∈ negatives a b c d := by
    intro pre n he
    apply hlast (l.take j ++ pre) n
    calc
      l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
      _ = (l.take j ++ pre) ++ [n] := by rw [he, List.append_assoc]
  obtain ⟨P,n,R,hdecomp,hP,hn⟩ := find_next_negative
    (fun i => i ∈ negatives a b c d) (l.drop j) hdrop hlastdrop
  let pre := l.take j
  have hprelen : pre.length = j := by simp [pre, List.length_take, Nat.min_eq_left hjlt.le]
  have heword : l = pre ++ P ++ n :: R := by
    calc
      l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
      _ = pre ++ P ++ n :: R := by rw [hdecomp]; simp only [pre, List.append_assoc]
  have hp : ∀ i ∈ P, 0 ≤ g i := by
    intro i hi
    have hil : i ∈ l := by rw [heword]; simp [hi]
    have hs := source_signs a b c d ha hb hc hd i (hmem i hil)
    rw [if_neg (hP i hi)] at hs
    exact hs.2.le
  let j' := pre.length + P.length
  have hnormalized : InStrip g N 0 (insertAt k l j') := by
    have h := slide_packet g N 0 k pre P (n :: R) 0 (by omega) hearpos hp
      (by simpa only [← heword, hprelen, Nat.add_zero] using hnewstrip)
    simpa only [← heword, j'] using h
  have hj' : j ≤ j' ∧ j' < k := by
    have hh := congrArg List.length heword
    simp only [List.length_append, List.length_cons] at hh
    dsimp [j']
    omega
  refine ⟨j', hj'.1, hj'.2, ?_, n, hn, ?_⟩
  · refine ⟨ear_perm k sigma j' hold.1, ?_, ?_⟩
    · exact (((ear_perm k sigma j' hold.1).trans
        (ear_perm k sigma j hold.1).symm).map (actualSource (k+1) (2*A))).sum_eq.trans hnew.2.1
    · intro m
      have hm := inStrip_prefix hnormalized m
      have he : (((earWord k sigma j').take m).map (actualSource (k+1) (2*A))).sum =
          (((insertAt k l j').take m).map g).sum := by
        rw [hgmap]
        simp only [List.map_take, hearvalues]
      rw [he]
      simpa only [hmod', hhalf, zero_add, Set.mem_Icc] using hm
  · rw [List.map_drop]
    change (l.drop j').head? = some n
    rw [heword]
    change (((pre ++ P) ++ n :: R).drop (pre ++ P).length).head? = some n
    simp

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
