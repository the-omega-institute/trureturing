/- GID: D5/S1/Words/Palindromes/GoldenRichness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:kernel-decide-small-cases-are-contained-in-this-formal-module)
   anchors: []
   digest: Every finite golden-word prefix has exactly length plus one palindromic factors. -/

import D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete
import D5.S1.Words.Palindromes.PalindromicFactors
import D5.S1.Words.ReturnWords.GoldenReturnItinerary
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

namespace D5.S1.Words

private def goldenPrefix (n : Nat) : List Bool :=
  List.ofFn fun i : Fin n => goldenWord i

private example : (palindromicFactors (goldenPrefix 1)).card = 2 := by decide
private example : (palindromicFactors (goldenPrefix 2)).card = 3 := by decide
private example : (palindromicFactors (goldenPrefix 3)).card = 4 := by decide
private example : (palindromicFactors (goldenPrefix 4)).card = 5 := by decide
private example : (palindromicFactors (goldenPrefix 5)).card = 6 := by decide
private example : (palindromicFactors (goldenPrefix 6)).card = 7 := by decide
private example : (palindromicFactors (goldenPrefix 7)).card = 8 := by decide
private example : (palindromicFactors (goldenPrefix 8)).card = 9 := by decide

private theorem goldenFactor_append (m n i : Nat) :
    goldenFactor (m + n) i = goldenFactor m i ++ goldenFactor n (i + m) := by
  apply List.ext_get
  · simp [goldenFactor]
  · intro k hkleft hkright
    by_cases hkm : k < m
    · simp only [List.get_eq_getElem]
      rw [List.getElem_append_left]
      · simp [goldenFactor]
      · simpa [goldenFactor] using hkm
    · simp only [List.get_eq_getElem]
      rw [List.getElem_append_right]
      · simp only [goldenFactor, List.length_ofFn, List.getElem_ofFn]
        congr 1
        omega
      · simpa [goldenFactor] using Nat.le_of_not_gt hkm

private theorem palindrome_getElem?_mirror {alpha : Type*} {w : List alpha}
    (hpal : List.Palindrome w) {i j : Nat} (hij : i + j + 1 = w.length) :
    w[i]? = w[j]? := by
  have h := congrArg (fun u : List alpha => u[i]?) hpal.reverse_eq
  rw [List.getElem?_reverse' hij] at h
  exact h.symm

private theorem golden_factor_reverse_occurs (m i : Nat) :
    ∃ j, (goldenFactor m i).reverse = goldenFactor m j := by
  let Q := i + m + 2
  let N := Nat.fib (Q + 2) - 2
  have hlevel := index_lt_diagonal_level Q
  rw [fibWord_length] at hlevel
  have hbound : i + m ≤ N := by
    have hlevel' : i + m + 2 < Nat.fib (i + m + 2 + 2) := by
      simpa [Q] using hlevel
    dsimp [Q, N]
    omega
  have hpal : List.Palindrome (goldenPrefix N) := by
    change List.Palindrome (List.ofFn fun i : Fin N => goldenWord i)
    rw [goldenWord_palindromic_prefix_iff]
    exact ⟨Q, by dsimp [Q]; omega, rfl⟩
  let j := N - (i + m)
  refine ⟨j, ?_⟩
  apply List.ext_get
  · simp [goldenFactor]
  · intro k hkleft hkright
    have hk : k < m := by simpa [goldenFactor] using hkright
    have hindex : i + (m - 1 - k) + (j + k) + 1 = N := by
      dsimp [j]
      omega
    have hiindex : i + (m - 1 - k) < N := by omega
    have hjindex : j + k < N := by omega
    have hmirror := palindrome_getElem?_mirror hpal (by
      simpa [goldenPrefix] using hindex)
    rw [List.getElem?_eq_getElem (by simpa [goldenPrefix] using hiindex),
      List.getElem?_eq_getElem (by simpa [goldenPrefix] using hjindex)] at hmirror
    simp only [goldenPrefix, List.getElem_ofFn, Option.some.injEq] at hmirror
    simp only [List.get_eq_getElem]
    rw [List.getElem_reverse]
    simp only [goldenFactor, List.length_ofFn, List.getElem_ofFn]
    exact hmirror

private theorem adjacent_golden_occurrences_iff {n : Nat} {p : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n p i j ↔
      i < j ∧ goldenFactor n i = p ∧ goldenFactor n j = p ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = p) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = p ∧ goldenFactor n j = p ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = p) = ∅) = true ↔ _
  simp

private theorem goldenFactor_reverse_window {n d i k e : Nat} (he : e ≤ d)
    (hreverse : (goldenFactor (d + n) i).reverse = goldenFactor (d + n) k) :
    (goldenFactor n (k + e)).reverse = goldenFactor n (i + (d - e)) := by
  apply List.ext_get
  · simp [goldenFactor]
  · intro x hxleft hxright
    have hx : x < n := by simpa [goldenFactor] using hxright
    let y := e + (n - 1 - x)
    have hy : y < d + n := by dsimp [y]; omega
    have hrelation : y + (d - e + x) + 1 = d + n := by
      dsimp [y]
      omega
    have hpoint := congrArg (fun w : List Bool => w[y]?) hreverse
    rw [List.getElem?_reverse' (by simpa [goldenFactor] using hrelation)] at hpoint
    have hmirrorIndex : d - e + x < d + n := by omega
    rw [List.getElem?_eq_getElem (by simpa [goldenFactor] using hmirrorIndex),
      List.getElem?_eq_getElem (by simpa [goldenFactor] using hy)] at hpoint
    simp only [goldenFactor, List.getElem_ofFn, Option.some.injEq] at hpoint
    have hleftIndex : k + y = k + e + (n - 1 - x) := by dsimp [y]; omega
    have hrightIndex : i + (d - e + x) = i + (d - e) + x := by omega
    rw [hleftIndex, hrightIndex] at hpoint
    simp only [List.get_eq_getElem]
    rw [List.getElem_reverse]
    simp only [goldenFactor, List.length_ofFn, List.getElem_ofFn]
    exact hpoint.symm

private theorem golden_complete_return_palindrome {p : List Bool} (hp : List.Palindrome p)
    (hn : 0 < p.length) {i j : Nat}
    (hadj : AdjacentGoldenOccurrences p.length p i j) :
    List.Palindrome (goldenFactor ((j - i) + p.length) i) := by
  have hs := adjacent_golden_occurrences_iff.mp hadj
  let d := j - i
  let c := goldenFactor (d + p.length) i
  let r := goldenFactor d i
  have hid : i + d = j := by dsimp [d]; omega
  have hreturn : c = r ++ p := by
    dsimp [c, r]
    rw [goldenFactor_append, hid, hs.2.2.1]
  have hstart : c = p ++ goldenFactor d (i + p.length) := by
    dsimp [c]
    rw [Nat.add_comm, goldenFactor_append, hs.2.1]
  obtain ⟨k, hreverse⟩ := golden_factor_reverse_occurs (d + p.length) i
  have hk : goldenFactor p.length k = p := by
    calc
      goldenFactor p.length k = (goldenFactor (d + p.length) k).take p.length := by
        rw [Nat.add_comm, goldenFactor_append]
        simp [goldenFactor]
      _ = c.reverse.take p.length := congrArg (List.take p.length) hreverse.symm
      _ = (r ++ p).reverse.take p.length := by rw [hreturn]
      _ = p := by simp [List.reverse_append, hp.reverse_eq]
  have hkd : goldenFactor p.length (k + d) = p := by
    calc
      goldenFactor p.length (k + d) = (goldenFactor (d + p.length) k).drop d := by
        rw [goldenFactor_append]
        simp [goldenFactor]
      _ = c.reverse.drop d := congrArg (List.drop d) hreverse.symm
      _ = (p ++ goldenFactor d (i + p.length)).reverse.drop d := by rw [hstart]
      _ = p := by simp [List.reverse_append, hp.reverse_eq, goldenFactor]
  have hadjMirror : AdjacentGoldenOccurrences p.length p k (k + d) := by
    apply adjacent_golden_occurrences_iff.mpr
    refine ⟨by dsimp [d]; omega, hk, hkd, Finset.filter_eq_empty_iff.mpr ?_⟩
    intro x hx hfactor
    have hxIoo := Finset.mem_Ioo.mp hx
    let e := x - k
    have hxeq : k + e = x := by dsimp [e]; omega
    have hepos : 0 < e := by dsimp [e]; omega
    have helt : e < d := by dsimp [e, d]; omega
    have hwindow := goldenFactor_reverse_window (n := p.length) (d := d)
      (i := i) (k := k) (e := e) helt.le hreverse
    have hfactor' : goldenFactor p.length (k + e) = p := by rw [hxeq]; exact hfactor
    have horiginal : goldenFactor p.length (i + (d - e)) = p := by
      rw [← hwindow, hfactor', hp.reverse_eq]
    have hbetween : i + (d - e) ∈
        (Finset.Ioo i j).filter (fun l => goldenFactor p.length l = p) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioo.mpr ⟨by omega, by dsimp [d]; omega⟩, horiginal⟩
    rw [hs.2.2.2] at hbetween
    simp at hbetween
  let s := goldenFactor d k
  have hrmem : r ∈ goldenReturnWords p.length p := by
    exact ⟨i, j, hadj, by simp [r, d]⟩
  have hsmem : s ∈ goldenReturnWords p.length p := by
    exact ⟨k, k + d, hadjMirror, by simp [s]⟩
  have hrs : r = s := golden_return_word_eq_of_length_eq hn hrmem hsmem (by
    simp [r, s, goldenFactor])
  apply List.Palindrome.of_reverse_eq
  calc
    c.reverse = goldenFactor (d + p.length) k := hreverse
    _ = s ++ p := by rw [goldenFactor_append, hkd]
    _ = r ++ p := by rw [hrs]
    _ = c := hreturn.symm

private theorem goldenPrefix_slice (n i m : Nat) (h : i + m ≤ n) :
    ((goldenPrefix n).drop i).take m = goldenFactor m i := by
  apply List.ext_get
  · simp [goldenPrefix, goldenFactor]
    omega
  · intro k hkleft hkright
    simp only [List.get_eq_getElem]
    simp [goldenPrefix, goldenFactor]

private theorem infix_goldenPrefix_occurs {u : List Bool} {n : Nat}
    (h : u <:+: goldenPrefix n) :
    ∃ i, i + u.length ≤ n ∧ u = goldenFactor u.length i := by
  rcases h with ⟨l, r, hlur⟩
  have hlength := congrArg List.length hlur
  have hbound : l.length + u.length ≤ n := by
    simp [goldenPrefix] at hlength
    omega
  refine ⟨l.length, hbound, ?_⟩
  calc
    u = ((goldenPrefix n).drop l.length).take u.length := by
      rw [← hlur]
      simp
    _ = goldenFactor u.length l.length := goldenPrefix_slice n l.length u.length hbound

private theorem goldenPrefix_succ (n : Nat) :
    goldenPrefix (n + 1) = goldenPrefix n ++ [goldenWord n] := by
  unfold goldenPrefix
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

private theorem exists_new_palindromic_suffix (n : Nat) :
    ∃ p, p ∈ palindromicFactors (goldenPrefix (n + 1)) ∧
      p ∉ palindromicFactors (goldenPrefix n) := by
  let w := goldenPrefix (n + 1)
  let predicate := fun m => List.Palindrome (w.drop (n + 1 - m))
  let m := Nat.findGreatest predicate (n + 1)
  have hone : predicate 1 := by
    dsimp [predicate, w]
    rw [goldenPrefix_succ]
    simpa [goldenPrefix] using List.Palindrome.singleton (goldenWord n)
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) (Nat.le_findGreatest (by omega) hone)
  have hmle : m ≤ n + 1 := Nat.findGreatest_le _
  have hmpal : predicate m := Nat.findGreatest_spec (by omega) hone
  let j := n + 1 - m
  let p := w.drop j
  have hjm : j + m = n + 1 := by dsimp [j]; omega
  have hplen : p.length = m := by simp [p, w, goldenPrefix, j]; omega
  have hpfactor : p = goldenFactor m j := by
    calc
      p = (w.drop j).take m := by
        rw [List.take_self_eq_iff]
        simp [p, w, goldenPrefix, j]
        omega
      _ = goldenFactor m j := by
        dsimp [w]
        exact goldenPrefix_slice (n + 1) j m (by omega)
  have hpsuffix : p <:+ w := by
    dsimp [p]
    exact List.drop_suffix j w
  refine ⟨p, mem_palindromicFactors.mpr ⟨hpsuffix.isInfix, ?_⟩, ?_⟩
  · simpa [predicate, p, j] using hmpal
  · intro hpold
    have hpold' := mem_palindromicFactors.mp hpold
    obtain ⟨i, hiend, hi⟩ := infix_goldenPrefix_occurs hpold'.1
    rw [hplen] at hiend hi
    have hij : i < j := by dsimp [j]; omega
    let starts := (Finset.range j).filter fun k => goldenFactor m k = p
    have histarts : i ∈ starts := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hij, hi.symm⟩
    have hstarts : starts.Nonempty := ⟨i, histarts⟩
    let i0 := starts.max' hstarts
    have hi0starts : i0 ∈ starts := Finset.max'_mem starts hstarts
    have hi0 := Finset.mem_filter.mp hi0starts
    have hi0lt : i0 < j := Finset.mem_range.mp hi0.1
    have hadj : AdjacentGoldenOccurrences m p i0 j := by
      apply adjacent_golden_occurrences_iff.mpr
      refine ⟨hi0lt, hi0.2, hpfactor.symm,
        Finset.filter_eq_empty_iff.mpr ?_⟩
      intro k hk hfactor
      have hkIoo := Finset.mem_Ioo.mp hk
      have hkstarts : k ∈ starts := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hkIoo.2, hfactor⟩
      have hkle := Finset.le_max' starts k hkstarts
      omega
    have hp' : List.Palindrome p := hpold'.2
    have hadj' : AdjacentGoldenOccurrences p.length p i0 j := by
      simpa [hplen] using hadj
    have hcomplete :=
      golden_complete_return_palindrome hp' (by rw [hplen]; exact hmpos) hadj'
    let q := goldenFactor ((j - i0) + m) i0
    have hqpal : List.Palindrome q := by simpa [q, hplen] using hcomplete
    have hi0q : i0 + ((j - i0) + m) = n + 1 := by omega
    have hqdrop : w.drop i0 = q := by
      calc
        w.drop i0 = (w.drop i0).take ((j - i0) + m) := by
          rw [List.take_self_eq_iff]
          simp [w, goldenPrefix]
          omega
        _ = q := by
          dsimp [w, q]
          exact goldenPrefix_slice (n + 1) i0 ((j - i0) + m) (by omega)
    have hqbound : (j - i0) + m ≤ n + 1 := by omega
    have hqpredicate : predicate ((j - i0) + m) := by
      dsimp [predicate]
      have hindex : n + 1 - ((j - i0) + m) = i0 := by omega
      rw [hindex, hqdrop]
      exact hqpal
    have hmax := Nat.le_findGreatest hqbound hqpredicate
    dsimp [m] at hmax
    omega

/-- Every finite prefix of the golden word has exactly `length + 1` palindromic factors. -/
theorem goldenWord_rich_prefix (n : Nat) :
    (palindromicFactors
      (List.ofFn fun i : Fin n => goldenWord i)).card = n + 1 := by
  change (palindromicFactors (goldenPrefix n)).card = n + 1
  induction n with
  | zero => decide
  | succ n ih =>
      change (palindromicFactors (goldenPrefix n)).card = n + 1 at ih
      have hprefix : goldenPrefix n <+: goldenPrefix (n + 1) := by
        rw [goldenPrefix_succ]
        exact List.prefix_append _ _
      have hsubset :
          palindromicFactors (goldenPrefix n) ⊆
            palindromicFactors (goldenPrefix (n + 1)) := by
        intro p hp
        rw [mem_palindromicFactors] at hp ⊢
        exact ⟨hp.1.trans hprefix.isInfix, hp.2⟩
      obtain ⟨p, hpnew, hpold⟩ := exists_new_palindromic_suffix n
      have hnonempty :
          (palindromicFactors (goldenPrefix (n + 1)) \
            palindromicFactors (goldenPrefix n)).Nonempty :=
        ⟨p, Finset.mem_sdiff.mpr ⟨hpnew, hpold⟩⟩
      have hpositive :
          0 < (palindromicFactors (goldenPrefix (n + 1)) \
            palindromicFactors (goldenPrefix n)).card :=
        Finset.card_pos.mpr hnonempty
      have hupper := palindromicFactors_card_le_length_add_one (goldenPrefix (n + 1))
      have hcard := Finset.card_sdiff_add_card_eq_card hsubset
      have hlength : (goldenPrefix (n + 1)).length = n + 1 := by
        simp [goldenPrefix]
      rw [hlength] at hupper
      omega

#print axioms goldenWord_rich_prefix

end D5.S1.Words
