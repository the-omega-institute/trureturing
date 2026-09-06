/- GID: D5/S0/Computability/Coding/ImmutableExtension
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/ImmutableExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact residual capacity characterizes extensions that preserve a frozen prefix code. -/

import D5.S0.Computability.Coding.KraftConverse

/-!
# Immutable prefix-code extension

This module strengthens the finite Kraft converse from construction-from-empty to an exact
criterion for extending a frozen finite prefix code without changing any existing codeword.
It supports the paper's immutable-code extension claim: a multiset of requested lengths is
feasible exactly when its cylinder demand fits the frozen code's residual capacity at every
requested depth.

The supporting shadow identity computes residual capacity without enumerating all candidate
words.  Short frozen words contribute their exact descendant-cylinder sizes, while frozen words
longer than the queried depth contribute the cardinality of an image finset of their distinct
depth prefixes.  Counting that image, rather than the long words themselves, is essential.

## Search receipt (2026-09-06)

Searched pinned mathlib and `D5` for `Compatible`, `freeAt`,
`extension_iff_depth_capacity`, immutable prefix-code extension, exact prefix-cylinder
cardinality, prefix/take/drop identities, `card_vector`, `card_biUnion`, disjoint finite unions,
filtered multiset sums, and images of `List.take`.  No existing immutable-extension criterion or
residual profile was found.  Exact hits reused below are `List.prefix_append_drop`,
`List.prefix_or_prefix_of_prefix`, `List.prefix_iff_eq_take`, `List.take_prefix`,
`Fintype.card_congr`, `Finset.card_image_of_injective`,
`Finset.card_sdiff_add_card_eq_card`, `Finset.card_union_of_disjoint`, `List.sum_toFinset`, and
`card_vector`.  The similarly named cylinder helpers in `KraftConverse` are private and therefore
were not treated as imported APIs.
-/

namespace D5.S0.Computability.Coding.ImmutableExtension

open D5.S0.Computability.Coding.PrefixFreeCode
open scoped BigOperators

/-- A finite word over the alphabet `Fin q`. -/
abbrev Word (q : ℕ) := List (Fin q)

/-- A word is compatible with a frozen code when it is prefix-incomparable with every frozen
word.  Both directions are required because new requests may be shorter than frozen words. -/
def Compatible {q : ℕ} (C : Finset (Word q)) (w : Word q) : Prop :=
  ∀ u ∈ C, ¬ (u <+: w) ∧ ¬ (w <+: u)

/-- The residual depth-`n` slots that are prefix-incomparable with the frozen code. -/
noncomputable def freeAt {q : ℕ} (C : Finset (Word q)) (n : ℕ) :
    Finset (List.Vector (Fin q) n) :=
  by
    classical
    exact Finset.univ.filter (fun v => Compatible C v.1)

/-- The total number of depth-`n` descendants demanded by requests of length at most `n`.
Multiplicity in the requested multiset is retained. -/
def demand (q : ℕ) (L : Multiset ℕ) (n : ℕ) : ℕ :=
  ((L.filter (fun l => l ≤ n)).map (fun l => q ^ (n - l))).sum

/-- `xs` realizes the requested length multiset while preserving the frozen code `C`: the new
words are distinct, disjoint from `C`, and the combined code is prefix-free. -/
def Extends {q : ℕ} (C : Finset (Word q))
    (L : Multiset ℕ) (xs : List (Word q)) : Prop :=
  xs.Nodup ∧
    Disjoint C xs.toFinset ∧
    (xs.map List.length : Multiset ℕ) = L ∧
    IsPrefixFree ((C ∪ xs.toFinset : Finset (Word q)) : Set (Word q))

/-- The depth-`n` cylinder below a word `u`. -/
private def descendants {q : ℕ} (u : Word q) (n : ℕ) :
    Finset (List.Vector (Fin q) n) :=
  by
    classical
    exact Finset.univ.filter (fun v => u <+: v.1)

/-- The certified depth-`n` prefix of a word longer than `n`. -/
private def takeVector {q n : ℕ} (u : Word q) (h : n < u.length) :
    List.Vector (Fin q) n :=
  ⟨u.take n, by simp [Nat.le_of_lt h]⟩

/-- Distinct depth-`n` prefixes of frozen words longer than `n`, represented as an image finset
so coincident long prefixes are counted only once. -/
noncomputable def longPrefixes {q : ℕ} (C : Finset (Word q)) (n : ℕ) :
    Finset (List.Vector (Fin q) n) := by
  classical
  let long := C.filter (fun u => n < u.length)
  exact long.attach.image
    (fun u => takeVector u.1 (by
      have hu : u.1 ∈ C.filter (fun x => n < x.length) := u.2
      exact (Finset.mem_filter.mp hu).2))

/-- Membership in `longPrefixes` is witnessed by a frozen long word with the displayed take. -/
private theorem mem_longPrefixes {q n : ℕ} {C : Finset (Word q)}
    {v : List.Vector (Fin q) n} :
    v ∈ longPrefixes C n ↔
      ∃ u ∈ C, n < u.length ∧ u.take n = v.1 := by
  classical
  simp only [longPrefixes, Finset.mem_image, Finset.mem_attach]
  constructor
  · rintro ⟨u, -, huv⟩
    refine ⟨u.1, (Finset.mem_filter.mp u.2).1,
      (Finset.mem_filter.mp u.2).2, ?_⟩
    exact congrArg Subtype.val huv
  · rintro ⟨u, huC, hun, huv⟩
    let ua : {x // x ∈ C.filter (fun x => n < x.length)} :=
      ⟨u, Finset.mem_filter.mpr ⟨huC, hun⟩⟩
    refine ⟨ua, by simp, ?_⟩
    exact Subtype.ext huv

def appendVector {q n : ℕ} (u : Word q) (h : u.length ≤ n)
    (v : List.Vector (Fin q) (n - u.length)) : List.Vector (Fin q) n :=
  ⟨u ++ v.1, by simp [v.2, Nat.add_sub_of_le h]⟩

/-- Appending a fixed prefix to certified suffix vectors is injective. -/
private theorem appendVector_injective {q n : ℕ} (u : Word q) (h : u.length ≤ n) :
    Function.Injective (appendVector u h) := by
  intro v w hvw
  apply Subtype.ext
  exact List.append_cancel_left (congrArg Subtype.val hvw)

/-- A depth cylinder is exactly the image of all suffix vectors of the complementary length. -/
private theorem descendants_eq_image {q n : ℕ} (u : Word q) (h : u.length ≤ n) :
    descendants u n = Finset.univ.image (appendVector u h) := by
  ext v
  simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro huv
    let s : List.Vector (Fin q) (n - u.length) :=
      ⟨v.1.drop u.length, by simp [v.2]⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact (List.prefix_append_drop huv).symm
  · rintro ⟨s, rfl⟩
    exact List.prefix_append _ _

/-- A word of length at most `n` has exactly `q^(n-|u|)` depth-`n` descendants. -/
private theorem card_descendants {q n : ℕ} (u : Word q) (h : u.length ≤ n) :
    (descendants u n).card = q ^ (n - u.length) := by
  rw [descendants_eq_image u h,
    Finset.card_image_of_injective _ (appendVector_injective u h)]
  simp [card_vector]

/-- Every descendant of a compatible word remains compatible with the frozen code. -/
private theorem descendants_subset_freeAt {q n : ℕ} {C : Finset (Word q)} {w : Word q}
    (hw : Compatible C w) :
    descendants w n ⊆ freeAt C n := by
  intro v hv
  simp only [descendants, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  simp only [freeAt, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u hu
  constructor
  · intro huv
    rcases List.prefix_or_prefix_of_prefix huv hv with huw | hwu
    · exact (hw u hu).1 huw
    · exact (hw u hu).2 hwu
  · intro hvu
    exact (hw u hu).2 (hv.trans hvu)

/-- Adjoining a compatible word removes precisely its depth cylinder from the residual slots. -/
private theorem freeAt_insert_eq_sdiff {q n : ℕ} {C : Finset (Word q)} {w : Word q}
    (hw : Compatible C w) (hwn : w.length ≤ n) :
    freeAt (insert w C) n = freeAt C n \ descendants w n := by
  classical
  ext v
  simp only [freeAt, descendants, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro u hu
      exact hv u (by simp [hu])
    · intro hwv
      exact (hv w (by simp)).1 hwv
  · rintro ⟨hv, hwv⟩ u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · refine ⟨hwv, fun hvw => ?_⟩
      have hwlen : u.length ≤ v.1.length := by simpa [v.2] using hwn
      have heq : v.1 = u := hvw.eq_of_length (le_antisymm hvw.length_le hwlen)
      exact hwv (heq ▸ by simp)
    · exact hv u hu

/-- Exact one-word residual accounting at every depth not shorter than the adjoined word. -/
private theorem card_freeAt_insert_add {q n : ℕ} {C : Finset (Word q)} {w : Word q}
    (hw : Compatible C w) (hwn : w.length ≤ n) :
    (freeAt (insert w C) n).card + q ^ (n - w.length) = (freeAt C n).card := by
  rw [freeAt_insert_eq_sdiff hw hwn, ← card_descendants w hwn]
  exact Finset.card_sdiff_add_card_eq_card (descendants_subset_freeAt hw)

/-- A member of a prefix-free supercode is compatible with a subcode that does not contain it. -/
private theorem compatible_of_prefixFree_of_notMem {q : ℕ}
    {B U : Finset (Word q)} {w : Word q}
    (hsub : B ⊆ U) (hwU : w ∈ U) (hwB : w ∉ B)
    (hpf : IsPrefixFree (U : Set (Word q))) : Compatible B w := by
  intro u hu
  have huU : u ∈ U := hsub hu
  constructor
  · intro huw
    have heq : u = w := hpf (by simpa using huU) (by simpa using hwU) huw
    exact hwB (heq ▸ hu)
  · intro hwu
    have heq : w = u := hpf (by simpa using hwU) (by simpa using huU) hwu
    exact hwB (heq ▸ hu)

/-- Exact residual accounting for a finite prefix-free family adjoined to a frozen code. -/
private theorem card_freeAt_union_add_sum {q n : ℕ} (C D : Finset (Word q))
    (hdisj : Disjoint C D)
    (hpf : IsPrefixFree ((C ∪ D : Finset (Word q)) : Set (Word q)))
    (hdepth : ∀ w ∈ D, w.length ≤ n) :
    (freeAt (C ∪ D) n).card + ∑ w ∈ D, q ^ (n - w.length) =
      (freeAt C n).card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert w D hwD ih =>
      have hwC : w ∉ C := by
        intro hwmem
        exact (Finset.disjoint_left.mp hdisj) hwmem (by simp)
      have hdisjD : Disjoint C D := by
        exact Finset.disjoint_left.mpr fun _ huC huD =>
          (Finset.disjoint_left.mp hdisj) huC (by simp [huD])
      have hpfD : IsPrefixFree ((C ∪ D : Finset (Word q)) : Set (Word q)) := by
        intro u hu v hv huv
        apply hpf (u := u) (v := v)
        · have hu' : u ∈ C ∪ D := by simpa using hu
          have : u ∈ C ∪ insert w D := by
            rw [Finset.mem_union, Finset.mem_insert]
            exact (Finset.mem_union.mp hu').imp_right Or.inr
          simpa using this
        · have hv' : v ∈ C ∪ D := by simpa using hv
          have : v ∈ C ∪ insert w D := by
            rw [Finset.mem_union, Finset.mem_insert]
            exact (Finset.mem_union.mp hv').imp_right Or.inr
          simpa using this
        · exact huv
      have hdepthD : ∀ u ∈ D, u.length ≤ n := by
        intro u hu
        exact hdepth u (by simp [hu])
      have hcomp : Compatible (C ∪ D) w := by
        apply compatible_of_prefixFree_of_notMem
          (B := C ∪ D) (U := C ∪ insert w D)
        · intro u hu
          rw [Finset.mem_union, Finset.mem_insert]
          exact (Finset.mem_union.mp hu).imp_right Or.inr
        · simp
        · simp [hwC, hwD]
        · exact hpf
      have hwdepth : w.length ≤ n := hdepth w (by simp)
      have hone := card_freeAt_insert_add hcomp hwdepth
      have hmany := ih hdisjD hpfD hdepthD
      simp only [Finset.sum_insert hwD]
      rw [show C ∪ insert w D = insert w (C ∪ D) by ext; simp]
      omega

/-- Relative to the short frozen words, the remaining slots partition into genuinely free slots
and the distinct prefixes of longer frozen words. -/
private theorem freeAt_union_longPrefixes {q n : ℕ} (C : Finset (Word q))
    (hC : IsPrefixFree (C : Set (Word q))) :
    freeAt C n ∪ longPrefixes C n =
      freeAt (C.filter (fun u => u.length ≤ n)) n := by
  classical
  ext v
  constructor
  · intro hv
    rw [Finset.mem_union] at hv
    rcases hv with hvfree | hvlong
    · simp only [freeAt, Finset.mem_filter, Finset.mem_univ, true_and] at hvfree ⊢
      intro u hu
      exact hvfree u (Finset.mem_filter.mp hu).1
    · obtain ⟨u, huC, hun, huv⟩ := mem_longPrefixes.mp hvlong
      have hvEq : takeVector u hun = v := by
        apply Subtype.ext
        exact huv
      subst v
      simp only [freeAt, Finset.mem_filter, Finset.mem_univ, true_and]
      intro s hs
      have hsC := (Finset.mem_filter.mp hs).1
      have hsn := (Finset.mem_filter.mp hs).2
      have htakePrefix : (takeVector u hun).1 <+: u := by
        simpa [takeVector] using (List.take_prefix n u)
      constructor
      · intro hstake
        have hsu : s <+: u := hstake.trans htakePrefix
        have heq : s = u := hC (by simpa using hsC) (by simpa using huC) hsu
        have hlenEq := congrArg List.length heq
        omega
      · intro htakes
        have htlen : (takeVector u hun).1.length = n := (takeVector u hun).2
        have hlen : s.length = n := le_antisymm hsn (by simpa [htlen] using htakes.length_le)
        have heq : (takeVector u hun).1 = s :=
          htakes.eq_of_length (by simpa [htlen, hlen])
        have hsu : s <+: u := heq ▸ htakePrefix
        have hsame : s = u := hC (by simpa using hsC) (by simpa using huC) hsu
        have hlenEq := congrArg List.length hsame
        omega
  · intro hv
    simp only [freeAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    by_cases hvC : Compatible C v.1
    · rw [Finset.mem_union]
      left
      simpa [freeAt] using hvC
    · rw [Finset.mem_union]
      right
      by_contra hvlong
      apply hvC
      intro u huC
      by_cases hun : u.length ≤ n
      · exact hv u (Finset.mem_filter.mpr ⟨huC, hun⟩)
      · have hnu : n < u.length := Nat.lt_of_not_ge hun
        constructor
        · intro huv
          have hlen := huv.length_le
          rw [v.2] at hlen
          omega
        · intro hvu
          apply hvlong
          apply mem_longPrefixes.mpr
          have ht := List.prefix_iff_eq_take.mp hvu
          rw [v.2] at ht
          exact ⟨u, huC, hnu, ht.symm⟩

/-- A genuinely free slot cannot be the depth prefix of a longer frozen word. -/
private theorem disjoint_freeAt_longPrefixes {q n : ℕ} (C : Finset (Word q)) :
    Disjoint (freeAt C n) (longPrefixes C n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvfree hvlong
  have hvcomp : Compatible C v.1 := by simpa [freeAt] using hvfree
  obtain ⟨u, huC, hun, huv⟩ := mem_longPrefixes.mp hvlong
  have hvEq : takeVector u hun = v := by
    apply Subtype.ext
    exact huv
  subst v
  exact (hvcomp u huC).2 (by
    simpa [takeVector] using (List.take_prefix n u))

/-- **Exact residual-capacity shadow identity.**  At depth `n`, genuinely free slots, the
descendant cylinders of short frozen words, and the distinct depth prefixes of long frozen words
partition all `q^n` words.  The last summand is an image-finset cardinal, so shared prefixes of
long words are counted once. -/
theorem freeAt_shadow_identity {q n : ℕ} (C : Finset (Word q))
    (hC : IsPrefixFree (C : Set (Word q))) :
    (freeAt C n).card +
        (∑ u ∈ C.filter (fun u => u.length ≤ n), q ^ (n - u.length)) +
        (longPrefixes C n).card = q ^ n := by
  classical
  let short := C.filter (fun u => u.length ≤ n)
  have hpfShort : IsPrefixFree (short : Set (Word q)) := by
    intro u hu v hv huv
    have hu' : u ∈ short := by simpa using hu
    have hv' : v ∈ short := by simpa using hv
    exact hC (by simpa using (Finset.mem_filter.mp hu').1)
      (by simpa using (Finset.mem_filter.mp hv').1) huv
  have hdepth : ∀ u ∈ short, u.length ≤ n := by
    intro u hu
    change u ∈ C.filter (fun u => u.length ≤ n) at hu
    exact (Finset.mem_filter.mp hu).2
  have haccount := card_freeAt_union_add_sum (q := q) (n := n) ∅ short
    (by simp) (by simpa using hpfShort) hdepth
  have hpartition := Finset.card_union_of_disjoint
    (disjoint_freeAt_longPrefixes (n := n) C)
  rw [freeAt_union_longPrefixes C hC] at hpartition
  have hempty : (freeAt (∅ : Finset (Word q)) n).card = q ^ n := by
    simp [freeAt, Compatible, card_vector]
  simp only [Finset.empty_union] at haccount
  rw [hempty] at haccount
  simp only [short] at haccount
  omega

/-- Depth demand is additive in the requested multiset. -/
private theorem demand_add (q n : ℕ) (L K : Multiset ℕ) :
    demand q (L + K) n = demand q L n + demand q K n := by
  simp [demand, Multiset.filter_add, Multiset.map_add]

/-- For a nodup word list, multiset demand is the corresponding filtered finset sum. -/
private theorem demand_map_lengths_eq_sum {q n : ℕ} (xs : List (Word q))
    (hxs : xs.Nodup) :
    demand q (xs.map List.length : Multiset ℕ) n =
      ∑ w ∈ xs.toFinset.filter (fun w => w.length ≤ n), q ^ (n - w.length) := by
  let ys := xs.filter (fun w => decide (w.length ≤ n))
  have hys : ys.Nodup := hxs.filter _
  calc
    demand q (xs.map List.length : Multiset ℕ) n =
        (ys.map (fun w => q ^ (n - w.length))).sum := by
      simp [demand, ys, List.filter_map, List.map_map, Function.comp_def]
    _ = ∑ w ∈ ys.toFinset, q ^ (n - w.length) :=
      (List.sum_toFinset (fun w => q ^ (n - w.length)) hys).symm
    _ = ∑ w ∈ xs.toFinset.filter (fun w => w.length ≤ n),
        q ^ (n - w.length) := by
      congr 1
      ext w
      simp [ys]

/-- Inserting a compatible word preserves prefix freedom. -/
private theorem isPrefixFree_insert_of_compatible {q : ℕ}
    {C : Finset (Word q)} {w : Word q}
    (hC : IsPrefixFree (C : Set (Word q))) (hw : Compatible C w) :
    IsPrefixFree ((insert w C : Finset (Word q)) : Set (Word q)) := by
  classical
  intro u hu v hv huv
  have hu' : u = w ∨ u ∈ C := by simpa using hu
  have hv' : v = w ∨ v ∈ C := by simpa using hv
  rcases hu' with rfl | huC
  · rcases hv' with rfl | hvC
    · rfl
    · exact ((hw v hvC).2 huv).elim
  · rcases hv' with rfl | hvC
    · exact ((hw u huC).1 huv).elim
    · exact hC (by simpa using huC) (by simpa using hvC) huv

/-- A compatible word is not already a member of the code. -/
private theorem compatible_not_mem {q : ℕ} {C : Finset (Word q)} {w : Word q}
    (hw : Compatible C w) : w ∉ C := by
  intro hwC
  exact (hw w hwC).1 (by simp)

/-- Sorted requests satisfying every depth constraint admit a greedy immutable extension. -/
private theorem exists_extension_sorted {q : ℕ} (C : Finset (Word q))
    (lengths : List ℕ)
    (hsorted : lengths.Pairwise (· ≤ ·))
    (hC : IsPrefixFree (C : Set (Word q)))
    (hcapacity : ∀ n ∈ lengths,
      demand q (lengths : Multiset ℕ) n ≤ (freeAt C n).card) :
    ∃ xs, Extends C (lengths : Multiset ℕ) xs := by
  classical
  induction lengths using List.reverseRecOn with
  | nil =>
      refine ⟨[], by simp [Extends, hC]⟩
  | append_singleton init l ih =>
      have hsortedInit : init.Pairwise (· ≤ ·) :=
        (List.pairwise_append.mp hsorted).1
      have hinitLe : ∀ k ∈ init, k ≤ l := fun k hk =>
        (List.pairwise_append.mp hsorted).2.2 k hk l (by simp)
      have hcapacityInit : ∀ n ∈ init,
          demand q (init : Multiset ℕ) n ≤ (freeAt C n).card := by
        intro n hn
        have hfull := hcapacity n (by simp [hn])
        rw [show ((init ++ [l] : List ℕ) : Multiset ℕ) =
            (init : Multiset ℕ) + ({l} : Multiset ℕ) by rfl,
          demand_add] at hfull
        omega
      obtain ⟨xs, hxs, hdisj, hlengths, hpf⟩ :=
        ih hsortedInit hcapacityInit
      let D := xs.toFinset
      have hdepth : ∀ w ∈ D, w.length ≤ l := by
        intro w hw
        apply hinitLe w.length
        have hwxs : w ∈ xs := by simpa [D] using hw
        have hmem : w.length ∈ (xs.map List.length : Multiset ℕ) := by
          simpa using List.mem_map.mpr ⟨w, hwxs, rfl⟩
        rw [hlengths] at hmem
        simpa using hmem
      have haccount := card_freeAt_union_add_sum C D hdisj hpf hdepth
      have hsum :
          (∑ w ∈ D, q ^ (l - w.length)) = demand q (init : Multiset ℕ) l := by
        rw [← hlengths, demand_map_lengths_eq_sum xs hxs]
        simp only [D]
        rw [Finset.filter_eq_self.mpr]
        exact fun w hw => hdepth w hw
      have hfull := hcapacity l (by simp)
      rw [show ((init ++ [l] : List ℕ) : Multiset ℕ) =
          (init : Multiset ℕ) + ({l} : Multiset ℕ) by rfl,
        demand_add] at hfull
      have hsingle : demand q ({l} : Multiset ℕ) l = 1 := by
        unfold demand
        rw [Multiset.filter_singleton]
        simp
      rw [hsingle] at hfull
      have hslot : (freeAt (C ∪ D) l).Nonempty := by
        rw [← Finset.card_pos]
        rw [hsum] at haccount
        omega
      obtain ⟨w, hwfree⟩ := hslot
      have hwcomp : Compatible (C ∪ D) w.1 := by
        simpa [freeAt] using hwfree
      have hwlen : w.1.length = l := w.2
      have hwnot : w.1 ∉ C ∪ D := compatible_not_mem hwcomp
      refine ⟨xs ++ [w.1], ?_, ?_, ?_, ?_⟩
      · have hwxs : w.1 ∉ xs := by
          intro hwmem
          exact hwnot (by simp [D, hwmem])
        simpa only [List.concat_eq_append] using
          (List.nodup_concat xs w.1).mpr ⟨hwxs, hxs⟩
      · apply Finset.disjoint_left.mpr
        intro u huC huNew
        have huNew' : u = w.1 ∨ u ∈ xs.toFinset := by simpa using huNew
        rcases huNew' with rfl | huD
        · exact hwnot (by simp [huC])
        · exact (Finset.disjoint_left.mp hdisj) huC huD
      · calc
          (↑((xs ++ [w.1]).map List.length) : Multiset ℕ) =
              (xs.map List.length : Multiset ℕ) + {w.1.length} := by
            rw [List.map_append]
            rfl
          _ = (init : Multiset ℕ) + {l} := by rw [hlengths, hwlen]
          _ = (↑(init ++ [l]) : Multiset ℕ) := rfl
      · rw [show C ∪ (xs ++ [w.1]).toFinset = insert w.1 (C ∪ D) by
          ext u
          simp [D, or_assoc, or_left_comm]]
        exact isPrefixFree_insert_of_compatible hpf hwcomp

/-- **Exact depth-sensitive criterion for immutable prefix-code extension.**  A requested length
multiset extends a frozen prefix-free code exactly when, at every requested depth, its full
multiplicity-sensitive cylinder demand fits the frozen code's residual slots.  No hypothesis
requires new words to be at least as long as frozen words. -/
theorem extension_iff_depth_capacity
    {q : ℕ} (_hq : 2 ≤ q)
    (C : Finset (Word q)) (L : Multiset ℕ)
    (hC : IsPrefixFree (C : Set (Word q))) :
    (∃ xs, Extends C L xs) ↔
      ∀ n ∈ L, demand q L n ≤ (freeAt C n).card := by
  classical
  constructor
  · rintro ⟨xs, hxs, hdisj, hlengths, hpf⟩ n hn
    let D := xs.toFinset.filter (fun w => w.length ≤ n)
    have hdisjD : Disjoint C D := by
      apply Finset.disjoint_left.mpr
      intro w hwC hwD
      exact (Finset.disjoint_left.mp hdisj) hwC (Finset.mem_filter.mp hwD).1
    have hpfD : IsPrefixFree ((C ∪ D : Finset (Word q)) : Set (Word q)) := by
      intro u hu v hv huv
      apply hpf (u := u) (v := v)
      · have hu' : u ∈ C ∪ D := by simpa using hu
        have : u ∈ C ∪ xs.toFinset := by
          rw [Finset.mem_union] at hu' ⊢
          exact hu'.imp_right fun h => (Finset.mem_filter.mp h).1
        simpa using this
      · have hv' : v ∈ C ∪ D := by simpa using hv
        have : v ∈ C ∪ xs.toFinset := by
          rw [Finset.mem_union] at hv' ⊢
          exact hv'.imp_right fun h => (Finset.mem_filter.mp h).1
        simpa using this
      · exact huv
    have hdepth : ∀ w ∈ D, w.length ≤ n := fun w hw => (Finset.mem_filter.mp hw).2
    have haccount := card_freeAt_union_add_sum C D hdisjD hpfD hdepth
    have hsum : demand q L n = ∑ w ∈ D, q ^ (n - w.length) := by
      rw [← hlengths, demand_map_lengths_eq_sum xs hxs]
    rw [hsum]
    omega
  · intro hcapacity
    let lengths := L.sort (· ≤ ·)
    have hsorted : lengths.Pairwise (· ≤ ·) := by simp [lengths]
    have hcoe : (lengths : Multiset ℕ) = L := Multiset.sort_eq L (· ≤ ·)
    have hcapSorted : ∀ n ∈ lengths,
        demand q (lengths : Multiset ℕ) n ≤ (freeAt C n).card := by
      intro n hn
      rw [hcoe]
      apply hcapacity n
      have hn' : n ∈ (lengths : Multiset ℕ) := by simpa using hn
      rw [hcoe] at hn'
      exact hn'
    obtain ⟨xs, hxs⟩ := exists_extension_sorted C lengths hsorted hC hcapSorted
    exact ⟨xs, by simpa [hcoe] using hxs⟩

end D5.S0.Computability.Coding.ImmutableExtension
