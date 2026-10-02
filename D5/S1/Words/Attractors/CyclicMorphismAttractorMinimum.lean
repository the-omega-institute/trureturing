/- GID: D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum
   generality: G
   mirror-B: D5/B/S1/Words/Attractors/CyclicMorphismAttractorMinimum
   mirror-E: none(waiver:structural-word-proof)
   anchors: []
   utility: none
   digest: Original cyclic morphism prefixes and unrestricted string attractor minima. -/

import D5.S1.Recurrence.Raney.MaximalBlockEvolution
import D5.S1.Words.Powers.WordPower
import D5.S1.Words.Attractors.FiniteWordAttractors
import D5.S1.Words.Attractors.PeriodicPrefixAttractors

namespace D5.S1.Words.Attractors

open TrureTuring.Raney D5.S1.Words.Powers

/-- The original substitution, including the terminal letter's zero-only image. -/
def cyclicMorphism {k : Nat} (hk : 0 < k) (c : Fin k → Nat) (a : Fin k) :
    List (Fin k) :=
  if h : a.val + 1 < k then
    List.replicate (c a) ⟨0, hk⟩ ++ [⟨a.val + 1, h⟩]
  else List.replicate (c a) ⟨0, hk⟩

/-- Digits of the coefficient word with its final coefficient decreased by one. -/
def cyclicDigit {k : Nat} (c : Fin k → Nat) (a : Fin k) : Nat :=
  if a.val + 1 = k then c a - 1 else c a

/-- Advance an original letter cyclically, including the terminal zero. -/
def cyclicNext {k : Nat} (hk : 0 < k) (a : Fin k) : Fin k :=
  ⟨(a.val + 1) % k, Nat.mod_lt _ hk⟩

/-- The weak cyclic maximum permits equality with rotations. -/
def CyclicMaximal {k : Nat} (c : Fin k → Nat) : Prop :=
  ∀ r : Nat, (List.ofFn (cyclicDigit c)).rotate r ≤ List.ofFn (cyclicDigit c)

/-- The literal finite substitution iterates on the original alphabet. -/
def cyclicWord {k : Nat} (hk : 0 < k) (c : Fin k → Nat) (n : Nat) : List (Fin k) :=
  morphismPower (cyclicMorphism hk c) n [⟨0, hk⟩]

/-- Original iterate lengths, with no numeration or coding replacement. -/
def cyclicLength {k : Nat} (hk : 0 < k) (c : Fin k → Nat) (n : Nat) : Nat :=
  (cyclicWord hk c n).length

/-- A finite presentation of the length-`m` fixed-point prefix. -/
def cyclicPrefix {k : Nat} (hk : 0 < k) (c : Fin k → Nat) (m : Nat) : List (Fin k) :=
  (cyclicWord hk c m).take m

/-- The iterate's interior, expressed on the original alphabet. -/
def cyclicInterior {k : Nat} (hk : 0 < k) (c : Fin k → Nat) :
    Nat → Fin k → List (Fin k)
  | 0, _ => []
  | n + 1, a => wordPower (cyclicDigit c a) (cyclicWord hk c n) ++
      cyclicInterior hk c n (cyclicNext hk a)

/-- Consecutive periodic coefficient digits at the specified original phase. -/
def cyclicSegment {k : Nat} (hk : 0 < k) (c : Fin k → Nat)
    (n : Nat) (a : Fin k) : List Nat :=
  List.ofFn fun i : Fin n => cyclicDigit c ⟨(a.val + i.val) % k, Nat.mod_lt _ hk⟩

/-- The original coefficient blocks in decreasing iterate order. -/
def cyclicBlockProduct {k : Nat} (hk : 0 < k) (c : Fin k → Nat)
    (n count : Nat) (hcount : count ≤ k) : List (Fin k) :=
  (List.ofFn fun a : Fin count => wordPower (c ⟨a.val, a.isLt.trans_le hcount⟩)
    (cyclicWord hk c (n - 1 - a.val))).flatten

/-- The complete original piecewise minimum statement. -/
def CyclicAttractorMinimum {k : Nat} (hk : 0 < k) (c : Fin k → Nat) : Prop :=
  ∀ m : Nat, 0 < m →
    (∀ i : Nat, i ≤ k - 2 → cyclicLength hk c i ≤ m →
      m < cyclicLength hk c (i + 1) → gamma (cyclicPrefix hk c m) = i + 1) ∧
    (cyclicLength hk c (k - 1) ≤ m → gamma (cyclicPrefix hk c m) = k)

/-- Literal interiors, nested iterates, strict growth, and stable prefix semantics. -/
theorem cyclic_iterate_structure {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩) :
    (∀ (n : Nat) (a : Fin k),
      morphismPower (cyclicMorphism (by omega) c) n [a] =
        cyclicInterior (by omega) c n a ++
          [⟨(a.val + n) % k, Nat.mod_lt _ (by omega)⟩]) ∧
    (∀ n, cyclicWord (by omega) c n <+: cyclicWord (by omega) c (n + 1)) ∧
    (∀ n, cyclicLength (by omega) c n < cyclicLength (by omega) c (n + 1)) ∧
    (∀ n, n + 1 ≤ cyclicLength (by omega) c n) ∧
    (Monotone fun n => cyclicLength (by omega) c (n + 1) - cyclicLength (by omega) c n) ∧
    (∀ (m n : Nat), m ≤ cyclicLength (by omega) c n →
      cyclicPrefix (by omega) c m = (cyclicWord (by omega) c n).take m) := by
  let hk0 : 0 < k := by omega
  let z : Fin k := ⟨0, hk0⟩
  let μ := cyclicMorphism hk0 c
  have image (a : Fin k) :
      μ a = List.replicate (cyclicDigit c a) z ++ [cyclicNext hk0 a] := by
    dsimp [μ, cyclicMorphism, cyclicDigit, cyclicNext, z]
    split_ifs with ha hlast' hlast'
    · omega
    · congr 1
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt ha]
    · have haeq : a.val + 1 = k := by omega
      have heq : a = ⟨k - 1, by omega⟩ := by apply Fin.ext; simp; omega
      have hc : 0 < c a := by have := hlast; rw [← heq] at this; omega
      simp only [haeq, Nat.mod_self]
      change List.replicate (c a) z = List.replicate (c a - 1) z ++ [z]
      have he : c a = (c a - 1) + 1 := by omega
      rw [he, List.replicate_add]
      simp
    · omega
  have power_singleton_flatMap (n : Nat) (xs : List (Fin k)) :
      xs.flatMap (fun a => morphismPower μ n [a]) = morphismPower μ n xs := by
    induction n with
    | zero => simp [morphismPower]
    | succ n ih =>
      simp only [morphismPower]
      rw [← List.flatMap_assoc, ih]
  have advance (n : Nat) (xs : List (Fin k)) :
      morphismPower μ (n + 1) xs = morphismPower μ n (xs.flatMap μ) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [morphismPower, ih, morphismPower]
  have interior (n : Nat) (a : Fin k) :
      morphismPower μ n [a] = cyclicInterior hk0 c n a ++
        [⟨(a.val + n) % k, Nat.mod_lt _ hk0⟩] := by
    induction n generalizing a with
    | zero => simp [morphismPower, cyclicInterior, Nat.mod_eq_of_lt a.isLt]
    | succ n ih =>
      rw [advance]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [image, ← power_singleton_flatMap]
      simp only [List.flatMap_append, List.flatMap_replicate, List.flatMap_singleton]
      rw [ih (cyclicNext hk0 a)]
      simp only [cyclicInterior, cyclicWord, μ, z, wordPower, List.append_assoc]
      congr 2
      simp only [List.singleton_inj]
      apply Fin.ext
      simp [cyclicNext, Nat.add_comm, Nat.add_left_comm]
  have base : [z] <+: μ z := by
    rw [image]
    have hd : cyclicDigit c z = c z := by simp [cyclicDigit, z]; omega
    rw [hd]
    have hc : c z = 1 + (c z - 1) := by dsimp [z]; omega
    rw [hc, List.replicate_add]
    simp only [List.replicate_one, List.append_assoc]
    exact List.prefix_append _ _
  have nest (n : Nat) : cyclicWord hk0 c n <+: cyclicWord hk0 c (n + 1) := by
    induction n with
    | zero => simpa [cyclicWord, morphismPower, μ, z] using base
    | succ n ih => exact ih.flatMap μ
  have nonerase (a : Fin k) : 1 ≤ (μ a).length := by simp [image]
  have len_flat (xs : List (Fin k)) : xs.length ≤ (xs.flatMap μ).length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons];
                       have := nonerase a; omega
  have grow (n : Nat) : cyclicLength hk0 c n < cyclicLength hk0 c (n + 1) := by
    induction n with
    | zero =>
      simp only [cyclicLength, cyclicWord, morphismPower, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_singleton]
      change 1 < (μ z).length
      rw [image]
      have hd : cyclicDigit c z = c z := by simp [cyclicDigit, z]; omega
      simp only [List.length_append, List.length_replicate, List.length_singleton, hd]
      dsimp [z] at *
      omega
    | succ n ih =>
      obtain ⟨tail, heq⟩ := nest n
      have ht : 0 < tail.length := by
        have hlen := congrArg List.length heq
        change (cyclicWord hk0 c n).length < (cyclicWord hk0 c (n + 1)).length at ih
        simp only [List.length_append] at hlen
        omega
      change (cyclicWord hk0 c (n + 1)).length <
        ((cyclicWord hk0 c (n + 1)).flatMap μ).length
      rw [← heq, List.flatMap_append, List.length_append, List.length_append]
      have htail := len_flat tail
      change (cyclicWord hk0 c n).length + tail.length <
        (cyclicWord hk0 c (n + 1)).length + (tail.flatMap μ).length
      change (cyclicWord hk0 c n).length < (cyclicWord hk0 c (n + 1)).length at ih
      omega
  have lower (n : Nat) : n + 1 ≤ cyclicLength hk0 c n := by
    induction n with
    | zero => simp [cyclicLength, cyclicWord, morphismPower]
    | succ n ih => have := grow n; omega
  have nesting (m n : Nat) (h : m ≤ n) : cyclicWord hk0 c m <+: cyclicWord hk0 c n := by
    induction h with
    | refl => exact List.prefix_refl _
    | @step n h ih => exact ih.trans (nest n)
  have gaps : Monotone fun n => cyclicLength hk0 c (n + 1) - cyclicLength hk0 c n := by
    apply monotone_nat_of_le_succ
    intro n
    obtain ⟨tail, heq⟩ := nest n
    have hlen := congrArg List.length heq
    have hnext := congrArg (fun xs : List (Fin k) => (xs.flatMap μ).length) heq
    simp only [List.length_append, List.flatMap_append] at hlen hnext
    have htail := len_flat tail
    change (cyclicWord hk0 c (n + 1)).length - (cyclicWord hk0 c n).length ≤
      (cyclicWord hk0 c (n + 2)).length - (cyclicWord hk0 c (n + 1)).length
    change (cyclicWord hk0 c n).length + tail.length =
      (cyclicWord hk0 c (n + 1)).length at hlen
    change (cyclicWord hk0 c (n + 1)).length + (tail.flatMap μ).length =
      (cyclicWord hk0 c (n + 2)).length at hnext
    omega
  refine ⟨interior, nest, grow, lower, gaps, ?_⟩
  intro m n hmn
  dsimp [cyclicPrefix]
  change m ≤ (cyclicWord hk0 c n).length at hmn
  have hmm : m ≤ (cyclicWord hk0 c m).length := by
    have := lower m
    change m + 1 ≤ (cyclicWord hk0 c m).length at this
    omega
  rcases le_total m n with h | h
  · exact ((nesting m n h).take m).eq_of_length (by simp only [List.length_take,
      Nat.min_eq_left hmm, Nat.min_eq_left hmn])
  · exact ((nesting n m h).take m).eq_of_length (by simp only [List.length_take,
      Nat.min_eq_left hmn, Nat.min_eq_left hmm]) |>.symm

/-- Removing the final letter gives a periodic prefix at every iterate level.
    The proof compares actual original-letter interiors, including equal rotations. -/
theorem cyclic_fractional_prefix {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩)
    (hcyc : CyclicMaximal c) (n : Nat) :
    (cyclicWord (by omega) c (n + 1)).dropLast <+:
      wordPower (c ⟨0, by omega⟩ + 1) (cyclicWord (by omega) c n) := by
  let hk0 : 0 < k := by omega
  let z : Fin k := ⟨0, hk0⟩
  have segments_maximal (s : Nat) (a : Fin k) :
      cyclicSegment hk0 c s a ≤ cyclicSegment hk0 c s ⟨0, hk0⟩ := by
    let d := List.ofFn (cyclicDigit c)
    have rotation (a : Fin k) : cyclicSegment hk0 c k a = d.rotate a.val := by
      apply List.ext_getElem
      · simp [cyclicSegment, d]
      · intro i hi hi'
        simp only [cyclicSegment, List.getElem_ofFn, List.getElem_rotate,
          d, List.length_ofFn]
        congr 1
        apply Fin.ext
        simp [Nat.add_comm]
    have zero : cyclicSegment hk0 c k ⟨0, hk0⟩ = d := by simpa using rotation ⟨0, hk0⟩
    by_contra hn
    have hlt : cyclicSegment hk0 c s ⟨0, hk0⟩ < cyclicSegment hk0 c s a := lt_of_not_ge hn
    rcases List.lt_iff_exists.mp hlt with ⟨heq, hlen⟩ | ⟨i, hi0, hia, hbefore, hat⟩
    · simp [cyclicSegment] at hlen
    have hi : i < s := by simpa [cyclicSegment] using hi0
    have him : i % k < k := Nat.mod_lt _ hk0
    have himi : i % k ≤ i := Nat.mod_le _ _
    have bad : cyclicSegment hk0 c k ⟨0, hk0⟩ < cyclicSegment hk0 c k a := by
      apply List.lt_iff_exists.mpr
      right
      refine ⟨i % k, by simpa [cyclicSegment] using him,
        by simpa [cyclicSegment] using him, ?_, ?_⟩
      · intro j hj
        have hj0 : j < i := hj.trans_le himi
        have he := hbefore j hj0
        simpa only [cyclicSegment, List.getElem_ofFn] using he
      · simpa only [cyclicSegment, List.getElem_ofFn, Fin.val_mk, Nat.zero_add,
          Nat.mod_mod, Nat.add_mod_mod] using hat
    rw [zero, rotation] at bad
    exact (not_lt_of_ge (hcyc a.val)) bad
  have hstructure := (cyclic_iterate_structure hk c h0 hlast).1
  have segment_succ (s : Nat) (a : Fin k) :
      cyclicSegment hk0 c (s + 1) a =
        cyclicDigit c a :: cyclicSegment hk0 c s (cyclicNext hk0 a) := by
    unfold cyclicSegment
    rw [List.ofFn_succ]
    congr 1
    · congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt a.isLt]
    · apply congrArg List.ofFn
      funext i
      congr 1
      apply Fin.ext
      simp [cyclicNext, Nat.add_comm, Nat.add_left_comm]
  have interior_prefix (s : Nat) : cyclicInterior hk0 c s z <+: cyclicWord hk0 c s := by
    change cyclicInterior hk0 c s z <+: morphismPower (cyclicMorphism hk0 c) s [z]
    rw [hstructure s z]
    exact List.prefix_append _ _
  have power_add (s t : Nat) (w : List (Fin k)) :
      wordPower (s + t) w = wordPower s w ++ wordPower t w := by
    unfold wordPower
    rw [List.replicate_add, List.flatten_append]
  have power_prefix {s t : Nat} (hst : s ≤ t) (w : List (Fin k)) :
      wordPower s w <+: wordPower t w := by
    apply List.IsPrefix.flatten
    apply List.prefix_replicate_iff.mpr
    simp [hst]
  have compare (s : Nat) (a b : Fin k)
      (hab : cyclicSegment hk0 c s a ≤ cyclicSegment hk0 c s b) :
      cyclicInterior hk0 c s a <+: cyclicInterior hk0 c s b := by
    induction s generalizing a b with
    | zero => simp [cyclicInterior]
    | succ s ih =>
      rw [segment_succ, segment_succ] at hab
      have cases : cyclicDigit c a < cyclicDigit c b ∨
          cyclicDigit c a = cyclicDigit c b ∧
            cyclicSegment hk0 c s (cyclicNext hk0 a) ≤
              cyclicSegment hk0 c s (cyclicNext hk0 b) := by
        rcases lt_or_eq_of_le hab with h | h
        · change List.Lex (· < ·) _ _ at h
          rcases List.cons_lex_cons_iff.mp h with h | ⟨he, ht⟩
          · exact Or.inl h
          · exact Or.inr ⟨he, le_of_lt ht⟩
        · obtain ⟨he, ht⟩ := List.cons.inj h
          exact Or.inr ⟨he, ht.le⟩
      rcases cases with hlt | ⟨heq, htail⟩
      · have ht : cyclicInterior hk0 c s (cyclicNext hk0 a) <+: cyclicWord hk0 c s :=
          (ih _ z (segments_maximal s _)).trans (interior_prefix s)
        have first : cyclicInterior hk0 c (s + 1) a <+:
            wordPower (cyclicDigit c a + 1) (cyclicWord hk0 c s) := by
          rw [cyclicInterior, power_add, wordPower_one, List.prefix_append_right_inj]
          exact ht
        exact (first.trans (power_prefix (by omega) _)).trans (List.prefix_append _ _)
      · simp only [cyclicInterior, heq, List.prefix_append_right_inj]
        exact ih _ _ htail
  have ht : cyclicInterior hk0 c n (cyclicNext hk0 z) <+: cyclicWord hk0 c n :=
    (compare n _ z (segments_maximal n _)).trans (interior_prefix n)
  change (morphismPower (cyclicMorphism hk0 c) (n + 1) [z]).dropLast <+: _
  rw [hstructure (n + 1) z, List.dropLast_concat, cyclicInterior]
  have hd : cyclicDigit c z = c z := by simp [cyclicDigit, z]; omega
  rw [hd, power_add, wordPower_one, List.prefix_append_right_inj]
  exact ht

/-- Both the short and full recurrences use the original coefficients and letters. -/
theorem cyclic_word_recurrence {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩) :
    (∀ (n : Nat) (hn : n < k), cyclicWord (by omega) c n =
      cyclicBlockProduct (by omega) c n n hn.le ++ [⟨n, hn⟩]) ∧
    (∀ (n : Nat), k ≤ n → cyclicWord (by omega) c n =
      cyclicBlockProduct (by omega) c n k le_rfl) := by
  let hk0 : 0 < k := by omega
  let z : Fin k := ⟨0, hk0⟩
  let phase (a : Fin k) (j : Nat) : Fin k := ⟨(a.val + j) % k, Nat.mod_lt _ hk0⟩
  have phase_zero (a : Fin k) : phase a 0 = a := by
    apply Fin.ext; simp [phase, Nat.mod_eq_of_lt a.isLt]
  have phase_next (a : Fin k) (j : Nat) :
      phase (cyclicNext hk0 a) j = phase a (j + 1) := by
    apply Fin.ext
    simp [phase, cyclicNext, Nat.add_comm, Nat.add_left_comm]
  have hstructure := (cyclic_iterate_structure hk c h0 hlast).1
  have expand (m s : Nat) (hms : m ≤ s) (a : Fin k) :
      cyclicInterior hk0 c s a =
        (List.ofFn fun j : Fin m => wordPower (cyclicDigit c (phase a j.val))
          (cyclicWord hk0 c (s - 1 - j.val))).flatten ++
        cyclicInterior hk0 c (s - m) (phase a m) := by
    induction m generalizing s a with
    | zero => simp [phase_zero]
    | succ m ih =>
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have hmt : m ≤ t := by omega
      rw [cyclicInterior, ih t hmt (cyclicNext hk0 a), List.ofFn_succ]
      simp only [List.flatten_cons, Fin.val_zero, phase_zero, Nat.sub_zero,
        Nat.add_sub_cancel, Fin.val_succ, List.append_assoc]
      congr 2
      · apply congrArg List.flatten
        apply congrArg List.ofFn
        funext j
        rw [phase_next]
        congr 2
        omega
      · congr 1
        · omega
        · exact phase_next a m
  have power_add (s t : Nat) (w : List (Fin k)) :
      wordPower (s + t) w = wordPower s w ++ wordPower t w := by
    unfold wordPower
    rw [List.replicate_add, List.flatten_append]
  refine ⟨?_, ?_⟩
  · intro n hn
    change morphismPower (cyclicMorphism hk0 c) n [z] = _
    rw [hstructure n z, expand n n le_rfl]
    simp only [Nat.sub_self, cyclicInterior, List.append_nil]
    have products :
        (List.ofFn fun j : Fin n => wordPower (cyclicDigit c (phase z j.val))
          (cyclicWord hk0 c (n - 1 - j.val))).flatten =
        cyclicBlockProduct hk0 c n n hn.le := by
      unfold cyclicBlockProduct
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext j
      have hj : j.val + 1 < k := by have := j.isLt; omega
      have hp : phase z j.val = ⟨j.val, j.isLt.trans hn⟩ := by
        apply Fin.ext; simp [phase, z, Nat.mod_eq_of_lt (j.isLt.trans hn)]
      simp [hp, cyclicDigit, ne_of_lt hj]
    rw [products]
    congr 2
    apply Fin.ext
    simp [z, Nat.mod_eq_of_lt hn]
  · intro n hn
    have hkk : k - 1 + 1 = k := by omega
    have hm : k - 1 ≤ n := by omega
    have hphase : phase z (k - 1) = ⟨k - 1, by omega⟩ := by
      apply Fin.ext; simp [phase, z, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
    have hphaseNext : cyclicNext hk0 ⟨k - 1, by omega⟩ = z := by
      apply Fin.ext; simp [cyclicNext, z, hkk]
    change morphismPower (cyclicMorphism hk0 c) n [z] = _
    rw [hstructure n z, expand (k - 1) n hm, hphase]
    have hs : n - (k - 1) = (n - k) + 1 := by omega
    rw [hs, cyclicInterior, hphaseNext]
    have firstProducts :
        (List.ofFn fun j : Fin (k - 1) => wordPower (cyclicDigit c (phase z j.val))
          (cyclicWord hk0 c (n - 1 - j.val))).flatten =
        cyclicBlockProduct hk0 c n (k - 1) (by omega) := by
      unfold cyclicBlockProduct
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext j
      have hj : j.val + 1 < k := by have := j.isLt; omega
      have hp : phase z j.val = ⟨j.val, by omega⟩ := by
        apply Fin.ext; simp [phase, z, Nat.mod_eq_of_lt (by omega : j.val < k)]
      simp [hp, cyclicDigit, ne_of_lt hj]
    rw [firstProducts]
    have hend : (⟨(z.val + n) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
        ⟨(z.val + (n - k)) % k, Nat.mod_lt _ hk0⟩ := by
      apply Fin.ext
      have he : n = k + (n - k) := by omega
      simp only [z, Nat.zero_add]
      conv_lhs => rw [he]
      simp
    rw [List.append_assoc, List.append_assoc, hend, ← hstructure (n - k) z]
    simp only [cyclicDigit, hkk, if_true]
    change cyclicBlockProduct hk0 c n (k - 1) (by omega) ++
      (wordPower (c ⟨k - 1, by omega⟩ - 1) (cyclicWord hk0 c (n - k)) ++
        cyclicWord hk0 c (n - k)) = cyclicBlockProduct hk0 c n k le_rfl
    have hc : c ⟨k - 1, by omega⟩ = (c ⟨k - 1, by omega⟩ - 1) + 1 := by omega
    have lastpower : wordPower (c ⟨k - 1, by omega⟩ - 1) (cyclicWord hk0 c (n - k)) ++
        cyclicWord hk0 c (n - k) = wordPower (c ⟨k - 1, by omega⟩)
          (cyclicWord hk0 c (n - k)) := by
      conv_rhs => rw [hc, power_add, wordPower_one]
    rw [lastpower]
    let f (a : Fin k) := wordPower (c a) (cyclicWord hk0 c (n - 1 - a.val))
    have hf := List.ofFn_succ_last (f := fun a : Fin (k - 1 + 1) => f (Fin.cast hkk a))
    have he : (List.ofFn fun a : Fin (k - 1 + 1) => f (Fin.cast hkk a)) =
        List.ofFn f := by
      simpa using (List.ofFn_congr hkk (fun a => f (Fin.cast hkk a)))
    rw [he] at hf
    unfold cyclicBlockProduct
    change _ = (List.ofFn f).flatten
    rw [hf]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, f, Fin.val_cast, Fin.val_castSucc, Fin.val_last]
    have hidx : n - 1 - (k - 1) = n - k := by omega
    rw [hidx]
    rfl

/-- The original all-parameter, all-prefix string-attractor minimum. -/
theorem result {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩)
    (hcyc : CyclicMaximal c) :
    ∀ m : Nat, 0 < m →
      (∀ i : Nat, i ≤ k - 2 → cyclicLength (by omega) c i ≤ m →
        m < cyclicLength (by omega) c (i + 1) →
          gamma (cyclicPrefix (by omega) c m) = i + 1) ∧
      (cyclicLength (by omega) c (k - 1) ≤ m →
        gamma (cyclicPrefix (by omega) c m) = k) := by
  classical
  let hk0 : 0 < k := by omega
  let w := cyclicPrefix hk0 c
  let U := cyclicLength hk0 c
  let B := fun n => U (n + 1) - 1
  let Δ := fun n => B n - U n
  let P := fun n => U n + if n < k then 0 else Δ (n - k)
  let Γ := fun n => (Finset.Icc (n + 1 - k) n).image fun j => U j - 1
  obtain ⟨hint, hnest, hgrow, hlower, hgaps, hstable⟩ := cyclic_iterate_structure hk c h0 hlast
  change ∀ n, U n < U (n + 1) at hgrow
  change ∀ n, n + 1 ≤ U n at hlower
  change Monotone (fun n => U (n + 1) - U n) at hgaps
  have hlen (m : Nat) : (w m).length = m := by
    have hm := hlower m
    change m + 1 ≤ (cyclicWord hk0 c m).length at hm
    simp only [w, cyclicPrefix, List.length_take]
    omega
  have hU : StrictMono U := strictMono_nat_of_lt_succ hgrow
  have hU0 : U 0 = 1 := by simp [U, cyclicLength, cyclicWord, morphismPower]
  have hpos (n : Nat) : 0 < U n := by have := hlower n; omega
  have hstep (n : Nat) : U n < U (n + 1) := hgrow n
  have hprefix (m n : Nat) (hmn : m ≤ n) : w m = (w n).take m := by
    have hn := hlower n
    have hmnU : m ≤ U n := by omega
    have hnU : n ≤ U n := by omega
    change cyclicPrefix hk0 c m = (cyclicPrefix hk0 c n).take m
    rw [hstable m n hmnU, hstable n n hnU, List.take_take, Nat.min_eq_left hmn]
  have wpref {m n : Nat} (h : m ≤ n) : w m <+: w n := by
    rw [hprefix m n h]; exact List.take_prefix _ _
  have hword (n : Nat) : w (U n) = cyclicWord hk0 c n := by
    change cyclicPrefix hk0 c (U n) = cyclicWord hk0 c n
    rw [hstable (U n) n le_rfl]
    exact List.take_length
  have hperiod (n : Nat) : List.HasPeriod (w (B n)) (U n) := by
    have hcap : w (B n) = (cyclicWord hk0 c (n + 1)).dropLast := by
      change cyclicPrefix hk0 c (B n) = _
      rw [hstable (B n) (n + 1) (by change U (n + 1) - 1 ≤ U (n + 1); omega), List.dropLast_eq_take]
      rfl
    rw [hcap]
    have hpower : List.HasPeriod
        (wordPower (c ⟨0, hk0⟩ + 1) (cyclicWord hk0 c n)) (U n) := by
      apply List.hasPeriod_iff_getElem?.mpr
      intro i hi
      change i < (wordPower (c ⟨0, hk0⟩ + 1) (cyclicWord hk0 c n)).length -
        (cyclicWord hk0 c n).length at hi
      exact wordPower_period_getElem? _ _ i (by rw [length_wordPower] at hi; omega)
    exact hpower.infix (cyclic_fractional_prefix hk c h0 hlast hcyc n).isInfix
  let b := fun n h => if hh : n - 1 - h < k then c ⟨n - 1 - h, hh⟩ else 0
  have stack (n count : Nat) (hck : count ≤ k) (hcn : count ≤ n) :
      descendingBlocks w U (b n) count (n - count) =
        cyclicBlockProduct hk0 c n count hck := by
    induction count with
    | zero => simp [descendingBlocks, cyclicBlockProduct]
    | succ count ih =>
      have hc : count < k := by omega
      have hstart : n - (count + 1) + 1 = n - count := by omega
      have hidx : n - 1 - (n - (count + 1)) = count := by omega
      rw [descendingBlocks, hstart, ih (by omega) (by omega)]
      have hb : b n (n - (count + 1)) = c ⟨count, hc⟩ := by simp [b, hidx, hc]
      rw [hb, hword]
      unfold cyclicBlockProduct
      rw [List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        Fin.val_castSucc, Fin.val_last]
      rw [show n - (count + 1) = n - 1 - count by omega]
  have hsuffix (n : Nat) (hkn : k ≤ n) : w (U (n - k)) <:+ w (U n) := by
    have hrec := (cyclic_word_recurrence hk c h0 hlast).2 n hkn
    have hw : w (U n) = descendingBlocks w U (b n) k (n - k) := by
      rw [hword, stack n k le_rfl hkn]; exact hrec
    have hc : 0 < b n (n - k) := by
      have hi : n - 1 - (n - k) = k - 1 := by omega
      have hl : k - 1 < k := by omega
      have h : 1 ≤ b n (n - k) := by simpa [b, hi, hl] using hlast
      omega
    have hp : w (U (n - k)) <:+ wordPower (b n (n - k)) (w (U (n - k))) := by
      conv_lhs => rw [← wordPower_one (w (U (n - k)))]
      apply List.IsSuffix.flatten
      apply List.suffix_replicate_iff.mpr
      simp only [List.length_replicate]
      exact ⟨by omega, trivial⟩
    have hd : descendingBlocks w U (b n) ((k - 1) + 1) (n - k) =
        descendingBlocks w U (b n) (k - 1) (n - k + 1) ++
          wordPower (b n (n - k)) (w (U (n - k))) := rfl
    rw [show (k - 1) + 1 = k by omega] at hd
    rw [hw, hd]
    exact hp.trans (List.suffix_append _ _)
  have intervals := nested_word_endpoint_attractors k hk w U hlen hprefix hU0 hU hgaps
    hperiod hsuffix
  change ∀ n, P n ≤ B n ∧ ∀ m, P n ≤ m → m ≤ B n → IsAttractor (w m) (Γ n) at intervals
  have cardΓ (n : Nat) : (Γ n).card ≤ min k (n + 1) := by
    have hc := Finset.card_image_le (s := Finset.Icc (n + 1 - k) n) (f := fun j => U j - 1)
    rw [Nat.card_Icc] at hc
    dsimp only [Γ]
    omega
  have lower (i m : Nat) (hi : i < k) (him : U i ≤ m) : i + 1 ≤ gamma (w m) := by
    have hletters : Finset.Iic (⟨i, hi⟩ : Fin k) ⊆ (w m).toFinset := by
      intro a ha
      have hai : a.val ≤ i := by
        have h : a ≤ (⟨i, hi⟩ : Fin k) := Finset.mem_Iic.mp ha
        exact h
      have ham : U a.val ≤ m := (hU.monotone hai).trans him
      have terminal : a ∈ cyclicWord hk0 c a.val := by
        have ht := hint a.val ⟨0, hk0⟩
        change cyclicWord hk0 c a.val = _ at ht
        have he : (⟨(0 + a.val) % k, Nat.mod_lt _ hk0⟩ : Fin k) = a := by
          apply Fin.ext; simp [Nat.mod_eq_of_lt a.isLt]
        rw [ht, he]; simp
      apply List.mem_toFinset.mpr
      exact (wpref ham).subset (by rw [hword]; exact terminal)
    have hc := Finset.card_le_card hletters
    rw [Fin.card_Iic] at hc
    exact hc.trans (attractor_minimum (w m)).2.2
  intro m hm
  change (∀ i, i ≤ k - 2 → U i ≤ m → m < U (i + 1) → gamma (w m) = i + 1) ∧
    (U (k - 1) ≤ m → gamma (w m) = k)
  refine ⟨?_, ?_⟩
  · intro i hik him hmnext
    have hi : i < k := by omega
    have hmP : P i ≤ m := by simpa only [P, if_pos hi, Nat.add_zero] using him
    have hmB : m ≤ B i := by dsimp only [B]; omega
    have upper := (attractor_minimum (w m)).2.1 (Γ i) ((intervals i).2 m hmP hmB)
    have hc := cardΓ i
    exact Nat.le_antisymm (by omega) (lower i m hi him)
  · intro hmk
    have existsn : ∃ n, m < U (n + 1) := by
      exact ⟨m, by have := hlower (m + 1); omega⟩
    let n := Nat.find existsn
    have hmnext : m < U (n + 1) := Nat.find_spec existsn
    have hnm : U n ≤ m := by
      by_cases hn0 : n = 0
      · rw [hn0, hU0]; omega
      · have hn' : n - 1 < n := by omega
        have h := Nat.find_min existsn hn'
        have he : n - 1 + 1 = n := by omega
        rw [he] at h; omega
    have hnk : k - 1 ≤ n := by
      by_contra hbad
      have hi : n + 1 ≤ k - 1 := by omega
      have h := hU.monotone hi
      omega
    have hmB : m ≤ B n := by dsimp only [B]; omega
    have hl : k ≤ gamma (w m) := by
      have h := lower (k - 1) m (by omega) hmk
      omega
    apply Nat.le_antisymm _ hl
    by_cases hmP : P n ≤ m
    · exact ((attractor_minimum (w m)).2.1 (Γ n) ((intervals n).2 m hmP hmB)).trans
        ((cardΓ n).trans (Nat.min_le_left _ _))
    · have hkn : k ≤ n := by
        by_contra hbad
        have hn : n < k := by omega
        have hp : P n = U n := by simp [P, hn]
        rw [hp] at hmP; omega
      let t := n - k
      let r := m - U n
      have hm : m = U n + r := by dsimp only [r]; omega
      have hr : r < Δ t := by
        have hp : P n = U n + Δ t := by simp only [P, if_neg (by omega : ¬n < k), t]
        rw [hp] at hmP; omega
      have hrB : r < B t := by dsimp only [Δ] at hr; omega
      have hperM : List.HasPeriod (w m) (U n) := (hperiod n).infix (wpref hmB).isInfix
      have htail : (w m).drop (U n) = w r := by
        have hp := hperM.drop_prefix (U n)
        have hrl : ((w m).drop (U n)).length = r := by rw [List.length_drop, hlen, hm]; omega
        have hrm : r ≤ m := by omega
        have he := (hp.take r).eq_of_length (by
          simp only [List.length_take, hrl, hlen, Nat.min_self, Nat.min_eq_left hrm])
        rw [(List.take_eq_self_iff _).mpr (by omega : ((w m).drop (U n)).length ≤ r),
          ← hprefix r m hrm] at he
        exact he
      have hWM : w m = descendingBlocks w U (b n) k t ++ w r := by
        rw [← List.take_append_drop (U n) (w m), ← hprefix (U n) m hnm, htail,
          stack n k le_rfl hkn, hword]
        exact congrArg (fun v => v ++ w r) ((cyclic_word_recurrence hk c h0 hlast).2 n hkn)
      obtain ⟨h, p, hth, hhn, hUp, hpN, hbound, hwindow, hright⟩ :=
        periodic_residual_scan w U (b n) hlen hprefix hU hpos hperiod k t (U n) r
          (w r) (w m) (by omega) (wpref hrB.le) (by rw [hlen]; exact hrB)
          (by rw [hlen]) hWM (by rw [hlen, hm]) (by
            have ht : t + k = n := by dsimp only [t]; omega
            rw [ht, hlen]; have := hpos n; omega)
      have hhn' : h ≤ n - 1 := by dsimp only [t] at hhn; omega
      have hold : IsAttractor ((w m).take (U n - 1)) (Γ (n - 1)) := by
        have hn : n - 1 + 1 = n := by omega
        have hBm : B (n - 1) ≤ m := by dsimp only [B]; rw [hn]; omega
        rw [← hprefix (U n - 1) m (by omega)]
        have h := (intervals (n - 1)).2 (B (n - 1)) (intervals (n - 1)).1 le_rfl
        simpa only [B, hn] using h
      have hqB : U h ≤ B h := by have := hstep h; dsimp only [B]; omega
      have hBN : B h ≤ U n - 1 := by
        have ht := hU.monotone (by omega : h + 1 ≤ n)
        dsimp only [B]; omega
      have hqS : U h - 1 ∈ Γ (n - 1) := by
        apply Finset.mem_image.mpr
        exact ⟨h, Finset.mem_Icc.mpr ⟨by dsimp only [t] at hth; omega, hhn'⟩, rfl⟩
      have hcut : B h = U n - 1 ∨ B h ∈ (Γ (n - 1)).erase (U h - 1) := by
        by_cases hh : h = n - 1
        · left; dsimp only [B]; rw [hh, show n - 1 + 1 = n by omega]
        · right
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_image.mpr ⟨h + 1,
            Finset.mem_Icc.mpr ⟨by dsimp only [t] at hth; omega, by omega⟩, rfl⟩⟩
          have := hstep h; have := hpos h; dsimp only [B]; omega
      have hwcap : (w m).take (B h) = w (B h) := (hprefix (B h) m (by omega)).symm
      rw [← hwcap] at hwindow hright
      have hs := attractor_window_transfer (w m) (U n) (U h) p (B h) (Γ (n - 1))
        (hpos n) (by rw [hlen]; exact hnm) (hpos h) hUp hpN hqB hBN
        hwindow hbound hold hqS hcut (Or.inr hright)
      exact ((attractor_minimum (w m)).2.1 _ hs.1).trans
        (hs.2.trans ((cardΓ (n - 1)).trans (Nat.min_le_left _ _)))

end D5.S1.Words.Attractors
