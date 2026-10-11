/- GID: D5/S1/Words/MBonacciSentinelDesubstitution
   generality: G
   mirror-B: D5/B/S1/Words/MBonacciSentinelDesubstitution
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Actual m-bonacci word, sentinel parsing and fully right-special descent. -/
import D5.S1.Words.RankOneMorphismIterationBoundDefs
import Mathlib.Data.List.Infix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciSentinelDesubstitution

open RankOneMorphismIterationBound (subst image subst_append image_add)
open AbelianBorders.AbelianBorderQuestionDefs (factor)

variable {m : ℕ} (hm : 2 ≤ m)

/-- The first letter, with positivity derived from the order bound. -/
def zero : Fin m := ⟨0, by omega⟩

/-- Cyclic successor on the actual alphabet. -/
def rot (a : Fin m) : Fin m :=
  if h : a.val + 1 < m then ⟨a.val + 1, h⟩ else zero hm

/-- The literal m-bonacci substitution. -/
def phi (a : Fin m) : List (Fin m) :=
  if h : a.val + 1 < m then [zero hm, ⟨a.val + 1, h⟩] else [zero hm]

private theorem phi_pos (a : Fin m) : 0 < (phi hm a).length := by
  unfold phi; split <;> simp

private theorem phi_len_le (a : Fin m) : (phi hm a).length ≤ 2 := by
  unfold phi; split <;> simp

private theorem rot_injective : Function.Injective (rot hm) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold rot zero at hv
  split_ifs at hv <;> apply Fin.ext <;> dsimp at hv <;> have := a.isLt <;>
    have := b.isLt <;> omega

private theorem subst_length_ge (s : List (Fin m)) : s.length ≤ (subst (phi hm) s).length := by
  induction s with
  | nil => simp [subst]
  | cons a s ih =>
    simp only [RankOneMorphismIterationBound.subst_cons, List.length_append, List.length_cons]
    have := phi_pos hm a
    omega

private theorem image_pos (k : ℕ) (a : Fin m) : 0 < (image (phi hm) k a).length := by
  induction k with
  | zero => simp [image]
  | succ k ih => exact lt_of_lt_of_le ih (subst_length_ge hm _)

private theorem image_step (k : ℕ) :
    image (phi hm) (k + 1) (zero hm) =
      image (phi hm) k (zero hm) ++ image (phi hm) k (⟨1, by omega⟩ : Fin m) := by
  rw [image_add _ k 1]
  simp [phi, zero, subst, show 0 + 1 < m by omega]

private theorem iterate_prefix_succ (k : ℕ) :
    image (phi hm) k (zero hm) <+: image (phi hm) (k + 1) (zero hm) := by
  rw [image_step]; exact List.prefix_append _ _

private theorem iterate_prefix {k t : ℕ} (h : k ≤ t) :
    image (phi hm) k (zero hm) <+: image (phi hm) t (zero hm) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  induction s with
  | zero => simp
  | succ s ih => exact (ih (by omega)).trans (iterate_prefix_succ hm (k + s))

private theorem iterate_growth (k : ℕ) : k + 1 ≤ (image (phi hm) k (zero hm)).length := by
  induction k with
  | zero => simp [image]
  | succ k ih =>
    rw [image_step, List.length_append]
    have := image_pos hm k (⟨1, by omega⟩ : Fin m)
    omega

/-- The actual limit of the nested, unbounded iterates, with no fixed-word premise. -/
def word (n : ℕ) : Fin m :=
  (image (phi hm) (n + 1) (zero hm))[n]'(by have := iterate_growth hm (n + 1); omega)

private theorem word_eq_iterate (k n : ℕ) (hn : n < (image (phi hm) k (zero hm)).length) :
    word hm n = (image (phi hm) k (zero hm))[n] := by
  have hk := iterate_prefix hm (Nat.le_max_left k (n + 1))
  have hn' := iterate_prefix hm (Nat.le_max_right k (n + 1))
  exact (hn'.getElem (by have := iterate_growth hm (n + 1); omega)).trans
    (hk.getElem hn).symm

private theorem factor_len (x : ℕ → Fin m) (i n : ℕ) : (factor x i n).length = n := by
  simp [factor]

private theorem factor_add (x : ℕ → Fin m) (i n t : ℕ) :
    factor x i (n + t) = factor x i n ++ factor x (i + n) t := by
  simp only [factor, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

private theorem factor_get (x : ℕ → Fin m) (i n j : ℕ) (hj : j < n) :
    (factor x i n)[j]'(by rw [factor_len]; exact hj) = x (i + j) := by
  simp [factor]

private theorem factor_take (x : ℕ → Fin m) (i n t : ℕ) (h : t ≤ n) :
    (factor x i n).take t = factor x i t := by
  simp [factor, ← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem iterate_factor (k : ℕ) :
    factor (word hm) 0 (image (phi hm) k (zero hm)).length = image (phi hm) k (zero hm) := by
  apply List.ext_getElem
  · exact factor_len _ _ _
  · intro i hi hj
    rw [factor_get _ _ _ _ (by simpa [factor_len] using hi)]
    simpa using word_eq_iterate hm k i hj

private theorem factor_of_prefix {s : List (Fin m)} {k : ℕ}
    (h : s <+: image (phi hm) k (zero hm)) : factor (word hm) 0 s.length = s := by
  have hlen := h.length_le
  rw [← iterate_factor hm k] at h
  have ht := List.prefix_iff_eq_take.mp h
  rw [factor_take _ _ _ _ hlen] at ht
  exact ht.symm

/-- The true boundary after the first `i` source letters. -/
def boundary (i : ℕ) : ℕ := (subst (phi hm) (factor (word hm) 0 i)).length

private theorem substituted_prefix (i : ℕ) :
    factor (word hm) 0 (boundary hm i) = subst (phi hm) (factor (word hm) 0 i) := by
  have hg : i ≤ (image (phi hm) (i + 1) (zero hm)).length := by
    have := iterate_growth hm (i + 1); omega
  have hp : factor (word hm) 0 i <+: image (phi hm) (i + 1) (zero hm) := by
    rw [← iterate_factor hm (i + 1), ← factor_take _ _ _ _ hg]
    exact List.take_prefix _ _
  exact factor_of_prefix hm (show subst (phi hm) (factor (word hm) 0 i) <+:
    image (phi hm) (i + 2) (zero hm) from hp.flatMap (phi hm))

private theorem boundary_zero : boundary hm 0 = 0 := by simp [boundary, factor, subst]

private theorem boundary_succ (i : ℕ) :
    boundary hm (i + 1) = boundary hm i + (phi hm (word hm i)).length := by
  simp only [boundary, factor_add, subst_append, List.length_append]
  simp [factor, subst]

private theorem boundary_strict : StrictMono (boundary hm) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [boundary_succ]
  have := phi_pos hm (word hm i)
  omega

private theorem block_factor (i : ℕ) :
    factor (word hm) (boundary hm i) (phi hm (word hm i)).length = phi hm (word hm i) := by
  have h := substituted_prefix hm (i + 1)
  rw [boundary_succ, factor_add, substituted_prefix hm i] at h
  rw [factor_add, subst_append] at h
  simpa [factor, subst] using List.append_cancel_left h

private theorem block_letter (i j : ℕ) (hj : j < (phi hm (word hm i)).length) :
    word hm (boundary hm i + j) = (phi hm (word hm i))[j] := by
  have h := congrArg (fun s : List (Fin m) => s[j]?) (block_factor hm i)
  simpa [List.getElem?_eq_getElem, factor_get, factor_len, hj] using h

private theorem at_boundary (i : ℕ) : word hm (boundary hm i) = zero hm := by
  have h := block_letter hm i 0 (phi_pos hm _)
  unfold phi at h
  split_ifs at h <;> simpa using h

private theorem after_boundary (i : ℕ) : word hm (boundary hm i + 1) = rot hm (word hm i) := by
  by_cases h : (word hm i).val + 1 < m
  · have hb := block_letter hm i 1 (by simp [phi, h])
    simpa [phi, rot, h] using hb
  · have hb := at_boundary hm (i + 1)
    rw [boundary_succ] at hb
    simpa [phi, rot, h] using hb

private theorem boundary_window (q : ℕ) :
    ∃ i, boundary hm i ≤ q ∧ q < boundary hm (i + 1) := by
  induction q with
  | zero =>
    refine ⟨0, by rw [boundary_zero], ?_⟩
    have := boundary_strict hm (show 0 < 1 by omega)
    rw [boundary_zero] at this
    exact this
  | succ q ih =>
    obtain ⟨i, hi, hj⟩ := ih
    by_cases h : q + 1 < boundary hm (i + 1)
    · exact ⟨i, by omega, h⟩
    · have hs := boundary_strict hm (show i + 1 < i + 1 + 1 by omega)
      exact ⟨i + 1, by omega, by omega⟩

private theorem zero_boundary (q : ℕ) :
    word hm q = zero hm ↔ ∃ i, q = boundary hm i := by
  constructor
  · intro hz
    obtain ⟨i, hi, hj⟩ := boundary_window hm q
    refine ⟨i, ?_⟩
    by_contra hne
    have hlt : boundary hm i < q := by omega
    rw [boundary_succ] at hj
    have hlen := phi_len_le hm (word hm i)
    have hq : q = boundary hm i + 1 := by omega
    have hs : (word hm i).val + 1 < m := by
      by_contra hn
      simp [phi, hn] at hj
      omega
    rw [hq, after_boundary, rot, dif_pos hs] at hz
    have hv := congrArg Fin.val hz
    simp [zero] at hv
  · rintro ⟨i, rfl⟩; exact at_boundary hm i

private theorem nonzero_next {q : ℕ} (h : word hm q ≠ zero hm) :
    word hm (q + 1) = zero hm := by
  obtain ⟨i, hi, hj⟩ := boundary_window hm q
  have hne : q ≠ boundary hm i := by intro he; exact h (he ▸ at_boundary hm i)
  have hl := phi_len_le hm (word hm i)
  have hp := phi_pos hm (word hm i)
  have hs := boundary_succ hm i
  have he : q + 1 = boundary hm (i + 1) := by omega
  rw [he]; exact at_boundary hm _

private theorem boundary_add (i n : ℕ) :
    boundary hm (i + n) = boundary hm i + (subst (phi hm) (factor (word hm) i n)).length := by
  simp only [boundary, factor_add, zero_add, subst_append, List.length_append]

private theorem factor_subst (i n : ℕ) :
    factor (word hm) (boundary hm i) (subst (phi hm) (factor (word hm) i n)).length =
      subst (phi hm) (factor (word hm) i n) := by
  have h := substituted_prefix hm (i + n)
  rw [boundary_add, factor_add, substituted_prefix hm i] at h
  rw [factor_add, subst_append] at h
  simp only [zero_add] at h
  exact List.append_cancel_left h

/-- Actual occurrence at an unrestricted natural start. -/
def Occ (s : List (Fin m)) (q : ℕ) : Prop := factor (word hm) q s.length = s

/-- Substitution with the final zero reserved as a sentinel. -/
def T (s : List (Fin m)) : List (Fin m) := subst (phi hm) s ++ [zero hm]

/-- Every letter is an actual right extension. -/
def FRS (r : List (Fin m)) : Prop := ∀ a : Fin m, ∃ q : ℕ, Occ hm (r ++ [a]) q

private theorem occ_nil (q : ℕ) : Occ hm [] q := by simp [Occ, factor]

private theorem occ_append (s t : List (Fin m)) (q : ℕ) :
    Occ hm (s ++ t) q ↔ Occ hm s q ∧ Occ hm t (q + s.length) := by
  unfold Occ
  rw [List.length_append, factor_add]
  constructor
  · intro h
    have ht := congrArg (List.take s.length) h
    have hd := congrArg (List.drop s.length) h
    constructor
    · simpa [factor_len] using ht
    · simpa [factor_len] using hd
  · rintro ⟨h, h'⟩; rw [h, h']

private theorem occ_singleton (a : Fin m) (q : ℕ) : Occ hm [a] q ↔ word hm q = a := by
  simp [Occ, factor]

private theorem occ_cons (a : Fin m) (s : List (Fin m)) (q : ℕ) :
    Occ hm (a :: s) q ↔ word hm q = a ∧ Occ hm s (q + 1) := by
  simpa [occ_singleton] using occ_append hm [a] s q

private theorem occ_letter {s : List (Fin m)} {q j : ℕ} (h : Occ hm s q) (hj : j < s.length) :
    word hm (q + j) = s[j] := by
  have hh := congrArg (fun w : List (Fin m) => w[j]?) h
  simpa [List.getElem?_eq_getElem, factor_get, factor_len, hj] using hh

private theorem boundary_occ {s : List (Fin m)} {i : ℕ} (h : Occ hm s i) :
    boundary hm (i + s.length) = boundary hm i + (subst (phi hm) s).length := by
  rw [boundary_add, h]

private theorem transport {s : List (Fin m)} {i : ℕ} (h : Occ hm s i) :
    Occ hm (T hm s) (boundary hm i) := by
  apply (occ_append hm _ _ _).mpr
  constructor
  · have hf := factor_subst hm i s.length
    rw [h] at hf
    exact hf
  · apply (occ_singleton hm _ _).mpr
    rw [← boundary_occ hm h]
    exact at_boundary hm _

private theorem t_head (s : List (Fin m)) :
    ∃ v, T hm s = zero hm :: v := by
  cases s with
  | nil => exact ⟨[], rfl⟩
  | cons a s =>
    rw [T, RankOneMorphismIterationBound.subst_cons]
    unfold phi
    split <;> exact ⟨_, rfl⟩

private theorem t_cons (a : Fin m) (s : List (Fin m)) :
    T hm (a :: s) = phi hm a ++ T hm s := by simp [T, List.append_assoc]

private theorem t_after {a : Fin m} {s : List (Fin m)} {q : ℕ}
    (h : Occ hm (T hm (a :: s)) q) : word hm (q + 1) = rot hm a := by
  by_cases ha : a.val + 1 < m
  · have hlen : 1 < (T hm (a :: s)).length := by simp [t_cons, phi, ha]
    simpa [t_cons, phi, rot, ha] using occ_letter hm h hlen
  · rw [t_cons] at h
    have ht := (occ_append hm _ _ _).mp h
    obtain ⟨v, hv⟩ := t_head hm s
    rw [hv] at ht
    have hh := ((occ_cons hm _ _ _).mp ht.2).1
    simpa [phi, rot, ha] using hh

private theorem sentinel_boundary (s : List (Fin m)) (i : ℕ) :
    Occ hm (T hm s) (boundary hm i) ↔ Occ hm s i := by
  constructor
  · induction s generalizing i with
    | nil => intro _; exact occ_nil hm _
    | cons a s ih =>
      intro h
      have hr := (after_boundary hm i).symm.trans (t_after hm h)
      have ha : word hm i = a := rot_injective hm hr
      rw [t_cons] at h
      have ht := ((occ_append hm _ _ _).mp h).2
      rw [← ha, ← boundary_succ] at ht
      exact (occ_cons hm _ _ _).mpr ⟨ha, ih (i + 1) ht⟩
  · exact transport hm

/-- Zeros are exactly unique true substitution boundaries, including position zero. -/
theorem zero_iff_unique_boundary (q : ℕ) :
    word hm q = zero hm ↔ ∃! i, q = boundary hm i := by
  rw [zero_boundary]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi, fun j hj => (boundary_strict hm).injective (hj.symm.trans hi)⟩
  · rintro ⟨i, hi, _⟩; exact ⟨i, hi⟩

/-- Sentinel occurrences have one actual source occurrence at a true boundary. -/
theorem sentinel_occurrence_iff (s : List (Fin m)) (q : ℕ) :
    Occ hm (T hm s) q ↔ ∃ i, q = boundary hm i ∧ Occ hm s i := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := t_head hm s
    have hz : word hm q = zero hm := by
      rw [hv] at h; exact ((occ_cons hm _ _ _).mp h).1
    obtain ⟨i, hi, _⟩ := (zero_iff_unique_boundary hm q).mp hz
    exact ⟨i, hi, (sentinel_boundary hm s i).mp (hi ▸ h)⟩
  · rintro ⟨i, rfl, hi⟩; exact transport hm hi

/-- The same source occurrence controls every cyclically relabeled right extension. -/
theorem right_extension_occurrence_iff (s : List (Fin m)) (b : Fin m) (q : ℕ) :
    Occ hm (T hm s ++ [rot hm b]) q ↔
      ∃ i, q = boundary hm i ∧ Occ hm (s ++ [b]) i := by
  constructor
  · intro h
    obtain ⟨ht, hb⟩ := (occ_append hm _ _ _).mp h
    obtain ⟨i, hi, hs⟩ := (sentinel_occurrence_iff hm s q).mp ht
    have he : q + (T hm s).length = boundary hm (i + s.length) + 1 := by
      rw [hi, boundary_occ hm hs]
      simp [T]
      omega
    rw [he, occ_singleton, after_boundary] at hb
    have hletter : word hm (i + s.length) = b := rot_injective hm hb
    exact ⟨i, hi, (occ_append hm _ _ _).mpr ⟨hs, (occ_singleton hm _ _).mpr hletter⟩⟩
  · rintro ⟨i, rfl, h⟩
    obtain ⟨hs, hb⟩ := (occ_append hm _ _ _).mp h
    apply (occ_append hm _ _ _).mpr
    refine ⟨transport hm hs, ?_⟩
    apply (occ_singleton hm _ _).mpr
    have he : boundary hm i + (T hm s).length = boundary hm (i + s.length) + 1 := by
      rw [boundary_occ hm hs]
      simp [T]
      omega
    rw [he, after_boundary, (occ_singleton hm _ _).mp hb]

private theorem t_shorter (s : List (Fin m)) : s.length < (T hm s).length := by
  have := subst_length_ge hm s
  simp only [T, List.length_append, List.length_singleton]
  omega

private theorem t_second (a : Fin m) (s : List (Fin m)) :
    (T hm (a :: s))[1]? = some (rot hm a) := by
  by_cases h : a.val + 1 < m
  · simp [t_cons, phi, rot, h]
  · obtain ⟨v, hv⟩ := t_head hm s
    simp [t_cons, phi, rot, h, hv]

private theorem t_injective : Function.Injective (T hm) := by
  intro s
  induction s with
  | nil =>
    intro t ht
    cases t with
    | nil => rfl
    | cons b t =>
      have hlen := congrArg List.length ht
      have hshort := t_shorter hm (b :: t)
      change 1 = (T hm (b :: t)).length at hlen
      simp only [List.length_cons] at hshort
      omega
  | cons a s ih =>
    intro t ht
    cases t with
    | nil =>
      have hlen := congrArg List.length ht
      have hshort := t_shorter hm (a :: s)
      change (T hm (a :: s)).length = 1 at hlen
      simp only [List.length_cons] at hshort
      omega
    | cons b t =>
      have hs := congrArg (fun w : List (Fin m) => w[1]?) ht
      rw [t_second, t_second] at hs
      have hab := rot_injective hm (Option.some.inj hs)
      subst b
      rw [t_cons, t_cons] at ht
      exact congrArg (List.cons a) (ih (List.append_cancel_left ht))

private theorem occ_ends {r : List (Fin m)} {q : ℕ} (hr : r ≠ []) (h : Occ hm r q) :
    r.getLast? = some (word hm (q + r.length - 1)) := by
  have hl : 0 < r.length := List.length_pos_iff.mpr hr
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
    ← occ_letter hm h (by omega)]
  congr 2
  omega

/-- A zero-to-zero actual factor has a unique shorter source word. The final zero
is reserved; in particular the one-letter zero word has the empty preimage. -/
theorem common_unique_preimage (r : List (Fin m)) (hr : r ≠ [])
    (ho : ∃ q, Occ hm r q) (hh : r.head? = some (zero hm))
    (hl : r.getLast? = some (zero hm)) :
    ∃! s : List (Fin m), r = T hm s ∧ s.length < r.length := by
  obtain ⟨q, hq⟩ := ho
  obtain ⟨v, hv⟩ := List.head?_eq_some_iff.mp hh
  have hzero : word hm q = zero hm := by
    rw [hv] at hq; exact ((occ_cons hm _ _ _).mp hq).1
  obtain ⟨i, hi⟩ := (zero_boundary hm q).mp hzero
  have hend : word hm (q + r.length - 1) = zero hm :=
    Option.some.inj ((occ_ends hm hr hq).symm.trans hl)
  obtain ⟨j, hj⟩ := (zero_boundary hm _).mp hend
  have hlen : 0 < r.length := List.length_pos_iff.mpr hr
  have hij : i ≤ j := by
    by_contra h
    have := boundary_strict hm (show j < i by omega)
    omega
  let s := factor (word hm) i (j - i)
  have hs : Occ hm s i := by simp [Occ, s, factor_len]
  have hB := boundary_occ hm hs
  have hjs : i + s.length = j := by simp [s, factor_len]; omega
  rw [hjs] at hB
  have hlength : (T hm s).length = r.length := by
    simp only [T, List.length_append, List.length_singleton]
    omega
  have heq : r = T hm s := by
    have ht := transport hm hs
    unfold Occ at ht hq
    rw [hlength, ← hi, hq] at ht
    exact ht
  refine ⟨s, ⟨heq, hlength ▸ t_shorter hm s⟩, ?_⟩
  intro t ht
  exact t_injective hm (ht.1.symm.trans heq)

private theorem frs_last {r : List (Fin m)} (hr : r ≠ []) (hf : FRS hm r) :
    r.getLast? = some (zero hm) := by
  let a : Fin m := ⟨1, by omega⟩
  obtain ⟨q, hq⟩ := hf a
  obtain ⟨hprefix, hright⟩ := (occ_append hm _ _ _).mp hq
  have hlen : 0 < r.length := List.length_pos_iff.mpr hr
  have hend : word hm (q + r.length - 1) = zero hm := by
    by_contra hne
    have hn := nonzero_next hm hne
    have he : q + r.length - 1 + 1 = q + r.length := by omega
    rw [he, (occ_singleton hm _ _).mp hright] at hn
    have hv := congrArg Fin.val hn
    simp [a, zero] at hv
  rw [occ_ends hm hr hprefix, hend]

/-- Fully right-special descent on the actual word. End-zero is derived from
the literal adjacency law; the unique preimage works at every start and extension. -/
theorem fully_right_special_descent (r : List (Fin m)) (hr : r ≠ [])
    (hh : r.head? = some (zero hm)) (hf : FRS hm r) :
    ∃! s : List (Fin m), r = T hm s ∧ s.length < r.length ∧ FRS hm s ∧
      (∀ q, Occ hm r q ↔ ∃ i, q = boundary hm i ∧ Occ hm s i) ∧
      (∀ b q, Occ hm (r ++ [rot hm b]) q ↔
        ∃ i, q = boundary hm i ∧ Occ hm (s ++ [b]) i) := by
  have ho : ∃ q, Occ hm r q := by
    obtain ⟨q, hq⟩ := hf (zero hm)
    exact ⟨q, ((occ_append hm _ _ _).mp hq).1⟩
  obtain ⟨s, hs, huniq⟩ := common_unique_preimage hm r hr ho hh (frs_last hm hr hf)
  refine ⟨s, ⟨hs.1, hs.2, ?_, ?_, ?_⟩, ?_⟩
  · intro b
    obtain ⟨q, hq⟩ := hf (rot hm b)
    rw [hs.1] at hq
    obtain ⟨i, _, hi⟩ := (right_extension_occurrence_iff hm s b q).mp hq
    exact ⟨i, hi⟩
  · intro q; rw [hs.1]; exact sentinel_occurrence_iff hm s q
  · intro b q; rw [hs.1]; exact right_extension_occurrence_iff hm s b q
  · intro t ht; exact huniq t ⟨ht.1, ht.2.1⟩

/-- Closed construction and exact block arithmetic for every order at least two. -/
theorem actual_word_laws :
    (∀ k, factor (word hm) 0 (image (phi hm) k (zero hm)).length =
      image (phi hm) k (zero hm)) ∧
    StrictMono (boundary hm) ∧ boundary hm 0 = 0 ∧
    (∀ i, boundary hm i = ∑ h ∈ Finset.range i, (phi hm (word hm h)).length) ∧
    (∀ i, factor (word hm) (boundary hm i) (phi hm (word hm i)).length = phi hm (word hm i)) ∧
    (∀ q, word hm q ≠ zero hm → word hm (q + 1) = zero hm) ∧
    (∀ a, (rot hm a).val = (a.val + 1) % m) := by
  refine ⟨iterate_factor hm, boundary_strict hm, boundary_zero hm, ?_, block_factor hm,
    fun _ h => nonzero_next hm h, ?_⟩
  · intro i
    induction i with
    | zero => simp [boundary_zero]
    | succ i ih => rw [boundary_succ, ih, Finset.sum_range_succ]
  · intro a
    by_cases h : a.val + 1 < m
    · simp [rot, h, Nat.mod_eq_of_lt h]
    · have he : a.val + 1 = m := by have := a.isLt; omega
      simp [rot, zero, he]

/-- Every occurrence lifts to the whole image, the sentinel image and the image
tail at the next position. Empty source words remain in the first two clauses. -/
theorem occurrence_transport (s : List (Fin m)) (i : ℕ) (hi : Occ hm s i) :
    Occ hm (subst (phi hm) s) (boundary hm i) ∧
    Occ hm (T hm s) (boundary hm i) ∧
    (s ≠ [] → Occ hm (subst (phi hm) s).tail (boundary hm i + 1)) := by
  have hs : Occ hm (subst (phi hm) s) (boundary hm i) := by
    have h := factor_subst hm i s.length
    rw [hi] at h
    exact h
  refine ⟨hs, transport hm hi, ?_⟩
  intro hne
  have hlen : 0 < (subst (phi hm) s).length :=
    lt_of_lt_of_le (List.length_pos_iff.mpr hne) (subst_length_ge hm s)
  cases he : subst (phi hm) s with
  | nil => simp [he] at hlen
  | cons a t =>
    rw [he] at hs
    exact ((occ_cons hm _ _ _).mp hs).2

end D5.S1.Words.MBonacciSentinelDesubstitution
