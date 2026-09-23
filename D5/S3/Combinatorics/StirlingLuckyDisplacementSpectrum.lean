/- GID: D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/StirlingLuckyDisplacementSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Count, mathlib/module/Mathlib.Data.List.Nodup]
   utility: none
   digest: Every displaced-car count between n and 2n-1 is attained by a Stirling permutation of order n. -/

import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.StirlingLuckyDisplacementSpectrum

/-
proof_shape: result: content
escape_witness: the interval occupancy invariant carried by `park_ascending_step` and
  `park_descending`; neither the invariant nor the displaced-car count it yields is an
  instantiation, projection or normalisation of a pinned upstream statement.
admission_basis: open-problem-resolution (issue #9275)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-! ### The parking process -/

/-- Walk upwards from `s`, skipping spots in `occ`, for at most `f` steps. -/
def freeFrom : ℕ → List ℕ → ℕ → ℕ
  | 0, _, s => s
  | (f + 1), occ, s => if s ∈ occ then freeFrom f occ (s + 1) else s

/-- An upper bound for the entries of `occ` that is also at least `p`. -/
def occBound (occ : List ℕ) (p : ℕ) : ℕ := occ.foldr max p

/-- The spot taken by a car with preference `p` when the spots in `occ` are already
occupied: the least free spot at or after `p`. The fuel `occBound occ p + 1` always
exceeds the distance from `p` to that spot. -/
def firstFree (occ : List ℕ) (p : ℕ) : ℕ := freeFrom (occBound occ p + 1) occ p

/-- The spots taken by the cars with preferences `w`, in order. -/
def parkAux : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | (p :: ps), occ => firstFree occ p :: parkAux ps (firstFree occ p :: occ)

/-- The spot taken by each car of `w`, starting from an empty lot. -/
def spots (w : List ℕ) : List ℕ := parkAux w []

/-- The displacement vector of `w`: the spot taken minus the spot preferred, car by car. -/
def dis (w : List ℕ) : List ℕ := List.zipWith (fun s p => s - p) (spots w) w

/-- The number of nonzero entries of `dis w`, that is, the number of unlucky cars. -/
def displaced (w : List ℕ) : ℕ := (dis w).countP (fun d => d != 0)

/-! ### Stirling permutations -/

/-- `w` is a Stirling permutation of order `n`: a word of length `2 * n` in which each of
`1, …, n` occurs exactly twice and nothing else occurs, and which has no subsequence
`v, u, v` with `u ≤ v`. -/
def IsStirling (n : ℕ) (w : List ℕ) : Prop :=
  w.length = 2 * n ∧
  (∀ v : ℕ, w.count v = if 1 ≤ v ∧ v ≤ n then 2 else 0) ∧
  ∀ v u : ℕ, u ≤ v → ¬ List.Sublist [v, u, v] w

/-! ### Proof-side machinery -/

/-- The spots occupied after the cars with preferences `w` have parked. -/
private def parkOcc : List ℕ → List ℕ → List ℕ
  | [], occ => occ
  | (p :: ps), occ => parkOcc ps (firstFree occ p :: occ)

/-- The number of displaced cars, computed alongside the parking process. -/
private def displacedAux : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | (p :: ps), occ =>
      (if firstFree occ p = p then 0 else 1) + displacedAux ps (firstFree occ p :: occ)

/-- Each entry of `l`, repeated twice in place. -/
private def double : List ℕ → List ℕ
  | [] => []
  | (x :: l) => x :: x :: double l

/-- `descend r = [r, r - 1, …, 1]`. -/
private def descend : ℕ → List ℕ
  | 0 => []
  | (r + 1) => (r + 1) :: descend r

/-- The witness word of order `n` with `j` descending pairs. -/
private def witness (n j : ℕ) : List ℕ :=
  double (List.range' (j + 1) (n - j) ++ descend j)

/-- The occupied spots are exactly the integers from `a` to `b`. -/
private def IsBlock (occ : List ℕ) (a b : ℕ) : Prop := ∀ s, s ∈ occ ↔ (a ≤ s ∧ s ≤ b)

/-! ### Elementary facts about the ingredients -/

private lemma range'_cons (s m : ℕ) : List.range' s (m + 1) = s :: List.range' (s + 1) m := rfl

private lemma length_range (s : ℕ) : ∀ m, (List.range' s m).length = m := by
  intro m
  induction m generalizing s with
  | zero => rfl
  | succ m ih => rw [range'_cons, List.length_cons, ih]

private lemma mem_range (v : ℕ) : ∀ (m s : ℕ),
    v ∈ List.range' s m ↔ (s ≤ v ∧ v < s + m) := by
  intro m
  induction m with
  | zero =>
      intro s
      rw [show List.range' s 0 = ([] : List ℕ) from rfl]
      simp only [List.not_mem_nil, false_iff]
      omega
  | succ m ih =>
      intro s
      rw [range'_cons]
      simp only [List.mem_cons, ih]
      omega

private lemma mem_descend (v : ℕ) : ∀ r, v ∈ descend r ↔ (1 ≤ v ∧ v ≤ r) := by
  intro r
  induction r with
  | zero =>
      rw [show descend 0 = ([] : List ℕ) from rfl]
      simp only [List.not_mem_nil, false_iff]
      omega
  | succ r ih =>
      rw [descend]
      simp only [List.mem_cons, ih]
      omega

private lemma nodup_range : ∀ (m s : ℕ), (List.range' s m).Nodup := by
  intro m
  induction m with
  | zero => intro s; rw [show List.range' s 0 = ([] : List ℕ) from rfl]; exact List.nodup_nil
  | succ m ih =>
      intro s
      rw [range'_cons, List.nodup_cons]
      refine ⟨?_, ih (s + 1)⟩
      rw [mem_range]
      omega

private lemma nodup_descend : ∀ r, (descend r).Nodup := by
  intro r
  induction r with
  | zero => rw [show descend 0 = ([] : List ℕ) from rfl]; exact List.nodup_nil
  | succ r ih =>
      rw [descend, List.nodup_cons]
      refine ⟨?_, ih⟩
      rw [mem_descend]
      omega

private lemma length_descend : ∀ r, (descend r).length = r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => rw [descend, List.length_cons, ih]

private lemma length_double : ∀ l : List ℕ, (double l).length = 2 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih => rw [double, List.length_cons, List.length_cons, List.length_cons, ih]; omega

private lemma count_double (v : ℕ) : ∀ l : List ℕ, (double l).count v = 2 * l.count v := by
  intro l
  induction l with
  | nil => rw [show double ([] : List ℕ) = ([] : List ℕ) from rfl, List.count_nil]
  | cons x l ih =>
      rw [double]
      simp only [List.count_cons, ih]
      split_ifs <;> omega

private lemma mem_double {x : ℕ} : ∀ {l : List ℕ}, x ∈ double l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [double]
  | cons y l ih => simp [double, ih]

private lemma double_append : ∀ (l₁ l₂ : List ℕ),
    double (l₁ ++ l₂) = double l₁ ++ double l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons x l ih => intro l₂; rw [List.cons_append, double, double, ih, List.cons_append,
      List.cons_append]

/-! ### The occupancy invariant -/

private lemma le_occBound {occ : List ℕ} {x p : ℕ} (hx : x ∈ occ) : x ≤ occBound occ p := by
  induction occ with
  | nil => cases hx
  | cons a l ih =>
      rw [occBound, List.foldr_cons]
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

private lemma freeFrom_not_mem {f : ℕ} {occ : List ℕ} {s : ℕ} (h : s ∉ occ) :
    freeFrom f occ s = s := by
  cases f with
  | zero => rfl
  | succ f => rw [freeFrom, if_neg h]

private lemma firstFree_not_mem {occ : List ℕ} {p : ℕ} (h : p ∉ occ) : firstFree occ p = p :=
  freeFrom_not_mem h

private lemma le_freeFrom : ∀ (f : ℕ) (occ : List ℕ) (s : ℕ), s ≤ freeFrom f occ s := by
  intro f
  induction f with
  | zero => intro occ s; exact le_rfl
  | succ f ih =>
      intro occ s
      by_cases h : s ∈ occ
      · rw [freeFrom, if_pos h]
        exact le_trans (Nat.le_succ s) (ih occ (s + 1))
      · rw [freeFrom, if_neg h]

private lemma le_firstFree (occ : List ℕ) (p : ℕ) : p ≤ firstFree occ p := le_freeFrom _ _ _

private lemma freeFrom_block {occ : List ℕ} {a b : ℕ} (hb : IsBlock occ a b) :
    ∀ (f p : ℕ), a ≤ p → p ≤ b + 1 → b + 1 - p ≤ f → freeFrom f occ p = b + 1 := by
  intro f
  induction f with
  | zero =>
      intro p _ hpb hf
      have hp : p = b + 1 := by omega
      subst hp
      rfl
  | succ f ih =>
      intro p hap hpb hf
      by_cases h : p ≤ b
      · have hmem : p ∈ occ := (hb p).2 ⟨hap, h⟩
        rw [freeFrom, if_pos hmem]
        exact ih (p + 1) (by omega) (by omega) (by omega)
      · have hp : p = b + 1 := by omega
        subst hp
        have hnm : b + 1 ∉ occ := fun hmem => by have := (hb (b + 1)).1 hmem; omega
        rw [freeFrom, if_neg hnm]

private lemma firstFree_block {occ : List ℕ} {a b p : ℕ} (hb : IsBlock occ a b)
    (hab : a ≤ b) (h1 : a ≤ p) (h2 : p ≤ b + 1) : firstFree occ p = b + 1 := by
  have hbm : b ∈ occ := (hb b).2 ⟨hab, le_rfl⟩
  have hbd : b ≤ occBound occ p := le_occBound hbm
  exact freeFrom_block hb _ p h1 h2 (by omega)

/-! ### Counting the displaced cars -/

private lemma displaced_eq_aux : ∀ (w occ : List ℕ),
    (List.zipWith (fun s p => s - p) (parkAux w occ) w).countP (fun d => d != 0)
      = displacedAux w occ := by
  intro w
  induction w with
  | nil => intro occ; simp [parkAux, displacedAux]
  | cons p ps ih =>
      intro occ
      have hle : p ≤ firstFree occ p := le_firstFree occ p
      rw [parkAux, List.zipWith_cons_cons, List.countP_cons, ih, displacedAux]
      by_cases h : firstFree occ p = p
      · simp [h]
      · have hne : firstFree occ p - p ≠ 0 := by omega
        simp [h, hne]
        omega

private lemma displacedAux_append : ∀ (l₁ l₂ occ : List ℕ),
    displacedAux (l₁ ++ l₂) occ = displacedAux l₁ occ + displacedAux l₂ (parkOcc l₁ occ) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ occ; rw [List.nil_append, displacedAux, parkOcc, Nat.zero_add]
  | cons p ps ih =>
      intro l₂ occ
      rw [List.cons_append, displacedAux, displacedAux, ih, parkOcc, Nat.add_assoc]

/-! ### The ascending block -/

private lemma park_ascending_step (j : ℕ) : ∀ (m t : ℕ) (occ : List ℕ), 1 ≤ t →
    IsBlock occ (j + 1) (j + 2 * t) →
    IsBlock (parkOcc (double (List.range' (j + 1 + t) m)) occ) (j + 1) (j + 2 * (t + m))
      ∧ displacedAux (double (List.range' (j + 1 + t) m)) occ = 2 * m := by
  intro m
  induction m with
  | zero => intro t occ _ hb; exact ⟨hb, rfl⟩
  | succ m ih =>
      intro t occ ht hb
      have hrw : List.range' (j + 1 + t) (m + 1)
          = (j + 1 + t) :: List.range' (j + 1 + (t + 1)) m := by
        rw [show j + 1 + (t + 1) = j + 1 + t + 1 from by omega]
        rfl
      have hab : j + 1 ≤ j + 2 * t := by omega
      have hv1 : j + 1 ≤ j + 1 + t := by omega
      have hf1 : firstFree occ (j + 1 + t) = j + 2 * t + 1 :=
        firstFree_block hb hab hv1 (by omega)
      have hb1 : IsBlock ((j + 2 * t + 1) :: occ) (j + 1) (j + 2 * t + 1) := by
        intro s; simp only [List.mem_cons, hb s]; omega
      have hf2 : firstFree ((j + 2 * t + 1) :: occ) (j + 1 + t) = j + 2 * t + 2 := by
        have h := firstFree_block hb1 (by omega) hv1 (by omega)
        omega
      have hb2 : IsBlock ((j + 2 * t + 2) :: (j + 2 * t + 1) :: occ) (j + 1)
          (j + 2 * (t + 1)) := by
        intro s; simp only [List.mem_cons, hb s]; omega
      obtain ⟨hB, hD⟩ := ih (t + 1) ((j + 2 * t + 2) :: (j + 2 * t + 1) :: occ) (by omega) hb2
      refine ⟨?_, ?_⟩
      · rw [hrw, double, parkOcc, parkOcc, hf1, hf2]
        rw [show j + 2 * (t + 1 + m) = j + 2 * (t + (m + 1)) from by omega] at hB
        exact hB
      · rw [hrw, double, displacedAux, displacedAux, hf1, hf2, hD,
          if_neg (by omega : ¬ (j + 2 * t + 1 = j + 1 + t)),
          if_neg (by omega : ¬ (j + 2 * t + 2 = j + 1 + t))]
        omega

private lemma park_ascending (n j : ℕ) (h : j < n) :
    IsBlock (parkOcc (double (List.range' (j + 1) (n - j))) []) (j + 1) (2 * n - j)
      ∧ displacedAux (double (List.range' (j + 1) (n - j))) [] = 2 * (n - j) - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  rw [hm]
  have hf1 : firstFree ([] : List ℕ) (j + 1) = j + 1 := firstFree_not_mem (by simp)
  have hb1 : IsBlock [j + 1] (j + 1) (j + 1) := by
    intro s; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have hf2 : firstFree [j + 1] (j + 1) = j + 2 := by
    have h2 := firstFree_block hb1 le_rfl le_rfl (by omega)
    omega
  have hb2 : IsBlock [j + 2, j + 1] (j + 1) (j + 2 * 1) := by
    intro s; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  obtain ⟨hB, hD⟩ := park_ascending_step j m 1 [j + 2, j + 1] le_rfl hb2
  refine ⟨?_, ?_⟩
  · rw [range'_cons, double, parkOcc, parkOcc, hf1, hf2]
    rw [show j + 2 * (1 + m) = 2 * n - j from by omega] at hB
    exact hB
  · rw [range'_cons, double, displacedAux, displacedAux, hf1, hf2, hD,
      if_pos (rfl : j + 1 = j + 1), if_neg (by omega : ¬ (j + 2 = j + 1))]
    omega

/-! ### The descending block -/

private lemma park_descending : ∀ (r b : ℕ) (occ : List ℕ), r + 1 ≤ b →
    IsBlock occ (r + 1) b →
    IsBlock (parkOcc (double (descend r)) occ) 1 (b + r)
      ∧ displacedAux (double (descend r)) occ = r := by
  intro r
  induction r with
  | zero =>
      intro b occ _ hb
      refine ⟨?_, rfl⟩
      simpa [descend, double, parkOcc] using hb
  | succ r ih =>
      intro b occ hrb hb
      have hnm : (r + 1) ∉ occ := fun hmem => by have := (hb (r + 1)).1 hmem; omega
      have hf1 : firstFree occ (r + 1) = r + 1 := firstFree_not_mem hnm
      have hb1 : IsBlock ((r + 1) :: occ) (r + 1) b := by
        intro s; simp only [List.mem_cons, hb s]; omega
      have hf2 : firstFree ((r + 1) :: occ) (r + 1) = b + 1 :=
        firstFree_block hb1 (by omega) le_rfl (by omega)
      have hb2 : IsBlock ((b + 1) :: (r + 1) :: occ) (r + 1) (b + 1) := by
        intro s; simp only [List.mem_cons, hb s]; omega
      obtain ⟨hB, hD⟩ := ih (b + 1) ((b + 1) :: (r + 1) :: occ) (by omega) hb2
      refine ⟨?_, ?_⟩
      · rw [descend, double, parkOcc, parkOcc, hf1, hf2]
        rw [show b + 1 + r = b + (r + 1) from by omega] at hB
        exact hB
      · rw [descend, double, displacedAux, displacedAux, hf1, hf2, hD,
          if_pos (rfl : r + 1 = r + 1), if_neg (by omega : ¬ (b + 1 = r + 1))]
        omega

/-! ### The witness is a Stirling permutation with the prescribed displacement -/

private lemma nodup_ingredients (n j : ℕ) :
    (List.range' (j + 1) (n - j) ++ descend j).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_range _ _, nodup_descend j, ?_⟩
  intro a ha b hb
  rw [mem_range] at ha
  rw [mem_descend] at hb
  omega

private lemma count_ingredients (n j v : ℕ) (h : j ≤ n) :
    (List.range' (j + 1) (n - j) ++ descend j).count v
      = if 1 ≤ v ∧ v ≤ n then 1 else 0 := by
  by_cases hv : 1 ≤ v ∧ v ≤ n
  · rw [if_pos hv]
    refine List.count_eq_one_of_mem (nodup_ingredients n j) ?_
    rw [List.mem_append, mem_range, mem_descend]
    omega
  · rw [if_neg hv]
    refine List.count_eq_zero_of_not_mem ?_
    rw [List.mem_append, mem_range, mem_descend]
    omega

private lemma count_witness (n j v : ℕ) (h : j ≤ n) :
    (witness n j).count v = if 1 ≤ v ∧ v ≤ n then 2 else 0 := by
  have h1 : (witness n j).count v
      = 2 * ((List.range' (j + 1) (n - j) ++ descend j).count v) := count_double v _
  rw [h1, count_ingredients n j v h]
  by_cases hv : 1 ≤ v ∧ v ≤ n
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv]

private lemma length_witness (n j : ℕ) (h : j ≤ n) : (witness n j).length = 2 * n := by
  have h1 : (witness n j).length
      = 2 * (List.range' (j + 1) (n - j) ++ descend j).length := length_double _
  rw [h1, List.length_append, length_range, length_descend]
  omega

private lemma no_pattern_double : ∀ (l : List ℕ), l.Nodup → ∀ v u : ℕ,
    ¬ List.Sublist [v, u, v] (double l) := by
  intro l
  induction l with
  | nil => intro _ v u hs; simp [double] at hs
  | cons x l ih =>
      intro hnd v u hs
      have hxl : x ∉ l := (List.nodup_cons.1 hnd).1
      have hl : l.Nodup := (List.nodup_cons.1 hnd).2
      have key : ∀ w : List ℕ, x ∈ w → List.Sublist w (double l) → False := by
        intro w hvw hw
        exact hxl (mem_double.1 (hw.subset hvw))
      rw [double] at hs
      cases hs with
      | cons _ hs1 =>
          cases hs1 with
          | cons _ hs2 => exact ih hl v u hs2
          | cons_cons _ hs2 => exact key _ (by simp) hs2
      | cons_cons _ hs1 =>
          cases hs1 with
          | cons _ hs2 => exact key _ (by simp) hs2
          | cons_cons _ hs2 => exact key _ (by simp) hs2

private lemma isStirling_witness (n j : ℕ) (h : j ≤ n) : IsStirling n (witness n j) := by
  refine ⟨length_witness n j h, fun v => count_witness n j v h, ?_⟩
  intro v u _
  exact no_pattern_double _ (nodup_ingredients n j) v u

private lemma displaced_witness (n j : ℕ) (h : j < n) :
    displaced (witness n j) = 2 * n - j - 1 := by
  have hw : witness n j
      = double (List.range' (j + 1) (n - j)) ++ double (descend j) := double_append _ _
  rw [displaced, dis, spots, displaced_eq_aux, hw, displacedAux_append]
  obtain ⟨hB, hD⟩ := park_ascending n j h
  obtain ⟨_, hD2⟩ := park_descending j (2 * n - j) _ (by omega) hB
  rw [hD, hD2]
  omega

/-! ### Problem 48 -/

/-- Problem 48 of Colmenarejo, Dawkins, Elder and Harris: for every order `n ≥ 1` and every
`i` between `n` and `2 * n - 1` there is a Stirling permutation of order `n` whose
displacement vector has exactly `i` nonzero entries, equivalently with exactly `i`
unlucky cars. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, n ≤ i → i ≤ 2 * n - 1 →
    ∃ w : List ℕ, IsStirling n w ∧ displaced w = i

theorem result : claim := by
  intro n hn i hi1 hi2
  refine ⟨witness n (2 * n - 1 - i), isStirling_witness n _ (by omega), ?_⟩
  rw [displaced_witness n _ (by omega)]
  omega

end D5.S3.Combinatorics.StirlingLuckyDisplacementSpectrum
