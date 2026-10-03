/- GID: D5/S3/ArithSums/GreedyBrickLabelledHistory
   generality: G
   mirror-B: D5/B/S3/ArithSums/GreedyBrickLabelledHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real supported placements and labelled literal rectangle histories. -/

import D5.S3.ArithSums.GreedyBrickCapacityTotality
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Choose

namespace D5.S3.ArithSums.GreedyBrickLabelledHistory

open GreedyBrickCapacityTotality

/-- Right endpoint of a floor-based row; absent rows have empty slices. This
is a geometric occupancy convention, not a birth-time default. -/
def rowEnd : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, y => if y = ws.length then w else rowEnd ws y

/-- The real half-open occupied wall reconstructed from row widths. -/
def wall (ws : List ℕ) (t z : ℝ) : Prop :=
  ∃ y : ℕ, (y : ℝ) ≤ z ∧ z < (y : ℝ) + 1 ∧ 0 ≤ t ∧ t < (rowEnd ws y : ℝ)

/-- A rectangle of width n and unit height at a real position. -/
def rectangle (n : ℕ) (x y t z : ℝ) : Prop :=
  x ≤ t ∧ t < x + n ∧ y ≤ z ∧ z < y + 1

/-- Physical placements independent of any scan: in the first quadrant,
nonoverlapping, and on the floor or fully supported on a row's upper face.
No axis contact or left-frontier condition is imposed. -/
def legal (n : ℕ) (ws : List ℕ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧
  (∀ t z, rectangle n x y t z → ¬ wall ws t z) ∧
  (y = 0 ∨ ∃ k : ℕ, y = (k : ℝ) + 1 ∧
    ∀ t, x ≤ t → t < x + n → t < (rowEnd ws k : ℝ))

/-- The source order is proved against all physically legal real positions;
it is not part of the definition of legal placement. -/
def sourceOptimal (n : ℕ) (ws : List ℕ) (x y : ℝ) : Prop :=
  legal n ws x y ∧ ∀ x' y', legal n ws x' y' → x ≤ x' ∧ y' ≤ y

set_option maxHeartbeats 1200000 in
-- The slice and competitor reductions share the recursive geometry proof budget.
/-- The integer-cell scan extends to the real plane, including competitors
with arbitrary real horizontal endpoints and every supported row height. -/
theorem continuous_row_geometry (n : ℕ) (hn : 0 < n) (ws : List ℕ)
    (hp : ws.Pairwise (· ≤ ·)) :
    ∃ x y : ℕ, PlacementSite n ws x y ∧
      sourceOptimal n ws (x : ℝ) (y : ℝ) ∧
      ∀ t z, wall (sourceRowStep n ws) t z ↔
        wall ws t z ∨ rectangle n (x : ℝ) (y : ℝ) t z := by
  have absent : ∀ vs : List ℕ, ∀ y, vs.length ≤ y → rowEnd vs y = 0 := by
    intro vs
    induction vs with
    | nil => simp [rowEnd]
    | cons v vs ih =>
      intro y hy
      have hy' : vs.length ≤ y := by simp only [List.length_cons] at hy; omega
      have hne : y ≠ vs.length := by simp only [List.length_cons] at hy; omega
      simp [rowEnd, hne, ih y hy']
  have cells : ∀ vs : List ℕ, ∀ u y, occupied vs u y ↔ u < rowEnd vs y := by
    intro vs
    induction vs with
    | nil => simp [occupied, rowEnd]
    | cons v vs ih =>
      intro u y
      by_cases he : y = vs.length
      · subst y
        simp [occupied, rowEnd, ih, absent vs vs.length le_rfl]
      · simp [occupied, rowEnd, he, ih]
  have slice : ∀ vs : List ℕ, ∀ t z, wall vs t z ↔
      0 ≤ t ∧ 0 ≤ z ∧ occupied vs (Nat.floor t) (Nat.floor z) := by
    intro vs t z
    constructor
    · rintro ⟨y, hy, hz, ht, hw⟩
      have hz0 : 0 ≤ z := le_trans (Nat.cast_nonneg y) hy
      have hf : Nat.floor z = y := by
        apply le_antisymm
        · have := (Nat.floor_lt hz0).mpr (show z < ((y + 1 : ℕ) : ℝ) by exact_mod_cast hz)
          omega
        · exact (Nat.le_floor_iff hz0).mpr hy
      refine ⟨ht, hz0, ?_⟩
      rw [cells, hf]
      exact (Nat.floor_lt ht).mpr hw
    · rintro ⟨ht, hz, hc⟩
      refine ⟨Nat.floor z, Nat.floor_le hz, Nat.lt_floor_add_one z, ht, ?_⟩
      exact (Nat.floor_lt ht).mp ((cells vs _ _).mp hc)
  have rect_slice : ∀ (a b : ℕ) t z, rectangle n (a : ℝ) (b : ℝ) t z ↔
      0 ≤ t ∧ 0 ≤ z ∧ Nat.floor z = b ∧ a ≤ Nat.floor t ∧ Nat.floor t < a + n := by
    intro a b t z
    constructor
    · rintro ⟨hat, htn, hbz, hzb⟩
      have ht : 0 ≤ t := (Nat.cast_nonneg a).trans hat
      have hz : 0 ≤ z := (Nat.cast_nonneg b).trans hbz
      have hf : Nat.floor z = b := by
        have hl := (Nat.le_floor_iff hz).mpr hbz
        have hu := (Nat.floor_lt hz).mpr (show z < ((b + 1 : ℕ) : ℝ) by exact_mod_cast hzb)
        omega
      refine ⟨ht, hz, hf, (Nat.le_floor_iff ht).mpr hat, ?_⟩
      exact (Nat.floor_lt ht).mpr (by exact_mod_cast htn)
    · rintro ⟨ht, hz, hf, ha, hu⟩
      refine ⟨(Nat.le_floor_iff ht).mp ha, ?_, ?_, ?_⟩
      · exact_mod_cast (Nat.floor_lt ht).mp hu
      · simpa [hf] using Nat.floor_le hz
      · simpa [hf] using Nat.lt_floor_add_one z
  obtain ⟨x, y, hs, hm, hadd⟩ := source_row_geometry n hn ws hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have competitor : ∀ a b : ℝ, legal n ws a b →
      ∃ q : ℕ, b = (q : ℝ) ∧ LegalBrick n ws (rowEnd ws q) q ∧ (rowEnd ws q : ℝ) ≤ a := by
    intro a b hl
    rcases hl with ⟨ha, hb, hd, hsup⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, b = (q : ℝ) := by
      rcases hsup with hzero | ⟨k, hk, _⟩
      · exact ⟨0, by simpa using hzero⟩
      · exact ⟨k + 1, by simpa using hk⟩
    subst b
    have hright : (rowEnd ws q : ℝ) ≤ a := by
      by_contra h
      have hw : a < (rowEnd ws q : ℝ) := lt_of_not_ge h
      have hh : wall ws a (q : ℝ) := ⟨q, le_rfl, by linarith, ha, hw⟩
      exact hd a (q : ℝ) ⟨le_rfl, by linarith, le_rfl, by linarith⟩ hh
    have hsupport : q = 0 ∨ rowEnd ws q + n ≤ rowEnd ws (q - 1) := by
      rcases hsup with hzero | ⟨k, hk, hkall⟩
      · exact Or.inl (by exact_mod_cast hzero)
      · have hqk : q = k + 1 := by exact_mod_cast hk
        have hup : a + n ≤ (rowEnd ws k : ℝ) := by
          by_contra h
          have hlt : (rowEnd ws k : ℝ) < a + n := lt_of_not_ge h
          have ht : max a (rowEnd ws k : ℝ) < a + n := max_lt (by linarith) hlt
          have hbad := hkall (max a (rowEnd ws k : ℝ)) (le_max_left _ _) ht
          exact (not_lt_of_ge (le_max_right _ _) hbad)
        right
        have hcast : (rowEnd ws q : ℝ) + n ≤ (rowEnd ws k : ℝ) := by linarith
        have hnat : rowEnd ws q + n ≤ rowEnd ws k := by exact_mod_cast hcast
        simpa [hqk] using hnat
    refine ⟨q, rfl, ?_, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu _
      rw [cells]
      omega
    · rcases hsupport with hzero | hsupport
      · exact Or.inl hzero
      · exact Or.inr (fun u _ hu => (cells ws u (q - 1)).mpr (by omega))
    · by_cases hz : rowEnd ws q = 0
      · exact Or.inl hz
      · exact Or.inr ((cells ws _ _).mpr (by omega))
  have hlegal : legal n ws (x : ℝ) (y : ℝ) := by
    refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_, ?_⟩
    · intro t z hr hw
      rcases (rect_slice x y t z).mp hr with ⟨ht, hz, hf, hx, hxn⟩
      have hc := ((slice ws t z).mp hw).2.2
      rw [hf] at hc
      exact hadd.2.1 (Nat.floor t) hx hxn hc
    · rcases hadd.2.2.1 with hy | hsupport
      · exact Or.inl (by exact_mod_cast hy)
      · by_cases hy : y = 0
        · exact Or.inl (by exact_mod_cast hy)
        · refine Or.inr ⟨y - 1, ?_, ?_⟩
          · have he : y - 1 + 1 = y := by omega
            exact_mod_cast he.symm
          · intro t hxt htn
            have ht : 0 ≤ t := (Nat.cast_nonneg x).trans hxt
            have hx := (Nat.le_floor_iff ht).mpr hxt
            have htn' : Nat.floor t < x + n := (Nat.floor_lt ht).mpr (by exact_mod_cast htn)
            have hc := hsupport (Nat.floor t) hx htn'
            exact (Nat.floor_lt ht).mp ((cells ws _ _).mp hc)
  refine ⟨x, y, hs, ⟨hlegal, ?_⟩, ?_⟩
  · intro a b hl
    obtain ⟨q, rfl, hq, hright⟩ := competitor a b hl
    obtain ⟨hx, hy⟩ := hm (rowEnd ws q) q hq
    have hxR : (x : ℝ) ≤ (rowEnd ws q : ℝ) := by exact_mod_cast hx
    exact ⟨hxR.trans hright, by exact_mod_cast hy⟩
  · intro t z
    rw [slice, slice, rect_slice]
    have hc := hadd.1 (Nat.floor t) (Nat.floor z)
    tauto

#print axioms continuous_row_geometry

/-- The union of bricks with their actual positive width labels. -/
def labelledWall (pos : ℕ → ℕ × ℕ) (N : ℕ) (t z : ℝ) : Prop :=
  ∃ i : ℕ, 0 < i ∧ i ≤ N ∧
    rectangle i (pos i).1 (pos i).2 t z

/-- Physical source rule expressed solely in the previously placed labelled
rectangles, without a row algorithm or an optimality premise. -/
def historyLegal (pos : ℕ → ℕ × ℕ) (N n : ℕ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧
  (∀ t z, rectangle n x y t z → ¬ labelledWall pos N t z) ∧
  (y = 0 ∨ ∀ t, x ≤ t → t < x + n →
    ∃ i : ℕ, 0 < i ∧ i ≤ N ∧ ((pos i).2 : ℝ) + 1 = y ∧
      ((pos i).1 : ℝ) ≤ t ∧ t < (pos i).1 + i)

def historyOptimal (pos : ℕ → ℕ × ℕ) (N n : ℕ) (x y : ℝ) : Prop :=
  historyLegal pos N n x y ∧
  ∀ x' y', historyLegal pos N n x' y' → x ≤ x' ∧ y' ≤ y

/-- Full closed bottom support, including the new brick's right endpoint.
The supporting upper faces are closed horizontal intervals. -/
def closedSupport (pos : ℕ → ℕ × ℕ) (N n : ℕ) (x y : ℝ) : Prop :=
  y = 0 ∨ ∀ t, x ≤ t → t ≤ x + n →
    ∃ i : ℕ, 0 < i ∧ i ≤ N ∧ ((pos i).2 : ℝ) + 1 = y ∧
      ((pos i).1 : ℝ) ≤ t ∧ t ≤ (pos i).1 + i

set_option maxHeartbeats 1200000 in
-- One chosen trajectory, its finite unions, and physical support transport
-- are constructed in the same proof.
/-- A single labelled history realizes every finite prefix of the literal
capacity trajectory. Its half-open rectangles are pairwise disjoint, hence
have disjoint interiors; every new brick obeys the physical source rule
against all real competitors in that same preceding labelled history. -/
theorem actual_labelled_history :
    ∃ pos : ℕ → ℕ × ℕ,
      (∀ N t z, wall (widths (trajectory N)) t z ↔ labelledWall pos N t z) ∧
      (∀ n, 0 < n → historyOptimal pos (n - 1) n (pos n).1 (pos n).2) ∧
      (∀ n, 0 < n → closedSupport pos (n - 1) n (pos n).1 (pos n).2) ∧
      (∀ i j, 0 < i → i < j → ∀ t z,
        rectangle i (pos i).1 (pos i).2 t z →
        ¬ rectangle j (pos j).1 (pos j).2 t z) := by
  classical
  have ordered : ∀ N, (widths (trajectory N)).Pairwise (· ≤ ·) := by
    intro N
    by_cases hN : N = 0
    · subst N
      simp [trajectory, widths]
    · exact (reachable_rows N (by omega)).2.1
  have choices := fun N => continuous_row_geometry (N + 1) (by omega)
    (widths (trajectory N)) (ordered N)
  choose px py hsite hopt hunion using choices
  let pos : ℕ → ℕ × ℕ := fun n => (px (n - 1), py (n - 1))
  have update : ∀ N t z, wall (widths (trajectory (N + 1))) t z ↔
      wall (widths (trajectory N)) t z ∨
        rectangle (N + 1) (pos (N + 1)).1 (pos (N + 1)).2 t z := by
    intro N t z
    have he := row_transition_correspondence (N + 1) (trajectory N) (by omega)
    change wall (widths (step (N + 1) (trajectory N))) t z ↔ _
    rw [he]
    simpa [pos] using hunion N t z
  have union : ∀ N t z, wall (widths (trajectory N)) t z ↔ labelledWall pos N t z := by
    intro N
    induction N with
    | zero =>
      intro t z
      constructor
      · rintro ⟨y, _, _, ht, hw⟩
        simp [trajectory, widths, rowEnd] at hw
        linarith
      · rintro ⟨i, hi, hi0, _⟩
        omega
    | succ N ih =>
      intro t z
      rw [update, ih]
      constructor
      · rintro (⟨i, hi, hiN, hr⟩ | hr)
        · exact ⟨i, hi, by omega, hr⟩
        · exact ⟨N + 1, by omega, le_rfl, hr⟩
      · rintro ⟨i, hi, hiN, hr⟩
        by_cases he : i = N + 1
        · subst i
          exact Or.inr hr
        · exact Or.inl ⟨i, hi, by omega, hr⟩
  have transport : ∀ N n x y, 0 < n →
      (historyLegal pos N n x y ↔ legal n (widths (trajectory N)) x y) := by
    intro N n x y hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · rintro ⟨hx, hy, hd, hs⟩
      refine ⟨hx, hy, ?_, ?_⟩
      · intro t z hr hw
        exact hd t z hr ((union N t z).mp hw)
      · rcases hs with hy0 | hs
        · exact Or.inl hy0
        · obtain ⟨i, hi, hiN, hitop, _, _⟩ := hs x le_rfl (by linarith)
          let k := (pos i).2
          have hky : y = (k : ℝ) + 1 := hitop.symm
          refine Or.inr ⟨k, hky, ?_⟩
          intro t hxt htn
          obtain ⟨j, hj, hjN, hjtop, hjx, hjn⟩ := hs t hxt htn
          have hjk : (pos j).2 = k := by
            have he : ((pos j).2 : ℝ) = (k : ℝ) := by linarith
            exact_mod_cast he
          have hw : wall (widths (trajectory N)) t (k : ℝ) :=
            (union N t (k : ℝ)).mpr ⟨j, hj, hjN, hjx, hjn,
              by simp [hjk], by simp [hjk]⟩
          rcases hw with ⟨r, hrlo, hrhi, _, hright⟩
          have hkr : k = r := by
            have hlo : r ≤ k := by exact_mod_cast hrlo
            have hhi : k < r + 1 := by exact_mod_cast hrhi
            omega
          simpa [hkr] using hright
    · rintro ⟨hx, hy, hd, hs⟩
      refine ⟨hx, hy, ?_, ?_⟩
      · intro t z hr hw
        exact hd t z hr ((union N t z).mpr hw)
      · rcases hs with hy0 | ⟨k, hk, hs⟩
        · exact Or.inl hy0
        · right
          intro t hxt htn
          have ht : 0 ≤ t := hx.trans hxt
          have hw : wall (widths (trajectory N)) t (k : ℝ) :=
            ⟨k, le_rfl, by linarith, ht, hs t hxt htn⟩
          obtain ⟨i, hi, hiN, hix, hin, hilo, hihi⟩ := (union N t (k : ℝ)).mp hw
          have hik : (pos i).2 = k := by
            have hlo : (pos i).2 ≤ k := by exact_mod_cast hilo
            have hhi : k < (pos i).2 + 1 := by exact_mod_cast hihi
            omega
          exact ⟨i, hi, hiN, by simpa [hik] using hk.symm, hix, hin⟩
  have optimal : ∀ n, 0 < n → historyOptimal pos (n - 1) n (pos n).1 (pos n).2 := by
    intro n hn
    have he : n - 1 + 1 = n := by omega
    have ho := hopt (n - 1)
    rw [he] at ho
    change sourceOptimal n (widths (trajectory (n - 1))) (pos n).1 (pos n).2 at ho
    refine ⟨(transport (n - 1) n _ _ hn).mpr ho.1, ?_⟩
    intro x y hl
    exact ho.2 x y ((transport (n - 1) n x y hn).mp hl)
  have full_support : ∀ n, 0 < n →
      closedSupport pos (n - 1) n (pos n).1 (pos n).2 := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    rcases (optimal n hn).1.2.2.2 with hground | hs
    · exact Or.inl hground
    · right
      intro t hxt htn
      by_cases hstrict : t < (pos n).1 + n
      · obtain ⟨i, hi, hiN, hitop, hix, hin⟩ := hs t hxt hstrict
        exact ⟨i, hi, hiN, hitop, hix, hin.le⟩
      · have he : t = (pos n).1 + n := by linarith
        obtain ⟨i, hi, hiN, hitop, hix, hin⟩ :=
          hs ((pos n).1 + n - (1/2 : ℝ)) (by linarith) (by linarith)
        have hright : ((pos n).1 : ℝ) + n ≤ (pos i).1 + i := by
          by_contra h
          have hlt : ((pos i).1 : ℝ) + i < (pos n).1 + n := lt_of_not_ge h
          have hnat : (pos i).1 + i < (pos n).1 + n := by exact_mod_cast hlt
          have hgap : (pos i).1 + i + 1 ≤ (pos n).1 + n := by omega
          have hgapR : ((pos i).1 : ℝ) + i + 1 ≤ (pos n).1 + n := by exact_mod_cast hgap
          linarith
        exact ⟨i, hi, hiN, hitop, by linarith, by simpa [he] using hright⟩
  refine ⟨pos, union, optimal, full_support, ?_⟩
  intro i j hi hij t z hri hrj
  have hj : 0 < j := by omega
  have hlegal := (optimal j hj).1
  exact hlegal.2.2.1 t z hrj ⟨i, hi, by omega, hri⟩

#print axioms actual_labelled_history

end D5.S3.ArithSums.GreedyBrickLabelledHistory
