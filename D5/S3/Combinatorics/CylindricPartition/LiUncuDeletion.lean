/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuDeletion
   mirror-E: none(waiver:simultaneous-peak-deletion)
   anchors: []
   utility: none
   digest: Peak deletion and insertion give a reversible decomposition of path words. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuRectangle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

/-- The edge alphabet for paths with horizontal edges at the floor. -/
inductive Step where
  | up
  | down
  | flat

open Step

/-- Simultaneously remove disjoint up-down pairs, recording their insertion slots. -/
def peakData : List Step → List Step × ℕ × List ℕ
  | up :: down :: w =>
      let d := peakData w
      (d.1, d.2.1 + 1, d.2.2)
  | s :: w =>
      let d := peakData w
      (s :: d.1, 0, d.2.1 :: d.2.2)
  | [] => ([], 0, [])

/-- Insert up-down pairs at successive vertices of a skeleton word. -/
def insertPeaks : List Step → ℕ → List ℕ → List Step
  | [], t, _ => (List.replicate t [up, down]).flatten
  | s :: _, t, [] => (List.replicate t [up, down]).flatten ++ [s]
  | s :: q, t, t' :: ts =>
      (List.replicate t [up, down]).flatten ++ s :: insertPeaks q t' ts

/-- Every skeleton vertex has a slot, and an old peak must be interrupted. -/
def Insertible : List Step → ℕ → List ℕ → Prop
  | [], _, [] => True
  | s :: q, _, t :: ts =>
      (match s, q with | up, down :: _ => 0 < t | _, _ => True) ∧ Insertible q t ts
  | _, _, _ => False

/-- Sum the abscissae of up-down peaks; `offset` is the initial abscissa. -/
def peakWeight : ℕ → List Step → ℕ
  | offset, up :: down :: w => offset + 1 + peakWeight (offset + 2) w
  | offset, _ :: w => peakWeight (offset + 1) w
  | _, [] => 0

/-- Deletion is a bijection onto the skeletons with mandatory peak interruptions. -/
theorem peak_deletion_bijection :
    ∃ e : List Step ≃ {d : List Step × ℕ × List ℕ // Insertible d.1 d.2.1 d.2.2},
      (∀ w, (e w).val = peakData w) ∧
      (∀ d, e.symm d = insertPeaks d.val.1 d.val.2.1 d.val.2.2) ∧
      (∀ d, (e.symm d).length = d.val.1.length + 2 * (d.val.2.1 + d.val.2.2.sum)) ∧
      (∀ d, peakWeight 0 (e.symm d) = (d.val.2.1 + d.val.2.2.sum) ^ 2 +
        ((d.val.2.2.zipIdx 1).map (fun p => p.1 * p.2)).sum) := by
  have add_pair (q : List Step) (t : ℕ) (ts : List ℕ) :
      insertPeaks q (t + 1) ts = up :: down :: insertPeaks q t ts := by
    cases q <;> cases ts <;>
      simp [insertPeaks, List.replicate_succ, List.flatten_cons]
  have keep_edge (s : Step) (q : List Step) (t : ℕ) (ts : List ℕ) :
      insertPeaks (s :: q) 0 (t :: ts) = s :: insertPeaks q t ts := by
    simp [insertPeaks]
  have reconstruct (w : List Step) :
      insertPeaks (peakData w).1 (peakData w).2.1 (peakData w).2.2 = w := by
    fun_induction peakData w
    · rename_i w d ih
      change insertPeaks (peakData w).1 ((peakData w).2.1 + 1) (peakData w).2.2 =
        up :: down :: w
      rw [add_pair, ih]
    · rename_i s w notpeak d ih
      change insertPeaks (s :: (peakData w).1) 0
        ((peakData w).2.1 :: (peakData w).2.2) = s :: w
      rw [keep_edge, ih]
    · rfl
  have head_irrel (q : List Step) (t t' : ℕ) (ts : List ℕ) :
      Insertible q t ts = Insertible q t' ts := by
    cases q <;> cases ts <;> rfl
  have admissible (w : List Step) :
      Insertible (peakData w).1 (peakData w).2.1 (peakData w).2.2 := by
    fun_induction peakData w
    · rename_i w d ih
      dsimp only at *
      simpa only [peakData, head_irrel _ _ (peakData w).2.1] using ih
    · rename_i s w notpeak d ih
      dsimp only at *
      simp only [Insertible]
      refine ⟨?_, ih⟩
      cases s with
      | down => trivial
      | flat => trivial
      | up =>
          cases hq : (peakData w).1 with
          | nil => simp
          | cons r q =>
              cases r with
              | up => trivial
              | flat => trivial
              | down =>
                  change 0 < (peakData w).2.1
                  by_contra hz
                  have ht : (peakData w).2.1 = 0 := by omega
                  cases hc : (peakData w).2.2 with
                  | nil => simp [Insertible, hq, hc] at ih
                  | cons t ts =>
                      have hw := reconstruct w
                      rw [hq, ht, hc, keep_edge] at hw
                      exact notpeak _ rfl hw.symm
    · trivial
  have keep_up (w : List Step) (h : ∀ z, w ≠ down :: z) :
      peakData (up :: w) = (up :: (peakData w).1, 0,
        (peakData w).2.1 :: (peakData w).2.2) := by
    cases w with
    | nil => rfl
    | cons s w =>
        cases s with
        | up => rfl
        | flat => rfl
        | down => exact (h w rfl).elim
  have up_survives (q : List Step) (t : ℕ) (ts : List ℕ)
      (h : Insertible (up :: q) 0 (t :: ts)) :
      ∀ z, insertPeaks q t ts ≠ down :: z := by
    cases t with
    | succ t => rw [add_pair]; simp
    | zero =>
        cases q with
        | nil => simp [insertPeaks]
        | cons s q =>
            cases ts with
            | nil => simp [Insertible] at h
            | cons t ts =>
                rw [keep_edge]
                cases s with
                | up => simp
                | flat => simp
                | down => simp [Insertible] at h
  have scan (q : List Step) (t : ℕ) (ts : List ℕ) (h : Insertible q t ts) :
      peakData (insertPeaks q t ts) = (q, t, ts) := by
    induction q generalizing t ts with
    | nil =>
        cases ts with
        | cons t' ts => simp [Insertible] at h
        | nil =>
            induction t with
            | zero => rfl
            | succ t ih => rw [add_pair, peakData, ih (by trivial)]
    | cons s q ih =>
        cases ts with
        | nil => simp [Insertible] at h
        | cons t' ts =>
            have hrest : Insertible q t' ts := h.2
            induction t with
            | zero =>
                rw [keep_edge]
                cases s with
                | down =>
                    simpa only [peakData] using congrArg
                      (fun d : List Step × ℕ × List ℕ => (down :: d.1, 0, d.2.1 :: d.2.2))
                      (ih t' ts hrest)
                | flat =>
                    simpa only [peakData] using congrArg
                      (fun d : List Step × ℕ × List ℕ => (flat :: d.1, 0, d.2.1 :: d.2.2))
                      (ih t' ts hrest)
                | up => rw [keep_up _ (up_survives q t' ts h), ih t' ts hrest]
            | succ t iht =>
                rw [add_pair, peakData, iht]
                simpa only [head_irrel _ _ t] using h
  have insertion_length (q : List Step) (t : ℕ) (ts : List ℕ)
      (h : Insertible q t ts) :
      (insertPeaks q t ts).length = q.length + 2 * (t + ts.sum) := by
    induction q generalizing t ts with
    | nil =>
        cases ts with
        | nil => simp [insertPeaks, List.length_flatten, List.sum_replicate]; omega
        | cons t' ts => simp [Insertible] at h
    | cons s q ih =>
        cases ts with
        | nil => simp [Insertible] at h
        | cons t' ts =>
            simp only [insertPeaks, List.length_append, List.length_cons,
              List.length_flatten, List.map_replicate, List.sum_replicate,
              List.length_cons, List.length_nil, List.sum_cons]
            rw [ih t' ts h.2]
            ring
  have index_shift (ts : List ℕ) (r : ℕ) :
      ((ts.zipIdx (r + 1)).map (fun p => p.1 * p.2)).sum =
        ((ts.zipIdx r).map (fun p => p.1 * p.2)).sum + ts.sum := by
    induction ts generalizing r with
    | nil => rfl
    | cons t ts ih =>
        simp only [List.zipIdx_cons, List.map_cons, List.sum_cons]
        rw [ih (r + 1)]
        ring
  have keep_up_weight (w : List Step) (offset : ℕ) (h : ∀ z, w ≠ down :: z) :
      peakWeight offset (up :: w) = peakWeight (offset + 1) w := by
    cases w with
    | nil => rfl
    | cons s w =>
        cases s with
        | up => rfl
        | flat => rfl
        | down => exact (h w rfl).elim
  have insertion_weight (q : List Step) (t : ℕ) (ts : List ℕ)
      (h : Insertible q t ts) (offset : ℕ) :
      peakWeight offset (insertPeaks q t ts) =
        (t + ts.sum) ^ 2 + offset * (t + ts.sum) +
          ((ts.zipIdx 1).map (fun p => p.1 * p.2)).sum := by
    induction q generalizing t ts offset with
    | nil =>
        cases ts with
        | cons t' ts => simp [Insertible] at h
        | nil =>
            induction t generalizing offset with
            | zero => simp [insertPeaks, peakWeight]
            | succ t iht =>
                rw [add_pair, peakWeight, iht (offset + 2) (by trivial)]
                simp only [List.sum_nil, Nat.add_zero, List.zipIdx_nil]
                ring
    | cons s q ih =>
        cases ts with
        | nil => simp [Insertible] at h
        | cons t' ts =>
            have hrest : Insertible q t' ts := h.2
            induction t generalizing offset with
            | zero =>
                rw [keep_edge]
                have he : peakWeight offset (s :: insertPeaks q t' ts) =
                    peakWeight (offset + 1) (insertPeaks q t' ts) := by
                  cases s with
                  | down => rfl
                  | flat => rfl
                  | up => exact keep_up_weight _ _ (up_survives q t' ts h)
                rw [he, ih t' ts hrest (offset + 1)]
                simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, zero_add]
                rw [index_shift ts 1]
                ring
            | succ t iht =>
                have hp : Insertible (s :: q) t (t' :: ts) := by
                  simpa only [head_irrel _ _ t] using h
                rw [add_pair, peakWeight, iht (offset + 2) hp]
                ring
  refine ⟨{
      toFun := fun w => ⟨peakData w, admissible w⟩
      invFun := fun d => insertPeaks d.val.1 d.val.2.1 d.val.2.2
      left_inv := reconstruct
      right_inv := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro d
    exact Subtype.ext (scan d.val.1 d.val.2.1 d.val.2.2 d.property)
  · intro w
    rfl
  · intro d
    rfl
  · intro d
    exact insertion_length d.val.1 d.val.2.1 d.val.2.2 d.property
  · intro d
    simpa using insertion_weight d.val.1 d.val.2.1 d.val.2.2 d.property 0

/-- Bounded paths have unit up/down edges and horizontal edges only at height zero. -/
def ValidPath : ℕ → ℤ → ℤ → List Step → Prop
  | H, a, b, [] => 0 ≤ a ∧ a ≤ H ∧ a = b
  | H, a, b, up :: w => 0 ≤ a ∧ a < H ∧ ValidPath H (a + 1) b w
  | H, a, b, down :: w => 0 < a ∧ a ≤ H ∧ ValidPath H (a - 1) b w
  | H, a, b, flat :: w => a = 0 ∧ ValidPath H a b w

/-- Deleting all peaks lowers the ceiling when both endpoints lie below it. -/
theorem peak_deletion_interior (H : ℕ) (hH : 1 ≤ H) (a b : ℤ)
    (ha : a < H) (hb : b < H) (w : List Step) (hw : ValidPath H a b w) :
    ValidPath (H - 1) a b (peakData w).1 := by
  have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  have ceiling_exit (w : List Step) (a b : ℤ) (hw : ValidPath H a b w)
      (hb : b < H) (hnot : ∀ z, w ≠ down :: z) : a < H := by
    cases w with
    | nil => simp only [ValidPath] at hw; omega
    | cons s w =>
        cases s with
        | up => exact hw.2.1
        | down => exact (hnot w rfl).elim
        | flat => simp only [ValidPath] at hw; omega
  fun_induction peakData w generalizing a b
  · rename_i w d ih
    change ValidPath (H - 1) a b (peakData w).1
    exact ih a b ha hb (by simpa using hw.2.2.2.2)
  · rename_i s w notpeak d ih
    change ValidPath (H - 1) a b (s :: (peakData w).1)
    cases s with
    | up =>
        have hstart : a + 1 < H :=
          ceiling_exit w (a + 1) b hw.2.2 hb (fun z hz => notpeak z rfl hz)
        exact ⟨hw.1, by omega, ih (a + 1) b hstart hb hw.2.2⟩
    | down => exact ⟨hw.1, by omega, ih (a - 1) b (by omega) hb hw.2.2⟩
    | flat => exact ⟨hw.1, ih a b ha hb hw.2⟩
  · change ValidPath (H - 1) a b []
    exact ⟨hw.1, by omega, hw.2.2⟩

/-- A nonempty ceiling-to-ceiling path loses its two surviving boundary edges as well. -/
theorem peak_deletion_ceiling (H : ℕ) (hH : 1 ≤ H) (w : List Step)
    (hne : w ≠ []) (hw : ValidPath H H H w) :
    ∃ q t ts, peakData w = (down :: (q ++ [up]), 0, t :: (ts ++ [0])) ∧
      ValidPath (H - 1) ((H : ℤ) - 1) ((H : ℤ) - 1) q ∧ Insertible q t ts := by
  have last_up (a : ℤ) (w : List Step) (hne : w ≠ []) (hw : ValidPath H a H w) :
      ∃ z, w = z ++ [up] ∧ ValidPath H a ((H : ℤ) - 1) z := by
    induction w generalizing a with
    | nil => exact (hne rfl).elim
    | cons s w ih =>
        by_cases he : w = []
        · subst w
          cases s with
          | up =>
              refine ⟨[], rfl, ?_⟩
              simp only [ValidPath] at hw ⊢
              exact ⟨hw.1, by omega, by omega⟩
          | down => simp only [ValidPath] at hw; omega
          | flat => simp only [ValidPath] at hw; omega
        · cases s with
          | up =>
              obtain ⟨z, hz, hp⟩ := ih (a + 1) he hw.2.2
              exact ⟨up :: z, by simp [hz], hw.1, hw.2.1, hp⟩
          | down =>
              obtain ⟨z, hz, hp⟩ := ih (a - 1) he hw.2.2
              exact ⟨down :: z, by simp [hz], hw.1, hw.2.1, hp⟩
          | flat =>
              obtain ⟨z, hz, hp⟩ := ih a he hw.2
              exact ⟨flat :: z, by simp [hz], hw.1, hp⟩
  have append_up (z : List Step) :
      peakData (z ++ [up]) =
        ((peakData z).1 ++ [up], (peakData z).2.1, (peakData z).2.2 ++ [0]) := by
    induction hn : z.length using Nat.strong_induction_on generalizing z with
    | h n ih =>
        have smaller (v : List Step) (hv : v.length < z.length) :
            peakData (v ++ [up]) =
              ((peakData v).1 ++ [up], (peakData v).2.1, (peakData v).2.2 ++ [0]) :=
          ih v.length (by omega) v rfl
        cases z with
        | nil => rfl
        | cons s z =>
            cases s with
            | down =>
                simp only [List.cons_append, peakData]
                rw [smaller z (by simp)]
            | flat =>
                simp only [List.cons_append, peakData]
                rw [smaller z (by simp)]
            | up =>
                cases z with
                | nil => rfl
                | cons s z =>
                    cases s with
                    | down =>
                        simp only [List.cons_append, peakData]
                        rw [smaller z (by simp)]
                    | up =>
                        change (up :: (peakData ((up :: z) ++ [up])).1, 0,
                          (peakData ((up :: z) ++ [up])).2.1 ::
                            (peakData ((up :: z) ++ [up])).2.2) = _
                        rw [smaller (up :: z) (by simp)]
                        rfl
                    | flat =>
                        change (up :: (peakData ((flat :: z) ++ [up])).1, 0,
                          (peakData ((flat :: z) ++ [up])).2.1 ::
                            (peakData ((flat :: z) ++ [up])).2.2) = _
                        rw [smaller (flat :: z) (by simp)]
                        rfl
  cases w with
  | nil => exact (hne rfl).elim
  | cons s w =>
      cases s with
      | up => exact (lt_irrefl (H : ℤ) hw.2.1).elim
      | flat => have : (H : ℤ) = 0 := hw.1; omega
      | down =>
          have htail : w ≠ [] := by
            intro he
            subst w
            have ht : (H : ℤ) - 1 = H := hw.2.2.2.2
            omega
          obtain ⟨z, hz, hp⟩ := last_up ((H : ℤ) - 1) w htail hw.2.2
          obtain ⟨e, he, _⟩ := peak_deletion_bijection
          have hi := (e z).property
          rw [he z] at hi
          refine ⟨(peakData z).1, (peakData z).2.1, (peakData z).2.2, ?_, ?_, hi⟩
          · rw [hz]
            simp only [peakData]
            rw [append_up]
          · exact peak_deletion_interior H hH _ _ (by omega) (by omega) z hp

/-- Inserting peaks into a lower-ceiling skeleton produces a valid upper-ceiling path. -/
theorem peak_insertion_valid (H : ℕ) (hH : 1 ≤ H) (a b : ℤ) (q : List Step)
    (t : ℕ) (ts : List ℕ) (hc : Insertible q t ts) (hw : ValidPath (H - 1) a b q) :
    ValidPath H a b (insertPeaks q t ts) := by
  have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  have bounds (a : ℤ) (q : List Step) (hw : ValidPath (H - 1) a b q) :
      0 ≤ a ∧ a < H := by
    cases q with
    | nil => exact ⟨hw.1, by have := hw.2.1; omega⟩
    | cons s q =>
        cases s with
        | up => exact ⟨hw.1, by have := hw.2.1; omega⟩
        | down => have h₁ := hw.1; have h₂ := hw.2.1; constructor <;> omega
        | flat => have ha := hw.1; constructor <;> omega
  have add_pair (q : List Step) (t : ℕ) (ts : List ℕ) :
      insertPeaks q (t + 1) ts = up :: down :: insertPeaks q t ts := by
    cases q <;> cases ts <;> simp [insertPeaks, List.replicate_succ, List.flatten_cons]
  have keep_edge (s : Step) (q : List Step) (t : ℕ) (ts : List ℕ) :
      insertPeaks (s :: q) 0 (t :: ts) = s :: insertPeaks q t ts := by
    simp [insertPeaks]
  have extend_pair (a : ℤ) (w : List Step) (ha : 0 ≤ a ∧ a < H)
      (hw : ValidPath H a b w) : ValidPath H a b (up :: down :: w) :=
    ⟨ha.1, ha.2, by omega, by omega, by simpa using hw⟩
  induction q generalizing a t ts with
  | nil =>
      cases ts with
      | cons t' ts => simp [Insertible] at hc
      | nil =>
          have hb := bounds a [] hw
          induction t with
          | zero => exact ⟨hw.1, by omega, hw.2.2⟩
          | succ t iht =>
              rw [add_pair]
              exact extend_pair a _ hb (iht (by trivial))
  | cons s q ih =>
      cases ts with
      | nil => simp [Insertible] at hc
      | cons t' ts =>
          have hb := bounds a (s :: q) hw
          induction t with
          | zero =>
              rw [keep_edge]
              cases s with
              | up =>
                  exact ⟨hw.1, by have := hw.2.1; omega, ih (a + 1) t' ts hc.2 hw.2.2⟩
              | down =>
                  exact ⟨hw.1, by have := hw.2.1; omega, ih (a - 1) t' ts hc.2 hw.2.2⟩
              | flat => exact ⟨hw.1, ih a t' ts hc.2 hw.2⟩
          | succ t iht =>
              rw [add_pair]
              exact extend_pair a _ hb (iht hc)

end D5.S3.Combinatorics.CylindricPartition.LiUncu
