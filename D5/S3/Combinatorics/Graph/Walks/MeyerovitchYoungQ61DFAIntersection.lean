/- GID: D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact free-endpoint word score of the complete DFA intersection encoding. -/
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete

/-!
For the DFA intersection encoding of Meyerovitch–Young Question 6.1, take the
disjoint union of the DFA state spaces, the union of their accepting states,
and the set of their initial states as the reset set. Alice has one vertex
with one loop per ordinary symbol and one delimiter loop. Bob has one edge
per ordered pair of states.

The integer cost of a prefix and its set of minimizing endpoints suffice to
compute the next cost. A delimiter closes a segment and restores the entire
reset set as the minimizing endpoints.
-/

namespace MeyerovitchYoungQ61DFAIntersection

open Maths
open MeyerovitchYoungQ61Complete
  (completeGraph matrixCost matrixMinimum matrixMinimum_spec wordCost wordCost_append)

variable {Q Letter : Type*} [DecidableEq Q]

/-- An ordinary letter follows `δ` for free. A delimiter resets to `S` and
charges one for an accepting departure. Every other move costs two. -/
def costs (δ : Q → Letter → Q) (S F : Finset Q) : Option Letter → Matrix Q Q ℤ
  | some a => fun i j => if δ i a = j then 0 else 2
  | none => fun i j => if j ∈ S then (if i ∈ F then 1 else 0) else 2

private def charge (F T : Finset Q) : ℕ := @ite ℕ (T ⊆ F) (Finset.instDecidableRelSubset T F) 1 0

private def scanStep (δ : Q → Letter → Q) (S F : Finset Q)
    (current : ℕ × Finset Q) : Option Letter → ℕ × Finset Q
  | some a => (current.1, current.2.image fun i => δ i a)
  | none => (current.1 + charge F current.2, S)

variable [Fintype Q]

/-- The constructive count of charged completed segments and the current
state set. The initial segment starts from all of `Q`. Each later segment
starts from `S`. An unfinished segment contributes no charge. -/
def scan (δ : Q → Letter → Q) (S F : Finset Q) (w : List (Option Letter)) : ℕ × Finset Q :=
  w.foldl (scanStep δ S F) (0, Finset.univ)

private theorem scan_append (δ : Q → Letter → Q) (S F : Finset Q)
    (w : List (Option Letter)) (a : Option Letter) :
    scan δ S F (w ++ [a]) = scanStep δ S F (scan δ S F w) a := by
  simp [scan, List.foldl_append]

/-- Update a vector of optimal endpoint scores by minimizing over the
departure state of the next edge. -/
private def update (A : Option Letter → Matrix Q Q ℤ) (a : Option Letter)
    (q : Q → ℤ) (j : Q) : ℤ :=
  ((Finset.univ : Finset Q).image fun i => q i + A a i j).min'
    ((show (Finset.univ : Finset Q).Nonempty from ⟨j, Finset.mem_univ j⟩).image _)

/-- The minimum prefix cost at each Bob endpoint, with free initial state. -/
def endpointScores (δ : Q → Letter → Q) (S F : Finset Q)
    (w : List (Option Letter)) : Q → ℤ :=
  w.foldl (fun q a => update (costs δ S F) a q) (fun _ => 0)

private theorem endpointScores_append (δ : Q → Letter → Q) (S F : Finset Q)
    (w : List (Option Letter)) (a : Option Letter) :
    endpointScores δ S F (w ++ [a]) =
      update (costs δ S F) a (endpointScores δ S F w) := by
  simp [endpointScores, List.foldl_append]

omit [DecidableEq Q] in
private theorem update_le (A : Option Letter → Matrix Q Q ℤ) (a : Option Letter)
    (q : Q → ℤ) (i j : Q) : update A a q j ≤ q i + A a i j :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

omit [DecidableEq Q] in
private theorem update_attains (A : Option Letter → Matrix Q Q ℤ) (a : Option Letter)
    (q : Q → ℤ) (j : Q) : ∃ i, q i + A a i j = update A a q j := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem _ _ :
    update A a q j ∈ (Finset.univ : Finset Q).image fun i => q i + A a i j)
  exact ⟨i, hi⟩

omit [DecidableEq Q] [Fintype Q] in
private theorem wordCost_concat (A : Option Letter → Matrix Q Q ℤ) (w : List (Option Letter))
    (a : Option Letter) {s i j : Q} (p : (completeGraph Q).Walk s i)
    (hlen : p.length = w.length) :
    wordCost (matrixCost A) (w ++ [a]) (p.concat (i, j) rfl).edges =
      wordCost (matrixCost A) w p.edges + A a i j := by
  erw [EdgeGraph.Walk.edges_concat]
  rw [wordCost_append _ (by simpa using hlen.symm)]
  simp [wordCost, matrixCost]

private theorem endpointScores_spec (δ : Q → Letter → Q) (S F : Finset Q)
    (w : List (Option Letter)) (j : Q) :
    (∃ s, ∃ p : (completeGraph Q).Walk s j, p.length = w.length ∧
      wordCost (matrixCost (costs δ S F)) w p.edges = endpointScores δ S F w j) ∧
    ∀ s (p : (completeGraph Q).Walk s j), p.length = w.length →
      endpointScores δ S F w j ≤ wordCost (matrixCost (costs δ S F)) w p.edges := by
  induction w using List.reverseRecOn generalizing j with
  | nil =>
    exact ⟨⟨j, .nil, rfl, rfl⟩, fun s p h => by cases p <;> simp_all [endpointScores, wordCost]⟩
  | append_singleton w a ih =>
    rw [endpointScores_append]
    constructor
    · obtain ⟨i, hi⟩ := update_attains (costs δ S F) a (endpointScores δ S F w) j
      obtain ⟨s, p, hlen, hp⟩ := (ih i).1
      exact ⟨s, p.concat (i, j) rfl, by simp [hlen],
        (wordCost_concat _ _ _ p hlen).trans (by rw [hp, hi])⟩
    · intro s p hlen
      cases p with
      | nil => simp at hlen
      | @concat i p e h =>
        rcases e with ⟨i', j'⟩
        change i' = i at h
        subst i'
        have hp : p.length = w.length := by simpa using hlen
        erw [wordCost_concat _ _ _ p hp]
        exact (update_le _ _ _ i j').trans (add_le_add ((ih i).2 s p hp) le_rfl)

private def summarizes (q : Q → ℤ) (b : ℤ) (T : Finset Q) : Prop :=
  T.Nonempty ∧ (∀ i, b ≤ q i) ∧ ∀ i, q i = b ↔ i ∈ T

private theorem summarizes_letter (δ : Q → Letter → Q) (S F : Finset Q) (a : Letter)
    {q : Q → ℤ} {b : ℤ} {T : Finset Q} (h : summarizes q b T) :
    summarizes (update (costs δ S F) (some a) q) b (T.image fun i => δ i a) := by
  have lower (j : Q) : b ≤ update (costs δ S F) (some a) q j := by
    obtain ⟨i, hi⟩ := update_attains (costs δ S F) (some a) q j
    rw [← hi]
    have hb := h.2.1 i
    by_cases hij : δ i a = j <;> simp [costs, hij] <;> omega
  refine ⟨h.1.image _, lower, fun j => ⟨?_, ?_⟩⟩
  · intro hj
    obtain ⟨i, hi⟩ := update_attains (costs δ S F) (some a) q j
    have hb := h.2.1 i
    by_cases hij : δ i a = j
    · exact Finset.mem_image.mpr ⟨i, (h.2.2 i).mp (by simpa [costs, hij, hj] using hi), hij⟩
    · simp [costs, hij, hj] at hi
      omega
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply le_antisymm _ (lower _)
    simpa [costs, (h.2.2 i).mpr hi] using update_le (costs δ S F) (some a) q i (δ i a)

private theorem summarizes_delimiter (δ : Q → Letter → Q) (S F : Finset Q) (hS : S.Nonempty)
    {q : Q → ℤ} {b : ℤ} {T : Finset Q} (h : summarizes q b T) :
    summarizes (update (costs δ S F) none q) (b + (charge F T : ℤ)) S := by
  have inside (j : Q) (hj : j ∈ S) :
      update (costs δ S F) none q j = b + (charge F T : ℤ) := by
    obtain ⟨i, hi⟩ := update_attains (costs δ S F) none q j
    have hb := h.2.1 i
    by_cases hTF : T ⊆ F
    · have lower : b + 1 ≤ update (costs δ S F) none q j := by
        by_cases hF : i ∈ F
        · simp [costs, hj, hF] at hi
          omega
        · have hne : q i ≠ b := fun he => hF (hTF ((h.2.2 i).mp he))
          simp [costs, hj, hF] at hi
          omega
      obtain ⟨t, ht⟩ := h.1
      have upper := update_le (costs δ S F) none q t j
      simp [costs, hj, hTF ht, (h.2.2 t).mpr ht] at upper
      simpa [charge, hTF] using le_antisymm upper lower
    · have lower : b ≤ update (costs δ S F) none q j := by
        by_cases hF : i ∈ F <;> simp [costs, hj, hF] at hi <;> omega
      obtain ⟨t, ht, htF⟩ := Finset.not_subset.mp hTF
      have upper := update_le (costs δ S F) none q t j
      simp [costs, hj, htF, (h.2.2 t).mpr ht] at upper
      simpa [charge, hTF] using le_antisymm upper lower
  have outside (j : Q) (hj : j ∉ S) : update (costs δ S F) none q j = b + 2 := by
    obtain ⟨i, hi⟩ := update_attains (costs δ S F) none q j
    obtain ⟨t, ht⟩ := h.1
    have hlower := h.2.1 i
    have hupper := update_le (costs δ S F) none q t j
    simp [costs, hj] at hi
    simp [costs, hj, (h.2.2 t).mpr ht] at hupper
    omega
  have hcharge : b + (charge F T : ℤ) < b + 2 := by
    by_cases hTF : T ⊆ F <;> simp [charge, hTF]
  refine ⟨hS, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · exact (inside j hj).ge
    · rw [outside j hj]
      exact hcharge.le
  · intro j
    by_cases hj : j ∈ S
    · simp [hj, inside j hj]
    · simp [hj, outside j hj, hcharge.ne']

private theorem scan_invariant (δ : Q → Letter → Q) (S F : Finset Q) (hS : S.Nonempty)
    (w : List (Option Letter)) :
    summarizes (endpointScores δ S F w) (scan δ S F w).1 (scan δ S F w).2 := by
  induction w using List.reverseRecOn with
  | nil =>
    exact ⟨hS.mono (Finset.subset_univ S), fun _ => le_rfl, fun _ => by simp [scan, endpointScores]⟩
  | append_singleton w a ih =>
    rw [endpointScores_append, scan_append]
    cases a with
    | none =>
      simpa only [scanStep, Nat.cast_add] using summarizes_delimiter δ S F hS ih
    | some a => exact summarizes_letter δ S F a ih

/-- On every word the actual free-endpoint matrix minimum is the count of
charged completed segments. The scan also gives its exact minimizing endpoints. -/
theorem matrixMinimum_eq_score (δ : Q → Letter → Q) (S F : Finset Q) (hS : S.Nonempty)
    (w : List (Option Letter)) :
    letI : Nonempty Q := hS.to_type
    matrixMinimum (costs δ S F) w = (scan δ S F w).1 ∧
    ∀ j, endpointScores δ S F w j = matrixMinimum (costs δ S F) w ↔
      j ∈ (scan δ S F w).2 := by
  let : Nonempty Q := hS.to_type
  obtain ⟨hne, hlower, hset⟩ := scan_invariant δ S F hS w
  have hactual := matrixMinimum_spec (costs δ S F) w
  have heq : matrixMinimum (costs δ S F) w = (scan δ S F w).1 := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hne
      obtain ⟨s, p, hlen, hp⟩ := (endpointScores_spec δ S F w j).1
      have h := hactual.2 p.edges ⟨s, j, p, rfl⟩ (by simpa using hlen)
      rwa [hp, (hset j).mpr hj] at h
    · obtain ⟨b, ⟨s, j, p, rfl⟩, hlen, hcost⟩ := hactual.1
      rw [← hcost]
      exact (hlower j).trans ((endpointScores_spec δ S F w j).2 s p (by simpa using hlen))
  exact ⟨heq, by simpa only [heq] using hset⟩

private theorem scan_detect (δ : Q → Letter → Q) (S F : Finset Q) (w : List (Option Letter)) :
    0 < (scan δ S F w).1 ↔
      ∃ u v, w = u ++ none :: v ∧ (scan δ S F u).2 ⊆ F := by
  induction w using List.reverseRecOn with
  | nil => simp [scan]
  | append_singleton w a ih =>
    have hex :
        (∃ u v, w ++ [a] = u ++ none :: v ∧ (scan δ S F u).2 ⊆ F) ↔
          (∃ u v, w = u ++ none :: v ∧ (scan δ S F u).2 ⊆ F) ∨
          (a = none ∧ (scan δ S F w).2 ⊆ F) := by
      constructor
      · rintro ⟨u, v, hv, hF⟩
        cases v using List.reverseRecOn with
        | nil =>
          obtain ⟨rfl, ha⟩ := List.append_inj' (show w ++ [a] = u ++ [none] from hv) rfl
          exact Or.inr ⟨List.cons.inj ha |>.1, hF⟩
        | append_singleton v b =>
          have h' : w ++ [a] = (u ++ none :: v) ++ [b] := by
            simpa only [List.append_assoc, List.cons_append] using hv
          have hw : w = u ++ none :: v := List.append_inj_left' h' rfl
          exact Or.inl ⟨u, v, hw, hF⟩
      · rintro (⟨u, v, rfl, hF⟩ | ⟨rfl, hF⟩)
        · exact ⟨u, v ++ [a], by simp [List.append_assoc], hF⟩
        · exact ⟨w, [], rfl, hF⟩
    rw [hex, ← ih, scan_append]
    cases a with
    | none => by_cases h : (scan δ S F w).2 ⊆ F <;> simp [scanStep, charge, h]
    | some a => simp [scanStep]

/-- The actual matrix minimum is positive exactly when some delimiter
closes a segment whose entire current state set accepts. -/
theorem matrixMinimum_pos_iff (δ : Q → Letter → Q) (S F : Finset Q) (hS : S.Nonempty)
    (w : List (Option Letter)) :
    letI : Nonempty Q := hS.to_type
    0 < matrixMinimum (costs δ S F) w ↔
      ∃ u v, w = u ++ none :: v ∧ (scan δ S F u).2 ⊆ F := by
  rw [(matrixMinimum_eq_score δ S F hS w).1]
  exact_mod_cast scan_detect δ S F w

end MeyerovitchYoungQ61DFAIntersection
