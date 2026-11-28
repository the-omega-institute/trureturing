/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalPath49
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cyclic order-49 witness with period three. -/

import OmegaBuild.Commands
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-!
Omega original.

The cyclic order-49 witness with period three. The finite state certificates
are checked by `decide`.

Write A = {0, ±2, ±3, ±5, ±8, ±11, ±13}. If every edge residual
has word length at most one, consecutive potential increments belong to A.
A state records the last two increments. The length-two and length-three
edge conditions give the transitions below. The explicit overapproximating
stages become empty after 13 increments, so the first 14 vertices suffice.
-/

namespace ChordalPath49

abbrev H := ZMod 49

/-- The requested symmetric generating list, with no zero. -/
def generators : List H := [2, -2, 3, -3, 5, -5, 8, -8, 11, -11, 13, -13]

/-- Exactly the zero-plus-generators unit ball. -/
def alphabet : List H := 0 :: generators

def h (i : ℕ) : H := if i % 3 = 0 then 5 else if i % 3 = 1 then 3 else -8

/-- Gains for a forward edge of length r. -/
def forwardGain (i r : ℕ) : H :=
  if r = 1 then 0 else if r = 2 then -h (i + 1) else if r = 3 then 2 * h i else 0

/-- Unit-word feasibility for all forward edges of the power path. -/
def UnitFeasible (N : ℕ) (p : Fin N → H) : Prop :=
  ∀ (i j : Fin N), i.val < j.val → j.val ≤ i.val + 3 →
    forwardGain i.val (j.val - i.val) - (p j - p i) ∈ alphabet

/-- A transition checks the newly completed length-two and length-three edges. -/
def localStep (i : ℕ) (q : H × H) (c : H) : Prop :=
  -h (i + 2) - (q.2 + c) ∈ alphabet ∧
  2 * h i - (q.1 + q.2 + c) ∈ alphabet

instance (i : ℕ) (q : H × H) (c : H) : Decidable (localStep i q c) := by
  unfold localStep
  infer_instance

/-- States after 2 increments: 84 pairs. -/
def stage0 : List (H × H) := [(0, 0), (0, 2), (0, 5), (0, 8), (0, 38), (0, 41), (0, 44), (0, 46), (2, 0), (2, 3), (2, 8), (2, 36), (2, 41), (2, 44), (2, 46), (2, 47), (3, 2), (3, 5), (3, 38), (3, 41), (3, 46), (5, 0), (5, 3), (5, 5), (5, 36), (5, 38), (5, 41), (5, 44), (5, 46), (8, 0), (8, 2), (8, 36), (8, 38), (8, 41), (8, 46), (11, 38), (11, 46), (13, 36), (13, 38), (13, 41), (13, 44), (13, 46), (36, 2), (36, 5), (36, 8), (36, 13), (36, 46), (38, 0), (38, 3), (38, 5), (38, 8), (38, 11), (38, 13), (38, 44), (38, 46), (41, 0), (41, 2), (41, 3), (41, 5), (41, 8), (41, 13), (41, 41), (41, 46), (44, 0), (44, 2), (44, 5), (44, 13), (44, 38), (44, 46), (46, 0), (46, 2), (46, 3), (46, 5), (46, 8), (46, 11), (46, 13), (46, 36), (46, 38), (46, 41), (46, 44), (46, 46), (46, 47), (47, 2), (47, 46)]

/-- States after 3 increments: 82 pairs. -/
def stage1 : List (H × H) := [(0, 0), (0, 3), (0, 5), (0, 8), (0, 11), (0, 13), (0, 44), (0, 46), (2, 3), (2, 8), (2, 11), (2, 44), (2, 47), (3, 0), (3, 2), (3, 3), (3, 5), (3, 8), (3, 13), (3, 41), (3, 46), (5, 0), (5, 3), (5, 5), (5, 8), (5, 11), (5, 41), (5, 44), (5, 47), (8, 0), (8, 2), (8, 3), (8, 5), (8, 8), (8, 11), (8, 13), (8, 36), (8, 38), (8, 41), (8, 44), (8, 46), (8, 47), (11, 0), (11, 2), (11, 5), (11, 8), (11, 38), (11, 46), (13, 0), (13, 3), (13, 8), (13, 36), (13, 41), (13, 44), (13, 46), (13, 47), (36, 8), (36, 13), (38, 8), (38, 11), (41, 3), (41, 5), (41, 8), (41, 11), (41, 13), (44, 0), (44, 2), (44, 5), (44, 8), (44, 11), (44, 13), (46, 0), (46, 3), (46, 8), (46, 11), (46, 13), (46, 47), (47, 2), (47, 5), (47, 8), (47, 13), (47, 46)]

/-- States after 4 increments: 77 pairs. -/
def stage2 : List (H × H) := [(0, 0), (0, 3), (0, 8), (0, 36), (0, 41), (0, 44), (0, 46), (0, 47), (2, 44), (2, 47), (3, 0), (3, 3), (3, 5), (3, 36), (3, 38), (3, 41), (3, 44), (3, 46), (5, 3), (5, 36), (5, 41), (5, 44), (5, 47), (8, 0), (8, 36), (8, 38), (8, 41), (8, 44), (8, 47), (11, 36), (11, 38), (11, 41), (11, 44), (11, 46), (13, 36), (13, 44), (36, 0), (36, 3), (36, 8), (36, 11), (36, 13), (36, 44), (38, 3), (38, 8), (38, 11), (38, 44), (38, 47), (41, 0), (41, 3), (41, 8), (41, 11), (41, 44), (41, 47), (44, 0), (44, 3), (44, 5), (44, 8), (44, 11), (44, 13), (44, 36), (44, 41), (44, 44), (44, 47), (46, 0), (46, 3), (46, 11), (46, 36), (46, 44), (46, 47), (47, 0), (47, 2), (47, 5), (47, 8), (47, 38), (47, 41), (47, 44), (47, 46)]

/-- States after 5 increments: 69 pairs. -/
def stage3 : List (H × H) := [(0, 0), (0, 2), (0, 5), (0, 8), (0, 38), (0, 41), (0, 44), (0, 46), (2, 36), (2, 41), (2, 44), (2, 46), (3, 2), (3, 5), (3, 38), (3, 41), (3, 46), (5, 36), (5, 38), (5, 41), (5, 44), (5, 46), (8, 0), (8, 2), (8, 36), (8, 38), (8, 41), (8, 46), (11, 38), (11, 46), (13, 36), (13, 38), (13, 41), (13, 44), (13, 46), (36, 2), (36, 5), (36, 8), (36, 13), (36, 46), (38, 0), (38, 3), (38, 5), (38, 8), (38, 44), (38, 46), (41, 0), (41, 2), (41, 3), (41, 5), (41, 8), (41, 41), (41, 46), (44, 0), (44, 2), (44, 5), (44, 13), (44, 38), (44, 46), (46, 0), (46, 2), (46, 36), (46, 38), (46, 41), (46, 44), (46, 46), (46, 47), (47, 2), (47, 46)]

/-- States after 6 increments: 54 pairs. -/
def stage4 : List (H × H) := [(0, 0), (0, 5), (0, 8), (0, 11), (0, 13), (0, 46), (2, 3), (2, 8), (2, 11), (2, 44), (2, 47), (3, 2), (3, 5), (3, 13), (5, 0), (5, 3), (5, 5), (5, 8), (5, 11), (5, 41), (8, 0), (8, 2), (8, 5), (8, 8), (8, 11), (8, 13), (8, 38), (8, 46), (13, 0), (13, 8), (13, 46), (36, 8), (36, 13), (38, 8), (38, 11), (41, 3), (41, 5), (41, 8), (41, 11), (41, 13), (44, 0), (44, 2), (44, 5), (44, 8), (44, 11), (44, 13), (46, 0), (46, 3), (46, 8), (46, 11), (46, 13), (46, 47), (47, 2), (47, 13)]

/-- States after 7 increments: 40 pairs. -/
def stage5 : List (H × H) := [(0, 0), (0, 3), (0, 8), (0, 36), (0, 44), (0, 47), (2, 44), (2, 47), (3, 0), (3, 3), (3, 36), (3, 44), (5, 3), (5, 36), (5, 44), (5, 47), (8, 0), (8, 36), (8, 41), (8, 44), (8, 47), (11, 36), (11, 38), (11, 41), (11, 44), (11, 46), (13, 36), (13, 44), (38, 11), (38, 47), (41, 11), (41, 47), (44, 11), (44, 47), (46, 3), (46, 11), (46, 47), (47, 0), (47, 8), (47, 44)]

/-- States after 8 increments: 27 pairs. -/
def stage6 : List (H × H) := [(0, 38), (0, 41), (0, 44), (0, 46), (3, 38), (3, 41), (3, 46), (8, 36), (8, 38), (11, 38), (11, 46), (36, 2), (36, 5), (36, 8), (36, 46), (38, 44), (38, 46), (41, 41), (41, 46), (44, 0), (44, 2), (44, 38), (44, 46), (46, 36), (46, 38), (47, 2), (47, 46)]

/-- States after 9 increments: 17 pairs. -/
def stage7 : List (H × H) := [(0, 13), (2, 8), (2, 11), (5, 5), (8, 2), (8, 13), (36, 13), (38, 8), (38, 11), (41, 5), (41, 13), (44, 2), (44, 13), (46, 0), (46, 8), (46, 11), (46, 13)]

/-- States after 10 increments: 8 pairs. -/
def stage8 : List (H × H) := [(0, 47), (2, 47), (5, 47), (8, 47), (11, 36), (11, 44), (13, 36), (13, 44)]

/-- States after 11 increments: 3 pairs. -/
def stage9 : List (H × H) := [(36, 46), (44, 38), (47, 46)]

/-- States after 12 increments: 1 pairs. -/
def stage10 : List (H × H) := [(46, 13)]

/-- States after 13 increments: 0 pairs. -/
def stage11 : List (H × H) := []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial_certificate :
    List.Forall (fun a => List.Forall (fun b =>
      -h 1 - (a + b) ∈ alphabet → (a, b) ∈ stage0) alphabet) alphabet := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate0 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 0 q c → (q.2, c) ∈ stage1) alphabet) stage0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate1 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 1 q c → (q.2, c) ∈ stage2) alphabet) stage1 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate2 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 2 q c → (q.2, c) ∈ stage3) alphabet) stage2 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate3 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 3 q c → (q.2, c) ∈ stage4) alphabet) stage3 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate4 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 4 q c → (q.2, c) ∈ stage5) alphabet) stage4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate5 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 5 q c → (q.2, c) ∈ stage6) alphabet) stage5 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate6 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 6 q c → (q.2, c) ∈ stage7) alphabet) stage6 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate7 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 7 q c → (q.2, c) ∈ stage8) alphabet) stage7 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate8 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 8 q c → (q.2, c) ∈ stage9) alphabet) stage8 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate9 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 9 q c → (q.2, c) ∈ stage10) alphabet) stage9 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step_certificate10 :
    List.Forall (fun q => List.Forall (fun c =>
      localStep 10 q c → (q.2, c) ∈ stage11) alphabet) stage10 := by
  decide

/-- Consume a bounded-list certificate without enumerating arbitrary potentials. -/
theorem certificate_apply {i : ℕ} {s t : List (H × H)}
    (cert : List.Forall (fun q => List.Forall (fun c =>
      localStep i q c → (q.2, c) ∈ t) alphabet) s)
    {a b c : H} (hab : (a, b) ∈ s) (hc : c ∈ alphabet)
    (hstep : localStep i (a, b) c) : (b, c) ∈ t :=
  (List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp cert (a, b) hab)) c hc hstep

/-- No sequence of 13 increments can satisfy the necessary edge conditions. -/
theorem no_unit_increment_sequence (d : ℕ → H)
    (hd : ∀ i < 13, d i ∈ alphabet)
    (h₂ : ∀ i < 12, -h (i + 1) - (d i + d (i + 1)) ∈ alphabet)
    (h₃ : ∀ i < 11, 2 * h i - (d i + d (i + 1) + d (i + 2)) ∈ alphabet) :
    False := by
  have hs0 : (d 0, d 1) ∈ stage0 :=
    (List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp initial_certificate (d 0) (hd 0 (by omega))))
      (d 1) (hd 1 (by omega)) (h₂ 0 (by omega))
  have hs1 : (d 1, d 2) ∈ stage1 :=
    certificate_apply step_certificate0 hs0 (hd 2 (by omega))
      ⟨h₂ 1 (by omega), h₃ 0 (by omega)⟩
  have hs2 : (d 2, d 3) ∈ stage2 :=
    certificate_apply step_certificate1 hs1 (hd 3 (by omega))
      ⟨h₂ 2 (by omega), h₃ 1 (by omega)⟩
  have hs3 : (d 3, d 4) ∈ stage3 :=
    certificate_apply step_certificate2 hs2 (hd 4 (by omega))
      ⟨h₂ 3 (by omega), h₃ 2 (by omega)⟩
  have hs4 : (d 4, d 5) ∈ stage4 :=
    certificate_apply step_certificate3 hs3 (hd 5 (by omega))
      ⟨h₂ 4 (by omega), h₃ 3 (by omega)⟩
  have hs5 : (d 5, d 6) ∈ stage5 :=
    certificate_apply step_certificate4 hs4 (hd 6 (by omega))
      ⟨h₂ 5 (by omega), h₃ 4 (by omega)⟩
  have hs6 : (d 6, d 7) ∈ stage6 :=
    certificate_apply step_certificate5 hs5 (hd 7 (by omega))
      ⟨h₂ 6 (by omega), h₃ 5 (by omega)⟩
  have hs7 : (d 7, d 8) ∈ stage7 :=
    certificate_apply step_certificate6 hs6 (hd 8 (by omega))
      ⟨h₂ 7 (by omega), h₃ 6 (by omega)⟩
  have hs8 : (d 8, d 9) ∈ stage8 :=
    certificate_apply step_certificate7 hs7 (hd 9 (by omega))
      ⟨h₂ 8 (by omega), h₃ 7 (by omega)⟩
  have hs9 : (d 9, d 10) ∈ stage9 :=
    certificate_apply step_certificate8 hs8 (hd 10 (by omega))
      ⟨h₂ 9 (by omega), h₃ 8 (by omega)⟩
  have hs10 : (d 10, d 11) ∈ stage10 :=
    certificate_apply step_certificate9 hs9 (hd 11 (by omega))
      ⟨h₂ 10 (by omega), h₃ 9 (by omega)⟩
  have hs11 : (d 11, d 12) ∈ stage11 :=
    certificate_apply step_certificate10 hs10 (hd 12 (by omega))
      ⟨h₂ 11 (by omega), h₃ 10 (by omega)⟩
  exact List.not_mem_nil hs11

/-- Negation preserves the explicit unit ball. -/
theorem alphabet_neg {x : H} (hx : x ∈ alphabet) : -x ∈ alphabet := by
  have cert : List.Forall (fun x : H => -x ∈ alphabet) alphabet := by decide
  exact List.forall_iff_forall_mem.mp cert x hx

/-- The increment obstruction applies to arbitrary potentials and every N ≥ 14. -/
theorem no_unit_feasible {N : ℕ} (hN : 14 ≤ N) (p : Fin N → H) :
    ¬ UnitFeasible N p := by
  intro hp
  let P : ℕ → H := fun n => if hn : n < N then p ⟨n, hn⟩ else 0
  let d : ℕ → H := fun i => P (i + 1) - P i
  have hres (i r : ℕ) (hr : 0 < r) (hr3 : r ≤ 3) (hi : i + r < N) :
      forwardGain i r - (P (i + r) - P i) ∈ alphabet := by
    have hi0 : i < N := by omega
    have he := hp ⟨i, hi0⟩ ⟨i + r, hi⟩ (by change i < i + r; omega) (by change i + r ≤ i + 3; omega)
    simpa [P, hi, hi0] using he
  apply no_unit_increment_sequence d
  · intro i hi
    have he := alphabet_neg (hres i 1 (by omega) (by omega) (by omega))
    simpa [forwardGain, d] using he
  · intro i hi
    have ht : d i + d (i + 1) = P (i + 2) - P i := by dsimp [d]; ring
    rw [ht]
    simpa [forwardGain] using hres i 2 (by omega) (by omega) (by omega)
  · intro i hi
    have ht : d i + d (i + 1) + d (i + 2) = P (i + 3) - P i := by dsimp [d]; ring
    rw [ht]
    simpa [forwardGain] using hres i 3 (by omega) (by omega) (by omega)

/-- The requested 27-vertex witness excludes residual budget one. -/
theorem p27_no_unit_potential (p : Fin 27 → H) : ¬ UnitFeasible 27 p :=
  no_unit_feasible (by omega) p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All possible triangle shapes and all three phases, checked in the kernel. -/
theorem triangle_certificate :
    ∀ (i : Fin 3) (a b : Fin 4), 0 < a.val → 0 < b.val → a.val + b.val ≤ 3 →
      forwardGain i.val a.val + forwardGain (i.val + a.val) b.val -
        forwardGain i.val (a.val + b.val) ∈ generators := by
  decide

/-- Every increasing triangle in every third power path has a requested generator defect. -/
theorem triangle_defect_mem (i a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 3) :
    forwardGain i a + forwardGain (i + a) b - forwardGain i (a + b) ∈ generators := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by omega)
  have he := triangle_certificate ⟨i % 3, hi⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ ha hb hab
  simpa [forwardGain, h, Nat.add_mod] using he

/-- The actual oriented defect on i < j < k of span at most three. -/
theorem ordered_triangle_defect_mem (i j k : ℕ)
    (hij : i < j) (hjk : j < k) (hik : k ≤ i + 3) :
    forwardGain i (j - i) + forwardGain j (k - j) - forwardGain i (k - i) ∈ generators := by
  have h1 : i + (j - i) = j := by omega
  have h2 : (j - i) + (k - j) = k - i := by omega
  simpa only [h1, h2] using
    triangle_defect_mem i (j - i) (k - j) (by omega) (by omega) (by omega)

/-- A finite word in exactly the requested generators, of length at most r. -/
def WordBudget (r : ℕ) (x : H) : Prop :=
  ∃ w : List H, (∀ y ∈ w, y ∈ generators) ∧ w.length ≤ r ∧ w.sum = x

/-- The visible 13-element list is exactly the residual word ball of radius one. -/
theorem wordBudget_one_iff (x : H) : WordBudget 1 x ↔ x ∈ alphabet := by
  constructor
  · rintro ⟨w, hw, hlen, hsum⟩
    cases w with
    | nil =>
      have hx : x = 0 := by simpa using hsum.symm
      simp [hx, alphabet]
    | cons a w =>
      cases w with
      | nil =>
        have hx : a = x := by simpa using hsum
        have ha := hw a (by simp)
        simpa [alphabet, hx] using List.mem_cons_of_mem 0 ha
      | cons b w => simp at hlen
  · intro hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact ⟨[], by simp, by simp, by simp⟩
    · exact ⟨[x], by simpa using hx, by simp, by simp⟩

/-- Every potential has an actual edge whose residual requires at least two letters. -/
theorem exists_edge_not_wordBudget_one {N : ℕ} (hN : 14 ≤ N) (p : Fin N → H) :
    ∃ i j : Fin N, i.val < j.val ∧ j.val ≤ i.val + 3 ∧
      ¬ WordBudget 1 (forwardGain i.val (j.val - i.val) - (p j - p i)) := by
  classical
  by_contra he
  apply no_unit_feasible hN p
  intro i j hij hspan
  apply (wordBudget_one_iff _).mp
  by_contra hn
  exact he ⟨i, j, hij, hspan, hn⟩

/-- Every triangle defect has a one-letter word in the requested generators. -/
theorem triangle_wordBudget_one (i j k : ℕ)
    (hij : i < j) (hjk : j < k) (hik : k ≤ i + 3) :
    WordBudget 1 (forwardGain i (j - i) + forwardGain j (k - j) - forwardGain i (k - i)) :=
  (wordBudget_one_iff _).mpr
    (List.mem_cons_of_mem 0 (ordered_triangle_defect_mem i j k hij hjk hik))


/-- Negation preserves the requested generator list. -/
theorem generators_neg {x : H} (hx : x ∈ generators) : -x ∈ generators := by
  have cert : List.Forall (fun x : H => -x ∈ generators) generators := by decide
  exact List.forall_iff_forall_mem.mp cert x hx

/-- Each phase value h_i is one of the requested generators. -/
theorem h_mem (i : ℕ) : h i ∈ generators := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by omega)
  have hc : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hc with hc | hc | hc <;> simp only [h, hc] <;> decide

/-- The zero potential has residual words of length at most two on every edge. -/
theorem forwardGain_wordBudget_two (i r : ℕ) (hr : 0 < r) (hr3 : r ≤ 3) :
    WordBudget 2 (forwardGain i r) := by
  have hc : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨[], by simp, by simp, by simp [forwardGain]⟩
  · refine ⟨[-h (i + 1)], ?_, by simp, by simp [forwardGain]⟩
    simpa using generators_neg (h_mem (i + 1))
  · refine ⟨[h i, h i], ?_, by simp, ?_⟩
    · simpa using h_mem i
    · simp [forwardGain]; ring

/-- A graph-independent word-budget formulation of reconstruction. -/
def ReconstructsWith (N r : ℕ) (p : Fin N → H) : Prop :=
  ∀ (i j : Fin N), i.val < j.val → j.val ≤ i.val + 3 →
    WordBudget r (forwardGain i.val (j.val - i.val) - (p j - p i))

/-- Exact finite-word optimum two, for every path length N ≥ 14. -/
theorem exact_word_optimum_two {N : ℕ} (hN : 14 ≤ N) :
    ReconstructsWith N 2 (fun _ => 0) ∧ ¬ ∃ p : Fin N → H, ReconstructsWith N 1 p := by
  constructor
  · intro i j hij hspan
    simpa using forwardGain_wordBudget_two i.val (j.val - i.val) (by omega) (by omega)
  · rintro ⟨p, hp⟩
    obtain ⟨i, j, hij, hspan, hbad⟩ := exists_edge_not_wordBudget_one hN p
    exact hbad (hp i j hij hspan)

/-- The exact requested P27^3 finite-word reconstruction statement. -/
theorem p27_exact_word_optimum_two :
    ReconstructsWith 27 2 (fun _ => 0) ∧ ¬ ∃ p : Fin 27 → H, ReconstructsWith 27 1 p :=
  exact_word_optimum_two (by omega)

/-- Nonzero and distinct letters make the Cayley generating set explicit. -/
theorem generators_nodup_nonzero : generators.Nodup ∧ (0 : H) ∉ generators := by decide

#print axioms p27_no_unit_potential
#print axioms exists_edge_not_wordBudget_one
#print axioms ordered_triangle_defect_mem
#print axioms p27_exact_word_optimum_two
#print axioms no_unit_increment_sequence

end ChordalPath49
