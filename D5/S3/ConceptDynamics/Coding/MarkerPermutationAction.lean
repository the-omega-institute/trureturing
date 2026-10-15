/- GID: D5/S3/ConceptDynamics/Coding/MarkerPermutationAction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/MarkerPermutationAction
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Faithful guarded marker permutations on original numbered Reset histories. -/

import D5.S3.ConceptDynamics.Coding.ResetAlternatingSquares
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
import D5.S3.ConceptDynamics.Coding.ResetAlternatingHistories

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.MarkerPermutationAction

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph)
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.Alternating
open Multiplicative

private abbrev Sign := ResetNumberedHistories.Sign
private def zeta : Sign := ofAdd true
private def origin {q : ℕ} (hq : 0 < q) : Vertex q := (zero hq, 1)
private def oneIndex {q : ℕ} (hq : 1 < q) : Fin q := ⟨1, by omega⟩
private def resetEdge {q : ℕ} (_hq : 0 < q) (i : Fin q) (h : Sign) : B q := .f i h
private def chainEdge {q : ℕ} (hq : 1 < q) : B q :=
  .a (zero (by omega)) zeta (by simpa [zero] using hq)
private def Aword {q : ℕ} (hq : 1 < q) : List (B q) :=
  [resetEdge (by omega) (zero (by omega)) 1,
    resetEdge (by omega) (zero (by omega)) zeta]
private def Bword {q : ℕ} (hq : 1 < q) : List (B q) :=
  [resetEdge (by omega) (zero (by omega)) 1,
    chainEdge hq,
    resetEdge (by omega) (oneIndex hq) zeta]
private theorem Aword_path {q : ℕ} (hq : 1 < q) :
    ListPath (by omega) (origin (by omega)) (Aword hq) (origin (by omega)) := by
  apply ListPath.cons
  · rfl
  · apply ListPath.cons
    · change (zero (by omega), flipSign (1 : Sign)) =
        (zero (by omega), zeta)
      simp [zeta, flipSign]
    · apply ListPath.nil
private theorem Bword_path {q : ℕ} (hq : 1 < q) :
    ListPath (by omega) (origin (by omega)) (Bword hq) (origin (by omega)) := by
  apply ListPath.cons
  · rfl
  · apply ListPath.cons
    · change (zero (by omega), flipSign (1 : Sign)) =
        (zero (by omega), zeta)
      simp [zeta, flipSign]
    · apply ListPath.cons
      · change (oneIndex hq, zeta) =
          (next (zero (by omega)) (by simpa [zero] using hq), zeta)
        congr 1
      · apply ListPath.nil
private theorem ListPath.append {q : ℕ} {hq : 0 < q}
    {v z u : Vertex q} {xs ys : List (B q)}
    (hxs : ListPath hq v xs z) (hys : ListPath hq z ys u) :
    ListPath hq v (xs ++ ys) u := by
  induction hxs with
  | nil v => simpa using hys
  | cons hx ht ih =>
      exact ListPath.cons hx (ih hys)
private def repeatWord {q : ℕ} (xs : List (B q)) : ℕ → List (B q)
  | 0 => []
  | n + 1 => xs ++ repeatWord xs n
private theorem repeatWord_path {q : ℕ} {hq : 0 < q}
    {v : Vertex q} (xs : List (B q))
    (hxs : ListPath hq v xs v) :
    ∀ n, ListPath hq v (repeatWord xs n) v
  | 0 => by simpa [repeatWord] using (ListPath.nil (hq := hq) v)
  | n + 1 => by
      rw [repeatWord]
      exact ListPath.append hxs (repeatWord_path xs hxs n)
private def dataChunk {q : ℕ} (hq : 1 < q) (b : Bool) : List (B q) :=
  if b then repeatWord (Aword hq) 3 else repeatWord (Bword hq) 2
private def dataWord {q k : ℕ} (hq : 1 < q) (b : Fin k → Bool) : List (B q) :=
  (List.ofFn (fun i : Fin k => dataChunk hq (b i))).flatten
private theorem dataChunk_path {q : ℕ} {hq : 1 < q} (b : Bool) :
    ListPath (by omega) (origin (by omega)) (dataChunk hq b) (origin (by omega)) := by
  simp only [dataChunk]
  split_ifs with hb
  · exact repeatWord_path (Aword hq) (Aword_path hq) 3
  · exact repeatWord_path (Bword hq) (Bword_path hq) 2
private theorem dataWord_path {q k : ℕ} {hq : 1 < q} (b : Fin k → Bool) :
    ListPath (by omega) (origin (by omega)) (dataWord hq b) (origin (by omega)) := by
  have flatten_path : ∀ (n : ℕ) (f : Fin n → List (B q)),
      (∀ i, ListPath (by omega) (origin (by omega)) (f i) (origin (by omega))) →
      ListPath (by omega) (origin (by omega)) (List.ofFn f).flatten (origin (by omega)) := by
    intro n
    induction n with
    | zero =>
        intro f hf
        simpa using (ListPath.nil (hq := by omega) (origin (by omega)))
    | succ n ih =>
        intro f hf
        let ft : Fin n → List (B q) := fun i => f i.succ
        have hft : ∀ i, ListPath (by omega) (origin (by omega)) (ft i) (origin (by omega)) :=
          fun i => hf i.succ
        have ht := ih ft hft
        rw [List.ofFn_succ]
        simpa [List.flatten_cons, ft] using ListPath.append (hf 0) ht
  exact flatten_path k (fun i => dataChunk hq (b i)) (fun i => dataChunk_path (hq := hq) (b i))
private theorem Aword_length {q : ℕ} (hq : 1 < q) : (Aword hq).length = 2 := by
  simp [Aword]
private theorem Bword_length {q : ℕ} (hq : 1 < q) : (Bword hq).length = 3 := by
  simp [Bword]
private theorem dataChunk_length {q : ℕ} (hq : 1 < q) (b : Bool) :
    (dataChunk hq b).length = 6 := by
  cases b <;> simp [dataChunk, repeatWord, Aword_length hq, Bword_length hq]
private theorem dataWord_length {q k : ℕ} (hq : 1 < q) (b : Fin k → Bool) :
    (dataWord hq b).length = 6 * k := by
  have hsum : ∀ (n : ℕ) (f : Fin n → Bool),
      (List.ofFn (fun i : Fin n => (dataChunk hq (f i)).length)).sum = 6 * n := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
        intro f
        let ft : Fin n → Bool := fun i => f i.succ
        simp [List.ofFn_succ, dataChunk_length hq]
        omega
  rw [dataWord, List.length_flatten]
  simpa [Function.comp_def, List.map_ofFn] using hsum k b
private theorem repeatWord_length {q : ℕ} (xs : List (B q)) (n : ℕ) :
    (repeatWord xs n).length = n * xs.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
      simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]
private def markerWord {q k : ℕ} (hq : 1 < q) : List (B q) :=
  repeatWord (Bword hq) (2 * k + 1) ++ Aword hq
private def markerTerminalEdge {q : ℕ} (hq : 1 < q) : B q :=
  resetEdge (by omega) (zero (by omega)) zeta
private theorem markerTerminalEdge_not_mem_Bword {q : ℕ} (hq : 1 < q) :
    markerTerminalEdge hq ∉ Bword hq := by
  simp only [markerTerminalEdge, Bword, resetEdge, chainEdge, zeta, oneIndex,
    List.mem_cons, List.mem_singleton, or_false]
  intro h
  rcases h with h | h | h | h
  · injection h with _ hb
    simpa [zeta] using hb
  · cases h
  · injection h with hs _
    have hi := congrArg Fin.val hs
    simp [zero, oneIndex] at hi
  · simp at h
private theorem markerWord_path {q k : ℕ} {hq : 1 < q} :
    ListPath (by omega) (origin (by omega)) (markerWord (k := k) hq) (origin (by omega)) := by
  rw [markerWord]
  exact ListPath.append
    (repeatWord_path (Bword hq) (Bword_path hq) (2 * k + 1)) (Aword_path hq)
private theorem markerWord_length {q k : ℕ} (hq : 1 < q) :
    (markerWord (k := k) hq).length = 6 * k + 5 := by
  rw [markerWord, List.length_append, repeatWord_length]
  rw [Bword_length hq, Aword_length hq]
  omega

namespace Guarded

universe u v

/-- Finite edge-offset overlap exclusion; no history or automorphism is assumed. -/
def NoPartialOverlap {E : Type u} {m : ℕ} (M : Fin m → E) : Prop :=
  ∀ r : ℕ, 0 < r → r < m →
    ¬ ∀ j : Fin (m - r), M ⟨r + j.val, by omega⟩ = M ⟨j.val, by omega⟩

/-- Only finite-word data, lengths, injectivity and overlap hypotheses. -/
structure Words (E : Type u) (I : Type v) (m d : ℕ) where
  marker : Fin m → E
  data : I → Fin d → E
  marker_pos : 0 < m
  data_short : d < m
  marker_unbordered : NoPartialOverlap marker
  data_injective : Function.Injective data
private theorem noPartialOverlap_of_unique_terminal {E : Type u} {m : ℕ}
    (M : Fin m → E) (hm : 0 < m)
    (hu : ∀ j, M j = M ⟨m - 1, by omega⟩ → j.val = m - 1) :
    NoPartialOverlap M := by
  intro r hr hrm h
  have he := h ⟨m - r - 1, by omega⟩
  have hidx : r + (m - r - 1) = m - 1 := by omega
  have he' : M ⟨m - r - 1, by omega⟩ = M ⟨m - 1, by omega⟩ := by
    simpa only [hidx] using he.symm
  have hi := hu _ he'
  dsimp only at hi
  omega

variable {E : Type u} {I : Type v} {m d : ℕ} (W : Words E I m d)

def Occurs (x : ℤ → E) (a : ℤ) : Prop :=
  ∀ j : Fin m, x (a + (j.val : ℤ)) = W.marker j

def Selected (x : ℤ → E) (a : ℤ) (i : I) : Prop :=
  Occurs W x a ∧ Occurs W x (a + (m : ℤ) + (d : ℤ)) ∧
    ∀ j : Fin d, x (a + (m : ℤ) + (j.val : ℤ)) = W.data i j
private theorem occurrence_separation {x : ℤ → E} {a b : ℤ}
    (ha : Occurs W x a) (hb : Occurs W x b) (hab : a < b) :
    a + (m : ℤ) ≤ b := by
  by_contra h
  have hr : 0 < (b - a).toNat := by omega
  have hrm : (b - a).toNat < m := by omega
  apply Words.marker_unbordered W (b - a).toNat hr hrm
  intro j
  have he := ha ⟨(b - a).toNat + j.val, by omega⟩
  have hf := hb ⟨j.val, by omega⟩
  have ht : a + (((b - a).toNat + j.val : ℕ) : ℤ) = b + (j.val : ℤ) := by
    omega
  rw [ht] at he
  exact he.symm.trans hf
private theorem consecutive_guards {x : ℤ → E} {a b : ℤ}
    (ha : Occurs W x a) (hr : Occurs W x (a + (m : ℤ) + (d : ℤ)))
    (hb : Occurs W x b) (hab : a < b) :
    a + (m : ℤ) + (d : ℤ) ≤ b := by
  have hleft := occurrence_separation W ha hb hab
  by_contra h
  have hright := occurrence_separation W hb hr (by omega)
  have hd := Words.data_short W
  omega
private theorem marker_avoids_gap {x : ℤ → E} {a b : ℤ}
    (ha : Occurs W x a) (hr : Occurs W x (a + (m : ℤ) + (d : ℤ)))
    (hb : Occurs W x b) (j : Fin m) :
    ¬ (a + (m : ℤ) ≤ b + (j.val : ℤ) ∧
      b + (j.val : ℤ) < a + (m : ℤ) + (d : ℤ)) := by
  by_cases hab : a < b
  · have h := consecutive_guards W ha hr hb hab
    omega
  · have hj := j.isLt
    omega
private theorem selected_starts_separated {x : ℤ → E} {a b : ℤ} {i l : I}
    (ha : Selected W x a i) (hb : Selected W x b l) (hab : a < b) :
    a + (m : ℤ) + (d : ℤ) ≤ b :=
  consecutive_guards W ha.1 ha.2.1 hb.1 hab
private theorem selected_start_unique {x : ℤ → E} {a b t : ℤ} {i l : I}
    (ha : Selected W x a i) (hb : Selected W x b l)
    (hat : a + (m : ℤ) ≤ t ∧ t < a + (m : ℤ) + (d : ℤ))
    (hbt : b + (m : ℤ) ≤ t ∧ t < b + (m : ℤ) + (d : ℤ)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := selected_starts_separated W ha hb hab
    omega
  · exact hab
  · have h := selected_starts_separated W hb ha hab
    omega
private theorem selected_label_unique {x : ℤ → E} {a : ℤ} {i l : I}
    (hi : Selected W x a i) (hl : Selected W x a l) : i = l := by
  apply Words.data_injective W
  funext j
  exact (hi.2.2 j).symm.trans (hl.2.2 j)

private structure Hit (x : ℤ → E) (t : ℤ) where
  start : ℤ
  symbol : I
  offset : Fin d
  selected : Selected W x start symbol
  coordinate : t = start + (m : ℤ) + (offset.val : ℤ)

/-- Simultaneous replacement changes only central data coordinates. -/
def replace (pi : Equiv.Perm I) (x : ℤ → E) (t : ℤ) : E := by
  classical
  exact if h : Nonempty (Hit W x t) then
    W.data (pi (Classical.choice h).symbol) (Classical.choice h).offset
  else x t
private theorem replace_at_selected (pi : Equiv.Perm I) {x : ℤ → E} {a : ℤ} {i : I}
    (hs : Selected W x a i) (j : Fin d) :
    replace W pi x (a + (m : ℤ) + (j.val : ℤ)) = W.data (pi i) j := by
  classical
  have h : Nonempty (Hit W x (a + (m : ℤ) + (j.val : ℤ))) :=
    ⟨⟨a, i, j, hs, rfl⟩⟩
  rw [replace, dif_pos h]
  let hit := Classical.choice h
  have ha : hit.start = a := selected_start_unique W
    (t := a + (m : ℤ) + (j.val : ℤ)) hit.selected hs
    (by have hj := hit.offset.isLt; have ht := hit.coordinate; omega)
    (by have hj := j.isLt; omega)
  have hitSelected : Selected W x a hit.symbol := by simpa [ha] using hit.selected
  have hi : hit.symbol = i := selected_label_unique W hitSelected hs
  have hj : hit.offset = j := by
    apply Fin.ext
    have ht := hit.coordinate
    simp only [ha] at ht
    omega
  change W.data (pi hit.symbol) hit.offset = _
  rw [hi, hj]
private theorem replace_on_marker (pi : Equiv.Perm I) {x : ℤ → E} {a : ℤ}
    (ha : Occurs W x a) (j : Fin m) :
    replace W pi x (a + (j.val : ℤ)) = x (a + (j.val : ℤ)) := by
  classical
  rw [replace]
  split_ifs with h
  · let hit := Classical.choice h
    have hn := marker_avoids_gap W hit.selected.1 hit.selected.2.1 ha j
    have hj := hit.offset.isLt
    have ht := hit.coordinate
    exfalso
    apply hn
    constructor <;> omega
  · rfl

/-- Every old marker is protected, and a new marker cannot cross its unchanged guards. -/
theorem marker_occurrences_invariant (pi : Equiv.Perm I) (x : ℤ → E) (a : ℤ) :
    Occurs W (replace W pi x) a ↔ Occurs W x a := by
  classical
  have old : ∀ b, Occurs W x b → Occurs W (replace W pi x) b := by
    intro b hb j
    rw [replace_on_marker W pi hb j]
    exact hb j
  constructor
  · intro ha j
    have hsame : replace W pi x (a + (j.val : ℤ)) = x (a + (j.val : ℤ)) := by
      rw [replace]
      split_ifs with h
      · let hit := Classical.choice h
        have hl := old hit.start hit.selected.1
        have hr := old (hit.start + (m : ℤ) + (d : ℤ)) hit.selected.2.1
        have hn := marker_avoids_gap W hl hr ha j
        have hj := hit.offset.isLt
        have ht := hit.coordinate
        exfalso
        apply hn
        constructor <;> omega
      · rfl
    exact hsame.symm.trans (ha j)
  · exact old a
private theorem replace_off_gap (pi : Equiv.Perm I) {x : ℤ → E} {t : ℤ}
    (h : ¬ Nonempty (Hit W x t)) : replace W pi x t = x t := by
  classical
  simp only [replace, dif_neg h]
private theorem selected_forward (pi : Equiv.Perm I) {x : ℤ → E} {a : ℤ} {i : I}
    (hi : Selected W x a i) : Selected W (replace W pi x) a (pi i) := by
  refine ⟨(marker_occurrences_invariant W pi x a).mpr hi.1,
    (marker_occurrences_invariant W pi x _).mpr hi.2.1, ?_⟩
  intro j
  exact replace_at_selected W pi hi j

/-- Exactly the same eligible intervals survive, with their data labels permuted. -/
theorem selected_iff (pi : Equiv.Perm I) (x : ℤ → E) (a : ℤ) (i : I) :
    Selected W (replace W pi x) a (pi i) ↔ Selected W x a i := by
  classical
  constructor
  · intro hi
    have hl := (marker_occurrences_invariant W pi x a).mp hi.1
    have hr := (marker_occurrences_invariant W pi x _).mp hi.2.1
    by_cases hold : ∃ l, Selected W x a l
    · obtain ⟨l, h⟩ := hold
      have he : pi l = pi i := selected_label_unique W (selected_forward W pi h) hi
      have hli := pi.injective he
      simpa [hli] using h
    · refine ⟨hl, hr, ?_⟩
      intro j
      have hnone : ¬ Nonempty (Hit W x (a + (m : ℤ) + (j.val : ℤ))) := by
        rintro ⟨hit⟩
        have hstart : hit.start = a := by
          rcases lt_trichotomy hit.start a with h | h | h
          · have hb := consecutive_guards W hit.selected.1 hit.selected.2.1 hl h
            have hc := hit.coordinate
            have hj := hit.offset.isLt
            omega
          · exact h
          · have hb := consecutive_guards W hl hr hit.selected.1 h
            have hc := hit.coordinate
            have hj := j.isLt
            omega
        apply hold
        exact ⟨hit.symbol, by simpa [hstart] using hit.selected⟩
      have he := hi.2.2 j
      rw [replace_off_gap W pi hnone] at he
      have hself : Selected W x a (pi i) := ⟨hl, hr, fun j => by
        have hnone : ¬ Nonempty (Hit W x (a + (m : ℤ) + (j.val : ℤ))) := by
          rintro ⟨hit⟩
          have hstart : hit.start = a := by
            rcases lt_trichotomy hit.start a with h | h | h
            · have hb := consecutive_guards W hit.selected.1 hit.selected.2.1 hl h
              have hc := hit.coordinate
              have hj := hit.offset.isLt
              omega
            · exact h
            · have hb := consecutive_guards W hl hr hit.selected.1 h
              have hc := hit.coordinate
              have hj := j.isLt
              omega
          exact hold ⟨hit.symbol, by simpa [hstart] using hit.selected⟩
        simpa only [replace_off_gap W pi hnone] using hi.2.2 j⟩
      exact False.elim (hold ⟨pi i, hself⟩)
  · exact selected_forward W pi
private theorem hit_nonempty_iff (pi : Equiv.Perm I) (x : ℤ → E) (t : ℤ) :
    Nonempty (Hit W (replace W pi x) t) ↔ Nonempty (Hit W x t) := by
  constructor
  · rintro ⟨hit⟩
    have hs : Selected W x hit.start (pi.symm hit.symbol) := by
      apply (selected_iff W pi x hit.start (pi.symm hit.symbol)).mp
      simpa using hit.selected
    exact ⟨⟨hit.start, pi.symm hit.symbol, hit.offset, hs, hit.coordinate⟩⟩
  · rintro ⟨hit⟩
    exact ⟨⟨hit.start, pi hit.symbol, hit.offset,
      selected_forward W pi hit.selected, hit.coordinate⟩⟩

/-- Composition acts on the same selected intervals with the ordinary permutation order. -/
theorem replace_mul (pi tau : Equiv.Perm I) (x : ℤ → E) :
    replace W pi (replace W tau x) = replace W (pi * tau) x := by
  classical
  funext t
  by_cases h : Nonempty (Hit W x t)
  · let hit := Classical.choice h
    rw [hit.coordinate]
    rw [replace_at_selected W pi (selected_forward W tau hit.selected) hit.offset,
      replace_at_selected W (pi * tau) hit.selected hit.offset]
    rfl
  · have h' := mt (hit_nonempty_iff W tau x t).mp h
    rw [replace_off_gap W pi h', replace_off_gap W tau h,
      replace_off_gap W (pi * tau) h]
private theorem replace_one (x : ℤ → E) : replace W 1 x = x := by
  classical
  funext t
  by_cases h : Nonempty (Hit W x t)
  · let hit := Classical.choice h
    rw [hit.coordinate, replace_at_selected W 1 hit.selected hit.offset]
    exact (hit.selected.2.2 hit.offset).symm
  · exact replace_off_gap W 1 h

/-- Both inverse laws follow from the same global interval invariance. -/
theorem replace_inverse (pi : Equiv.Perm I) (x : ℤ → E) :
    replace W pi⁻¹ (replace W pi x) = x ∧
      replace W pi (replace W pi⁻¹ x) = x := by
  constructor
  · rw [replace_mul, inv_mul_cancel, replace_one]
  · rw [replace_mul, mul_inv_cancel, replace_one]

/-- A symmetric original-edge window determines the replacement coordinate. -/
theorem replace_local (pi : Equiv.Perm I) (x y : ℤ → E) (t : ℤ)
    (hxy : ∀ s : ℤ, t - ((m + d : ℕ) : ℤ) ≤ s →
      s ≤ t + ((m + d : ℕ) : ℤ) → x s = y s) :
    replace W pi x t = replace W pi y t := by
  classical
  have transfer : ∀ {x y : ℤ → E},
      (∀ s : ℤ, t - ((m + d : ℕ) : ℤ) ≤ s →
        s ≤ t + ((m + d : ℕ) : ℤ) → x s = y s) →
      ∀ hit : Hit W x t, Selected W y hit.start hit.symbol := by
    intro x y h hit
    have ht := hit.coordinate
    have hj := hit.offset.isLt
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hji := j.isLt
      rw [← h (hit.start + (j.val : ℤ)) (by omega) (by omega)]
      exact hit.selected.1 j
    · intro j
      have hji := j.isLt
      rw [← h (hit.start + (m : ℤ) + (d : ℤ) + (j.val : ℤ))
        (by omega) (by omega)]
      exact hit.selected.2.1 j
    · intro j
      have hji := j.isLt
      rw [← h (hit.start + (m : ℤ) + (j.val : ℤ)) (by omega) (by omega)]
      exact hit.selected.2.2 j
  by_cases hx : Nonempty (Hit W x t)
  · let hit := Classical.choice hx
    rw [hit.coordinate]
    rw [replace_at_selected W pi hit.selected hit.offset,
      replace_at_selected W pi (transfer hxy hit) hit.offset]
  · have hy : ¬ Nonempty (Hit W y t) := by
      rintro ⟨hit⟩
      exact hx ⟨⟨hit.start, hit.symbol, hit.offset,
        transfer (fun s h₁ h₂ => (hxy s h₁ h₂).symm) hit, hit.coordinate⟩⟩
    rw [replace_off_gap W pi hx, replace_off_gap W pi hy]
    exact hxy t (by omega) (by omega)
private theorem selected_translate (x : ℤ → E) (a c : ℤ) (i : I) :
    Selected W (fun t => x (t + c)) a i ↔ Selected W x (a + c) i := by
  simp only [Selected, Occurs]
  constructor <;> rintro ⟨hl, hr, hd⟩
  · exact ⟨fun j => by simpa [add_assoc, add_comm, add_left_comm] using hl j,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hr j,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hd j⟩
  · exact ⟨fun j => by simpa [add_assoc, add_comm, add_left_comm] using hl j,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hr j,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hd j⟩

/-- Replacement commutes with every integer translation, in particular UNIT shift. -/
theorem replace_translate (pi : Equiv.Perm I) (x : ℤ → E) (c t : ℤ) :
    replace W pi (fun s => x (s + c)) t = replace W pi x (t + c) := by
  classical
  by_cases h : Nonempty (Hit W (fun s => x (s + c)) t)
  · let hit := Classical.choice h
    have hs := (selected_translate W x hit.start c hit.symbol).mp hit.selected
    have ht : t + c = (hit.start + c) + (m : ℤ) + (hit.offset.val : ℤ) := by
      have hc := hit.coordinate
      omega
    calc
      _ = replace W pi (fun s => x (s + c))
          (hit.start + (m : ℤ) + (hit.offset.val : ℤ)) :=
        congrArg (replace W pi (fun s => x (s + c))) hit.coordinate
      _ = W.data (pi hit.symbol) hit.offset :=
        replace_at_selected W pi hit.selected hit.offset
      _ = replace W pi x ((hit.start + c) + (m : ℤ) + (hit.offset.val : ℤ)) :=
        (replace_at_selected W pi hs hit.offset).symm
      _ = _ := congrArg (replace W pi x) ht.symm
  · have h' : ¬ Nonempty (Hit W x (t + c)) := by
      rintro ⟨hit⟩
      apply h
      exact ⟨⟨hit.start - c, hit.symbol, hit.offset,
        (selected_translate W x _ c _).mpr (by simpa using hit.selected),
        by have ht := hit.coordinate; omega⟩⟩
    rw [replace_off_gap W pi h, replace_off_gap W pi h']
private def windowExtension (w : Fin (2 * (m + d) + 1) → E) (s : ℤ) : E :=
  if h : 0 ≤ s + ((m + d : ℕ) : ℤ) ∧
      s + ((m + d : ℕ) : ℤ) < (2 * (m + d) + 1 : ℕ) then
    w ⟨(s + ((m + d : ℕ) : ℤ)).toNat, by omega⟩
  else w ⟨m + d, by omega⟩
private theorem replace_continuous [TopologicalSpace E] [DiscreteTopology E]
    (pi : Equiv.Perm I) : Continuous (replace W pi) := by
  classical
  apply continuous_pi
  intro t
  let f : (Fin (2 * (m + d) + 1) → E) → E :=
    fun w => replace W pi (windowExtension w) 0
  let win : (ℤ → E) → Fin (2 * (m + d) + 1) → E :=
    fun x j => x (t - ((m + d : ℕ) : ℤ) + (j.val : ℤ))
  have hw : Continuous win := continuous_pi (fun j => continuous_apply _)
  have he : (fun x => replace W pi x t) = f ∘ win := by
    funext x
    change replace W pi x t = replace W pi (windowExtension (win x)) 0
    rw [← (by simpa using replace_translate W pi x t 0 :
      replace W pi (fun s => x (s + t)) 0 = replace W pi x t)]
    apply replace_local W pi
    intro s hs₁ hs₂
    have hnat : 0 ≤ s + ((m + d : ℕ) : ℤ) ∧
        s + ((m + d : ℕ) : ℤ) < (2 * (m + d) + 1 : ℕ) := by omega
    change x (s + t) = windowExtension (win x) s
    unfold windowExtension
    rw [dif_pos hnat]
    change x (s + t) = x (t - ((m + d : ℕ) : ℤ) +
      (((s + ((m + d : ℕ) : ℤ)).toNat : ℕ) : ℤ))
    apply congrArg x
    omega
  rw [he]
  exact (continuous_of_discreteTopology : Continuous f).comp hw

universe w
variable {V : Type w} (G : DirectedMultigraph V E)

/-- Legal equal-endpoint finite loops; these are discharged for Reset below. -/
structure Loops (p : V) : Prop where
  data_pos : 0 < d
  marker_legal : ∀ j : Fin m, ∀ hj : j.val + 1 < m,
    G.target (W.marker j) = G.source (W.marker ⟨j.val + 1, hj⟩)
  marker_source : G.source (W.marker ⟨0, W.marker_pos⟩) = p
  marker_target : G.target (W.marker ⟨m - 1, by have h := W.marker_pos; omega⟩) = p
  data_legal : ∀ i j, ∀ hj : j.val + 1 < d,
    G.target (W.data i j) = G.source (W.data i ⟨j.val + 1, hj⟩)
  data_source : ∀ i, G.source (W.data i ⟨0, data_pos⟩) = p
  data_target : ∀ i, G.target (W.data i ⟨d - 1, by omega⟩) = p

variable {p : V} (L : Loops W G p)

include L in
private theorem replace_legal (pi : Equiv.Perm I) (x : History G) (t : ℤ) :
    G.target (replace W pi x.val t) = G.source (replace W pi x.val (t + 1)) := by
  classical
  by_cases ht : Nonempty (Hit W x.val t)
  · let hit := Classical.choice ht
    rw [hit.coordinate, replace_at_selected W pi hit.selected hit.offset]
    by_cases hj : hit.offset.val + 1 < d
    · have hn : hit.start + (m : ℤ) + (hit.offset.val : ℤ) + 1 =
          hit.start + (m : ℤ) + ((hit.offset.val + 1 : ℕ) : ℤ) := by omega
      rw [hn, replace_at_selected W pi hit.selected ⟨_, hj⟩]
      exact L.data_legal (pi hit.symbol) hit.offset hj
    · have hjlast : hit.offset = ⟨d - 1, by have hd := L.data_pos; omega⟩ := by
        apply Fin.ext
        dsimp only
        have hi := hit.offset.isLt
        omega
      have hn : hit.start + (m : ℤ) + (hit.offset.val : ℤ) + 1 =
          hit.start + (m : ℤ) + (d : ℤ) + (0 : ℤ) := by
        have hi := hit.offset.isLt
        omega
      have hm := replace_on_marker W pi hit.selected.2.1 ⟨0, W.marker_pos⟩
      have he := hit.selected.2.1 ⟨0, W.marker_pos⟩
      simp only [Fin.val_zero, Int.natCast_zero] at hm he
      rw [hn, hm, he, hjlast, L.data_target, L.marker_source]
  · rw [replace_off_gap W pi ht]
    by_cases hn : Nonempty (Hit W x.val (t + 1))
    · let hit := Classical.choice hn
      have hjzero : hit.offset.val = 0 := by
        by_contra hj
        apply ht
        exact ⟨⟨hit.start, hit.symbol, ⟨hit.offset.val - 1, by
          have hi := hit.offset.isLt; omega⟩, hit.selected,
          by dsimp only; have hc := hit.coordinate; omega⟩⟩
      have hc : t + 1 = hit.start + (m : ℤ) + (0 : ℤ) := by
        have hc := hit.coordinate
        omega
      have hj : hit.offset = ⟨0, L.data_pos⟩ := Fin.ext hjzero
      have hs := x.property t
      have he := hit.selected.2.2 ⟨0, L.data_pos⟩
      have hr := replace_at_selected W pi hit.selected ⟨0, L.data_pos⟩
      simp only [Fin.val_zero, Int.natCast_zero] at he hr
      rw [← hc] at he
      rw [hc, hr, L.data_source]
      rw [he, L.data_source] at hs
      exact hs
    · rw [replace_off_gap W pi hn]
      exact x.property t

/-- The simultaneous rule on the original legal-history subtype. -/
def onHistory (pi : Equiv.Perm I) (x : History G) : History G :=
  ⟨replace W pi x.val, replace_legal W G L pi x⟩
private theorem onHistory_continuous [TopologicalSpace E] [DiscreteTopology E]
    (pi : Equiv.Perm I) : Continuous (onHistory W G L pi) :=
  Continuous.subtype_mk ((replace_continuous W pi).comp continuous_subtype_val) _

/-- Both directions are local continuous maps of the ACTUAL legal-history space. -/
def homeomorph [TopologicalSpace E] [DiscreteTopology E] (pi : Equiv.Perm I) :
    History G ≃ₜ History G where
  toFun := onHistory W G L pi
  invFun := onHistory W G L pi⁻¹
  left_inv x := Subtype.ext (replace_inverse W pi x.val).1
  right_inv x := Subtype.ext (replace_inverse W pi x.val).2
  continuous_toFun := onHistory_continuous W G L pi
  continuous_invFun := onHistory_continuous W G L pi⁻¹

/-- A permutation action in the FULL unit-shift centralizer, with its real composition law. -/
def action [Fintype V] [Fintype E] [DecidableEq V]
    [TopologicalSpace V] [DiscreteTopology V]
    [TopologicalSpace E] [DiscreteTopology E] :
    Equiv.Perm I →* StandardBeamHomeomorphisms.FullAut G where
  toFun pi := ⟨homeomorph W G L pi, by
    intro x
    apply Subtype.ext
    funext t
    exact replace_translate W pi x.val 1 t⟩
  map_one' := by
    apply Subtype.ext
    ext x t
    exact congrFun (replace_one W x.val) t
  map_mul' pi tau := by
    apply Subtype.ext
    ext x t
    exact congrFun (replace_mul W pi tau x.val).symm t
private def templateEdge (i : I) (j : Fin (2 * m + d)) : E :=
  if h₀ : j.val < m then W.marker ⟨j.val, h₀⟩
  else if h₁ : j.val < m + d then W.data i ⟨j.val - m, by omega⟩
  else W.marker ⟨j.val - m - d, by omega⟩
private theorem template_left (i : I) (j : Fin m) :
    templateEdge W i ⟨j.val, by omega⟩ = W.marker j := by
  simp only [templateEdge, dif_pos j.isLt]
private theorem template_data (i : I) (j : Fin d) :
    templateEdge W i ⟨m + j.val, by omega⟩ = W.data i j := by
  have hj := j.isLt
  simp only [templateEdge, dif_neg (by omega : ¬ m + j.val < m),
    dif_pos (by omega : m + j.val < m + d)]
  congr 1
  apply Fin.ext
  dsimp only
  omega
private theorem template_right (i : I) (j : Fin m) :
    templateEdge W i ⟨m + d + j.val, by omega⟩ = W.marker j := by
  have hj := j.isLt
  simp only [templateEdge, dif_neg (by omega : ¬ m + d + j.val < m),
    dif_neg (by omega : ¬ m + d + j.val < m + d)]
  congr 1
  apply Fin.ext
  dsimp only
  omega
private def templateWord (i : I) : LegalWord G (2 * m + d) where
  edge := templateEdge W i
  legal := by
    intro j hj
    by_cases h₀ : j.val < m
    · by_cases hn : j.val + 1 < m
      · simpa only [templateEdge, dif_pos h₀, dif_pos hn] using
          L.marker_legal ⟨j.val, h₀⟩ hn
      · have he : j.val = m - 1 := by omega
        have he' : j.val + 1 = m := by omega
        have hd := L.data_pos
        simp only [templateEdge, dif_pos h₀, dif_neg hn,
          dif_pos (by omega : j.val + 1 < m + d)]
        have hs : (⟨j.val + 1 - m, by omega⟩ : Fin d) = ⟨0, hd⟩ := by
          apply Fin.ext; dsimp only; omega
        have ht : (⟨j.val, h₀⟩ : Fin m) = ⟨m - 1, by omega⟩ := Fin.ext he
        rw [hs, ht, L.marker_target, L.data_source]
    · by_cases h₁ : j.val < m + d
      · by_cases hn : j.val + 1 < m + d
        · have hn₀ : ¬ j.val + 1 < m := by omega
          simp only [templateEdge, dif_neg h₀, dif_pos h₁, dif_neg hn₀, dif_pos hn]
          convert L.data_legal i ⟨j.val - m, by omega⟩ (by dsimp; omega) using 1
          congr 2
          apply Fin.ext
          dsimp only
          omega
        · have hn₀ : ¬ j.val + 1 < m := by omega
          have hd := L.data_pos
          have hm := W.marker_pos
          simp only [templateEdge, dif_neg h₀, dif_pos h₁, dif_neg hn₀, dif_neg hn]
          have hs : (⟨j.val + 1 - m - d, by omega⟩ : Fin m) = ⟨0, hm⟩ := by
            apply Fin.ext; dsimp only; omega
          have ht : (⟨j.val - m, by omega⟩ : Fin d) = ⟨d - 1, by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          rw [hs, ht, L.data_target, L.marker_source]
      · have hn₀ : ¬ j.val + 1 < m := by omega
        have hn₁ : ¬ j.val + 1 < m + d := by omega
        simp only [templateEdge, dif_neg h₀, dif_neg h₁, dif_neg hn₀, dif_neg hn₁]
        convert L.marker_legal ⟨j.val - m - d, by omega⟩ (by dsimp; omega) using 1
        congr 2
        apply Fin.ext
        dsimp only
        omega

/-- Positive legal-word realization makes the original-history action faithful. -/
theorem action_injective [Fintype V] [Fintype E] [DecidableEq V]
    [TopologicalSpace V] [DiscreteTopology V]
    [TopologicalSpace E] [DiscreteTopology E] (hG : Essential G) :
    Function.Injective (action W G L) := by
  intro pi tau he
  apply Equiv.ext
  intro i
  let w := templateWord W G L i
  have hm := W.marker_pos
  obtain ⟨x, hx⟩ := exists_history_containing G hG w (by omega)
  have hs : Selected W x.val 0 i := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hj := hx ⟨j.val, by omega⟩
      simpa only [w, templateWord, template_left, zero_add] using hj
    · intro j
      have hj := hx ⟨m + d + j.val, by omega⟩
      simp only [w, templateWord, template_right] at hj
      simpa only [zero_add, Int.natCast_add, add_assoc] using hj
    · intro j
      have hj := hx ⟨m + j.val, by omega⟩
      simpa only [w, templateWord, template_data, zero_add, Int.natCast_add] using hj
  apply W.data_injective
  funext j
  have ha := congrArg (fun f : StandardBeamHomeomorphisms.FullAut G =>
    (f.val x).val (0 + (m : ℤ) + (j.val : ℤ))) he
  change replace W pi x.val _ = replace W tau x.val _ at ha
  simpa only [replace_at_selected W pi hs j, replace_at_selected W tau hs j] using ha

end Guarded
private theorem repeatWord_not_mem {q : ℕ} (xs : List (B q)) (e : B q)
    (he : e ∉ xs) (n : ℕ) : e ∉ repeatWord xs n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simpa [repeatWord, List.mem_append] using And.intro he ih
private def markerPrefix {q k : ℕ} (hq : 1 < q) : List (B q) :=
  repeatWord (Bword hq) (2 * k + 1) ++
    [resetEdge (by omega) (zero (by omega)) 1]
private theorem marker_snoc {q k : ℕ} (hq : 1 < q) :
    markerWord (k := k) hq = markerPrefix (k := k) hq ++ [markerTerminalEdge hq] := by
  simp [markerPrefix, markerWord, Aword, markerTerminalEdge, List.append_assoc]
private theorem markerPrefix_not_mem_terminal {q k : ℕ} (hq : 1 < q) :
    markerTerminalEdge hq ∉ markerPrefix (k := k) hq := by
  have h := repeatWord_not_mem (Bword hq) (markerTerminalEdge hq)
    (markerTerminalEdge_not_mem_Bword hq) (2 * k + 1)
  have ht : markerTerminalEdge hq ≠ resetEdge (by omega) (zero (by omega)) 1 := by
    simp [markerTerminalEdge, resetEdge, zeta]
  simpa [markerPrefix, List.mem_append] using And.intro h ht
private theorem marker_terminal_unique {q k : ℕ} (hq : 1 < q)
    (j : Fin (markerWord (k := k) hq).length)
    (hj : (markerWord (k := k) hq).get j = markerTerminalEdge hq) :
    j.val = (markerWord (k := k) hq).length - 1 := by
  have hlen : (markerWord (k := k) hq).length = (markerPrefix (k := k) hq).length + 1 := by
    rw [marker_snoc hq, List.length_append]
    simp
  by_contra hne
  have hlt : j.val < (markerPrefix (k := k) hq).length := by omega
  apply markerPrefix_not_mem_terminal hq
  have hg : (markerPrefix (k := k) hq)[j.val]'hlt = markerTerminalEdge hq := by
    simpa only [marker_snoc hq, List.get_eq_getElem,
      List.getElem_append_left hlt] using hj
  rw [← hg]
  exact List.getElem_mem hlt
private theorem dataChunk_injective {q : ℕ} (hq : 1 < q) :
    Function.Injective (dataChunk hq) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · have hh := congrArg (fun xs : List (B q) => xs[1]?) h
    simp [dataChunk, repeatWord, Aword, Bword, chainEdge, resetEdge] at hh
  · have hh := congrArg (fun xs : List (B q) => xs[1]?) h
    simp [dataChunk, repeatWord, Aword, Bword, chainEdge, resetEdge] at hh
  · rfl
private theorem dataWord_injective {q k : ℕ} (hq : 1 < q) :
    Function.Injective (dataWord (k := k) hq) := by
  induction k with
  | zero => intro f g h; exact Subsingleton.elim _ _
  | succ k ih =>
      intro f g h
      have he : dataChunk hq (f 0) ++ dataWord hq (fun j => f j.succ) =
          dataChunk hq (g 0) ++ dataWord hq (fun j => g j.succ) := by
        simpa only [dataWord, List.ofFn_succ, List.flatten_cons] using h
      have hh := congrArg (List.take 6) he
      have ht := congrArg (List.drop 6) he
      rw [List.take_left' (dataChunk_length hq (f 0)),
        List.take_left' (dataChunk_length hq (g 0))] at hh
      rw [List.drop_left' (dataChunk_length hq (f 0)),
        List.drop_left' (dataChunk_length hq (g 0))] at ht
      have hx : f 0 = g 0 := dataChunk_injective hq hh
      have hy : (fun j : Fin k => f j.succ) = fun j => g j.succ := ih ht
      funext j
      refine Fin.cases hx (fun i => congrFun hy i) j

/-- Actual numbered expanded edges in the finite marker. -/
def resetMarker {q k : ℕ} (hq : 1 < q) :
    Fin (6 * k + 5) → CountedGroupOverlap.Edge (resetMatrix q) × Sign := fun j =>
  originalEdge (by omega) ((markerWord (k := k) hq).get
    ⟨j.val, by rw [markerWord_length hq]; exact j.isLt⟩)

/-- Actual numbered expanded edges in each data word. -/
def resetData {q k : ℕ} (hq : 1 < q) (b : Fin k → Bool) :
    Fin (6 * k) → CountedGroupOverlap.Edge (resetMatrix q) × Sign := fun j =>
  originalEdge (by omega) ((dataWord hq b).get
    ⟨j.val, by rw [dataWord_length hq b]; exact j.isLt⟩)
private theorem resetMarker_unique_terminal {q k : ℕ} (hq : 1 < q)
    (j : Fin (6 * k + 5))
    (hj : resetMarker (k := k) hq j =
      resetMarker (k := k) hq ⟨6 * k + 4, by omega⟩) :
    j.val = 6 * k + 4 := by
  have he := (actualEdgeEquiv (by omega : 0 < q)).injective hj
  have hlast : (markerWord (k := k) hq).get
      ⟨6 * k + 4, by rw [markerWord_length hq]; omega⟩ = markerTerminalEdge hq := by
    have hlen : (markerPrefix (k := k) hq).length = 6 * k + 4 := by
      have hm := markerWord_length (k := k) hq
      rw [marker_snoc hq, List.length_append] at hm
      simp only [List.length_singleton] at hm
      omega
    simp only [marker_snoc hq, List.get_eq_getElem,
      List.getElem_append_right (by omega : (markerPrefix (k := k) hq).length ≤ 6 * k + 4),
      hlen, Nat.sub_self, List.getElem_cons_zero]
  have hu := marker_terminal_unique (k := k) hq
    ⟨j.val, by rw [markerWord_length hq]; exact j.isLt⟩ (he.trans hlast)
  simpa [markerWord_length hq] using hu
private theorem resetData_injective {q k : ℕ} (hq : 1 < q) :
    Function.Injective (resetData (k := k) hq) := by
  intro f g he
  apply dataWord_injective hq
  apply List.ext_get (by rw [dataWord_length hq f, dataWord_length hq g])
  intro n hn hm
  have hj : n < 6 * k := by simpa [dataWord_length hq f] using hn
  exact (actualEdgeEquiv (by omega : 0 < q)).injective (congrFun he ⟨n, hj⟩)

/-- The finite-word hypotheses are discharged on the original expanded ResetGraph edges. -/
def resetWords {q k : ℕ} (hq : 1 < q) :
    Guarded.Words (CountedGroupOverlap.Edge (resetMatrix q) × Sign)
      (Fin k → Bool) (6 * k + 5) (6 * k) where
  marker := resetMarker hq
  data := resetData hq
  marker_pos := by omega
  data_short := by omega
  marker_unbordered := Guarded.noPartialOverlap_of_unique_terminal (resetMarker hq)
    (by omega) (by
      intro j hj
      exact resetMarker_unique_terminal hq j (by simpa using hj))
  data_injective := resetData_injective hq
private theorem listPath_first {q : ℕ} {hq : 0 < q} {v z : Vertex q}
    {xs : List (B q)} (hp : ListPath hq v xs z) (hn : 0 < xs.length) :
    sourceB (xs.get ⟨0, hn⟩) = v := by
  cases hp with
  | nil => simp at hn
  | cons hs tail => exact hs
private theorem listPath_last {q : ℕ} {hq : 0 < q} {v z : Vertex q}
    {xs : List (B q)} (hp : ListPath hq v xs z) :
    ∀ hn : 0 < xs.length,
      targetB hq (xs.get ⟨xs.length - 1, by omega⟩) = z := by
  induction hp with
  | nil => intro hn; simp at hn
  | @cons v z x xs hs tail ih =>
      intro hn
      cases xs with
      | nil => cases tail; rfl
      | cons y ys =>
          simpa only [List.length_cons, Nat.add_sub_cancel,
            List.get_eq_getElem, List.getElem_cons_succ] using ih (by simp)
private theorem listPath_seam {q : ℕ} {hq : 0 < q} {v z : Vertex q}
    {xs : List (B q)} (hp : ListPath hq v xs z) :
    ∀ j : ℕ, ∀ hj : j + 1 < xs.length,
      targetB hq (xs.get ⟨j, by omega⟩) = sourceB (xs.get ⟨j + 1, hj⟩) := by
  induction hp with
  | nil => intro j hj; simp at hj
  | @cons v z x xs hs tail ih =>
      intro j hj
      cases j with
      | zero =>
          have hxs : 0 < xs.length := by simp only [List.length_cons] at hj; omega
          simpa only [List.get_eq_getElem, List.getElem_cons_zero,
            List.getElem_cons_succ, Nat.zero_add] using (listPath_first tail hxs).symm
      | succ j =>
          have hn : j + 1 < xs.length := by simp only [List.length_cons] at hj; omega
          simpa only [List.get_eq_getElem, List.getElem_cons_succ,
            Nat.succ_eq_add_one] using ih j hn

/-- Legal marker and data loops in the actual numbered expanded graph, for k>0. -/
def resetLoops {q k : ℕ} (hq : 1 < q) (hk : 0 < k) :
    Guarded.Loops (resetWords (k := k) hq) (expandedGraph (resetMatrix q))
      (origin (by omega)) where
  data_pos := by omega
  marker_legal := by
    intro j hj
    dsimp only [resetWords, resetMarker]
    rw [actual_target, actual_source]
    exact listPath_seam (markerWord_path (k := k) (hq := hq)) j.val
      (by rw [markerWord_length hq]; exact hj)
  marker_source := by
    dsimp only [resetWords, resetMarker]
    rw [actual_source]
    exact listPath_first (markerWord_path (k := k) (hq := hq))
      (by rw [markerWord_length hq]; omega)
  marker_target := by
    dsimp only [resetWords, resetMarker]
    rw [actual_target]
    convert listPath_last (markerWord_path (k := k) (hq := hq))
      (by rw [markerWord_length hq]; omega) using 1
    congr 2
    apply Fin.ext
    dsimp only
    rw [markerWord_length hq]
  data_legal := by
    intro i j hj
    dsimp only [resetWords, resetData]
    rw [actual_target, actual_source]
    exact listPath_seam (dataWord_path (hq := hq) i) j.val
      (by rw [dataWord_length hq i]; exact hj)
  data_source := by
    intro i
    dsimp only [resetWords, resetData]
    rw [actual_source]
    exact listPath_first (dataWord_path (hq := hq) i)
      (by rw [dataWord_length hq i]; omega)
  data_target := by
    intro i
    dsimp only [resetWords, resetData]
    rw [actual_target]
    convert listPath_last (dataWord_path (hq := hq) i)
      (by rw [dataWord_length hq i]; omega) using 1
    congr 2
    apply Fin.ext
    dsimp only
    rw [dataWord_length hq i]

/-- The faithful simultaneous marker action on ALL original Reset histories. -/
def resetAction {q k : ℕ} (hq : 1 < q) (hk : 0 < k) :
    Equiv.Perm (Fin k → Bool) →*
      StandardBeamHomeomorphisms.FullAut (expandedGraph (resetMatrix q)) :=
  Guarded.action (resetWords hq) _ (resetLoops hq hk)

theorem resetAction_injective {q k : ℕ} (hq : 1 < q) (hk : 0 < k) :
    Function.Injective (resetAction hq hk) :=
  Guarded.action_injective (resetWords hq) _ (resetLoops hq hk)
    (reset_expanded_essential q (by omega))

end D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
