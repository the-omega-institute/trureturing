import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.HypercubeCritical.SignedEightCycle

/-! The local four- and five-hole calculation for a five-cube with one
forbidden odd vertex. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExcessCycles

open BalancedCriticalSpectrum (Q)

private def axes : List Nat := [1, 2, 4, 8, 16]
private def even : List Nat := [0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30]
private def odd : List Nat := [1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31]

private def neighbors (P : List Nat) (x : Nat) : List Nat :=
  (axes.map (fun i => x ^^^ i)).filter P.contains

private def selectedEven (extra : List Nat) : List Nat :=
  even.filter (fun x => x != 0 && x != 24 && !extra.contains x)

private def eligible (P : List Nat) : List Nat :=
  odd.filter (fun x => x != 8 && let d := (neighbors P x).length; decide (1 ≤ d ∧ d ≤ 3))

private def intersection (X Y : List Nat) : List Nat := X.filter Y.contains

private def forbiddenFour (rows : List (List Nat)) : Bool :=
  (rows.sublistsLen 2).any fun
    | [u, v] => decide (2 ≤ (intersection u v).length)
    | _ => false

private def forbiddenSix (rows : List (List Nat)) : Bool :=
  (rows.sublistsLen 3).any fun
    | [u, v, w] =>
        let uv := intersection u v
        let uw := intersection u w
        let vw := intersection v w
        match uv, uw, vw with
        | [a], [b], [c] => a != b && a != c && b != c
        | _, _, _ => false
    | _ => false

private def survives (P R : List Nat) (limit : Nat) : Bool :=
  let rows := R.map (neighbors P)
  decide (limit < (rows.map List.length).sum) &&
    P.all (fun x => decide ((neighbors R x).length ≤ 3)) &&
    !forbiddenFour rows && !forbiddenSix rows

private def presentWalk (support : List Nat) (start : Nat) (word : List Nat) : Bool :=
  match word with
  | [] => true
  | i :: rest =>
      let next := start ^^^ i
      support.contains next && presentWalk support next rest

private def forbiddenEight (P R : List Nat) : Bool :=
  let support := P ++ R
  support.any fun x => axes.any fun a => axes.any fun b => axes.any fun c => axes.any fun d =>
    a != b && a != c && a != d && b != c && b != d && c != d &&
      presentWalk support x [a, b, c, a] && presentWalk support x [d, c, b, d]

private def checked (h limit : Nat) : Bool :=
  ((even.filter (fun x => x != 0 && x != 24)).sublistsLen (h - 2)).all fun extra =>
    let P := selectedEven extra
    ((eligible P).sublists).all fun R =>
      !survives P R limit || forbiddenEight P R

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The kernel evaluates the finite family of local support pairs.
/-- All subcubic candidates without a square or hexagon that exceed the
four- or five-hole edge limit contain the same eight-cycle word. -/
theorem local_excess_cycles : checked 4 14 = true ∧ checked 5 19 = true := by
  constructor <;> decide +kernel

private theorem excess_word {h limit : Nat} (hc : checked h limit = true)
    (extra R : List Nat) (hextra : List.Sublist extra (even.filter (fun x => x != 0 && x != 24)))
    (hsize : extra.length = h - 2) (hR : List.Sublist R (eligible (selectedEven extra)))
    (hlarge : survives (selectedEven extra) R limit = true) :
    forbiddenEight (selectedEven extra) R = true := by
  unfold checked at hc
  have hrow := List.all_eq_true.mp hc extra (List.mem_sublistsLen.mpr ⟨hextra, hsize⟩)
  have hwalk := List.all_eq_true.mp hrow R (List.mem_sublists.mpr hR)
  simpa only [hlarge, Bool.not_true, Bool.false_or] using hwalk

private theorem transfer_walk {n : Nat} {S : Finset (Q n)} {support : List Nat}
    (point : Nat → Q n) (axis : Nat → Fin n)
    (hpoint : ∀ x ∈ support, point x ∈ S)
    (hflip : ∀ x, ∀ i ∈ axes, point (x ^^^ i) = BalancedCriticalSpectrum.flip (point x) (axis i))
    (x : Nat) (hx : x ∈ support) (word : List Nat) (hw : ∀ i ∈ word, i ∈ axes)
    (hpath : presentWalk support x word = true) :
    ∀ y ∈ (word.map axis).scanl BalancedCriticalSpectrum.flip (point x), y ∈ S := by
  induction word generalizing x with
  | nil => simpa using hpoint x hx
  | cons i rest ih =>
      simp only [presentWalk, Bool.and_eq_true, List.contains_iff_mem] at hpath
      intro y hy
      rw [List.map_cons, List.scanl_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hpoint x hx
      · rw [← hflip x i (hw i (List.mem_cons_self ..))] at hy
        exact ih (x ^^^ i) hpath.1 (fun j hj => hw j (List.mem_cons_of_mem _ hj)) hpath.2 y hy

private theorem signed_word_impossible {n : Nat} {S : Finset (Q n)} (P R : List Nat)
    (point : Nat → Q n) (axis : Nat → Fin n)
    (hinj : ∀ a ∈ axes, ∀ b ∈ axes, axis a = axis b → a = b)
    (hpoint : ∀ x ∈ P ++ R, point x ∈ S)
    (hflip : ∀ x, ∀ i ∈ axes, point (x ^^^ i) = BalancedCriticalSpectrum.flip (point x) (axis i))
    (hbal : BalancedCriticalSpectrum.IsBalanced S) (hbad : forbiddenEight P R = true) :
    False := by
  unfold forbiddenEight at hbad
  obtain ⟨x, hx, h⟩ := List.any_eq_true.mp hbad
  obtain ⟨a, ha, h⟩ := List.any_eq_true.mp h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.mp h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.mp h
  obtain ⟨d, hd, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, _⟩, hbc⟩, hbd⟩, hcd⟩, hl⟩, hr⟩ := h
  have hleft := transfer_walk point axis hpoint hflip x hx [a, b, c, a]
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> assumption) hl
  have hright := transfer_walk point axis hpoint hflip x hx [d, c, b, d]
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> assumption) hr
  exact SignedEightCycle.no_selected_eight_paths hbal (point x)
    (fun h => hab (hinj a ha b hb h)) (fun h => hac (hinj a ha c hc h))
    (fun h => hbc (hinj b hb c hc h)) (fun h => hbd (hinj b hb d hd h.symm))
    (fun h => hcd (hinj c hc d hd h.symm)) hleft hright

/-- A coordinate representation of a balanced support excludes the finite
excess-edge configurations at four and five holes. -/
theorem no_mapped_excess {n : Nat} {S : Finset (Q n)} {h limit : Nat}
    (hcase : (h = 4 ∧ limit = 14) ∨ (h = 5 ∧ limit = 19))
    (extra R : List Nat) (hextra : List.Sublist extra (even.filter (fun x => x != 0 && x != 24)))
    (hsize : extra.length = h - 2) (hR : List.Sublist R (eligible (selectedEven extra)))
    (point : Nat → Q n) (axis : Nat → Fin n)
    (hinj : ∀ a ∈ axes, ∀ b ∈ axes, axis a = axis b → a = b)
    (hpoint : ∀ x ∈ selectedEven extra ++ R, point x ∈ S)
    (hflip : ∀ x, ∀ i ∈ axes, point (x ^^^ i) = BalancedCriticalSpectrum.flip (point x) (axis i))
    (hbal : BalancedCriticalSpectrum.IsBalanced S)
    (hdegree : (selectedEven extra).all (fun x => decide ((neighbors R x).length ≤ 3)) = true)
    (hfour : forbiddenFour (R.map (neighbors (selectedEven extra))) = false)
    (hsix : forbiddenSix (R.map (neighbors (selectedEven extra))) = false) :
    (R.map (fun x => (neighbors (selectedEven extra) x).length)).sum ≤ limit := by
  by_contra! hlarge
  have hsurvives : survives (selectedEven extra) R limit = true := by
    simp only [survives, hdegree, hfour, hsix, Bool.not_false, Bool.and_true]
    apply decide_eq_true
    rw [List.map_map]
    exact hlarge
  have hc : checked h limit = true := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact local_excess_cycles.1
    · exact local_excess_cycles.2
  exact signed_word_impossible (selectedEven extra) R point axis hinj hpoint hflip hbal
    (excess_word hc extra R hextra hsize hR hsurvives)

#print axioms local_excess_cycles
#print axioms no_mapped_excess

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExcessCycles
