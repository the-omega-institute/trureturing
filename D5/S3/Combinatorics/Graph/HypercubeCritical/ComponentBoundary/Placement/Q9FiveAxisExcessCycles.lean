import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
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

private def axisIndex (i : Nat) : Fin 5 :=
  ⟨i.log2 % 5, Nat.mod_lt _ (by decide)⟩

private theorem axisIndex_pow : ∀ i : Fin 5, axisIndex (2 ^ i.val) = i := by decide

private theorem axis_word (a : Nat) (ha : a ∈ axes) : ∃ i : Fin 5, a = 2 ^ i.val := by
  simp only [axes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

open Classical in
/-- Interpret a five-bit word by translating the embedded coordinate axes. -/
private noncomputable def wordPoint {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n) (word : Nat) : Q n :=
  fun k =>
    let j := Function.invFun e k
    if e j = k then z k ^^ word.testBit j.val else z k

open Classical in
private theorem wordPoint_flip {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n)
    (word : Nat) (i : Fin 5) :
    wordPoint e z (word ^^^ 2 ^ i.val) =
      BalancedCriticalSpectrum.flip (wordPoint e z word) (e i) := by
  funext k
  have hinv : Function.LeftInverse (Function.invFun e) e :=
    Function.leftInverse_invFun e.injective
  by_cases hki : k = e i
  · subst k
    simp [wordPoint, hinv i, Nat.testBit_xor]
  · by_cases hk : e (Function.invFun e k) = k
    · have hij : i.val ≠ (Function.invFun e k).val := by
        intro he
        exact hki (hk.symm.trans (congrArg e (Fin.ext he)).symm)
      simp [wordPoint, hk, BalancedCriticalSpectrum.flip, hki,
        Nat.testBit_xor, hij]
    · simp [wordPoint, hk, BalancedCriticalSpectrum.flip, hki]

open Classical in
private theorem wordPoint_coord {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n)
    (w : Nat) (i : Fin 5) : wordPoint e z w (e i) = (z (e i) ^^ w.testBit i.val) := by
  have h : Function.LeftInverse (Function.invFun e) e :=
    Function.leftInverse_invFun e.injective
  simp [wordPoint, h i]

open Classical in
private theorem wordPoint_zero {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n) :
    wordPoint e z 0 = z := by
  funext k
  simp [wordPoint]

open Classical in
private theorem wordPoint_xor_axis {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n)
    (w a : Nat) (ha : a ∈ axes) :
    wordPoint e z (w ^^^ a) =
      BalancedCriticalSpectrum.flip (wordPoint e z w) (e (axisIndex a)) := by
  obtain ⟨i, rfl⟩ := axis_word a ha
  rw [axisIndex_pow]
  exact wordPoint_flip e z w i

open Classical in
private theorem wordPoint_sameFibre {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n)
    (w : Nat) {k : Fin n} (hk : k ∉ Finset.univ.map e) : wordPoint e z w k = z k := by
  have h : e (Function.invFun e k) ≠ k := by
    intro he
    exact hk (Finset.mem_map.mpr ⟨_, Finset.mem_univ _, he⟩)
  simp [wordPoint, h]

open Classical in
private theorem wordPoint_injOn {n : Nat} (e : Fin 5 ↪ Fin n) (z : Q n)
    {u v : Nat} (hu : u < 32) (hv : v < 32) (h : wordPoint e z u = wordPoint e z v) :
    u = v := by
  have hb : BitVec.ofNat 5 u = BitVec.ofNat 5 v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have he := congrFun h (e ⟨i, hi⟩)
    rw [wordPoint_coord, wordPoint_coord] at he
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    cases hz : z (e ⟨i, hi⟩) <;> simpa [hz] using he
  have hn := congrArg BitVec.toNat hb
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using hn

open Classical in
private theorem wordPoint_surj {n : Nat} (e : Fin 5 ↪ Fin n) (z x : Q n)
    (hf : ∀ k ∉ Finset.univ.map e, x k = z k) :
    ∃ w < 32, wordPoint e z w = x := by
  let bits := (cubeBitVec 5).symm (fun i => z (e i) ^^ x (e i))
  refine ⟨bits.toNat, bits.isLt, ?_⟩
  funext k
  by_cases hk : k ∈ Finset.univ.map e
  · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
    rw [wordPoint_coord]
    have he : bits.toNat.testBit i.val = (z (e i) ^^ x (e i)) :=
      congrFun ((cubeBitVec 5).apply_symm_apply (fun j => z (e j) ^^ x (e j))) i
    rw [he]
    cases z (e i) <;> cases x (e i) <;> rfl
  · rw [wordPoint_sameFibre e z _ hk, hf k hk]

open Q9IsotropicHuang (parity)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private def setAxes (w : Nat) : List Nat := axes.filter (fun a => (w &&& a) != 0)

private theorem xor_setAxes : ∀ w : Fin 32,
    (setAxes w.val).foldl Nat.xor 0 = w.val := by decide

private theorem odd_eq_setAxes : ∀ w : Fin 32,
    w.val ∈ odd ↔ ((setAxes w.val).length % 2 = 1) := by decide

private theorem parity_wordPoint_fold (e : Fin 5 ↪ Fin 9) (z : Q 9)
    (word : List Nat) (hword : ∀ a ∈ word, a ∈ axes) (start : Nat) :
    parity (wordPoint e z (word.foldl Nat.xor start)) =
      (parity (wordPoint e z start) ^^ decide (word.length % 2 = 1)) := by
  induction word generalizing start with
  | nil => simp
  | cons a rest ih =>
      rw [List.foldl_cons, ih (fun x hx => hword x (List.mem_cons_of_mem _ hx))]
      change (parity (wordPoint e z (start ^^^ a)) ^^ _) = _
      rw [wordPoint_xor_axis e z start a (hword a (List.mem_cons_self ..)), parity_flip]
      have hmod : (rest.length + 1) % 2 = 1 ↔ rest.length % 2 ≠ 1 := by omega
      simp only [List.length_cons, hmod, decide_not]
      cases parity (wordPoint e z start) <;> cases decide (rest.length % 2 = 1) <;> rfl

private theorem parity_wordPoint (e : Fin 5 ↪ Fin 9) (z : Q 9) {w : Nat} (hw : w < 32) :
    parity (wordPoint e z w) = (parity z ^^ decide (w ∈ odd)) := by
  have hx := xor_setAxes ⟨w, hw⟩
  have hp := parity_wordPoint_fold e z (setAxes w)
    (fun a ha => (List.mem_filter.mp ha).1) 0
  rw [hx, wordPoint_zero] at hp
  simpa only [odd_eq_setAxes ⟨w, hw⟩] using hp

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open SimpleGraph (Walk)

private theorem mem_neighbors_iff {P : List Nat} {u v : Nat} :
    v ∈ neighbors P u ↔ v ∈ P ∧ ∃ a ∈ axes, u ^^^ a = v := by
  simp only [neighbors, List.mem_filter, List.mem_map, List.contains_iff_mem]
  tauto

private theorem neighbor_adj {n : Nat} (point : Nat → Q n) (axis : Nat → Fin n)
    (hflip : ∀ x, ∀ i ∈ axes,
      point (x ^^^ i) = BalancedCriticalSpectrum.flip (point x) (axis i))
    {P : List Nat} {u v : Nat} (hv : v ∈ neighbors P u) :
    (hypercube n).Adj (point u) (point v) := by
  obtain ⟨_, a, ha, rfl⟩ := mem_neighbors_iff.mp hv
  rw [hflip u a ha]
  exact BalancedCriticalSpectrum.flip_adj _ _

private theorem neighbors_nodup (P : List Nat) (u : Nat) : (neighbors P u).Nodup := by
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro a b h
    have he := congrArg (Nat.xor u) h
    change u ^^^ (u ^^^ a) = u ^^^ (u ^^^ b) at he
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using he
  · decide

private theorem no_short_cycles_in_rows {n : Nat} {S : Finset (Q n)} (P R : List Nat)
    (hnodup : R.Nodup) (hsep : ∀ u ∈ R, ∀ v ∈ P, u ≠ v)
    (point : Nat → Q n) (axis : Nat → Fin n)
    (hinj : ∀ u ∈ P ++ R, ∀ v ∈ P ++ R, point u = point v → u = v)
    (hpoint : ∀ x ∈ P ++ R, point x ∈ S)
    (hflip : ∀ x, ∀ i ∈ axes,
      point (x ^^^ i) = BalancedCriticalSpectrum.flip (point x) (axis i))
    (hbal : BalancedCriticalSpectrum.IsBalanced S) :
    forbiddenFour (R.map (neighbors P)) = false ∧
      forbiddenSix (R.map (neighbors P)) = false := by
  let f (x : Nat) (hx : x ∈ P ++ R) : (S : Set (Q n)) := ⟨point x, hpoint x hx⟩
  let G := (hypercube n).induce (S : Set (Q n))
  have fR {x : Nat} (hx : x ∈ R) : x ∈ P ++ R := List.mem_append.mpr (Or.inr hx)
  have fP {x : Nat} (hx : x ∈ P) : x ∈ P ++ R := List.mem_append.mpr (Or.inl hx)
  have near {x y : Nat} (hx : x ∈ R) (hy : y ∈ neighbors P x) :
      G.Adj (f x (fR hx)) (f y (fP (mem_neighbors_iff.mp hy).1)) :=
    neighbor_adj point axis hflip hy
  have fne {x y : Nat} {hx : x ∈ P ++ R} {hy : y ∈ P ++ R} (h : x ≠ y) :
      f x hx ≠ f y hy := fun he => h (hinj x hx y hy (congrArg Subtype.val he))
  have pair_members {L : List Nat} (hn : L.Nodup) (hl : 2 ≤ L.length) :
      ∃ x ∈ L, ∃ y ∈ L, x ≠ y := by
    cases L with
    | nil => simp at hl
    | cons x tail =>
      cases tail with
      | nil => simp at hl
      | cons y rest =>
        exact ⟨x, by simp, y, by simp, fun he => (List.nodup_cons.mp hn).1 (by simp [he])⟩
  constructor
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨L, hL, h⟩ := List.any_eq_true.mp h
    obtain ⟨sub, hsub, rfl⟩ :=
      List.sublist_map_iff.mp (List.mem_sublistsLen.mp hL).1
    have hlen : sub.length = 2 := by simpa using (List.mem_sublistsLen.mp hL).2
    obtain ⟨u, v, rfl⟩ := List.length_eq_two.mp hlen
    have hu : u ∈ R := hsub.subset (by simp)
    have hv : v ∈ R := hsub.subset (by simp)
    have huv := List.not_nodup_pair u
    have hn : u ≠ v := by
      intro he
      subst v
      exact huv (hnodup.sublist hsub)
    have hl : 2 ≤ (intersection (neighbors P u) (neighbors P v)).length := by
      simpa only [List.map_cons, List.map_nil, decide_eq_true_eq] using h
    obtain ⟨a, ha, b, hb, hab⟩ := pair_members
      ((neighbors_nodup P u).filter _) hl
    simp only [List.mem_filter, List.contains_iff_mem] at ha hb
    have hau := near hu ha.1
    have hav := near hv ha.2
    have hbu := near hu hb.1
    have hbv := near hv hb.2
    let p := Walk.cons hau (Walk.cons hav.symm (Walk.cons hbv (Walk.cons hbu.symm Walk.nil)))
    have hp : p.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_, by simp [p]⟩
      simp only [p, Walk.getVert_cons_succ, Walk.tail_cons, Walk.isPath_copy]
      have haP := (mem_neighbors_iff.mp ha.1).1
      have hbP := (mem_neighbors_iff.mp hb.1).1
      let U := f u (fR hu)
      let V := f v (fR hv)
      let A := f a (fP haP)
      let B := f b (fP hbP)
      rw [Walk.isPath_def]
      change [A, V, B, U].Nodup
      have hav' : A ≠ V :=
        fne (hx := fP haP) (hy := fR hv) (hsep v hv a haP).symm
      have hab' : A ≠ B :=
        fne (hx := fP haP) (hy := fP hbP) hab
      have hau' : A ≠ U :=
        fne (hx := fP haP) (hy := fR hu) (hsep u hu a haP).symm
      have hvb' : V ≠ B :=
        fne (hx := fR hv) (hy := fP hbP) (hsep v hv b hbP)
      have hvu' : V ≠ U :=
        fne (hx := fR hv) (hy := fR hu) hn.symm
      have hbu' : B ≠ U :=
        fne (hx := fP hbP) (hy := fR hu) (hsep u hu b hbP).symm
      simp [hav', hab', hau', hvb', hvu', hbu']
    exact BalancedCubeGirth.no_four_cycle hbal p hp (by rfl)
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨L, hL, h⟩ := List.any_eq_true.mp h
    obtain ⟨sub, hsub, rfl⟩ :=
      List.sublist_map_iff.mp (List.mem_sublistsLen.mp hL).1
    have hlen : sub.length = 3 := by simpa using (List.mem_sublistsLen.mp hL).2
    obtain ⟨u, v, w, rfl⟩ := List.length_eq_three.mp hlen
    have hu : u ∈ R := hsub.subset (by simp)
    have hv : v ∈ R := hsub.subset (by simp)
    have hw : w ∈ R := hsub.subset (by simp)
    have hn : u ≠ v ∧ u ≠ w ∧ v ≠ w := by
      simpa [and_assoc] using hnodup.sublist hsub
    simp only [List.map_cons, List.map_nil] at h
    generalize ea : intersection (neighbors P u) (neighbors P v) = A at h
    generalize eb : intersection (neighbors P u) (neighbors P w) = B at h
    generalize ec : intersection (neighbors P v) (neighbors P w) = C at h
    obtain ⟨a, b, c, rfl, rfl, rfl, hab, hac, hbc⟩ :
        ∃ a b c : Nat, A = [a] ∧ B = [b] ∧ C = [c] ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      rcases A with _ | ⟨a, _ | ⟨a', as⟩⟩ <;> try contradiction
      rcases B with _ | ⟨b, _ | ⟨b', bs⟩⟩ <;> try contradiction
      rcases C with _ | ⟨c, _ | ⟨c', cs⟩⟩ <;> try contradiction
      simp only [Bool.and_eq_true, bne_iff_ne] at h
      exact ⟨a, b, c, rfl, rfl, rfl, h.1.1, h.1.2, h.2⟩
    have ha : a ∈ neighbors P u ∧ a ∈ neighbors P v := by
      have hm : a ∈ intersection (neighbors P u) (neighbors P v) := by simp [ea]
      simpa only [intersection, List.mem_filter, List.contains_iff_mem] using hm
    have hb : b ∈ neighbors P u ∧ b ∈ neighbors P w := by
      have hm : b ∈ intersection (neighbors P u) (neighbors P w) := by simp [eb]
      simpa only [intersection, List.mem_filter, List.contains_iff_mem] using hm
    have hc : c ∈ neighbors P v ∧ c ∈ neighbors P w := by
      have hm : c ∈ intersection (neighbors P v) (neighbors P w) := by simp [ec]
      simpa only [intersection, List.mem_filter, List.contains_iff_mem] using hm
    let p := Walk.cons (near hu ha.1) (Walk.cons (near hv ha.2).symm
      (Walk.cons (near hv hc.1) (Walk.cons (near hw hc.2).symm
        (Walk.cons (near hw hb.2) (Walk.cons (near hu hb.1).symm Walk.nil)))))
    have hp : p.IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_, by simp [p]⟩
      simp only [p, Walk.getVert_cons_succ, Walk.tail_cons, Walk.isPath_copy]
      have haP := (mem_neighbors_iff.mp ha.1).1
      have hbP := (mem_neighbors_iff.mp hb.1).1
      have hcP := (mem_neighbors_iff.mp hc.1).1
      let U := f u (fR hu)
      let V := f v (fR hv)
      let W := f w (fR hw)
      let A := f a (fP haP)
      let B := f b (fP hbP)
      let C := f c (fP hcP)
      rw [Walk.isPath_def]
      change [A, V, C, W, B, U].Nodup
      have hav' : A ≠ V :=
        fne (hx := fP haP) (hy := fR hv) (hsep v hv a haP).symm
      have hac' : A ≠ C :=
        fne (hx := fP haP) (hy := fP hcP) hac
      have haw' : A ≠ W :=
        fne (hx := fP haP) (hy := fR hw) (hsep w hw a haP).symm
      have hab' : A ≠ B :=
        fne (hx := fP haP) (hy := fP hbP) hab
      have hau' : A ≠ U :=
        fne (hx := fP haP) (hy := fR hu) (hsep u hu a haP).symm
      have hvc' : V ≠ C :=
        fne (hx := fR hv) (hy := fP hcP) (hsep v hv c hcP)
      have hvw' : V ≠ W :=
        fne (hx := fR hv) (hy := fR hw) hn.2.2
      have hvb' : V ≠ B :=
        fne (hx := fR hv) (hy := fP hbP) (hsep v hv b hbP)
      have hvu' : V ≠ U :=
        fne (hx := fR hv) (hy := fR hu) hn.1.symm
      have hcw' : C ≠ W :=
        fne (hx := fP hcP) (hy := fR hw) (hsep w hw c hcP).symm
      have hcb' : C ≠ B :=
        fne (hx := fP hcP) (hy := fP hbP) hbc.symm
      have hcu' : C ≠ U :=
        fne (hx := fP hcP) (hy := fR hu) (hsep u hu c hcP).symm
      have hwb' : W ≠ B :=
        fne (hx := fR hw) (hy := fP hbP) (hsep w hw b hbP)
      have hwu' : W ≠ U :=
        fne (hx := fR hw) (hy := fR hu) hn.2.1.symm
      have hbu' : B ≠ U :=
        fne (hx := fP hbP) (hy := fR hu) (hsep u hu b hbP).symm
      simp [hav', hac', haw', hab', hau', hvc', hvw', hvb', hvu', hcw', hcb', hcu', hwb', hwu', hbu']
    exact BalancedCubeGirth.no_six_cycle hbal p hp (by rfl)

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9InactiveContactFibre (freeEdges restrictToFibre sameFibre)

private theorem even_bounds : ∀ w ∈ even, w < 32 := by decide
private theorem odd_bounds : ∀ w ∈ odd, w < 32 := by decide
private theorem even_odd_disjoint : ∀ w ∈ even, w ∉ odd := by decide
private theorem even_odd_total : ∀ w : Fin 32, w.val ∈ even ∨ w.val ∈ odd := by decide
private theorem even_xor_axis : ∀ w ∈ even, ∀ a ∈ axes, w ^^^ a ∈ odd := by decide

private theorem wordPoint_mem_even (e : Fin 5 ↪ Fin 9) (z : Q 9)
    {w : Nat} (hw : w < 32) : w ∈ even ↔ parity (wordPoint e z w) = parity z := by
  rw [parity_wordPoint e z hw]
  have h : w ∈ even ↔ w ∉ odd :=
    ⟨even_odd_disjoint w, fun h => (even_odd_total ⟨w, hw⟩).resolve_right h⟩
  cases parity z <;> simp [h]

private theorem axisCode_mem : ∀ i : Fin 5, (2 ^ i.val : Nat) ∈ axes := by decide

private theorem degree_of_neighbors (S : Finset (Q 9)) (e : Fin 5 ↪ Fin 9) (z : Q 9)
    (P : List Nat) (x : Nat)
    (hP : ∀ w ∈ P, wordPoint e z w ∈ S)
    (hdeg : ∀ y ∈ S, (directions S y).card ≤ 3) (hx : wordPoint e z x ∈ S) :
    (neighbors P x).length ≤ 3 := by
  classical
  have hcard := List.toFinset_card_of_nodup (neighbors_nodup P x)
  rw [← hcard]
  let transport (w : Nat) := e (axisIndex (x ^^^ w))
  have hinj : Set.InjOn transport (neighbors P x).toFinset := by
    intro u hu v hv he
    obtain ⟨_, a, ha, rfl⟩ := mem_neighbors_iff.mp (List.mem_toFinset.mp hu)
    obtain ⟨_, b, hb, rfl⟩ := mem_neighbors_iff.mp (List.mem_toFinset.mp hv)
    change e (axisIndex (x ^^^ (x ^^^ a))) = e (axisIndex (x ^^^ (x ^^^ b))) at he
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at he
    obtain ⟨i, rfl⟩ := axis_word a ha
    obtain ⟨j, rfl⟩ := axis_word b hb
    rw [axisIndex_pow, axisIndex_pow] at he
    rw [e.injective he]
  rw [← Finset.card_image_of_injOn hinj]
  apply (Finset.card_le_card (t := directions S (wordPoint e z x)) ?_).trans (hdeg _ hx)
  intro i hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hwP, a, ha, rfl⟩ := mem_neighbors_iff.mp (List.mem_toFinset.mp hw)
  have hxw : x ^^^ (x ^^^ a) = a := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  apply (mem_directions _ _ _).mpr
  rw [show transport (x ^^^ a) = e (axisIndex a) from congrArg (e ∘ axisIndex) hxw,
    ← wordPoint_xor_axis e z x a ha]
  exact hP _ hwP

private theorem list_edge_count (P R : List Nat) (hR : R.Nodup) :
    (R.toFinset.biUnion fun y =>
      (neighbors P y).toFinset.image (fun x => (y, x))).card =
      (R.map (fun y => (neighbors P y).length)).sum := by
  classical
  induction R with
  | nil => simp
  | cons y tail ih =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hR
      have hmem : y ∉ tail.toFinset := by simpa using hn
      rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint]
      · rw [ih ht]
        rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
        simp [List.toFinset_card_of_nodup (neighbors_nodup P y)]
      · apply Finset.disjoint_left.mpr
        rintro ⟨v, x⟩ hv hv'
        obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.mp hv'
        obtain ⟨_, _, e₁⟩ := Finset.mem_image.mp hv
        obtain ⟨_, _, e₂⟩ := Finset.mem_image.mp hx
        have he : y = u := congrArg Prod.fst (e₁.trans e₂.symm)
        exact hmem (he ▸ hu)

private theorem word_edge_equiv_count
    (S : Finset (Q 9)) (e : Fin 5 ↪ Fin 9) (z : Q 9)
    (P R : List Nat) (hn : R.Nodup)
    (hP : ∀ x, x ∈ P ↔ x ∈ even ∧ wordPoint e z x ∈ S)
    (hR : ∀ y, y ∈ R ↔ y ∈ odd ∧ wordPoint e z y ∈ S ∧ (neighbors P y).length ≠ 0) :
    let A := univ.map e
    let L := (restrictToFibre S A z).filter (fun v => parity v = parity z)
    (freeEdges S L A).card = (R.map (fun y => (neighbors P y).length)).sum := by
  classical
  intro A L
  let edges := R.toFinset.biUnion (fun y =>
    (neighbors P y).toFinset.image (fun x => (y, x)))
  have hmem {y x : Nat} : (y, x) ∈ edges ↔ y ∈ R ∧ x ∈ neighbors P y := by
    simp [edges, and_comm, and_left_comm]
  let encode (p : Nat × Nat) : Q 9 × Fin 9 :=
    (wordPoint e z p.2, e (axisIndex (p.1 ^^^ p.2)))
  have hflip {y x : Nat} (hx : x ∈ neighbors P y) :
      flip (wordPoint e z x) (e (axisIndex (y ^^^ x))) = wordPoint e z y := by
    obtain ⟨_, a, ha, rfl⟩ := mem_neighbors_iff.mp hx
    have he : y ^^^ (y ^^^ a) = a := by
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [he, wordPoint_xor_axis e z y a ha, BalancedCriticalSpectrum.flip_flip]
  rw [← list_edge_count P R hn]
  symm
  apply Finset.card_bij (s := edges) (t := freeEdges S L A) (fun p _ => encode p)
  · rintro ⟨y, x⟩ hb
    obtain ⟨hy, hx⟩ := hmem.mp hb
    obtain ⟨hxe, hxS⟩ := (hP x).mp (mem_neighbors_iff.mp hx).1
    have hxL : wordPoint e z x ∈ L := by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hxS, ?_⟩, ?_⟩
      · exact fun k hk => wordPoint_sameFibre e z x hk
      · exact (wordPoint_mem_even e z (even_bounds _ hxe)).mp hxe
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨hxL, mem_map.mpr ⟨_, mem_univ _, rfl⟩⟩,
      by simpa only [encode, hflip hx] using ((hR y).mp hy).2.1⟩
  · rintro ⟨y, x⟩ hb ⟨v, u⟩ hc he
    obtain ⟨hy, hx⟩ := hmem.mp hb
    obtain ⟨hv, hu⟩ := hmem.mp hc
    have hxe := ((hP x).mp (mem_neighbors_iff.mp hx).1).1
    have hue := ((hP u).mp (mem_neighbors_iff.mp hu).1).1
    have hex : x = u := wordPoint_injOn e z (even_bounds x hxe) (even_bounds u hue)
      (congrArg Prod.fst he)
    have he' := congrArg (fun p : Q 9 × Fin 9 => flip p.1 p.2) he
    change flip (wordPoint e z x) (e (axisIndex (y ^^^ x))) =
      flip (wordPoint e z u) (e (axisIndex (v ^^^ u))) at he'
    rw [hflip hx, hflip hu] at he'
    have hey := wordPoint_injOn e z (odd_bounds y ((hR y).mp hy).1)
      (odd_bounds v ((hR v).mp hv).1) he'
    rw [hex, hey]
  · rintro ⟨p, i⟩ hi
    obtain ⟨hpi, hflipS⟩ := mem_filter.mp hi
    obtain ⟨hp, hia⟩ := mem_product.mp hpi
    obtain ⟨hpS, hpF⟩ := mem_filter.mp (mem_filter.mp hp).1
    have hpParity := (mem_filter.mp hp).2
    obtain ⟨a, _, rfl⟩ := mem_map.mp hia
    obtain ⟨x, hx, rfl⟩ := wordPoint_surj e z p hpF
    have hxe := (wordPoint_mem_even e z hx).mpr hpParity
    let y := x ^^^ 2 ^ a.val
    have ha := axisCode_mem a
    have hyO : y ∈ odd := even_xor_axis x hxe _ ha
    have hyS : wordPoint e z y ∈ S := by
      simpa only [y, wordPoint_flip] using hflipS
    have hyx : y ^^^ 2 ^ a.val = x := by simp [y, Nat.xor_assoc]
    have hnx : x ∈ neighbors P y := mem_neighbors_iff.mpr
      ⟨(hP x).mpr ⟨hxe, hpS⟩, _, ha, hyx⟩
    have hn' : (neighbors P y).length ≠ 0 := by
      intro he
      simp [List.length_eq_zero_iff.mp he] at hnx
    have hyR := (hR y).mpr ⟨hyO, hyS, hn'⟩
    refine ⟨(y, x), hmem.mpr ⟨hyR, hnx⟩, ?_⟩
    have hxya : y ^^^ x = 2 ^ a.val := by
      dsimp [y]
      rw [Nat.xor_comm x (2 ^ a.val), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    simp [encode, hxya, axisIndex_pow]

open Classical in
private theorem normalized_local_capacity (S : Finset (Q 9)) (e : Fin 5 ↪ Fin 9) (z : Q 9)
    (hbal : BalancedCriticalSpectrum.IsBalanced S)
    (hdeg : ∀ x ∈ S, (directions S x).card ≤ 3)
    (h0 : wordPoint e z 0 ∉ S) (h8 : wordPoint e z 8 ∉ S) (h24 : wordPoint e z 24 ∉ S) :
    let A := univ.map e
    let L := (restrictToFibre S A z).filter (fun v => parity v = parity z)
    let H := (restrictToFibre univ A z).filter (fun v => parity v = parity z ∧ v ∉ S)
    H.card = 4 ∨ H.card = 5 → (freeEdges S L A).card + 6 ≤ 5 * H.card := by
  intro A L H hcase
  let point := wordPoint e z
  let extra := (even.filter (fun x => x != 0 && x != 24)).filter
    (fun x => decide (point x ∉ S))
  let P := selectedEven extra
  let R := (eligible P).filter (fun y => decide (point y ∈ S))
  have hP (x : Nat) : x ∈ P ↔ x ∈ even ∧ point x ∈ S := by
    have ht : (!extra.contains x) = true ↔ x ∉ extra := by simp
    simp only [P, selectedEven, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ht]
    have he : x ∈ extra ↔ (x ∈ even ∧ x ≠ 0 ∧ x ≠ 24) ∧ point x ∉ S := by
      simp [extra, and_comm, and_assoc]
    rw [he]
    constructor
    · tauto
    · rintro ⟨hx, hxS⟩
      have hx0 : x ≠ 0 := fun he => h0 (he ▸ hxS)
      have hx24 : x ≠ 24 := fun he => h24 (he ▸ hxS)
      tauto
  have hR (y : Nat) : y ∈ R ↔ y ∈ odd ∧ point y ∈ S ∧ (neighbors P y).length ≠ 0 := by
    simp only [R, eligible, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hy, _, hdegree⟩, hyS⟩
      exact ⟨hy, hyS, by omega⟩
    · rintro ⟨hy, hyS, hpos⟩
      refine ⟨⟨hy, fun he => h8 (he ▸ hyS), ?_, ?_⟩, hyS⟩
      · omega
      · exact degree_of_neighbors S e z P y (fun _ hx => ((hP _).mp hx).2) hdeg hyS
  have hRsub : List.Sublist R (eligible P) := List.filter_sublist
  have hRnodup : R.Nodup := by
    apply List.Nodup.filter
    apply List.Nodup.filter
    decide
  have hfibre : H.card = (even.toFinset.filter (fun w => point w ∉ S)).card := by
    symm
    apply Finset.card_bij (fun w _ => point w)
    · intro w hw
      obtain ⟨hw, hwS⟩ := mem_filter.mp hw
      have hwe := List.mem_toFinset.mp hw
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
        fun k hk => wordPoint_sameFibre e z w hk⟩,
        (wordPoint_mem_even e z (even_bounds _ hwe)).mp hwe, hwS⟩
    · intro w hw u hu h
      exact wordPoint_injOn e z (even_bounds _ (List.mem_toFinset.mp (mem_filter.mp hw).1))
        (even_bounds _ (List.mem_toFinset.mp (mem_filter.mp hu).1)) h
    · intro w hw
      obtain ⟨hwF, hwp, hwS⟩ := mem_filter.mp hw
      obtain ⟨v, hv, rfl⟩ := wordPoint_surj e z w (mem_filter.mp hwF).2
      exact ⟨v, mem_filter.mpr ⟨List.mem_toFinset.mpr
        ((wordPoint_mem_even e z hv).mpr hwp), hwS⟩, rfl⟩
  have hextra : extra.length = H.card - 2 := by
    let raw := even.toFinset.filter (fun w => point w ∉ S)
    have ha : extra.toFinset = (raw.erase 0).erase 24 := by
      ext w
      simp only [extra, raw, List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
        bne_iff_ne, decide_eq_true_eq, mem_erase, mem_filter]
      tauto
    have hnodup : extra.Nodup := ((show even.Nodup by decide).filter _).filter _
    have hz : 0 ∈ raw := mem_filter.mpr ⟨by decide, h0⟩
    have ht : 24 ∈ raw.erase 0 := mem_erase.mpr ⟨by decide, mem_filter.mpr ⟨by decide, h24⟩⟩
    have hzc := card_erase_add_one hz
    have htc := card_erase_add_one ht
    rw [← List.toFinset_card_of_nodup hnodup, ha]
    change H.card = raw.card at hfibre
    omega
  have hpoint (x : Nat) (hx : x ∈ P ++ R) : point x ∈ S := by
    rcases List.mem_append.mp hx with hx | hx
    · exact ((hP x).mp hx).2
    · exact ((hR x).mp hx).2.1
  have hword (x : Nat) (hx : x ∈ P ++ R) : x < 32 := by
    rcases List.mem_append.mp hx with hx | hx
    · exact even_bounds x ((hP x).mp hx).1
    · exact odd_bounds x ((hR x).mp hx).1
  have hcycle := no_short_cycles_in_rows P R hRnodup (by
      intro x hx y hy he
      subst y
      exact even_odd_disjoint x ((hP x).mp hy).1 ((hR x).mp hx).1)
    point (e ∘ axisIndex) (fun x hx y hy => wordPoint_injOn e z (hword x hx) (hword y hy))
    hpoint (wordPoint_xor_axis e z) hbal
  have hdegP : P.all (fun x => decide ((neighbors R x).length ≤ 3)) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    exact decide_eq_true (degree_of_neighbors S e z R x
      (fun y hy => ((hR y).mp hy).2.1) hdeg ((hP x).mp hx).2)
  have hinj : ∀ a ∈ axes, ∀ b ∈ axes, (e ∘ axisIndex) a = (e ∘ axisIndex) b → a = b := by
    intro a ha b hb h
    obtain ⟨i, rfl⟩ := axis_word a ha
    obtain ⟨j, rfl⟩ := axis_word b hb
    change e (axisIndex (2 ^ i.val)) = e (axisIndex (2 ^ j.val)) at h
    rw [axisIndex_pow, axisIndex_pow] at h
    rw [e.injective h]
  let limit := 5 * H.card - 6
  have hlimit : (H.card = 4 ∧ limit = 14) ∨ (H.card = 5 ∧ limit = 19) := by
    dsimp [limit]
    omega
  have hbound := no_mapped_excess hlimit extra R List.filter_sublist hextra hRsub point
    (e ∘ axisIndex) hinj hpoint (wordPoint_xor_axis e z) hbal hdegP hcycle.1 hcycle.2
  change (R.map (fun x => (neighbors P x).length)).sum ≤ limit at hbound
  rw [word_edge_equiv_count S e z P R hRnodup hP hR]
  dsimp [limit] at hbound
  omega

open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9InactiveContactFibre (adjacent_fibre_missing_centre)
open private flip_same_fibre from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre

open Classical in
/-- At four or five holes, a pure fibre exposed to the opposite component
loses enough free edges to satisfy the linear bound with a deficit of six. -/
theorem adjacent_fibre_four_five_hole_capacity {C D : Finset (Q 9)} (b : Bool) {x : Q 9}
    (hx : x ∈ C) (hp : parity x = b)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (e : Fin 5 ↪ Fin 9) {i j k : Fin 9}
    (hi : i ∉ univ.map e) (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmj : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hmk : ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hbal : BalancedCriticalSpectrum.IsBalanced D)
    (hdeg : ∀ v ∈ D, (directions D v).card ≤ 3) :
    let y := flip x i
    let A := univ.map e
    let L := (restrictToFibre D A y).filter (fun v => parity v = b)
    let H := (restrictToFibre univ A y).filter (fun v => parity v = b ∧ v ∉ D)
    H.card = 4 ∨ H.card = 5 → (freeEdges D L A).card + 6 ≤ 5 * H.card := by
  intro y A L H hcase
  have hne (l : Fin 9) (hl : l ∈ A) : i ≠ l := fun he => hi (he.symm ▸ hl)
  obtain ⟨hyD, hypar, hjD, hkD⟩ :=
    adjacent_fibre_missing_centre b hx hp hsep (hne j hj) (hne k hk) hmj hmk
  let z := flip y j
  obtain ⟨a, _, ha⟩ := mem_map.mp hj
  obtain ⟨c, _, hc⟩ := mem_map.mp hk
  let τ := Equiv.swap (3 : Fin 5) a
  let σ := (Equiv.swap (4 : Fin 5) (τ.symm c)).trans τ
  let f := σ.toEmbedding.trans e
  have hτ : τ 3 = a := Equiv.swap_apply_left _ _
  have h3 : f 3 = j := by
    have hne : (3 : Fin 5) ≠ τ.symm c := by
      intro he
      have h := congrArg τ he
      rw [hτ, Equiv.apply_symm_apply] at h
      exact hjk (ha.symm.trans ((congrArg e h).trans hc))
    change e (τ (Equiv.swap 4 (τ.symm c) 3)) = j
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 5) ≠ 4) hne, hτ, ha]
  have h4 : f 4 = k := by
    change e (τ (Equiv.swap 4 (τ.symm c) 4)) = k
    rw [Equiv.swap_apply_left, Equiv.apply_symm_apply, hc]
  have hA : (univ.map f : Finset (Fin 9)) = A := by
    ext l
    constructor
    · intro hl
      obtain ⟨t, _, rfl⟩ := mem_map.mp hl
      exact mem_map.mpr ⟨σ t, mem_univ _, rfl⟩
    · intro hl
      obtain ⟨t, _, rfl⟩ := mem_map.mp hl
      refine mem_map.mpr ⟨σ.symm t, mem_univ _, ?_⟩
      change e (σ (σ.symm t)) = e t
      rw [Equiv.apply_symm_apply]
  have hpar : parity z = b := by
    change parity (flip (flip x i) j) = b
    rw [parity_flip, parity_flip, Bool.not_not, hp]
  have hF (S : Finset (Q 9)) : restrictToFibre S A z = restrictToFibre S A y := by
    ext v
    simp only [restrictToFibre, mem_filter, sameFibre]
    have he (l : Fin 9) (hl : l ∉ A) : z l = y l := flip_same_fibre hj l hl
    apply and_congr_right'
    exact ⟨fun hv l hl => (hv l hl).trans (he l hl), fun hv l hl => (hv l hl).trans (he l hl).symm⟩
  have h0 : wordPoint f z 0 ∉ D := by simpa only [wordPoint_zero] using hjD
  have h8 : wordPoint f z 8 ∉ D := by
    have he := wordPoint_flip f z 0 (3 : Fin 5)
    change wordPoint f z 8 = flip (wordPoint f z 0) (f 3) at he
    rw [wordPoint_zero, h3, show z = flip y j from rfl, BalancedCriticalSpectrum.flip_flip] at he
    exact he.symm ▸ hyD
  have h24 : wordPoint f z 24 ∉ D := by
    have he := wordPoint_flip f z 0 (3 : Fin 5)
    change wordPoint f z 8 = flip (wordPoint f z 0) (f 3) at he
    rw [wordPoint_zero, h3, show z = flip y j from rfl, BalancedCriticalSpectrum.flip_flip] at he
    have he' := wordPoint_flip f z 8 (4 : Fin 5)
    change wordPoint f z 24 = flip (wordPoint f z 8) (f 4) at he'
    rw [he, h4] at he'
    exact he'.symm ▸ hkD
  have hb := normalized_local_capacity D f z hbal hdeg h0 h8 h24
  dsimp only at hb
  rw [hA, hF D, hF univ, hpar] at hb
  exact hb hcase

#print axioms adjacent_fibre_four_five_hole_capacity

#print axioms local_excess_cycles
#print axioms no_mapped_excess

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisExcessCycles
