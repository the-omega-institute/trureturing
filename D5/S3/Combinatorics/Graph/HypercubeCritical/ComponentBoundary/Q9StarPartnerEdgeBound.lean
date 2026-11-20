/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarPartnerEdgeBound
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Typed edge constraints for balanced cubic partners of the Q9 star. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound

/-! Count cube edges by the two endpoint types using coordinate flips. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerEdgeBound

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open Q9StarPartnerBound (Sstar)

local notation "flip" => BalancedCriticalSpectrum.flip
open private kind B orbitSize cap degreeInto degreeInto_eq indicator vertex_inequalities
  eligible_of_separated partner_subset_B from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound

private abbrev Orbit := Nat × Nat × Nat

private def orbitList : List Orbit :=
  (List.range 4).flatMap fun r =>
    (List.range (4 - r)).flatMap fun g => (List.range 4).map fun k => (r, g, k)

private def orbitTypes : Finset Orbit := orbitList.toFinset

private def orbit (q : Orbit) : Finset (Q 9) := Finset.univ.filter fun x => kind x = q

private def selected (D : Finset (Q 9)) (q : Orbit) : Finset (Q 9) :=
  D.filter fun x => kind x = q

/-- The type multiset of the nine flips, expressed as a list with multiplicity. -/
private def row : Orbit → List Orbit
  | (r, g, k) =>
    List.replicate (2 * r) (r - 1, g, k) ++
    List.replicate (2 * g) (r, g - 1, k) ++
    List.replicate (3 - r - g) (r + 1, g, k) ++
    List.replicate (3 - r - g) (r, g + 1, k) ++
    List.replicate k (r, g, k - 1) ++
    List.replicate (3 - k) (r, g, k + 1)

private def multiplicity (q r : Orbit) : Nat := (row q).count r

private def active : Orbit → Bool
  | (r, g, k) => if k ≤ 1 then decide (2 ≤ r)
                 else if k = 2 then decide (1 ≤ r ∨ 2 ≤ g)
                 else true

private def evenCap (q : Orbit) : Nat := 2 * (((row q).filter active).length / 2)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the type row of every cube point by finite kernel reduction.
private theorem cube_type_rows : ∀ x : Q 9,
    kind x ∈ orbitTypes ∧
    ((List.finRange 9).map fun i => kind (flip x i)).Perm (row (kind x)) ∧
    cap x = (evenCap (kind x) : Int) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Compute the size of each of the forty type fibers over the 512 cube points.
private theorem orbit_cards : ∀ q ∈ orbitTypes, (orbit q).card = orbitSize q := by
  suffices h : ∀ q ∈ orbitList, (orbit q).card = orbitSize q by
    simpa [orbitTypes] using h
  decide +kernel

private theorem neighbor_count (x : Q 9) (r : Orbit) :
    (directions (orbit r) x).card = multiplicity (kind x) r := by
  classical
  rw [multiplicity, ← (cube_type_rows x).2.1.count_eq r]
  simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
  rw [List.countP_eq_length_filter]
  -- Both counts filter the nine directions by the type of the flipped point.
  have hf : directions (orbit r) x =
      ((List.finRange 9).filter fun i => kind (flip x i) == r).toFinset := by
    ext i
    simp [orbit]
  rw [hf, List.toFinset_card_of_nodup ((List.nodup_finRange 9).filter _)]

/-- An oriented cube edge is encoded by its first endpoint and its direction. -/
private def darts (A C : Finset (Q 9)) : Finset (Q 9 × Fin 9) :=
  (A ×ˢ Finset.univ).filter fun p => flip p.1 p.2 ∈ C

private theorem darts_card (A C : Finset (Q 9)) :
    (darts A C).card = ∑ x ∈ A, (directions C x).card := by
  classical
  simp only [darts, directions, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

private theorem reverse_darts (A C : Finset (Q 9)) : (darts A C).card = (darts C A).card := by
  apply Finset.card_bij (fun p _ => (flip p.1 p.2, p.2))
  · rintro ⟨x, i⟩ h
    simpa [darts, BalancedCriticalSpectrum.flip_flip, and_comm] using h
  · rintro ⟨x, i⟩ _ ⟨y, j⟩ _ he
    have hij := congrArg Prod.snd he
    change i = j at hij
    subst j
    have hxy := congrArg (fun p : Q 9 × Fin 9 => flip p.1 i) he
    change flip (flip x i) i = flip (flip y i) i at hxy
    rw [BalancedCriticalSpectrum.flip_flip, BalancedCriticalSpectrum.flip_flip] at hxy
    exact congrArg (fun z => (z, i)) hxy
  · rintro ⟨x, i⟩ h
    exact ⟨(flip x i, i), by simpa [darts, BalancedCriticalSpectrum.flip_flip, and_comm] using h,
      by simp [BalancedCriticalSpectrum.flip_flip]⟩

private theorem darts_to_orbit (A : Finset (Q 9)) (q r : Orbit)
    (hA : A ⊆ orbit q) :
    (darts A (orbit r)).card = multiplicity q r * A.card := by
  rw [darts_card, Finset.sum_const_nat, Nat.mul_comm]
  intro x hx
  have ht : kind x = q := (Finset.mem_filter.mp (hA hx)).2
  rw [neighbor_count, ht]

private def occupancy (D : Finset (Q 9)) (q : Orbit) : Nat := (selected D q).card

private def edgeCount (D : Finset (Q 9)) (q r : Orbit) : Nat :=
  (darts (selected D q) (selected D r)).card

private theorem selected_subset_orbit (D : Finset (Q 9)) (q : Orbit) :
    selected D q ⊆ orbit q := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

private theorem edgeCount_symm (D : Finset (Q 9)) (q r : Orbit) :
    edgeCount D q r = edgeCount D r q := reverse_darts _ _

private theorem occupancy_le (D : Finset (Q 9)) {q : Orbit} (hq : q ∈ orbitTypes) :
    occupancy D q ≤ orbitSize q :=
  (Finset.card_le_card (selected_subset_orbit D q)).trans_eq (orbit_cards q hq)

/-- Bounds obtained by intersecting the two endpoint restrictions on a type-pair edge set. -/
private theorem edge_overlap (D : Finset (Q 9)) {q : Orbit} (hq : q ∈ orbitTypes)
    (r : Orbit) :
    edgeCount D q r ≤ multiplicity q r * occupancy D q ∧
    edgeCount D q r ≤ multiplicity r q * occupancy D r ∧
    multiplicity q r * occupancy D q + multiplicity r q * occupancy D r ≤
      edgeCount D q r + multiplicity q r * orbitSize q ∧
    edgeCount D q r ≤ multiplicity q r * orbitSize q := by
  classical
  let source := darts (selected D q) (orbit r)
  let target := darts (orbit q) (selected D r)
  let whole := darts (orbit q) (orbit r)
  have hsource : source.card = multiplicity q r * occupancy D q :=
    darts_to_orbit _ _ _ (selected_subset_orbit D q)
  have htarget : target.card = multiplicity r q * occupancy D r :=
    (reverse_darts _ _).trans (darts_to_orbit _ _ _ (selected_subset_orbit D r))
  have hwhole : whole.card = multiplicity q r * orbitSize q := by
    dsimp [whole]
    rw [darts_to_orbit _ q r (fun _ hx => hx), orbit_cards q hq]
  have hinter : (source ∩ target).card = edgeCount D q r := by
    congr 1
    ext p
    simp only [source, target, darts, selected, orbit, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, and_true, true_and]
    tauto
  have hsrc : source ⊆ whole := by
    intro p hp
    simp only [source, whole, darts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true] at hp ⊢
    exact ⟨selected_subset_orbit D q hp.1, hp.2⟩
  have htgt : target ⊆ whole := by
    intro p hp
    simp only [target, whole, darts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true] at hp ⊢
    exact ⟨hp.1, selected_subset_orbit D r hp.2⟩
  have hu := Finset.card_le_card (Finset.union_subset hsrc htgt)
  have hi := Finset.card_inter_add_card_union source target
  have hl := Finset.card_le_card (Finset.inter_subset_left (s₁ := source) (s₂ := target))
  have hr := Finset.card_le_card (Finset.inter_subset_right (s₁ := source) (s₂ := target))
  rw [hinter, hsource] at hl
  rw [hinter, htarget] at hr
  rw [hinter, hsource, htarget] at hi
  rw [hwhole] at hu
  exact ⟨hl, hr, by omega, by omega⟩

private theorem sum_darts_by_type (A D : Finset (Q 9)) :
    (∑ r ∈ orbitTypes, (darts A (selected D r)).card) = (darts A D).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : Q 9 × Fin 9 => kind (flip p.1 p.2))
    (t := orbitTypes) (s := darts A D) (fun p _ => (cube_type_rows (flip p.1 p.2)).1)]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ext p
  simp [darts, selected, and_assoc]

open Classical in
/-- Partitioning the selected edges by the other endpoint type recovers the cubic degree. -/
private theorem internal_degree_row (D : Finset (Q 9)) (q : Orbit)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3) :
    (∑ r ∈ orbitTypes, edgeCount D q r) = 3 * occupancy D q := by
  unfold edgeCount occupancy
  rw [sum_darts_by_type, darts_card, Finset.sum_const_nat, Nat.mul_comm]
  exact fun x hx => regular_directions D hr (Finset.mem_filter.mp hx).1

private theorem sum_ambient_degrees (D : Finset (Q 9)) (q : Orbit) :
    (∑ x ∈ orbit q, (directions D x).card) =
      ∑ r ∈ orbitTypes, multiplicity r q * occupancy D r := by
  rw [← darts_card, ← sum_darts_by_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [reverse_darts, darts_to_orbit _ r q (selected_subset_orbit D r)]
  rfl

open Classical in
private theorem ambient_degree_row (D : Finset (Q 9)) {q : Orbit} (hq : q ∈ orbitTypes)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) :
    (∑ r ∈ orbitTypes, (multiplicity r q : Int) * (occupancy D r : Int)) +
        ((evenCap q : Int) - 3) * (occupancy D q : Int) ≤
      (evenCap q : Int) * (orbitSize q : Int) := by
  classical
  have hs := Finset.sum_le_sum (s := orbit q) fun x hx => (vertex_inequalities hr hb hD x).1
  have hcap (x : Q 9) (hx : x ∈ orbit q) : cap x = (evenCap q : Int) := by
    rw [(cube_type_rows x).2.2, (Finset.mem_filter.mp hx).2]
  have hdeg : (∑ x ∈ orbit q, degreeInto D x) =
      ∑ r ∈ orbitTypes, (multiplicity r q : Int) * (occupancy D r : Int) := by
    simp only [degreeInto_eq, ← Nat.cast_mul, ← Nat.cast_sum, sum_ambient_degrees]
  have hind : (∑ x ∈ orbit q, indicator D x) = (occupancy D q : Int) := by
    have hf : (orbit q).filter (· ∈ D) = selected D q := by ext; simp [selected, orbit, and_comm]
    unfold occupancy
    rw [← hf]
    simp [indicator, Finset.filter_mem_eq_inter]
  calc
    _ = ∑ x ∈ orbit q, (degreeInto D x + (cap x - 3) * indicator D x) := by
      rw [Finset.sum_add_distrib, hdeg, ← hind, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun x hx => by rw [hcap x hx]
    _ ≤ ∑ x ∈ orbit q, cap x := hs
    _ = _ := by
      rw [Finset.sum_congr rfl hcap, Finset.sum_const, nsmul_eq_mul, orbit_cards q hq, mul_comm]

private theorem orbit_list_nodup : orbitList.Nodup := by decide +kernel

private theorem active_kind (x : Q 9) : active (kind x) = B x := by
  cases h : kind x with
  | mk r gk =>
    obtain ⟨g, k⟩ := gk
    simp [active, B, h]

private theorem occupancy_of_inactive (D : Finset (Q 9)) (hD : ∀ x ∈ D, B x = true)
    {q : Orbit} (hq : active q = false) : occupancy D q = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxD, ht⟩ := Finset.mem_filter.mp hx
  have h := active_kind x
  rw [ht, hq, hD x hxD] at h
  contradiction

private theorem sum_filtered_orbits (p : Orbit → Bool) (f : Orbit → Int)
    (hz : ∀ r ∈ orbitTypes, p r = false → f r = 0) :
    ((orbitList.filter p).map f).sum = ∑ r ∈ orbitTypes, f r := by
  classical
  rw [← List.sum_toFinset _ (orbit_list_nodup.filter _)]
  apply Finset.sum_subset
  · intro r hr
    exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hr)).1
  · intro r hr hn
    apply hz r hr
    cases h : p r
    · rfl
    · exact (hn (List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨List.mem_toFinset.mp hr, h⟩))).elim

private inductive Variable where
  | vertex (q : Orbit)
  | edge (q r : Orbit)
  deriving DecidableEq

/-- Both orientations of a type-pair edge refer to the same variable. -/
private def edgeVariable (q r : Orbit) : Variable :=
  if r.1 < q.1 ∨
      (r.1 = q.1 ∧ (r.2.1 < q.2.1 ∨ (r.2.1 = q.2.1 ∧ r.2.2 < q.2.2))) then
    .edge r q
  else
    .edge q r

private def value (D : Finset (Q 9)) : Variable → Int
  | .vertex q => occupancy D q
  | .edge q r => edgeCount D q r

private theorem value_edgeVariable (D : Finset (Q 9)) (q r : Orbit) :
    value D (edgeVariable q r) = (edgeCount D q r : Int) := by
  unfold edgeVariable
  split
  · exact congrArg (fun n : Nat => (n : Int)) (edgeCount_symm D r q)
  · rfl

private inductive Constraint where
  | degree (q : Orbit)
  | internal (q : Orbit)
  | occupancyCap (q : Orbit)
  | source (q r : Orbit)
  | target (q r : Orbit)
  | overlap (q r : Orbit)
  | edgeCap (q r : Orbit)

private def sourceType : Constraint → Orbit
  | .degree q | .internal q | .occupancyCap q => q
  | .source q _ | .target q _ | .overlap q _ | .edgeCap q _ => q

private def terms : Constraint → List (Variable × Int)
  | .degree q =>
    ((orbitList.filter fun r => active r && multiplicity r q != 0).map fun r =>
      (.vertex r, (multiplicity r q : Int))) ++
    (if active q then [(.vertex q, (evenCap q : Int) - 3)] else [])
  | .internal q =>
    ((orbitList.filter fun r => active r && multiplicity q r != 0).map fun r =>
      (edgeVariable q r, 1)) ++ [(.vertex q, -3)]
  | .occupancyCap q => [(.vertex q, 1)]
  | .source q r => [(.edge q r, 1), (.vertex q, -(multiplicity q r : Int))]
  | .target q r => [(.edge q r, 1), (.vertex r, -(multiplicity r q : Int))]
  | .overlap q r =>
    [(.vertex q, multiplicity q r), (.vertex r, multiplicity r q), (.edge q r, -1)]
  | .edgeCap q r => [(.edge q r, 1)]

private def rhs : Constraint → Int
  | .degree q => (evenCap q : Int) * (orbitSize q : Int)
  | .occupancyCap q => orbitSize q
  | .overlap q r | .edgeCap q r => (multiplicity q r : Int) * (orbitSize q : Int)
  | .internal _ | .source _ _ | .target _ _ => 0

private def evaluate (v : Variable → Int) (ts : List (Variable × Int)) : Int :=
  (ts.map fun (key, coeff) => coeff * v key).sum

private theorem evaluate_degree (D : Finset (Q 9)) (hD : ∀ x ∈ D, B x = true) (q : Orbit) :
    evaluate (value D) (terms (.degree q)) =
      (∑ r ∈ orbitTypes, (multiplicity r q : Int) * (occupancy D r : Int)) +
      ((evenCap q : Int) - 3) * (occupancy D q : Int) := by
  simp only [evaluate, terms, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, value]
  congr 1
  · apply sum_filtered_orbits
    intro r _ hz
    by_cases ha : active r = false
    · rw [occupancy_of_inactive D hD ha]
      simp
    · have hm : multiplicity r q = 0 := by simpa [ha] using hz
      simp [hm]
  · cases h : active q <;> simp [h, occupancy_of_inactive D hD]

open Classical in
private theorem evaluate_internal (D : Finset (Q 9)) {q : Orbit} (hq : q ∈ orbitTypes)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ∀ x ∈ D, B x = true) :
    evaluate (value D) (terms (.internal q)) = 0 := by
  simp only [evaluate, terms, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
    value_edgeVariable]
  change ((orbitList.filter fun r => active r && multiplicity q r != 0).map
      fun r => (edgeCount D q r : Int)).sum + -3 * (occupancy D q : Int) = 0
  rw [sum_filtered_orbits, ← Nat.cast_sum, internal_degree_row D q hr, Nat.cast_mul]
  · ring
  · intro r _ hz
    obtain ⟨hsource, htarget, _⟩ := edge_overlap D hq r
    by_cases ha : active r = false
    · rw [occupancy_of_inactive D hD ha, mul_zero] at htarget
      exact_mod_cast htarget.antisymm (Nat.zero_le _)
    · have hm : multiplicity q r = 0 := by simpa [ha] using hz
      rw [hm, zero_mul] at hsource
      exact_mod_cast hsource.antisymm (Nat.zero_le _)

private def allowedWeight (w : Int) (c : Constraint) : Prop :=
  match c with
  | .internal _ => True
  | _ => 0 ≤ w

private instance (w : Int) (c : Constraint) : Decidable (allowedWeight w c) := by
  cases c <;> unfold allowedWeight <;> infer_instance

open Classical in
private theorem weighted_row (D : Finset (Q 9))
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) (w : Int) (c : Constraint)
    (hq : sourceType c ∈ orbitTypes) (hw : allowedWeight w c) :
    w * evaluate (value D) (terms c) ≤ w * rhs c := by
  cases c <;> simp only [sourceType] at hq
  case internal q => simp [evaluate_internal D hq hr hD, rhs]
  case degree q =>
    exact mul_le_mul_of_nonneg_left
      (by rw [evaluate_degree D hD]; exact ambient_degree_row D hq hr hb hD) hw
  case occupancyCap q =>
    apply mul_le_mul_of_nonneg_left _ hw
    simpa [evaluate, terms, rhs, value] using (Int.ofNat_le.mpr (occupancy_le D hq))
  case source q r =>
    apply mul_le_mul_of_nonneg_left _ hw
    have h := Int.ofNat_le.mpr (edge_overlap D hq r).1
    simp [evaluate, terms, value, rhs, Nat.cast_mul] at h ⊢
    linarith only [h]
  case target q r =>
    apply mul_le_mul_of_nonneg_left _ hw
    have h := Int.ofNat_le.mpr (edge_overlap D hq r).2.1
    simp [evaluate, terms, value, rhs, Nat.cast_mul] at h ⊢
    linarith only [h]
  case overlap q r =>
    apply mul_le_mul_of_nonneg_left _ hw
    have h := Int.ofNat_le.mpr (edge_overlap D hq r).2.2.1
    simp [evaluate, terms, value, rhs, Nat.cast_mul] at h ⊢
    linarith only [h]
  case edgeCap q r =>
    apply mul_le_mul_of_nonneg_left _ hw
    simpa [evaluate, terms, rhs, value, Nat.cast_mul] using
      (Int.ofNat_le.mpr (edge_overlap D hq r).2.2.2)

-- Nonzero row multipliers in lexicographic type and edge order, followed by the cap corrections.
private def weights : List (Int × Constraint) :=
  [(33, .degree (0, 3, 3)), (13, .degree (1, 0, 3)), (27, .degree (1, 1, 0)),
   (19, .degree (1, 1, 1)), (3, .degree (1, 1, 3)), (14, .degree (2, 0, 2)),
   (16, .degree (2, 1, 0)), (5, .degree (2, 1, 2)),
   (19, .overlap (0, 0, 3) (1, 0, 3)), (49, .overlap (0, 1, 3) (0, 2, 3)),
   (26, .source (0, 2, 2) (0, 2, 3)), (96, .source (0, 2, 2) (0, 3, 2)),
   (14, .overlap (0, 2, 3) (1, 2, 3)), (22, .target (0, 3, 2) (0, 3, 3)),
   (5, .overlap (1, 0, 2) (1, 0, 3)), (6, .source (1, 0, 2) (1, 1, 2)),
   (9, .target (1, 0, 2) (1, 1, 2)), (10, .overlap (1, 0, 2) (2, 0, 2)),
   (19, .overlap (1, 0, 3) (1, 1, 3)), (75, .overlap (1, 1, 2) (1, 2, 2)),
   (19, .overlap (1, 1, 3) (2, 1, 3)), (21, .overlap (1, 2, 2) (1, 2, 3)),
   (13, .target (2, 0, 0) (2, 0, 1)), (13, .target (2, 0, 0) (2, 1, 0)),
   (46, .overlap (2, 0, 0) (3, 0, 0)), (25, .overlap (2, 0, 1) (2, 0, 2)),
   (34, .overlap (2, 0, 1) (3, 0, 1)), (13, .overlap (2, 0, 2) (2, 1, 2)),
   (54, .source (2, 0, 3) (3, 0, 3)), (1, .target (2, 1, 1) (2, 1, 2)),
   (19, .overlap (2, 1, 2) (2, 1, 3)), (59, .source (3, 0, 2) (3, 0, 3)),
   (-1, .internal (0, 0, 3)), (1, .internal (0, 1, 3)), (-74, .internal (0, 2, 2)),
   (48, .internal (0, 2, 3)), (-22, .internal (0, 3, 2)), (-16, .internal (1, 0, 2)),
   (20, .internal (1, 0, 3)), (1, .internal (1, 1, 2)), (-1, .internal (1, 1, 3)),
   (74, .internal (1, 2, 2)), (1, .internal (1, 2, 3)), (-13, .internal (2, 0, 0)),
   (26, .internal (2, 0, 2)), (-20, .internal (2, 0, 3)), (-1, .internal (2, 1, 2)),
   (20, .internal (2, 1, 3)), (58, .internal (3, 0, 0)), (34, .internal (3, 0, 1)),
   (-26, .internal (3, 0, 2)), (-33, .internal (3, 0, 3)),
   (1, .occupancyCap (0, 0, 3)), (1, .occupancyCap (0, 2, 3)), (1, .occupancyCap (0, 3, 2)),
   (1, .occupancyCap (0, 3, 3)), (1, .occupancyCap (1, 2, 2)), (1, .occupancyCap (2, 0, 1)),
   (2, .occupancyCap (2, 1, 0)), (1, .occupancyCap (2, 1, 2)), (1, .occupancyCap (3, 0, 3)),
   (1, .edgeCap (1, 0, 2) (1, 0, 3)), (1, .edgeCap (2, 0, 0) (3, 0, 0))]

private def scaledTerms (wc : Int × Constraint) : List (Variable × Int) :=
  (terms wc.2).map fun (key, coeff) => (key, wc.1 * coeff)

private def combinedTerms : List (Variable × Int) := weights.flatMap scaledTerms

private def objectiveTerms : List (Variable × Int) :=
  (orbitList.filter active).map fun q => (.vertex q, 100)

private def coefficient (ts : List (Variable × Int)) (key : Variable) : Int :=
  (ts.map fun (v, c) => if key = v then c else 0).sum

private def variableList : List Variable := (combinedTerms ++ objectiveTerms).map Prod.fst

private theorem evaluate_by_coefficient (v : Variable → Int) (ts : List (Variable × Int))
    (keys : Finset Variable) (hkeys : ∀ t ∈ ts, t.1 ∈ keys) :
    evaluate v ts = ∑ k ∈ keys, coefficient ts k * v k := by
  classical
  induction ts with
  | nil => simp [evaluate, coefficient]
  | cons t ts ih =>
    have ht := hkeys t (List.mem_cons_self)
    have hs := ih (fun s h => hkeys s (List.mem_cons_of_mem _ h))
    simp only [evaluate, List.map_cons, List.sum_cons] at hs ⊢
    rw [hs]
    simp only [coefficient, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    have step (k : Variable) :
        (if k = t.1 then t.2 else 0) * v k = if k = t.1 then t.2 * v t.1 else 0 := by
      by_cases hk : k = t.1 <;> simp [hk]
    simp only [step, Finset.sum_ite_eq', ht, ite_true]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the multiplier signs, row indices, coefficient domination and right-hand side.
private theorem certificate_checked :
    (∀ wc ∈ weights, sourceType wc.2 ∈ orbitTypes ∧ allowedWeight wc.1 wc.2) ∧
    (∀ v ∈ variableList, coefficient objectiveTerms v ≤ coefficient combinedTerms v) ∧
    (weights.map fun wc => wc.1 * rhs wc.2).sum = 14221 := by
  decide +kernel

private theorem evaluate_combined (D : Finset (Q 9)) (rows : List (Int × Constraint)) :
    evaluate (value D) (rows.flatMap scaledTerms) =
      (rows.map fun wc => wc.1 * evaluate (value D) (terms wc.2)).sum := by
  induction rows with
  | nil => rfl
  | cons wc rows ih =>
    simp only [List.flatMap_cons, evaluate, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, scaledTerms, List.map_map, Function.comp_def, mul_assoc,
      List.sum_map_mul_left] at ih ⊢
    rw [ih]

open Classical in
private theorem weighted_sum_le (D : Finset (Q 9))
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) (rows : List (Int × Constraint))
    (hrows : ∀ wc ∈ rows, sourceType wc.2 ∈ orbitTypes ∧ allowedWeight wc.1 wc.2) :
    (rows.map fun wc => wc.1 * evaluate (value D) (terms wc.2)).sum ≤
      (rows.map fun wc => wc.1 * rhs wc.2).sum := by
  induction rows with
  | nil => simp
  | cons wc rest ih =>
    obtain ⟨hq, hw⟩ := hrows wc List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (weighted_row D hr hb hD wc.1 wc.2 hq hw)
      (ih fun t ht => hrows t (List.mem_cons_of_mem _ ht))

private theorem objective_le_combined (D : Finset (Q 9)) :
    evaluate (value D) objectiveTerms ≤ evaluate (value D) combinedTerms := by
  rw [evaluate_by_coefficient _ objectiveTerms variableList.toFinset,
    evaluate_by_coefficient _ combinedTerms variableList.toFinset]
  · apply Finset.sum_le_sum
    intro v hv
    apply mul_le_mul_of_nonneg_right (certificate_checked.2.1 v (List.mem_toFinset.mp hv))
    cases v <;> exact Int.natCast_nonneg _
  · intro t ht
    exact List.mem_toFinset.mpr (List.mem_map_of_mem (List.mem_append_left _ ht))
  · intro t ht
    exact List.mem_toFinset.mpr (List.mem_map_of_mem (List.mem_append_right _ ht))

private theorem objective_eq (D : Finset (Q 9)) (hD : ∀ x ∈ D, B x = true) :
    evaluate (value D) objectiveTerms = 100 * (D.card : Int) := by
  have hcard : D.card = ∑ q ∈ orbitTypes, occupancy D q :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => (cube_type_rows x).1)
  simp only [evaluate, objectiveTerms, List.map_map, Function.comp_def, value]
  rw [List.sum_map_mul_left, sum_filtered_orbits, hcard, Nat.cast_sum]
  exact fun q _ hq => by rw [occupancy_of_inactive D hD hq]; rfl

open Classical in
/-- A separated induced cubic Huang-balanced partner of the 72-point Q9 star
has at most 138 vertices. -/
theorem partner_card_le_138 (D : Finset (Q 9))
    (hdisj : Disjoint Sstar D)
    (hcross : ∀ s ∈ Sstar, ∀ d ∈ D, ¬ (hypercube 9).Adj s d)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) : D.card ≤ 138 := by
  have hD := partner_subset_B hr hb (fun _ => eligible_of_separated hdisj hcross)
  have hcard : 100 * (D.card : Int) ≤ 14221 := by
    calc
      _ = evaluate (value D) objectiveTerms := (objective_eq D hD).symm
      _ ≤ evaluate (value D) combinedTerms := objective_le_combined D
      _ = _ := evaluate_combined D weights
      _ ≤ _ := weighted_sum_le D hr hb hD weights certificate_checked.1
      _ = 14221 := certificate_checked.2.2
  have hdiv := direction_edge_count (d := 3) D hr hb (0 : Fin 9)
  omega

#print axioms cube_type_rows
#print axioms orbit_cards
#print axioms edge_overlap
#print axioms internal_degree_row
#print axioms ambient_degree_row
#print axioms certificate_checked
#check partner_card_le_138
#print axioms partner_card_le_138

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerEdgeBound
