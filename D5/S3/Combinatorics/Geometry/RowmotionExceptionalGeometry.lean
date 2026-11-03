/- GID: D5/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionExceptionalGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native endpoint counting for the complement of separated three-row states. -/

import D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Endpoint encodings and finite fiber bounds for actual three-row convex states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder

namespace D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry

/-- All actual interval-closed states, including the empty set. -/
def convexStates (n : ℕ) : Finset (Set (Fin 3 × Fin n)) := by
  classical
  exact Finset.univ.filter Set.OrdConnected

/-- The original separated family is excluded on the full state carrier. -/
def exceptionalGeometry (n : ℕ) : Finset (Set (Fin 3 × Fin n)) := by
  classical
  exact (convexStates n).filter (fun I => ¬ Separated I)

private def rowState {n : ℕ} (a b : Fin 3 → Fin n) : Set (Fin 3 × Fin n) :=
  {p | a p.1 ≤ p.2 ∧ p.2 ≤ b p.1}

private theorem row_representation {n : ℕ} (hn : 2 ≤ n)
    (I : Set (Fin 3 × Fin n)) (hI : I.OrdConnected) :
    ∃ a b : Fin 3 → Fin n, rowState a b = I := by
  classical
  have rows (r : Fin 3) : ∃ a b : Fin n,
      ∀ x : Fin n, (r, x) ∈ I ↔ a ≤ x ∧ x ≤ b := by
    let s : Finset (Fin n) := Finset.univ.filter (fun x => (r, x) ∈ I)
    by_cases hs : s.Nonempty
    · refine ⟨s.min' hs, s.max' hs, ?_⟩
      intro x
      constructor
      · intro hx
        have hm : x ∈ s := by simpa [s] using hx
        exact ⟨s.min'_le x hm, s.le_max' x hm⟩
      · intro hx
        have ha : (r, s.min' hs) ∈ I := by
          simpa [s] using s.min'_mem hs
        have hb : (r, s.max' hs) ∈ I := by
          simpa [s] using s.max'_mem hs
        exact hI.out ha hb ⟨⟨le_rfl, hx.1⟩, ⟨le_rfl, hx.2⟩⟩
    · refine ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
      intro x
      have hnone : (r, x) ∉ I := by
        intro hx
        apply hs
        exact ⟨x, by simpa [s] using hx⟩
      simp only [hnone, false_iff]
      intro hx
      have h₁ := hx.1
      have h₂ := hx.2
      change 1 ≤ x.val at h₁
      change x.val ≤ 0 at h₂
      omega
  choose a b hab using rows
  refine ⟨a, b, ?_⟩
  ext p
  exact (hab p.1 p.2).symm

private theorem endpoints_antitone {n : ℕ} (a b : Fin 3 → Fin n)
    (h : (rowState a b).OrdConnected) (hne : ∀ r, a r ≤ b r) :
    Antitone a ∧ Antitone b := by
  constructor
  · intro r s hrs
    by_contra hn
    have has : a r < a s := lt_of_not_ge hn
    have ha : (r, a r) ∈ rowState a b := ⟨le_rfl, hne r⟩
    have hb : (s, a s) ∈ rowState a b := ⟨le_rfl, hne s⟩
    have hc : (s, a r) ∈ rowState a b :=
      h.out ha hb ⟨⟨hrs, le_rfl⟩, ⟨le_rfl, has.le⟩⟩
    exact (not_le_of_gt has) hc.1
  · intro r s hrs
    by_contra hn
    have hbs : b r < b s := lt_of_not_ge hn
    have ha : (r, b r) ∈ rowState a b := ⟨hne r, le_rfl⟩
    have hb : (s, b s) ∈ rowState a b := ⟨hne s, le_rfl⟩
    have hc : (r, b s) ∈ rowState a b :=
      h.out ha hb ⟨⟨le_rfl, hbs.le⟩, ⟨hrs, le_rfl⟩⟩
    exact (not_le_of_gt hbs) hc.2

/-- Actual convex states with at least one empty row. -/
def missingRowStates (n : ℕ) : Finset (Set (Fin 3 × Fin n)) := by
  classical
  exact (convexStates n).filter (fun I => ∃ r, ∀ x, (r, x) ∉ I)

/-- Deleting an empty row leaves at most four free column endpoints. -/
theorem missing_row_bound {n : ℕ} (hn : 2 ≤ n) :
    (missingRowStates n).card ≤ 3 * n ^ 4 := by
  classical
  let zero : Fin n := ⟨0, by omega⟩
  let decodeMissing : (Fin 3 × (Fin 2 → Fin n × Fin n)) → Set (Fin 3 × Fin n) :=
    fun v => {p | p.1 ≠ v.1 ∧
      ((Fin.insertNth (α := fun _ => Fin n × Fin n) v.1 (zero, zero) v.2 p.1)).1 ≤ p.2 ∧
      p.2 ≤ ((Fin.insertNth (α := fun _ => Fin n × Fin n) v.1 (zero, zero) v.2 p.1)).2}
  have hs : missingRowStates n ⊆ Finset.univ.image decodeMissing := by
    intro I hI
    obtain ⟨hconv, r, hr⟩ := Finset.mem_filter.mp hI
    have hc : I.OrdConnected := (Finset.mem_filter.mp hconv).2
    obtain ⟨a, b, hab⟩ := row_representation hn I hc
    refine Finset.mem_image.mpr ⟨(r, r.removeNth (fun j => (a j, b j))),
      Finset.mem_univ _, ?_⟩
    ext p
    dsimp [decodeMissing]
    rw [Fin.insertNth_removeNth]
    by_cases hpr : p.1 = r
    · simp only [hpr, not_true_eq_false, false_and]
      have hp : p = (r, p.2) := Prod.ext hpr rfl
      rw [hp]
      exact (iff_false_intro (hr p.2)).symm
    · rw [Function.update_of_ne hpr]
      simp only [hpr, not_false_eq_true, true_and]
      rw [← hab]
      rfl
  calc
    (missingRowStates n).card ≤ (Finset.univ.image decodeMissing).card :=
      Finset.card_le_card hs
    _ ≤ (Finset.univ : Finset (Fin 3 × (Fin 2 → Fin n × Fin n))).card :=
      Finset.card_image_le
    _ = 3 * n ^ 4 := by simp; ring

private def signedOffset (L x y : ℕ) : ℤ :=
  if (x : ℤ) + 7 < y then (x : ℤ) + L - y
  else if (y : ℤ) + 7 < x then (x : ℤ) - y - L
  else (x : ℤ) - y

private theorem signedOffset_bounds {L x y : ℕ}
    (hx : x < L) (hy : y < L)
    (h : min (Nat.dist x y) (L - Nat.dist x y) < 8) :
    -7 ≤ signedOffset L x y ∧ signedOffset L x y ≤ 7 := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy] at h
    simp only [min_lt_iff] at h
    unfold signedOffset
    split_ifs <;> omega
  · rw [Nat.dist_eq_sub_of_le_right hyx] at h
    simp only [min_lt_iff] at h
    unfold signedOffset
    split_ifs <;> omega

private theorem signedOffset_injective {n c y : ℕ} :
    Function.Injective (fun x : Fin n => signedOffset (n + 4) (x.val + c) y) := by
  intro x z he
  have hx := x.isLt
  have hz := z.isLt
  dsimp only [signedOffset] at he
  split_ifs at he <;> apply Fin.ext <;> omega

private theorem close_values_bound {n c y : ℕ}
    (hc : c ≤ 2) (hy : y < n + 4) :
    (Finset.univ.filter (fun x : Fin n =>
      min (Nat.dist (x.val + c) y) ((n + 4) - Nat.dist (x.val + c) y) < 8)).card ≤ 15 := by
  classical
  let s := Finset.univ.filter (fun x : Fin n =>
    min (Nat.dist (x.val + c) y) ((n + 4) - Nat.dist (x.val + c) y) < 8)
  have hs : Set.MapsTo (fun x : Fin n => signedOffset (n + 4) (x.val + c) y)
      s (Finset.Icc (-7 : ℤ) 7) := by
    intro x hx
    have hb := signedOffset_bounds (by have := x.isLt; omega) hy
      (Finset.mem_filter.mp hx).2
    exact Finset.mem_Icc.mpr hb
  have hi := Finset.card_le_card_of_injOn
    (fun x : Fin n => signedOffset (n + 4) (x.val + c) y) hs
    signedOffset_injective.injOn
  change s.card ≤ 15
  norm_num only [Int.card_Icc] at hi
  exact hi

private def shift (k : Fin 6) : ℕ := if k.val < 3 then 0 else 2

private def site {n : ℕ} (f : Fin 6 → Fin n) (k : Fin 6) : ℕ :=
  (f k).val + shift k

private def badPair {n : ℕ} (p q : Fin 6) : Finset (Fin 6 → Fin n) := by
  classical
  exact Finset.univ.filter (fun f =>
    min (Nat.dist (site f p) (site f q)) ((n + 4) - Nat.dist (site f p) (site f q)) < 8)

private theorem badPair_bound {n : ℕ} (hn : 2 ≤ n) (p q : Fin 6) (hpq : p ≠ q) :
    (badPair (n := n) p q).card ≤ 15 * n ^ 5 := by
  classical
  let zero : Fin n := ⟨0, by omega⟩
  let fibers (g : Fin 5 → Fin n) := (badPair p q).filter (fun f => p.removeNth f = g)
  have hfiber (g : Fin 5 → Fin n) : (fibers g).card ≤ 15 := by
    let t : Fin 6 → Fin n := Fin.insertNth (α := fun _ => Fin n) p zero g
    let y := site t q
    let u := Finset.univ.filter (fun x : Fin n =>
      min (Nat.dist (x.val + shift p) y) ((n + 4) - Nat.dist (x.val + shift p) y) < 8)
    have hqf (f : Fin 6 → Fin n) (hf : p.removeNth f = g) : t q = f q := by
      dsimp [t]
      rw [← hf, Fin.insertNth_removeNth, Function.update_of_ne hpq.symm]
    have hm : Set.MapsTo (fun f : Fin 6 → Fin n => f p) (fibers g) u := by
      intro f hf
      obtain ⟨hb, hg⟩ := Finset.mem_filter.mp hf
      have hh := (Finset.mem_filter.mp hb).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [y, site]
      rw [hqf f hg]
      exact hh
    have hi : Set.InjOn (fun f : Fin 6 → Fin n => f p) (fibers g) := by
      intro f hf f' hf' he
      have h₁ := (Finset.mem_filter.mp hf).2
      have h₂ := (Finset.mem_filter.mp hf').2
      change f p = f' p at he
      calc
        f = Fin.insertNth p (f p) (p.removeNth f) := (Fin.insertNth_self_removeNth p f).symm
        _ = Fin.insertNth p (f' p) (p.removeNth f') := by rw [h₁, h₂, he]
        _ = f' := Fin.insertNth_self_removeNth p f'
    have hc : shift p ≤ 2 := by unfold shift; split_ifs <;> omega
    have hy : y < n + 4 := by
      have ht := (t q).isLt
      have hq : shift q ≤ 2 := by unfold shift; split_ifs <;> omega
      dsimp [y, site]
      omega
    exact (Finset.card_le_card_of_injOn _ hm hi).trans (close_values_bound hc hy)
  calc
    (badPair (n := n) p q).card = ∑ g : Fin 5 → Fin n, (fibers g).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _g : Fin 5 → Fin n, 15 := Finset.sum_le_sum (fun g _ => hfiber g)
    _ = 15 * n ^ 5 := by simp; ring

private def badTuples (n : ℕ) : Finset (Fin 6 → Fin n) := by
  classical
  exact (Finset.univ.filter (fun pq : Fin 6 × Fin 6 => pq.1 < pq.2)).biUnion
    (fun pq => badPair pq.1 pq.2)

private theorem badTuples_bound {n : ℕ} (hn : 2 ≤ n) :
    (badTuples n).card ≤ 225 * n ^ 5 := by
  classical
  let pairs := Finset.univ.filter (fun pq : Fin 6 × Fin 6 => pq.1 < pq.2)
  have hc : pairs.card = 15 := by decide
  calc
    (badTuples n).card ≤ ∑ pq ∈ pairs, (badPair (n := n) pq.1 pq.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ pairs, 15 * n ^ 5 := by
      apply Finset.sum_le_sum
      intro pq hpq
      exact badPair_bound hn pq.1 pq.2 (ne_of_lt (Finset.mem_filter.mp hpq).2)
    _ = 225 * n ^ 5 := by simp [hc]; ring

private def raw {n : ℕ} (a b : Fin 3 → Fin n) (k : Fin 6) : Fin n :=
  if h : k.val < 3 then a ⟨k.val, h⟩ else b ⟨k.val - 3, by omega⟩

private def decodeRows {n : ℕ} (f : Fin 6 → Fin n) : Set (Fin 3 × Fin n) :=
  rowState (fun r => f ⟨r.val, by omega⟩) (fun r => f ⟨r.val + 3, by omega⟩)

private theorem decodeRows_raw {n : ℕ} (a b : Fin 3 → Fin n) :
    decodeRows (raw a b) = rowState a b := by
  ext p
  simp [decodeRows, rowState, raw]

private theorem site_raw {n : ℕ} (a b : Fin 3 → Fin n) (k : Fin 6) :
    site (raw a b) k = (endpointSites a b k).val := by
  unfold site raw shift endpointSites
  split_ifs <;> rfl

private theorem separated_of_distances {n : ℕ} (a b : Fin 3 → Fin n)
    (hc : (rowState a b).OrdConnected) (hne : ∀ r, a r ≤ b r)
    (hg : ∀ r s : Fin 6, r < s →
      8 ≤ min (Nat.dist (endpointSites a b r).val (endpointSites a b s).val)
        ((n + 4) - Nat.dist (endpointSites a b r).val (endpointSites a b s).val)) :
    Separated (rowState a b) := by
  obtain ⟨ha, hb⟩ := endpoints_antitone a b hc hne
  have has : StrictAnti a := by
    intro r s hrs
    refine lt_of_le_of_ne (ha hrs.le) ?_
    intro he
    have h := hg ⟨r.val, by omega⟩ ⟨s.val, by omega⟩ hrs
    have heq : (endpointSites a b ⟨r.val, by omega⟩).val =
        (endpointSites a b ⟨s.val, by omega⟩).val := by
      simpa [endpointSites, r.isLt, s.isLt] using (congrArg Fin.val he).symm
    rw [heq, Nat.dist_self] at h
    simp at h
  have hbs : StrictAnti b := by
    intro r s hrs
    refine lt_of_le_of_ne (hb hrs.le) ?_
    intro he
    have hrs' : (⟨r.val + 3, by omega⟩ : Fin 6) < ⟨s.val + 3, by omega⟩ := by
      change r.val + 3 < s.val + 3
      exact Nat.add_lt_add_right hrs 3
    have h := hg _ _ hrs'
    have heq : (endpointSites a b ⟨r.val + 3, by omega⟩).val =
        (endpointSites a b ⟨s.val + 3, by omega⟩).val := by
      simpa [endpointSites] using congrArg (fun x : Fin n => x.val + 2) he.symm
    rw [heq, Nat.dist_self] at h
    simp at h
  exact ⟨⟨a, b, has, hbs, hne, hg⟩, rfl⟩

/-- The separated complement is bounded on all convex subsets of the rectangle. -/
theorem exceptional_geometry_bound {n : ℕ} (hn : 11 ≤ n) :
    (exceptionalGeometry n).card ≤ 233 * n ^ 5 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hs : exceptionalGeometry n ⊆ missingRowStates n ∪ (badTuples n).image decodeRows := by
    intro I hI
    obtain ⟨hc, hsep⟩ := Finset.mem_filter.mp hI
    have hconv : I.OrdConnected := (Finset.mem_filter.mp hc).2
    by_cases hm : ∃ r, ∀ x, (r, x) ∉ I
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, hm⟩)
    · push Not at hm
      obtain ⟨a, b, hab⟩ := row_representation hn2 I hconv
      have hne : ∀ r, a r ≤ b r := by
        intro r
        obtain ⟨x, hx⟩ := hm r
        rw [← hab] at hx
        exact hx.1.trans hx.2
      have hbad : ∃ r s : Fin 6, r < s ∧
          min (Nat.dist (endpointSites a b r).val (endpointSites a b s).val)
            ((n + 4) - Nat.dist (endpointSites a b r).val (endpointSites a b s).val) < 8 := by
        by_contra hh
        push Not at hh
        apply hsep
        rw [← hab]
        exact separated_of_distances a b (hab ▸ hconv) hne hh
      obtain ⟨r, s, hrs, hdist⟩ := hbad
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨raw a b, ?_, (decodeRows_raw a b).trans hab⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨(r, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [site_raw] using hdist⟩
  calc
    (exceptionalGeometry n).card ≤ (missingRowStates n ∪ (badTuples n).image decodeRows).card :=
      Finset.card_le_card hs
    _ ≤ (missingRowStates n).card + ((badTuples n).image decodeRows).card := Finset.card_union_le _ _
    _ ≤ 3 * n ^ 4 + 225 * n ^ 5 := Nat.add_le_add (missing_row_bound hn2)
      (Finset.card_image_le.trans (badTuples_bound hn2))
    _ ≤ 233 * n ^ 5 := by
      have hp : n ^ 4 ≤ n ^ 5 := calc
        n ^ 4 = n ^ 4 * 1 := by omega
        _ ≤ n ^ 4 * n := Nat.mul_le_mul_left _ (by omega)
        _ = n ^ 5 := by ring
      omega

end D5.S3.Combinatorics.Geometry.RowmotionExceptionalGeometry
