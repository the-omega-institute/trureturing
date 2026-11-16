/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: Bound actual twelve-cycle low incidences and force a capacity contradiction. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Batteries.Tactic.OpenPrivate

/-! Incidence capacity and actual low vertices on an embedded twelve-cycle. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwelveCapacity

open SimpleGraph GirthSliceCounting
open scoped BigOperators

attribute [local instance] Classical.propDecidable

open private lowPair low_pair_excluded_by_common_high
  low_pair_excluded_by_short_paths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private unique_low_partner from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricLowPartners

/-- Count actual incidences. A point on the right contributes at most one,
plus one precisely when it has at least two neighbors on the left. -/
theorem incidence_capacity
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (W : Finset A) (U : Finset B) (r : A → B → Prop) [DecidableRel r]
    (hW : ∀ x ∈ W, ∃ y ∈ U, r x y)
    (hU : ∀ y ∈ U, (W.filter fun x => r x y).card ≤ 2) :
    W.card ≤ U.card + (U.filter fun y => 2 ≤ (W.filter fun x => r x y).card).card := by
  have hlower : W.card ≤ ∑ x ∈ W, (U.bipartiteAbove r x).card := by
    calc
      W.card = ∑ _x ∈ W, (1 : ℕ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hW x hx
        exact Finset.card_pos.mpr
          ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
  have hupper : (∑ y ∈ U, (W.bipartiteBelow r y).card) ≤
      U.card + (U.filter fun y => 2 ≤ (W.filter fun x => r x y).card).card := by
    calc
      _ ≤ ∑ y ∈ U, (1 + if 2 ≤ (W.filter fun x => r x y).card then 1 else 0) := by
        apply Finset.sum_le_sum
        intro y hy
        change (W.filter fun x => r x y).card ≤ _
        have hh := hU y hy
        split_ifs <;> omega
      _ = U.card + ∑ y ∈ U,
          (if 2 ≤ (W.filter fun x => r x y).card then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = _ := by
        rw [Finset.card_eq_sum_ones
          (U.filter fun y => 2 ≤ (W.filter fun x => r x y).card), Finset.sum_filter]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := W) (t := U)] at hlower
  exact hlower.trans hupper

/-- Nonantipodal distinct same-parity indices in C12 have a real cycle
path of length two or four. Only this finite index fact is computed. -/
private theorem nonopposite_same_parity_path_witness :
    ∀ i j : Fin 12, i ≠ j → i.val % 2 = j.val % 2 → j ≠ i + 6 →
      (∃ k : Fin 12, (cycleGraph 12).Adj i k ∧ (cycleGraph 12).Adj j k) ∨
      ∃ p m q : Fin 12, (cycleGraph 12).Adj i p ∧ (cycleGraph 12).Adj p m ∧
        (cycleGraph 12).Adj m q ∧ (cycleGraph 12).Adj j q ∧ i ≠ m ∧ p ≠ q := by
  decide +kernel

private def front (i : Fin 6) : Fin 12 := ⟨i.val, by omega⟩

private theorem diameter_canonical_witness :
    ∀ i j : Fin 12, j = i + 6 →
      ∃ k : Fin 6,
        (i = front k ∧ j = front k + 6) ∨
        (j = front k ∧ i = front k + 6) := by
  decide +kernel

private theorem same_slot_indices :
    ∀ i j : Fin 6, i.val / 2 = j.val / 2 →
      i = j ∨ front j = front i + 1 ∨ front i = front j + 1 := by
  decide +kernel

private theorem adjacent_diameter_indices :
    ∀ i : Fin 12,
      (cycleGraph 12).Adj i (i + 1) ∧
      (cycleGraph 12).Adj (i + 6) ((i + 1) + 6) ∧
      i ≠ i + 6 ∧ i + 1 ≠ (i + 1) + 6 := by
  decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem opposite_side_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b : V} (ha : a ∈ L) (hb : b ∈ R) : ¬ lowPair G a b := by
  rintro ⟨w, _hw, haw, hbw⟩
  have hwR := hpart.mem_of_mem_adj ha haw
  have hbL := hpart.symm.mem_of_mem_adj hwR hbw.symm
  exact Set.disjoint_left.mp hpart.disjoint hbL hb

private theorem nonopposite_same_parity_low_pair_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    {i j : Fin 12} (hij : i ≠ j) (hpar : i.val % 2 = j.val % 2)
    (hopp : j ≠ i + 6) (hiR : c i ∈ R) : ¬ lowPair G (c i) (c j) := by
  have hcij : c i ≠ c j := fun he => hij (hc he)
  rcases nonopposite_same_parity_path_witness i j hij hpar hopp with
    ⟨k, hik, hjk⟩ | ⟨p, m, q, hip, hpm, hmq, hjq, him, hpq⟩
  · exact low_pair_excluded_by_common_high hpart hg hiR (hc3 k)
      (hcycle i k hik) (hcycle j k hjk) hcij
  · exact low_pair_excluded_by_short_paths hpart hg hiR (hc3 p) (hc3 q)
      (hcycle i p hip) (hcycle p m hpm) (hcycle m q hmq) (hcycle j q hjq)
      hcij (fun he => him (hc he)) (fun he => hpq (hc he))

/-- An actual low shared by two distinct C12 high vertices joins a diameter.
The distinctness premise is essential: lowPair also admits diagonal pairs. -/
private theorem cycle_low_pair_is_diameter
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {i j : Fin 12} (hij : i ≠ j) (hp : lowPair G (c i) (c j)) : j = i + 6 := by
  by_contra hopp
  by_cases hpar : i.val % 2 = j.val % 2
  · by_cases hi0 : i.val % 2 = 0
    · exact nonopposite_same_parity_low_pair_excluded hpart.symm hg c hc hc3 hcycle
        hij hpar hopp (hcL i hi0) hp
    · have hi1 : i.val % 2 = 1 := by omega
      exact nonopposite_same_parity_low_pair_excluded hpart hg c hc hc3 hcycle
        hij hpar hopp (hcR i hi1) hp
  · by_cases hi0 : i.val % 2 = 0
    · have hj1 : j.val % 2 = 1 := by omega
      exact opposite_side_low_pair_excluded hpart (hcL i hi0) (hcR j hj1) hp
    · have hi1 : i.val % 2 = 1 := by omega
      have hj0 : j.val % 2 = 0 := by omega
      exact opposite_side_low_pair_excluded hpart.symm (hcR i hi1) (hcL j hj0) hp

/-- Two actual three-step paths around adjacent diameters have the same
endpoints. Girth forces their first internal vertices to agree, contradicting
the degrees two and three. No skeleton or abstract-pair premise is used. -/
private theorem adjacent_diameters_excluded_of_mem
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (i : Fin 12) (hi : c i ∈ L)
    (hp : lowPair G (c i) (c (i + 6))) :
    ¬ lowPair G (c (i + 1)) (c ((i + 1) + 6)) := by
  rcases hp with ⟨l, hl, hil, hi6l⟩
  rintro ⟨m, hm, hi1m, hi7m⟩
  obtain ⟨ha, hb, hn, hn'⟩ := adjacent_diameter_indices i
  have h02 : c i ≠ c (i + 6) := fun he => hn (hc he)
  have h13 : l ≠ c ((i + 1) + 6) := by
    intro he
    rw [he, hc3] at hl
    omega
  have h02' : c i ≠ m := by
    intro he
    rw [← he, hc3] at hm
    omega
  have h13' : c (i + 1) ≠ c ((i + 1) + 6) := fun he => hn' (hc he)
  have he := three_walk_endpoint_injective hpart hg hi hi
    hil hi6l.symm (hcycle _ _ hb)
    (hcycle _ _ ha) hi1m hi7m.symm h02 h13 h02' h13' ⟨rfl, rfl⟩
  have hlc : l = c (i + 1) := he.2.1
  rw [hlc, hc3] at hl
  omega

private theorem adjacent_diameters_excluded
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    (i : Fin 12) (hp : lowPair G (c i) (c (i + 6))) :
    ¬ lowPair G (c (i + 1)) (c ((i + 1) + 6)) := by
  by_cases hi0 : i.val % 2 = 0
  · exact adjacent_diameters_excluded_of_mem hpart hg c hc hc3 hcycle i (hcL i hi0) hp
  · have hi1 : i.val % 2 = 1 := by omega
    exact adjacent_diameters_excluded_of_mem hpart.symm hg c hc hc3 hcycle i (hcR i hi1) hp

/-- The actual embedded cycle vertex set. -/
def cycleVertices (c : Fin 12 → V) : Finset V := Finset.univ.image c

/-- All actual degree-two vertices with at least two actual cycle neighbors. -/
def internalLows (G : SimpleGraph V) (c : Fin 12 → V) : Finset V :=
  (degreeTwo G Finset.univ).filter fun l =>
    2 ≤ ((cycleVertices c).filter fun x => G.Adj x l).card

private def occupiedDiameters (G : SimpleGraph V) (c : Fin 12 → V) : Finset (Fin 6) :=
  Finset.univ.filter fun k => lowPair G (c (front k)) (c (front k + 6))

/-- Group the six real diameters in three consecutive pairs. Actual girth
excludes simultaneous occupancy inside each pair. -/
private theorem occupied_diameters_card_le_three
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R) :
    (occupiedDiameters G c).card ≤ 3 := by
  let slot : Fin 6 → Fin 3 := fun k => ⟨k.val / 2, by omega⟩
  have hinj : Set.InjOn slot (↑(occupiedDiameters G c) : Set (Fin 6)) := by
    intro i hi j hj he
    have hs : i.val / 2 = j.val / 2 := congrArg Fin.val he
    have hpi : lowPair G (c (front i)) (c (front i + 6)) := (Finset.mem_filter.mp hi).2
    have hpj : lowPair G (c (front j)) (c (front j + 6)) := (Finset.mem_filter.mp hj).2
    rcases same_slot_indices i j hs with hij | hij | hji
    · exact hij
    · exact False.elim ((adjacent_diameters_excluded hpart hg c hc hc3 hcycle hcL hcR
        (front i) hpi) (by simpa only [hij] using hpj))
    · exact False.elim ((adjacent_diameters_excluded hpart hg c hc hc3 hcycle hcL hcR
        (front j) hpj) (by simpa only [hji] using hpi))
  have hcard := Finset.card_le_card_of_injOn slot
    (t := (Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _) hinj
  simpa using hcard

/-- Every actual internal low lies over an occupied canonical diameter.
This statement covers all low witnesses, not only chosen witnesses. -/
private theorem internal_low_diameter_witness
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R)
    {l : V} (hl : l ∈ internalLows G c) :
    ∃ k ∈ occupiedDiameters G c, G.Adj (c (front k)) l := by
  have hl2 : G.degree l = 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
  have hn : 1 < ((cycleVertices c).filter fun x => G.Adj x l).card :=
    lt_of_lt_of_le (by decide) (Finset.mem_filter.mp hl).2
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hn
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hb).1
  have hij : i ≠ j := fun he => hab (congrArg c he)
  have hil : G.Adj (c i) l := (Finset.mem_filter.mp ha).2
  have hjl : G.Adj (c j) l := (Finset.mem_filter.mp hb).2
  have hd := cycle_low_pair_is_diameter hpart hg c hc hc3 hcycle hcL hcR hij
    ⟨l, hl2, hil, hjl⟩
  obtain ⟨k, hk | hk⟩ := diameter_canonical_witness i j hd
  · refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact ⟨l, hl2, by simpa only [hk.1] using hil, by simpa only [hk.2] using hjl⟩
    · simpa only [hk.1] using hil
  · refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact ⟨l, hl2, by simpa only [hk.1] using hjl, by simpa only [hk.2] using hil⟩
    · simpa only [hk.1] using hjl

/-- At most three actual lows can have two C12 neighbors. Uniqueness of a
low at each high vertex prevents multiple lows on the same diameter. -/
theorem internal_low_count_le_three
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R) :
    (internalLows G c).card ≤ 3 := by
  have hex := fun i => unique_low_partner hdeg hlow (hc3 i) (hchigh i)
  choose w p hw _hp _hcp _hcw _hpw _hN _huniqP huniqW using hex
  have hsub : internalLows G c ⊆ (occupiedDiameters G c).image (fun k => w (front k)) := by
    intro l hl
    obtain ⟨k, hk, hkl⟩ := internal_low_diameter_witness hpart hg c hc hc3 hcycle hcL hcR hl
    have hl2 : G.degree l = 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
    exact Finset.mem_image.mpr ⟨k, hk, (huniqW (front k) l hl2 hkl).symm⟩
  calc
    (internalLows G c).card ≤ ((occupiedDiameters G c).image (fun k => w (front k))).card :=
      Finset.card_le_card hsub
    _ ≤ (occupiedDiameters G c).card := Finset.card_image_le
    _ ≤ 3 := occupied_diameters_card_le_three hpart hg c hc hc3 hcycle hcL hcR

/-- The capacity inequality uses every actual low in the graph. A low has
at most two cycle neighbors because its full graph degree is two. -/
theorem cycle_capacity_bound
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2) :
    12 ≤ (degreeTwo G Finset.univ).card + (internalLows G c).card := by
  have hW : ∀ x ∈ cycleVertices c, ∃ l ∈ degreeTwo G Finset.univ, G.Adj x l := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, p, hl, _hp, _hcp, hcl, _rest⟩ :=
      unique_low_partner hdeg hlow (hc3 i) (hchigh i)
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hcl⟩
  have hU : ∀ l ∈ degreeTwo G Finset.univ,
      ((cycleVertices c).filter fun x => G.Adj x l).card ≤ 2 := by
    intro l hl
    have hsub : (cycleVertices c).filter (fun x => G.Adj x l) ⊆ G.neighborFinset l := by
      intro x hx
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hx).2.symm
    have hh := Finset.card_le_card hsub
    simpa only [SimpleGraph.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hl).2] using hh
  have hcap := incidence_capacity (cycleVertices c) (degreeTwo G Finset.univ) G.Adj hW hU
  have hcard : (cycleVertices c).card = 12 := by
    rw [cycleVertices, Finset.card_image_of_injective _ hc]
    simp
  simpa only [hcard, internalLows] using hcap

/-- With eight actual low vertices the C12 high component would require
12 <= 8 + 3 incidences after accounting for its internal lows. -/
theorem twelve_cycle_impossible
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hcount : (degreeTwo G Finset.univ).card = 8)
    (c : Fin 12 → V) (hc : Function.Injective c)
    (hc3 : ∀ i, G.degree (c i) = 3)
    (hchigh : ∀ i, (degreeThree G (G.neighborFinset (c i))).card = 2)
    (hcycle : ∀ i j, (cycleGraph 12).Adj i j → G.Adj (c i) (c j))
    (hcL : ∀ i, i.val % 2 = 0 → c i ∈ L)
    (hcR : ∀ i, i.val % 2 = 1 → c i ∈ R) : False := by
  have hinternal := internal_low_count_le_three hpart hdeg hlow hg c hc hc3 hchigh hcycle hcL hcR
  have hcapacity := cycle_capacity_bound hdeg hlow c hc hc3 hchigh
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwelveCapacity
