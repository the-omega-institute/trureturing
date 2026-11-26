/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Three extensions at each ridge force a sharp count of minimum contact displacements. -/

module

public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The three extensions of a contact ridge constrain the whole displacement family. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

private def axes (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

private def extensions (F : Finset (Finset α)) (S : Finset α) : Finset α :=
  (axes F).filter fun i => i ∉ S ∧ insert i S ∈ F

private def link (F : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  (F.filter fun T => i ∈ T).image fun T => T.erase i

private theorem mem_axes {F : Finset (Finset α)} {i : α} :
    i ∈ axes F ↔ ∃ T ∈ F, i ∈ T := Finset.mem_biUnion

private theorem mem_extensions {F : Finset (Finset α)} {S : Finset α} {i : α} :
    i ∈ extensions F S ↔ i ∉ S ∧ insert i S ∈ F := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_axes.mpr ⟨_, h.2, Finset.mem_insert_self _ _⟩, h⟩

private theorem mem_link {F : Finset (Finset α)} {i : α} {S : Finset α} :
    S ∈ link F i ↔ i ∉ S ∧ insert i S ∈ F := by
  constructor
  · intro h
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hTF, hi⟩ := Finset.mem_filter.mp hT
    exact ⟨Finset.notMem_erase _ _, by simpa [Finset.insert_erase hi] using hTF⟩
  · rintro ⟨hi, hS⟩
    exact Finset.mem_image.mpr ⟨insert i S, Finset.mem_filter.mpr ⟨hS, Finset.mem_insert_self _ _⟩,
      Finset.erase_insert hi⟩

private theorem card_link {F : Finset (Finset α)} {i : α} :
    (link F i).card = (F.filter fun T => i ∈ T).card := by
  apply Finset.card_image_of_injOn
  intro T hT U hU heq
  have hiT := (Finset.mem_filter.mp hT).2
  have hiU := (Finset.mem_filter.mp hU).2
  exact (Finset.insert_erase hiT).symm.trans (congrArg (insert i) heq |>.trans
    (Finset.insert_erase hiU))

private theorem extensions_link {F : Finset (Finset α)} {i : α} {S : Finset α}
    (hi : i ∉ S) :
    extensions (link F i) S = extensions F (insert i S) := by
  ext j
  rw [mem_extensions, mem_extensions, mem_link]
  constructor
  · rintro ⟨hjS, hij, hF⟩
    have hji : j ≠ i := fun h => hij (h ▸ Finset.mem_insert_self j S)
    rw [Finset.insert_comm] at hF
    exact ⟨by simp [hji, hjS], hF⟩
  · rintro ⟨hj, hF⟩
    have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
    have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self j S)
    have hF' : insert i (insert j S) ∈ F := by
      rwa [Finset.insert_comm]
    exact ⟨hjS, by simp [Ne.symm hji, hi], hF'⟩

private theorem sum_link_card (F : Finset (Finset α)) :
    (∑ i ∈ axes F, (link F i).card) = ∑ T ∈ F, T.card := by
  calc
    _ = ∑ i ∈ axes F, ∑ T ∈ F.filter (fun T => i ∈ T), (1 : ℕ) := by
      simp [card_link]
    _ = ∑ i ∈ axes F, ∑ T ∈ F, if i ∈ T then (1 : ℕ) else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ T ∈ F, ∑ i ∈ axes F, if i ∈ T then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      have hfilter : (axes F).filter (fun i => i ∈ T) = T := by
        ext i
        exact Finset.mem_filter.trans ⟨And.right, fun hi => ⟨mem_axes.mpr ⟨T, hT, hi⟩, hi⟩⟩
      simp [← Finset.sum_filter, hfilter]

private theorem weight_count (d : ℕ) (F : Finset (Finset α)) (hne : F.Nonempty)
    (hsize : ∀ T ∈ F, T.card = d)
    (hthree : ∀ T ∈ F, ∀ i ∈ T, 3 ≤ (extensions F (T.erase i)).card) :
    (d + 2).choose 2 ≤ F.card ∧
      (0 < d → (d + 2 ≤ (axes F).card ∧
        ((axes F).card * (d + 1).choose 2 ≤ d * F.card))) := by
  induction d generalizing F with
  | zero =>
    exact ⟨by simpa using Finset.card_pos.mpr hne, by omega⟩
  | succ d ih =>
    have hlink (i : α) (hi : i ∈ axes F) : (d + 2).choose 2 ≤ (link F i).card := by
      obtain ⟨T, hT, hiT⟩ := mem_axes.mp hi
      have hne' : (link F i).Nonempty := ⟨T.erase i, mem_link.mpr
        ⟨Finset.notMem_erase _ _, by simpa [Finset.insert_erase hiT] using hT⟩⟩
      have hs' (S : Finset α) (hS : S ∈ link F i) : S.card = d := by
        obtain ⟨hiS, hSF⟩ := mem_link.mp hS
        have h := hsize _ hSF
        rw [Finset.card_insert_of_notMem hiS] at h
        omega
      have ht' (S : Finset α) (hS : S ∈ link F i) (j : α) (hj : j ∈ S) :
          3 ≤ (extensions (link F i) (S.erase j)).card := by
        obtain ⟨hiS, hSF⟩ := mem_link.mp hS
        have hji : j ≠ i := fun h => hiS (h ▸ hj)
        have h := hthree _ hSF j (Finset.mem_insert_of_mem hj)
        rw [Finset.erase_insert_of_ne hji.symm] at h
        rwa [extensions_link (fun hh => hiS (Finset.mem_of_mem_erase hh))]
      exact (ih _ hne' hs' ht').1
    have haxes : d + 3 ≤ (axes F).card := by
      obtain ⟨T, hT⟩ := hne
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < T.card by simp [hsize _ hT])
      have hs : ∀ j ∈ T.erase i, j ∈ axes F :=
        fun j hj => mem_axes.mpr ⟨T, hT, Finset.mem_of_mem_erase hj⟩
      have he : extensions F (T.erase i) ⊆ axes F :=
        fun j hj => (Finset.mem_filter.mp hj).1
      have hdis : Disjoint (T.erase i) (extensions F (T.erase i)) := by
        exact Finset.disjoint_left.mpr fun j hj hje => (Finset.mem_filter.mp hje).2.1 hj
      have hle := Finset.card_le_card (Finset.union_subset hs he)
      rw [Finset.card_union_of_disjoint hdis] at hle
      have hc := Finset.card_erase_add_one hi
      have ht := hsize _ hT
      have h3 := hthree _ hT i hi
      omega
    have hsum : (axes F).card * (d + 2).choose 2 ≤ (d + 1) * F.card := by
      calc
        _ = ∑ i ∈ axes F, (d + 2).choose 2 := by simp
        _ ≤ ∑ i ∈ axes F, (link F i).card := Finset.sum_le_sum hlink
        _ = ∑ _T ∈ F, (d + 1) := sum_link_card F |>.trans (Finset.sum_congr rfl hsize)
        _ = _ := by simp [Nat.mul_comm]
    have hbalance : (d + 3) * (d + 2).choose 2 = (d + 1) * (d + 3).choose 2 := by
      simpa [Nat.mul_comm, Nat.add_assoc] using Nat.choose_mul_succ_eq (d + 2) 2
    have hbound := Nat.mul_le_mul_right ((d + 2).choose 2) haxes
    have hprod := hbound.trans hsum
    rw [hbalance] at hprod
    exact ⟨Nat.le_of_mul_le_mul_left hprod (Nat.succ_pos d), fun _ => ⟨haxes, hsum⟩⟩

/-- Each ridge of a nonempty uniform displacement family has at least three
possible extensions. The number of displacements is then at least
`(d + 2).choose 2`. Equality gives every `d`-subset of one `d + 2`-set. -/
public theorem card_and_eq_powerset_of_three_extensions (d : ℕ) (hd : 0 < d)
    (F : Finset (Finset α)) (hne : F.Nonempty)
    (hsize : ∀ T ∈ F, T.card = d)
    (hthree : ∀ T ∈ F, ∀ i ∈ T,
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ j ∈ ({a, b, c} : Finset α), j ∉ T.erase i ∧ insert j (T.erase i) ∈ F)) :
    (d + 2).choose 2 ≤ F.card ∧
      (F.card = (d + 2).choose 2 →
        ∃ A : Finset α, A.card = d + 2 ∧ F = A.powersetCard d) := by
  have hext (T : Finset α) (hT : T ∈ F) (i : α) (hi : i ∈ T) :
      3 ≤ (extensions F (T.erase i)).card := by
    obtain ⟨a, b, c, hab, hac, hbc, he⟩ := hthree T hT i hi
    have hsub : ({a, b, c} : Finset α) ⊆ extensions F (T.erase i) := by
      intro j hj
      have h := he j hj
      exact mem_extensions.mpr h
    simpa [hab, hac, hbc] using Finset.card_le_card hsub
  obtain ⟨hbound, h⟩ := weight_count d F hne hsize hext
  obtain ⟨haxes, hdouble⟩ := h hd
  refine ⟨hbound, fun hF => ⟨axes F, ?_⟩⟩
  have hb : d * (d + 2).choose 2 = (d + 2) * (d + 1).choose 2 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    simpa [Nat.mul_comm, Nat.add_assoc] using (Nat.choose_mul_succ_eq (e + 2) 2).symm
  rw [hF, hb] at hdouble
  have hpos : 0 < (d + 1).choose 2 := Nat.choose_pos (by omega)
  have hcard : (axes F).card = d + 2 :=
    le_antisymm (Nat.le_of_mul_le_mul_right hdouble hpos) haxes
  refine ⟨hcard, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro T hT
    exact Finset.mem_powersetCard.mpr ⟨fun i hi => mem_axes.mpr ⟨T, hT, hi⟩, hsize _ hT⟩
  · rw [Finset.card_powersetCard, hcard, hF, ← Nat.choose_symm (show 2 ≤ d + 2 by omega)]
    simp

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
