/- GID: D5/S3/Combinatorics/OddIndependence/OddGridPadding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddIndependence/OddGridPadding
   mirror-E: none(waiver:coordinate-bridge)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Zero padding relates coordinate crosses to four-neighbour grid vertices. -/

import D5.S3.Combinatorics.OddIndependence.OddGridDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddIndependence.OddGridPadding

open OddGridDefs

/-- The indicator of the grid set, with two initial zero rows and columns. -/
def padded {n : ℕ} (S : Finset (Fin n × Fin n)) (x y : ℕ) : Bool :=
  decide ((x, y) ∈ S.image (fun v => (v.1.val + 2, v.2.val + 2)))

/-- A cross in the padded coordinates has an interior grid centre. -/
theorem cross_of_padded {n : ℕ} (S : Finset (Fin n × Fin n)) (x y : ℕ)
    (h : padded S x (y + 1) = true ∧ padded S (x + 1) y = true ∧
      padded S (x + 1) (y + 2) = true ∧ padded S (x + 2) (y + 1) = true) :
    ∃ v : Fin n × Fin n, 4 ≤ ((grid n).neighborSet v).ncard ∧
      ∀ w, (grid n).Adj v w → w ∈ S := by
  classical
  have hb (a b : ℕ) : padded S a b = true ↔
      ∃ v ∈ S, v.1.val + 2 = a ∧ v.2.val + 2 = b := by
    simp [padded, Finset.mem_image, Prod.mk.injEq]
  obtain ⟨u, hu, hux, huy⟩ := (hb _ _).mp h.1
  obtain ⟨l, hl, hlx, hly⟩ := (hb _ _).mp h.2.1
  obtain ⟨r, hr, hrx, hry⟩ := (hb _ _).mp h.2.2.1
  obtain ⟨d, hd, hdx, hdy⟩ := (hb _ _).mp h.2.2.2
  have hxu := u.1.isLt
  have hxl := l.1.isLt
  have hxd := d.1.isLt
  have hyl := l.2.isLt
  have hyr := r.2.isLt
  have hyu := u.2.isLt
  let v : Fin n × Fin n := (⟨x - 1, by omega⟩, ⟨y - 1, by omega⟩)
  have hneul : u ≠ l := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.1.val) he
    omega
  have hneur : u ≠ r := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.1.val) he
    omega
  have hneud : u ≠ d := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.1.val) he
    omega
  have hnelr : l ≠ r := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.2.val) he
    omega
  have hneld : l ≠ d := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.1.val) he
    omega
  have hnerd : r ≠ d := by
    intro he
    have := congrArg (fun a : Fin n × Fin n => a.1.val) he
    omega
  have huv : (grid n).Adj v u := by
    simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
    left
    constructor
    · right; dsimp [v]; omega
    · apply Fin.ext; dsimp [v]; omega
  have hlv : (grid n).Adj v l := by
    simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
    right
    constructor
    · right; dsimp [v]; omega
    · apply Fin.ext; dsimp [v]; omega
  have hrv : (grid n).Adj v r := by
    simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
    right
    constructor
    · left; dsimp [v]; omega
    · apply Fin.ext; dsimp [v]; omega
  have hdv : (grid n).Adj v d := by
    simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
    left
    constructor
    · left; dsimp [v]; omega
    · apply Fin.ext; dsimp [v]; omega
  refine ⟨v, ?_, ?_⟩
  · have hsub : (({u, l, r, d} : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) ⊆
        (grid n).neighborSet v := by
      intro a ha
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({u, l, r, d} : Finset (Fin n × Fin n)).card = 4 := by
      simp [hneul, hneur, hneud, hnelr, hneld, hnerd]
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset, hcard] at hle
    exact hle
  · intro w hw
    have hwu : w = u ∨ w = l ∨ w = r ∨ w = d := by
      simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj] at hw
      rcases hw with ⟨hwx, hwy⟩ | ⟨hwy, hwx⟩
      · have hwy' := congrArg Fin.val hwy
        rcases hwx with hwx | hwx
        · right; right; right
          apply Prod.ext <;> apply Fin.ext <;> dsimp [v] at * <;> omega
        · left
          apply Prod.ext <;> apply Fin.ext <;> dsimp [v] at * <;> omega
      · have hwx' := congrArg Fin.val hwx
        rcases hwy with hwy | hwy
        · right; right; left
          apply Prod.ext <;> apply Fin.ext <;> dsimp [v] at * <;> omega
        · right; left
          apply Prod.ext <;> apply Fin.ext <;> dsimp [v] at * <;> omega
    rcases hwu with rfl | rfl | rfl | rfl <;> assumption

end D5.S3.Combinatorics.OddIndependence.OddGridPadding
