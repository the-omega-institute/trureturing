/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyMatching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyMatching
   mirror-E: none(waiver:antipodal-matching-colouring)
   anchors: [mathlib/module/Mathlib.Order.Interval.Set.Monotone]
   utility: none
   digest: Short edges with an antipodal matching avoid odd alternating paths. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyRanks
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyOrder
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring
import Mathlib.Order.Interval.Set.Monotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs

/-- Adding antipodal edges supplies one extra red neighbour while preserving odd path avoidance. -/
theorem antipodal_circular_colouring {n r : ℕ} (heven : n % 2 = 0)
    (hn : 2 * r < n) :
    ∃ G : SimpleGraph (Fin n),
      letI := Classical.propDecidable
      ¬DihedralEmbeddable (altPath (2 * r + 3)) G ∧
        ∀ x, Gᶜ.degree x ≤ n - 2 * r - 2 := by
  classical
  let a := 2 * r + 3
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y =>
    (Nat.dist x.val y.val ≤ r ∨ n - Nat.dist x.val y.val ≤ r) ∨
      Nat.dist x.val y.val = n / 2
  have hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧
      ((Nat.dist x.val y.val ≤ r ∨ n - Nat.dist x.val y.val ≤ r) ∨
        Nat.dist x.val y.val = n / 2) := by
    intro x y
    simp only [G, SimpleGraph.fromRel_adj, Nat.dist_comm y.val x.val, or_self]
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨s, refl, ψ, hψ, hE⟩
    obtain ⟨q, hq, hdist⟩ := alternating_ranks a
    have hval := dihedralPerm_val (k := a) s refl
    have hinj := dihedralPerm_injective a s refl
    have stretch_arcs := circular_order_stretch ψ hψ
    have central : ∀ (j : ℕ) (hjlt : j + 1 < a), (j = r ∨ j = r + 1) →
        ∃ (x y : Fin a), x = q ⟨j, by dsimp [a]; omega⟩ ∧
          y = q ⟨j + 1, by dsimp [a]; omega⟩ ∧
          Nat.dist (ψ (dihedralPerm s refl x)).val
            (ψ (dihedralPerm s refl y)).val = n / 2 := by
      intro j hjlt hj
      let x := q ⟨j, by omega⟩
      let y := q ⟨j + 1, hjlt⟩
      refine ⟨x, y, rfl, rfl, ?_⟩
      have hxy : Nat.dist x.val y.val = a - 1 - j := by
        rw [hq, hq, hdist j hjlt]
      let u := dihedralPerm s refl x
      let v := dihedralPerm s refl y
      have hu := hval x
      have hv := hval y
      change u.val = _ at hu
      change v.val = _ at hv
      have harcs : r + 1 ≤ Nat.dist u.val v.val ∧
          r + 1 ≤ a - Nat.dist u.val v.val := by
        have hx := x.isLt
        have hy := y.isLt
        have hs : s % a < a := Nat.mod_lt _ (by dsimp [a]; omega)
        unfold Nat.dist at hxy ⊢
        cases refl <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu hv <;>
          split_ifs at hu hv <;> dsimp [a] at * <;> omega
      have hstretch := stretch_arcs u v
      have hedge : (altPath a).Adj x y := by
        rw [altPath, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨j, hjlt, hq _, hq _⟩⟩
        intro he
        have he' := congrArg Fin.val he
        unfold Nat.dist at hxy
        dsimp [a] at *
        omega
      have hred := (hadj _ _).mp (hE x y hedge)
      change ψ u ≠ ψ v ∧
        ((Nat.dist (ψ u).val (ψ v).val ≤ r ∨
          n - Nat.dist (ψ u).val (ψ v).val ≤ r) ∨
          Nat.dist (ψ u).val (ψ v).val = n / 2) at hred
      dsimp [u, v, a] at harcs hstretch hred
      omega
    obtain ⟨x, y, hx, hy, hxy⟩ := central r (by dsimp [a]; omega) (Or.inl rfl)
    obtain ⟨y', z, hy', hz, hyz⟩ :=
      central (r + 1) (by dsimp [a]; omega) (Or.inr rfl)
    have hyy : y = y' := by rw [hy, hy']
    rw [← hyy] at hyz
    have heq : ψ (dihedralPerm s refl x) = ψ (dihedralPerm s refl z) := by
      apply Fin.ext
      have h₁ := (ψ (dihedralPerm s refl x)).isLt
      have h₂ := (ψ (dihedralPerm s refl y)).isLt
      have h₃ := (ψ (dihedralPerm s refl z)).isLt
      unfold Nat.dist at hxy hyz
      omega
    have heq' := hinj (hψ.injective heq)
    rw [hx, hz] at heq'
    have heq'' := congrArg Fin.val (q.injective heq')
    change r = r + 1 + 1 at heq''
    omega
  · intro x
    have hsub : ∀ y : Fin n, (y - x).val =
        if x.val ≤ y.val then y.val - x.val else n + y.val - x.val := by
      intro y
      have hx := x.isLt
      have hy := y.isLt
      split_ifs with h
      · exact Fin.sub_val_of_le h
      · rw [Fin.sub_def]
        simp only [Fin.val_mk, Nat.mod_eq_of_lt (by omega : n - x.val + y.val < n)]
        omega
    have hblue : ∀ y : Gᶜ.neighborSet x,
        r + 1 ≤ (y.val - x).val ∧ (y.val - x).val ≤ n - r - 1 ∧
          (y.val - x).val ≠ n / 2 := by
      intro y
      have hy := y.prop
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.compl_adj, hadj] at hy
      have hxlt := x.isLt
      have hylt := y.val.isLt
      have hne : x ≠ y.val := hy.1
      have hd : r < Nat.dist x.val y.val ∧ r < n - Nat.dist x.val y.val ∧
          Nat.dist x.val y.val ≠ n / 2 := by
        refine ⟨?_, ?_, ?_⟩
        · by_contra h
          exact hy.2 ⟨hne, Or.inl (Or.inl (by omega))⟩
        · by_contra h
          exact hy.2 ⟨hne, Or.inl (Or.inr (by omega))⟩
        · intro h
          exact hy.2 ⟨hne, Or.inr h⟩
      rw [hsub]
      unfold Nat.dist at hd
      split_ifs <;> omega
    let f : Gᶜ.neighborSet x → Fin (n - 2 * r - 2) := fun y =>
      ⟨if (y.val - x).val < n / 2 then (y.val - x).val - (r + 1)
        else (y.val - x).val - (r + 2), by
        have hy := hblue y
        split_ifs <;> omega⟩
    have hf : Function.Injective f := by
      intro y z he
      apply Subtype.ext
      apply Fin.ext
      have he' :
          (if (y.val - x).val < n / 2 then (y.val - x).val - (r + 1)
            else (y.val - x).val - (r + 2)) =
          (if (z.val - x).val < n / 2 then (z.val - x).val - (r + 1)
            else (z.val - x).val - (r + 2)) := congrArg Fin.val he
      have hylt := y.val.isLt
      have hzlt := z.val.isLt
      have hxlt := x.isLt
      have dy := hblue y
      have dz := hblue z
      have hd : (y.val - x).val = (z.val - x).val := by
        split_ifs at he' <;> omega
      simp only [hsub] at hd
      split_ifs at hd <;> omega
    let I : Fintype (Gᶜ.neighborSet x) :=
      @Subtype.fintype (Fin n) (· ∈ Gᶜ.neighborSet x)
        (fun _ => Classical.propDecidable _) (Fin.fintype n)
    have hcard := @Fintype.card_le_of_injective (Gᶜ.neighborSet x)
      (Fin (n - 2 * r - 2)) I (Fin.fintype _) f hf
    change @SimpleGraph.degree _ Gᶜ x I ≤ _
    rw [← @SimpleGraph.card_neighborSet_eq_degree _ Gᶜ x I]
    simpa only [Fintype.card_fin] using hcard


end D5.S3.Combinatorics.DihedralRamsey
