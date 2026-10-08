/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyStar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyStar
   mirror-E: none(waiver:shared-star-degree-characterization)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Star placement under either dihedral orientation is characterized by degree. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs Finset

/-- A star can be cyclically placed precisely when its centre has enough neighbours. -/
theorem star_iff_degree {b n : ℕ} (hb : 2 ≤ b) (refl : Bool)
    (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∃ (s : ℕ) (ψ : Fin b → Fin n), StrictMono ψ ∧
      ∀ i j, (startStar b).Adj i j →
        G.Adj (ψ (dihedralPerm s refl i)) (ψ (dihedralPerm s refl j))) ↔
      ∃ v, b - 1 ≤ G.degree v := by
  classical
  let z : Fin b := ⟨0, by omega⟩
  constructor
  · rintro ⟨s, ψ, hψ, he⟩
    let f := ψ ∘ dihedralPerm s refl
    have hf : Function.Injective f := hψ.injective.comp (dihedralPerm_injective b s refl)
    refine ⟨f z, ?_⟩
    have hsub : (univ.erase z).image f ⊆ G.neighborFinset (f z) := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      have hiz : i ≠ z := (mem_erase.mp hi).1
      apply (G.mem_neighborFinset _ _).mpr
      apply he z i
      rw [startStar, SimpleGraph.fromRel_adj]
      refine ⟨Ne.symm hiz, Or.inl ⟨rfl, ?_⟩⟩
      intro hi0
      exact hiz (Fin.ext hi0)
    have hc := card_le_card hsub
    rw [card_image_of_injective _ hf, card_erase_of_mem (mem_univ z), card_univ,
      Fintype.card_fin, G.card_neighborFinset_eq_degree] at hc
    exact hc
  · rintro ⟨v, hv⟩
    obtain ⟨t, ht, htc⟩ := exists_subset_card_eq hv
    have hvt : v ∉ t := fun h => G.notMem_neighborFinset_self v (ht h)
    let u := insert v t
    have huc : u.card = b := by
      dsimp [u]
      rw [card_insert_of_notMem hvt, htc]
      omega
    let ψ := u.orderEmbOfFin huc
    let q := (u.orderIsoOfFin huc).symm ⟨v, mem_insert_self v t⟩
    have hψq : ψ q = v := by
      exact congrArg Subtype.val ((u.orderIsoOfFin huc).apply_symm_apply _)
    let s := if refl then q.val + 1 else q.val
    have h0 : dihedralPerm s refl z = q := by
      apply Fin.ext
      cases refl
      · simp [dihedralPerm, s, z, Nat.mod_eq_of_lt q.is_lt]
      · simp only [dihedralPerm, s, z, ↓reduceIte, Nat.sub_zero]
        have he : b - 1 + (q.val + 1) = b + q.val := by omega
        rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt q.is_lt]
    refine ⟨s, ψ, ψ.strictMono, ?_⟩
    intro i j hij
    rw [startStar, SimpleGraph.fromRel_adj] at hij
    have leaf : ∀ i : Fin b, i.val ≠ 0 → G.Adj v (ψ (dihedralPerm s refl i)) := by
      intro i hi
      have him : ψ (dihedralPerm s refl i) ∈ u := u.orderEmbOfFin_mem huc _
      have hine : ψ (dihedralPerm s refl i) ≠ v := by
        intro heq
        have hd := ψ.injective (heq.trans hψq.symm)
        have hi0 := dihedralPerm_injective b s refl (hd.trans h0.symm)
        exact hi (congrArg Fin.val hi0)
      have hit : ψ (dihedralPerm s refl i) ∈ t :=
        (mem_insert.mp him).resolve_left hine
      exact (G.mem_neighborFinset _ _).mp (ht hit)
    rcases hij.2 with h | h
    · have hi : i = z := Fin.ext h.1
      subst i
      rw [h0, hψq]
      exact leaf j h.2
    · have hj : j = z := Fin.ext h.1
      subst j
      rw [h0, hψq]
      exact (leaf i h.2).symm

end D5.S3.Combinatorics.DihedralRamsey
