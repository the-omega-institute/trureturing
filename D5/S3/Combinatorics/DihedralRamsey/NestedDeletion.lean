/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedDeletion
   mirror-E: none(waiver:nested-matching-edge-deletion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Removing one host vertex loses at most one cyclic nested matching edge. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedSelection
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedDeletion

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs NestedSelection Finset

/-- Removing the last host vertex loses at most one nested matching edge. -/
theorem delete_last {n k : ℕ} (hk : 1 < k) (G : SimpleGraph (Fin (n + 1)))
    (hcopy : CyclicEmbeddable (nestMatching (2 * k)) G) :
    CyclicEmbeddable (nestMatching (2 * (k - 1))) (G.comap Fin.castSucc) := by
  classical
  letI : NeZero (2 * k) := ⟨by omega⟩
  obtain ⟨ψ, hψ, c, hc, hG⟩ :=
    (NestedMatching.cyclic_iff_reflection (by omega) (by omega) G).mp hcopy
  let t : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
  let p : Fin (2 * k) → Fin (2 * k) := fun i => c - i
  have hp : Function.Involutive p := by
    intro i
    simp [p, sub_eq_add_neg]
  have hs : ∀ i, (i.val + (p i).val) % (2 * k) = c.val := by
    intro i
    have hh : i + p i = c := by simp [p]
    simpa only [Fin.val_add] using congrArg Fin.val hh
  have hne : ∀ i, i ≠ p i := by
    intro i hi
    have hh := hs i
    rw [← hi] at hh
    have hmod := congrArg (fun x : ℕ => x % 2) hh
    rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 * k from dvd_mul_right 2 k)] at hmod
    omega
  let S : Finset (Fin (2 * k)) := (univ.erase t).erase (p t)
  have size : S.card = 2 * (k - 1) := by
    dsimp [S]
    rw [card_erase_of_mem (mem_erase.mpr ⟨(hne t).symm, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  have keep : ∀ i ∈ S, p i ∈ S := by
    intro i hi
    have hpi : i ≠ p t := (mem_erase.mp hi).1
    have hit : i ≠ t := (mem_erase.mp (mem_erase.mp hi).2).1
    apply mem_erase.mpr
    refine ⟨?_, mem_erase.mpr ⟨?_, mem_univ _⟩⟩
    · intro h
      exact hit (hp.injective h)
    · intro h
      apply hpi
      have hh := congrArg p h
      simpa only [hp i] using hh
  let H : SimpleGraph (Fin (2 * k)) := SimpleGraph.fromRel fun i j =>
    i ∈ S ∧ j ∈ S ∧ (i.val + j.val) % (2 * k) = c.val
  have hH := (modular_sum_set (by omega) S c (by omega) H
    (by intro i hi; exact ⟨p i, keep i hi, hne i, hs i⟩)
    (by
      intro i hi j hj hij hs'
      apply (SimpleGraph.fromRel_adj _ _ _).mpr
      exact ⟨hij, Or.inl ⟨hi, hj, hs'⟩⟩)).2
  rw [size] at hH
  obtain ⟨χ, hχ, d, hd, hedge⟩ :=
    (NestedMatching.cyclic_iff_reflection (by omega) (by omega) H).mp hH
  letI : NeZero (2 * (k - 1)) := ⟨by omega⟩
  have support : ∀ i, χ i ∈ S := by
    intro i
    have hh : i + (d - i) = d := by simp
    have he := hedge i (d - i) (by simpa only [Fin.val_add] using congrArg Fin.val hh)
    have he' := (SimpleGraph.fromRel_adj _ _ _).mp he
    rcases he'.2 with h | h
    · exact h.1
    · exact h.2.1
  have below : ∀ i, (ψ (χ i)).val < n := by
    intro i
    have hmem := support i
    have hit : χ i ≠ t := (mem_erase.mp (mem_erase.mp hmem).2).1
    have hlt : χ i < t := by
      have hi := (χ i).isLt
      change (χ i).val < 2 * k - 1
      have hval : (χ i).val ≠ 2 * k - 1 := fun hh => hit (Fin.ext hh)
      omega
    have hh := hψ hlt
    have hb := (ψ t).isLt
    change (ψ (χ i)).val < (ψ t).val at hh
    omega
  let η : Fin (2 * (k - 1)) → Fin n := fun i => ⟨(ψ (χ i)).val, below i⟩
  have hη : StrictMono η := by
    intro i j hij
    exact hψ (hχ hij)
  apply (NestedMatching.cyclic_iff_reflection (by omega) (by omega)
    (G.comap Fin.castSucc)).mpr
  refine ⟨η, hη, d, hd, ?_⟩
  intro i j hij
  have he := hedge i j hij
  have he' := (SimpleGraph.fromRel_adj _ _ _).mp he
  have sum : ((χ i).val + (χ j).val) % (2 * k) = c.val := by
    rcases he'.2 with h | h
    · exact h.2.2
    · simpa only [Nat.add_comm] using h.2.2
  exact hG (χ i) (χ j) sum


end D5.S3.Combinatorics.DihedralRamsey.NestedDeletion
