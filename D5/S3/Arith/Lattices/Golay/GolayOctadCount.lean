/- GID: D5/S3/Arith/Lattices/Golay/GolayOctadCount
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Golay/GolayOctadCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural binary-code second moment and the actual Golay octad count. -/

import D5.S3.Arith.Lattices.Golay.GolayEncoder
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-! # Octads from self-duality and the second weight moment

Two-coordinate projections are onto: failure would put a weight-two word in
the self-dual code. Translation makes their four fibers equicardinal. Counting
ordered distinct pairs of occupied coordinates then determines the weight-eight
coefficient from the spectrum and the all-ones complement involution.
-/

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

open scoped BigOperators
noncomputable section
namespace D5.S3.Arith.Lattices.Golay.GolayOctadCount
open GolayEncoder
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

abbrev Octad := {c : code // weight (c : Word) = 8}

private theorem bit_cases (a : F2) : a = 0 ∨ a = 1 := by
  have ha := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left; apply ZMod.val_injective 2; simpa using h
  · right; apply ZMod.val_injective 2; change a.val = 1; exact h

private def support (v : Word) : Finset (Fin 24) := {i | v i ≠ 0}

private theorem support_card (v : Word) : (support v).card = weight v := by
  simp only [support, Finset.card_eq_sum_ones, Finset.sum_filter, weight]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = 0 <;> simp [h]

private theorem complement_weight (v : Word) :
    weight v + weight (fun i => 1 + v i) = 24 := by
  unfold weight
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin 24, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases bit_cases (v i) with h | h <;> norm_num [h]
    _ = 24 := by simp

private def pairProjection (C : Submodule F2 Word) (i j : Fin 24) : C →+ F2 × F2 where
  toFun c := (c.val i, c.val j)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem pairProjection_surjective
    (C : Submodule F2 Word)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (hdual : coordinatePairing.orthogonal C = C)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v)
    (i j : Fin 24) (hij : i ≠ j) :
    Function.Surjective (pairProjection C i j) := by
  have hsep : ∃ c : C, c.val i ≠ c.val j := by
    by_contra h
    push_neg at h
    let v : Word := Pi.single i 1 + Pi.single j 1
    have hs : support v = {i, j} := by
      ext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [support, v, Pi.single_apply]
    have hw : weight v = 2 := by rw [← support_card, hs]; simp [hij]
    have hv : v ∈ C := by
      rw [← hdual, LinearMap.BilinForm.mem_orthogonal_iff]
      intro c hc
      change Matrix.dotProduct c v = 0
      rw [v, Matrix.dotProduct_add, Matrix.dotProduct_single_one,
        Matrix.dotProduct_single_one, h ⟨c, hc⟩]
      rcases bit_cases (c j) with h | h <;> norm_num [h]
    have hn : v ≠ 0 := by intro he; simp [he, weight] at hw
    have := hmin v hv hn
    omega
  obtain ⟨c, hc⟩ := hsep
  let one : C := ⟨fun _ => 1, hones⟩
  rintro ⟨a, b⟩
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · exact ⟨0, rfl⟩
  · rcases bit_cases (c.val i) with hi | hi <;>
      rcases bit_cases (c.val j) with hj | hj
    · exact (hc (hi.trans hj.symm)).elim
    · exact ⟨c, Prod.ext hi hj⟩
    · refine ⟨one + c, ?_⟩
      change (1 + c.val i, 1 + c.val j) = (0, 1)
      norm_num [hi, hj]
    · exact (hc (hi.trans hj.symm)).elim
  · rcases bit_cases (c.val i) with hi | hi <;>
      rcases bit_cases (c.val j) with hj | hj
    · exact (hc (hi.trans hj.symm)).elim
    · refine ⟨one + c, ?_⟩
      change (1 + c.val i, 1 + c.val j) = (1, 0)
      norm_num [hi, hj]
    · exact ⟨c, Prod.ext hi hj⟩
    · exact (hc (hi.trans hj.symm)).elim
  · exact ⟨one, rfl⟩

private theorem pair_fiber_card
    (C : Submodule F2 Word) (hcard : Nat.card C = 4096)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (hdual : coordinatePairing.orthogonal C = C)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v)
    (i j : Fin 24) (hij : i ≠ j) :
    (Finset.univ.filter fun c : C => c.val i = 1 ∧ c.val j = 1).card = 1024 := by
  let f := pairProjection C i j
  have hf := pairProjection_surjective C hones hdual hmin i j hij
  have he (p : F2 × F2) :
      (Finset.univ.filter fun c : C => f c = p).card =
        (Finset.univ.filter fun c : C => f c = (1, 1)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf p) (hf (1, 1))
  have hs := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset C) (Finset.univ : Finset (F2 × F2)) f
  simp only [he, Finset.mem_univ, Finset.filter_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul] at hs
  have hC : Fintype.card C = 4096 := by simpa [Nat.card_eq_fintype_card] using hcard
  have hp : (Finset.univ.filter fun c : C => f c = (1, 1)).card = 1024 := by
    omega
  simpa only [f, pairProjection, Prod.mk.injEq] using hp

end D5.S3.Arith.Lattices.Golay.GolayOctadCount
