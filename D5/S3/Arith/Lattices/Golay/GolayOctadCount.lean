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

private theorem one_add_one : (1 : F2) + 1 = 0 := by decide

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
      rcases bit_cases (v i) with h | h <;> norm_num [h, one_add_one]
    _ = 24 := by simp

def pairProjection (C : Submodule F2 Word) (i j : Fin 24) : C →+ F2 × F2 where
  toFun c := (c.val i, c.val j)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pairProjection_surjective
    (C : Submodule F2 Word)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (hdual : coordinatePairing.orthogonal C = C)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v)
    (i j : Fin 24) (hij : i ≠ j) :
    Function.Surjective (pairProjection C i j) := by
  have hsep : ∃ c : C, c.val i ≠ c.val j := by
    by_contra h
    push Not at h
    let v : Word := Pi.single i 1 + Pi.single j 1
    have hs : support v = {i, j} := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [support, v, hij]
      · by_cases hkj : k = j
        · subst k
          simp [support, v, Ne.symm hij]
        · simp [support, v, Pi.single_apply, hki, hkj]
    have hw : weight v = 2 := by rw [← support_card, hs]; simp [hij]
    have hv : v ∈ C := by
      rw [← hdual, LinearMap.BilinForm.mem_orthogonal_iff]
      intro c hc
      change dotProduct c (Pi.single i 1 + Pi.single j 1) = 0
      rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one]
      have he : c i = c j := h ⟨c, hc⟩
      rw [he]
      rcases bit_cases (c j) with h | h <;> norm_num [h, one_add_one]
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
      norm_num [hi, hj, one_add_one]
    · exact (hc (hi.trans hj.symm)).elim
  · rcases bit_cases (c.val i) with hi | hi <;>
      rcases bit_cases (c.val j) with hj | hj
    · exact (hc (hi.trans hj.symm)).elim
    · refine ⟨one + c, ?_⟩
      change (1 + c.val i, 1 + c.val j) = (1, 0)
      norm_num [hi, hj, one_add_one]
    · exact ⟨c, Prod.ext hi hj⟩
    · exact (hc (hi.trans hj.symm)).elim
  · exact ⟨one, rfl⟩

theorem pair_fiber_card
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
  change (Finset.univ.filter fun c : C => (c.val i, c.val j) = (1, 1)).card = 1024 at hp
  simpa only [Prod.mk.injEq] using hp

private theorem bit_ne_zero (a : F2) : a ≠ 0 ↔ a = 1 := by
  rcases bit_cases a with rfl | rfl <;> norm_num

private theorem word_pair_count (v : Word) :
    (∑ p : Fin 24 × Fin 24,
      if p.1 ≠ p.2 ∧ v p.1 = 1 ∧ v p.2 = 1 then 1 else 0) =
        weight v * (weight v - 1) := by
  have he : (Finset.univ.filter fun p : Fin 24 × Fin 24 =>
      p.1 ≠ p.2 ∧ v p.1 = 1 ∧ v p.2 = 1) = (support v).offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag, support, bit_ne_zero]
    tauto
  rw [← Finset.card_filter, he, Finset.offDiag_card, support_card, Nat.mul_sub_one]

private theorem second_moment
    (C : Submodule F2 Word) (hcard : Nat.card C = 4096)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (hdual : coordinatePairing.orthogonal C = C)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v) :
    (∑ c : C, weight (c : Word) * (weight (c : Word) - 1)) = 565248 := by
  calc
    _ = ∑ c : C, ∑ p : Fin 24 × Fin 24,
        if p.1 ≠ p.2 ∧ c.val p.1 = 1 ∧ c.val p.2 = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      exact (word_pair_count c.val).symm
    _ = ∑ p : Fin 24 × Fin 24, ∑ c : C,
        if p.1 ≠ p.2 ∧ c.val p.1 = 1 ∧ c.val p.2 = 1 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ p : Fin 24 × Fin 24, if p.1 ≠ p.2 then 1024 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.1 = p.2
      · simp [hp]
      · simp only [Ne, hp, not_false_eq_true, true_and, ite_true]
        rw [← Finset.card_filter]
        exact pair_fiber_card C hcard hones hdual hmin p.1 p.2 hp
    _ = (Finset.univ : Finset (Fin 24)).offDiag.card * 1024 := by
      rw [← Finset.sum_filter]
      have he : (Finset.univ.filter fun p : Fin 24 × Fin 24 => p.1 ≠ p.2) =
          (Finset.univ : Finset (Fin 24)).offDiag := by
        ext p
        simp
      rw [he, Finset.sum_const, smul_eq_mul]
    _ = 565248 := by rw [Finset.offDiag_card]; norm_num

private def weightCount (C : Submodule F2 Word) (w : ℕ) : ℕ :=
  Fintype.card {c : C // weight (c : Word) = w}

private theorem weightCount_sum (C : Submodule F2 Word) (w : ℕ) :
    (∑ c : C, if weight (c : Word) = w then 1 else 0) = weightCount C w := by
  rw [weightCount, Fintype.card_subtype, Finset.card_filter]

private theorem complementary_counts
    (C : Submodule F2 Word)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (a b : ℕ) (hab : a + b = 24) : weightCount C a = weightCount C b := by
  let one : C := ⟨fun _ => 1, hones⟩
  apply Fintype.card_congr ((Equiv.addLeft one).subtypeEquiv ?_)
  intro c
  have hc := complement_weight c.val
  change weight c.val = a ↔ weight (fun i => 1 + c.val i) = b
  omega

/-- The weight-eight coefficient is forced by self-duality, minimum distance,
the spectrum and the all-ones word. No enumeration of codewords is involved. -/
theorem octad_count_of_self_dual
    (C : Submodule F2 Word) (hcard : Nat.card C = 4096)
    (hones : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (hdual : coordinatePairing.orthogonal C = C)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v)
    (hspectrum : ∀ v ∈ C,
      weight v = 0 ∨ weight v = 8 ∨ weight v = 12 ∨ weight v = 16 ∨ weight v = 24) :
    Nat.card {c : C // weight (c : Word) = 8} = 759 := by
  have hC : Fintype.card C = 4096 := by simpa [Nat.card_eq_fintype_card] using hcard
  have h0 : weightCount C 0 = 1 := by
    have he : ∀ c : C, weight c.val = 0 ↔ c = 0 := by
      intro c
      constructor
      · intro hc
        by_contra hn
        have hv : c.val ≠ 0 := by intro hv; apply hn; exact Subtype.ext hv
        have := hmin c.val c.property hv
        omega
      · rintro rfl
        simp [weight]
    calc
      weightCount C 0 = Fintype.card {c : C // c = 0} :=
        Fintype.card_congr (Equiv.subtypeEquivRight he)
      _ = 1 := Fintype.card_subtype_eq (0 : C)
  have h24 : weightCount C 24 = 1 :=
    (complementary_counts C hones 0 24 (by omega)).symm.trans h0
  have h16 : weightCount C 16 = weightCount C 8 :=
    (complementary_counts C hones 8 16 (by omega)).symm
  have partition (c : C) : (1 : ℕ) =
      (if weight c.val = 0 then 1 else 0) +
      (if weight c.val = 8 then 1 else 0) +
      (if weight c.val = 12 then 1 else 0) +
      (if weight c.val = 16 then 1 else 0) +
      (if weight c.val = 24 then 1 else 0) := by
    rcases hspectrum c.val c.property with h | h | h | h | h <;> norm_num [h]
  have hp := Finset.sum_congr (s₁ := (Finset.univ : Finset C)) rfl
    (fun c _ => partition c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, weightCount_sum, hC, h0, h24, h16] at hp
  have moment (c : C) : weight c.val * (weight c.val - 1) =
      56 * (if weight c.val = 8 then 1 else 0) +
      132 * (if weight c.val = 12 then 1 else 0) +
      240 * (if weight c.val = 16 then 1 else 0) +
      552 * (if weight c.val = 24 then 1 else 0) := by
    rcases hspectrum c.val c.property with h | h | h | h | h <;> norm_num [h]
  have hm := Finset.sum_congr (s₁ := (Finset.univ : Finset C)) rfl
    (fun c _ => moment c)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, weightCount_sum,
    second_moment C hcard hones hdual hmin, h24, h16] at hm
  have h8 : weightCount C 8 = 759 := by omega
  simpa [weightCount, Nat.card_eq_fintype_card] using h8

/-- Apply the structural moment theorem to the original polynomial Golay code. -/
theorem octad_card : Nat.card Octad = 759 :=
  octad_count_of_self_dual code code_card all_ones_mem self_dual minimum_weight weight_spectrum

#print axioms octad_count_of_self_dual
#print axioms octad_card

end D5.S3.Arith.Lattices.Golay.GolayOctadCount
