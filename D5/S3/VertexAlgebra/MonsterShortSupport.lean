/- GID: D5/S3/VertexAlgebra/MonsterShortSupport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterShortSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd binary relations have unique representatives of weight at most half. -/

/-
proof_shape: odd_binary_short_support: content
escape_witness: The seven-section kernel is exactly the repetition line, and an odd
  complement argument gives existence and uniqueness of a coefficient support of size at most three.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/VertexAlgebra/MonsterFusionSpan.fusion_span_and_capacity.
-/

import D5.S3.VertexAlgebra.MonsterFusionSpan
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterShortSupport

open D5.S3.VertexAlgebra.MonsterCharacterCarry
open D5.S3.VertexAlgebra.MonsterFusionSpan

abbrev Coeff := Fin 7 → F

private def firstSix (c : Coeff) : Six :=
  (c 0, c 1, c 2, c 3, c 4, c 5)

private def allSix : Six := (1, 1, 1, 1, 1, 1)

/- The seventh section is the sum of the six basis sections.  The frozen
   fusion-span theorem identifies it with the missing nonzero section. -/
def fullMap (f : E → E → F) (c : Coeff) : Label :=
  sixMap f (firstSix c) + c 6 • sixMap f allSix

private theorem f2_cases (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem fullMap_split (f : E → E → F) (c : Coeff) :
    fullMap f c = sixMap f (firstSix c) + c 6 • sixMap f allSix := rfl

private theorem allOnes_map (f : E → E → F) (hf : IsSignTable f) :
    fullMap f (fun _ => 1) = 0 := by
  simp [fullMap, firstSix, allSix]
  apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _

private theorem fullMap_add (f : E → E → F) (a b : Coeff) :
    fullMap f (fun i => a i + b i) = fullMap f a + fullMap f b := by
  simp [fullMap, sixMap, firstSix, allSix, add_smul, Pi.add_apply, Pi.smul_apply]
  abel

private theorem kernel_iff (f : E → E → F) (hf : IsSignTable f) (c : Coeff) :
    fullMap f c = 0 ↔ ∃ t : F, ∀ i, c i = t := by
  rw [fullMap_split]
  have hbij := (fusion_span_and_capacity f hf).1
  have hline (t : F) : t • sixMap f allSix = sixMap f (t, t, t, t, t, t) := by
    simp [sixMap, allSix, smul_add]
  constructor
  · intro h
    have hc : firstSix c = (c 6, c 6, c 6, c 6, c 6, c 6) := hbij.1 (by
      have hneg := add_eq_zero_iff_eq_neg.mp h
      have htuple : -sixMap f (c 6, c 6, c 6, c 6, c 6, c 6) =
          sixMap f (c 6, c 6, c 6, c 6, c 6, c 6) := by
        apply Prod.ext <;> funext i <;> exact CharTwo.neg_eq _
      simpa [hline, htuple] using hneg
      )
    refine ⟨c 6, ?_⟩
    intro i
    fin_cases i
    · exact congrArg (fun z : Six => z.1) hc
    · exact congrArg (fun z : Six => z.2.1) hc
    · exact congrArg (fun z : Six => z.2.2.1) hc
    · exact congrArg (fun z : Six => z.2.2.2.1) hc
    · exact congrArg (fun z : Six => z.2.2.2.2.1) hc
    · exact congrArg (fun z : Six => z.2.2.2.2.2) hc
    · rfl
  · rintro ⟨t, ht⟩
    have hc : firstSix c = (t, t, t, t, t, t) := by
      apply Prod.ext
      · exact ht 0
      · apply Prod.ext
        · exact ht 1
        · apply Prod.ext
          · exact ht 2
          · apply Prod.ext
            · exact ht 3
            · apply Prod.ext
              · exact ht 4
              · exact ht 5
    have ht6 := ht 6
    rw [hc, ht6, hline]
    apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _

/-- Hamming support weight of a seven-section coefficient vector. -/
def weight (c : Coeff) : Nat := (Finset.univ.filter (fun i => c i = 1)).card

private theorem weight_complement (c : Coeff) :
    weight c + weight (fun i => c i + 1) = 7 := by
  classical
  unfold weight
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 7))) (fun i => c i = 1)
  have hfilter : (Finset.univ.filter (fun i => ¬ c i = 1)) =
      (Finset.univ.filter (fun i => c i + 1 = 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcases := f2_cases (c i)
    rcases hcases with h | h <;> simp [h]
  rw [hfilter] at hcard
  simpa using hcard

private theorem complement_map (f : E → E → F) (hf : IsSignTable f) (c : Coeff) :
    fullMap f (fun i => c i + 1) = fullMap f c := by
  rw [fullMap_add, allOnes_map f hf]
  simp

private theorem short_exists (f : E → E → F) (hf : IsSignTable f) (x : Label) :
    ∃ c : Coeff, fullMap f c = x ∧ weight c ≤ 3 := by
  obtain ⟨a, ha⟩ := (fusion_span_and_capacity f hf).1.2 x
  let c : Coeff := ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2, 0]
  have hc : fullMap f c = x := by
    rw [fullMap_split]
    simpa [c, firstSix, allSix] using ha
  by_cases hw : weight c ≤ 3
  · exact ⟨c, hc, hw⟩
  · let d : Coeff := fun i => c i + 1
    have hd : fullMap f d = x := by simpa [d] using (complement_map f hf c).trans hc
    have hsum := weight_complement c
    have hsum' : weight c + weight d = 7 := by simpa [d] using hsum
    have hdc : weight d ≤ 3 := by omega
    exact ⟨d, hd, hdc⟩

/-- Every six-bit label has a unique seven-section coefficient vector of support at most three.

This is the finite odd-relation statement used by the four character classes.  It concerns
the auxiliary label space only; it does not assert a VOA realization or an OPE coefficient. -/
theorem unique_short_support (f : E → E → F) (hf : IsSignTable f) (x : Label) :
    ∃! c : Coeff, fullMap f c = x ∧ weight c ≤ 3 := by
  obtain ⟨c, hc, hw⟩ := short_exists f hf x
  refine ⟨c, ⟨hc, hw⟩, ?_⟩
  intro d hd
  have hz : fullMap f (fun i => c i + d i) = 0 := by
    rw [fullMap_add, hc, hd.1]
    apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _
  obtain ⟨t, ht⟩ := (kernel_iff f hf _).mp hz
  by_cases ht0 : t = 0
  · funext i
    have := ht i
    have hcd : c i + d i = 0 := by simpa [ht0] using this
    have hdc : c i = -d i := add_eq_zero_iff_eq_neg.mp hcd
    simpa [CharTwo.neg_eq, eq_comm] using hdc
  · have ht1 : t = 1 := by
      fin_cases t
      · exact (ht0 rfl).elim
      · rfl
    have hcomp : weight c + weight d = 7 := by
      unfold weight
      have hcard := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 7))) (fun i => c i = 1)
      have hfilter : (Finset.univ.filter (fun i => ¬ c i = 1)) =
          (Finset.univ.filter (fun i => d i = 1)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hci
          have hsum := ht i
          have hcases := f2_cases (c i)
          rcases hcases with h | h
          · have : d i = 1 := by simpa [h, ht1] using hsum
            exact this
          · exact (hci h).elim
        · intro hdi hci
          have hsum := ht i
          simp [hci, hdi, ht1] at hsum
      rw [hfilter] at hcard
      simpa using hcard
    have hdw := hd.2
    exfalso
    omega

end D5.S3.VertexAlgebra.MonsterShortSupport
