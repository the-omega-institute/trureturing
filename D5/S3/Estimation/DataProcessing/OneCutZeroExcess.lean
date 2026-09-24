/- GID: D5/S3/Estimation/DataProcessing/OneCutZeroExcess
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/OneCutZeroExcess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero excess in a twisted cycle is exactly the explicit one-cut support. -/

import D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.OneCutZeroExcess

open Set Function MeasureTheory
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation

/-- Internal edges at which consecutive labels differ. -/
noncomputable def internalFailures {B : Type*} {n : ℕ} (y : Fin (n + 1) → B) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => y i.castSucc ≠ y i.succ

/-- The internal failures together with the twisted closing edge. -/
noncomputable def failureCount {B : Type*} {n : ℕ} (g : B ≃ B)
    (y : Fin (n + 1) → B) : ℕ := by
  classical
  exact (internalFailures y).card + if y 0 = g (y (Fin.last n)) then 0 else 1

/-- A moving anchor forces one failure. -/
noncomputable def movingAnchor {B : Type*} {n : ℕ} (g : B ≃ B)
    (y : Fin (n + 1) → B) : ℕ := by
  classical
  exact if y 0 = g (y 0) then 0 else 1

/-- The tuple before a cut is the anchor and after it is its inverse image. -/
def cutTuple {B : Type*} {n : ℕ} (g : B ≃ B) (k : Fin (n + 1))
    (x : B) : Fin (n + 1) → B := fun j => if j ≤ k then x else g.symm x

/-- The union of all one-cut sectors, including fixed diagonal tuples. -/
def oneCutSet {B : Type*} {n : ℕ} (g : B ≃ B) : Set (Fin (n + 1) → B) :=
  {y | ∃ k, y = cutTuple g k (y 0)}

/-- The failure count dominates the moving-anchor indicator, and equality
holds precisely on the one-cut tuples. The alphabet need not be finite. -/
theorem failure_count_equality_iff_one_cut {B : Type*} {n : ℕ}
    (g : B ≃ B) (y : Fin (n + 1) → B) :
    movingAnchor g y ≤ failureCount g y ∧
      (failureCount g y = movingAnchor g y ↔ y ∈ oneCutSet g) := by
  classical
  have segment (a b : Fin (n + 1)) (hab : a ≤ b)
      (h : ∀ i : Fin n, a.val ≤ i.val → i.val < b.val →
        y i.castSucc = y i.succ) : y a = y b := by
    have aux : ∀ t : ℕ, ∀ ht : t ≤ n, a.val ≤ t → t ≤ b.val →
        y a = y ⟨t, by omega⟩ := by
      intro t
      induction t with
      | zero =>
        intro ht ha hb
        have : a = 0 := Fin.ext (show a.val = 0 from by omega)
        subst a
        rfl
      | succ t ih =>
        intro ht ha hb
        by_cases heq : a.val = t + 1
        · congr 1
          exact Fin.ext heq
        · have ha' : a.val ≤ t := by omega
          exact (ih (by omega) ha' (by omega)).trans
            (h ⟨t, by omega⟩ ha' (show t < b.val from by omega))
    exact aux b.val (by omega) hab le_rfl
  have constant (h : internalFailures y = ∅) (j : Fin (n + 1)) : y 0 = y j := by
    apply segment 0 j (Fin.zero_le j)
    intro i _ _
    have hi : i ∉ internalFailures y := by rw [h]; simp
    simpa [internalFailures] using hi
  have lower : movingAnchor g y ≤ failureCount g y := by
    by_cases hfix : y 0 = g (y 0)
    · simp only [movingAnchor, if_pos hfix, Nat.zero_le]
    · by_cases hbad : (internalFailures y).Nonempty
      · have hc := Finset.card_pos.mpr hbad
        simp only [movingAnchor, if_neg hfix, failureCount]
        omega
      · have he : internalFailures y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hbad
        have hl := constant he (Fin.last n)
        simp [movingAnchor, failureCount, he, ← hl, hfix]
  refine ⟨lower, ?_⟩
  constructor
  · intro heq
    by_cases hbad : (internalFailures y).Nonempty
    · obtain ⟨k, hk⟩ := hbad
      have hcard : (internalFailures y).card = 1 := by
        have hp := Finset.card_pos.mpr ⟨k, hk⟩
        have hb : movingAnchor g y ≤ 1 := by unfold movingAnchor; split <;> omega
        unfold failureCount at heq
        omega
      have hsingle : internalFailures y = {k} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
        have : k = a := by simpa only [ha, Finset.mem_singleton] using hk
        simpa only [this] using ha
      have hclose : y 0 = g (y (Fin.last n)) := by
        have hb : movingAnchor g y ≤ 1 := by unfold movingAnchor; split <;> omega
        simp only [failureCount, hcard] at heq
        split at heq <;> omega
      have good (i : Fin n) (hi : i ≠ k) : y i.castSucc = y i.succ := by
        have : i ∉ internalFailures y := by simp [hsingle, hi]
        simpa [internalFailures] using this
      refine ⟨k.castSucc, funext fun j => ?_⟩
      change y j = if j ≤ k.castSucc then y 0 else g.symm (y 0)
      split
      · rename_i hj
        exact (segment 0 j (Fin.zero_le j) (fun i _ hi =>
          good i (by
            intro he
            subst i
            change j.val ≤ k.val at hj
            change k.val < j.val at hi
            omega))).symm
      · rename_i hj
        have htail : y j = y (Fin.last n) :=
          segment j (Fin.last n) (Fin.le_last j) (fun i hi _ =>
            good i (by
              intro he
              subst i
              change ¬ j.val ≤ k.val at hj
              change j.val ≤ k.val at hi
              omega))
        rw [htail, hclose, g.symm_apply_apply]
    · exact ⟨Fin.last n, funext fun j => by
        simpa only [cutTuple, if_pos (Fin.le_last j)] using
          (constant (Finset.not_nonempty_iff_eq_empty.mp hbad) j).symm⟩
  · rintro ⟨k, hy⟩
    have h0 : cutTuple g k (y 0) 0 = y 0 := by simp [cutTuple]
    have hanchor : movingAnchor g (cutTuple g k (y 0)) = movingAnchor g y := by
      simp [movingAnchor, h0]
    have hinv : (y 0 = g.symm (y 0)) ↔ y 0 = g (y 0) := by
      constructor
      · intro h
        have := congrArg g h
        simpa using this.symm
      · intro h
        have := congrArg g.symm h
        simpa using this.symm
    have hcalc : failureCount g (cutTuple g k (y 0)) = movingAnchor g y := by
      by_cases hfix : y 0 = g (y 0)
      · have hi := hinv.mpr hfix
        have hc : cutTuple g k (y 0) = fun _ => y 0 := by
          funext j
          simp only [cutTuple, ← hi, ite_self]
        simp only [failureCount, movingAnchor, internalFailures, hc, ne_eq, not_true_eq_false,
          Finset.filter_false, Finset.card_empty, if_pos hfix, Nat.zero_add]
      · by_cases hk : k.val = n
        · have hk' : k = Fin.last n := Fin.ext hk
          simp only [failureCount, movingAnchor, internalFailures, cutTuple, hk',
            if_pos (Fin.le_last _), ne_eq, not_true_eq_false, Finset.filter_false,
            Finset.card_empty, if_neg hfix, Nat.zero_add]
        · have hkn : k.val < n := by omega
          have hb : internalFailures (cutTuple g k (y 0)) = {⟨k.val, hkn⟩} := by
            ext i
            change (i ∈ Finset.univ.filter (fun i : Fin n =>
              cutTuple g k (y 0) i.castSucc ≠ cutTuple g k (y 0) i.succ)) ↔ _
            rw [Finset.mem_filter]
            simp only [Finset.mem_univ, true_and, Finset.mem_singleton, cutTuple]
            by_cases hi : i.val < k.val
            · have h₁ : i.castSucc ≤ k := show i.val ≤ k.val from hi.le
              have h₂ : i.succ ≤ k := show i.val + 1 ≤ k.val from hi
              simp only [if_pos h₁, if_pos h₂, ne_eq, not_true_eq_false, false_iff]
              exact fun h => hi.ne (congrArg Fin.val h)
            · by_cases he : i.val = k.val
              · have h₁ : i.castSucc ≤ k := show i.val ≤ k.val from he.le
                have h₂ : ¬ i.succ ≤ k := by change ¬ i.val + 1 ≤ k.val; omega
                simp only [if_pos h₁, if_neg h₂, ne_eq, hinv, hfix, not_false_eq_true, true_iff]
                exact Fin.ext (show i.val = (⟨k.val, hkn⟩ : Fin n).val from he)
              · have h₁ : ¬ i.castSucc ≤ k := by change ¬ i.val ≤ k.val; omega
                have h₂ : ¬ i.succ ≤ k := by change ¬ i.val + 1 ≤ k.val; omega
                simp only [if_neg h₁, if_neg h₂, ne_eq, not_true_eq_false, false_iff]
                exact fun h => he (congrArg Fin.val h)
          have hlast : ¬ Fin.last n ≤ k := by change ¬ n ≤ k.val; omega
          simp only [failureCount, movingAnchor, hb, Finset.card_singleton, cutTuple,
            if_pos (Fin.zero_le k), if_neg hlast, Equiv.apply_symm_apply,
            if_pos, if_neg hfix, Nat.add_zero]
    calc
      failureCount g y = failureCount g (cutTuple g k (y 0)) := congrArg (failureCount g) hy
      _ = movingAnchor g y := hcalc

#print axioms failure_count_equality_iff_one_cut

end D5.S3.Estimation.DataProcessing.OneCutZeroExcess
