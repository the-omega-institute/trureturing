/- GID: D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conjugate failure multiplicities give the exact normal-closure loss gap. -/

import D5.S3.ConceptDynamics.Attribution.FixedKernelMass
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass

namespace D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity

variable {G S : Type*} [Group G] [MulAction G S] [Fintype S]

open Classical in
private theorem loss_gap_identity (H : Subgroup G) (a : S → ℝ)
    (invariant : ∀ (g : G) s, a (g • s) = a s) (d : ℕ) :
    let lossSets := Set.range fun g : G => {s : S | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
    let N := Subgroup.normalClosure (H : Set G)
    let total := ∑ s, a s
    (Nat.card ↥lossSets : ℝ) * (total - seedFixedMass (G := H) a) -
      (d : ℝ) * (total - seedFixedMass (G := N) a) =
      ∑ s, if ∀ n : N, n • s = s then 0 else
        a s * ((Nat.card {B : lossSets // s ∈ B.val} : ℝ) - d) := by
  classical
  let N := Subgroup.normalClosure (H : Set G)
  let broken (g : G) : Set S := {s | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
  let Events := Set.range broken
  let _ : Fintype Events := Fintype.ofFinite _
  let normalFixed (s : S) := ∀ n : N, n • s = s
  let lost (B : Events) (s : S) : ℝ := if s ∈ B.val then a s else 0
  let lostNormal (s : S) : ℝ := if normalFixed s then 0 else a s
  have fixed_notin (s : S) (hf : normalFixed s) (B : Events) : s ∉ B.val := by
    obtain ⟨g, eq⟩ := B.property
    intro hBroken
    rw [← eq] at hBroken
    change ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s at hBroken
    apply hBroken
    intro h
    let n : N := ⟨g * h.val * g⁻¹, Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨h.val, h.property, isConj_iff.mpr ⟨g, rfl⟩⟩)⟩
    change h.val • (g⁻¹ • s) = g⁻¹ • s
    have hn := hf n
    change (g * h.val * g⁻¹) • s = s at hn
    rw [mul_smul, mul_smul] at hn
    have shifted := congrArg (fun y : S => g⁻¹ • y) hn
    simpa only [inv_smul_smul] using shifted
  have pointwise (s : S) :
      (∑ B, lost B s) - (d : ℝ) * lostNormal s =
        if normalFixed s then 0 else
          a s * ((Nat.card {B : Events // s ∈ B.val} : ℝ) - d) := by
    by_cases hf : normalFixed s
    · simp [lost, lostNormal, hf, fixed_notin s hf]
    · have counted : (∑ B, lost B s) =
          (Nat.card {B : Events // s ∈ B.val} : ℝ) * a s := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rw [show (fun B => lost B s) = (fun B => if s ∈ B.val then a s else 0) by rfl,
          ← sum_filter, sum_const, nsmul_eq_mul]
      simp only [lostNormal, hf, ite_false, counted]
      rw [mul_sub, mul_comm (a s), mul_comm (a s)]
  have complement (p : S → Prop) [DecidablePred p] :
      (∑ s, if p s then 0 else a s) = ∑ s, a s - ∑ s, (if p s then a s else 0) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun s _ => by split <;> simp_all)
  have equal_loss (B : Events) :
      (∑ s, lost B s) = ∑ s, a s - seedFixedMass (G := H) a := by
    obtain ⟨g, eq⟩ := B.property
    let move : Equiv.Perm S := MulAction.toPerm g
    rw [← Equiv.sum_comp move]
    have summands : (fun s => lost B (move s)) =
        fun s => if ∀ h : H, h • s = s then 0 else a s := by
      funext s
      unfold lost
      rw [← eq]
      simp only [broken, Set.mem_ofPred_eq, move, MulAction.toPerm_apply, inv_smul_smul,
        ite_not, invariant]
    rw [summands, complement, seedFixedMass, sum_filter]
  have normal_loss : (∑ s, lostNormal s) =
      ∑ s, a s - seedFixedMass (G := N) a := by
    rw [seedFixedMass, sum_filter]
    exact complement normalFixed
  have event_loss : (∑ s : S, ∑ B : Events, lost B s) =
      (Fintype.card Events : ℝ) * (∑ s, a s - seedFixedMass (G := H) a) := by
    rw [sum_comm]
    simp only [equal_loss, sum_const, card_univ, nsmul_eq_mul]
  change (Nat.card Events : ℝ) * (∑ s, a s - seedFixedMass (G := H) a) -
    (d : ℝ) * (∑ s, a s - seedFixedMass (G := N) a) = _
  rw [Nat.card_eq_fintype_card, ← event_loss, ← normal_loss, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl (fun s _ => pointwise s)

open Classical in
/-- The loss gap counts excess event memberships on seeds moved by the normal closure.
When the multiplicity lower bound holds on the positive support, the gap is
nonnegative and vanishes exactly when those seeds have multiplicity d. -/
theorem normal_closure_loss_gap_and_eq (H : Subgroup G) (a : S → ℝ)
    (nonneg : ∀ s, 0 ≤ a s) (invariant : ∀ (g : G) s, a (g • s) = a s) (d : ℕ) :
    let events := Set.range fun g : G => {s : S | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
    let N := Subgroup.normalClosure (H : Set G)
    let total := ∑ s, a s
    let count (s : S) := Nat.card {B : events // s ∈ B.val}
    let lhs := (d : ℝ) * (total - seedFixedMass (G := N) a)
    let rhs := (Nat.card ↥events : ℝ) * (total - seedFixedMass (G := H) a)
    (rhs - lhs = ∑ s, if ∀ n : N, n • s = s then 0 else a s * ((count s : ℝ) - d)) ∧
    ((∀ s : S, 0 < a s → (¬∀ n : N, n • s = s) → d ≤ count s) →
      lhs ≤ rhs ∧ ((lhs = rhs) ↔
        ∀ s : S, 0 < a s → (¬∀ n : N, n • s = s) → count s = d)) := by
  classical
  intro E N total count lhs rhs
  let summand (s : S) :=
    if ∀ n : N, n • s = s then 0 else a s * ((count s : ℝ) - d)
  have gap : rhs - lhs = ∑ s, summand s := loss_gap_identity H a invariant d
  refine ⟨gap, fun lower => ?_⟩
  have each_nonneg (s : S) : 0 ≤ summand s := by
    unfold summand
    split
    · exact le_rfl
    · next moved =>
      rcases eq_or_lt_of_le (nonneg s) with zero | positive
      · simp [← zero]
      · exact mul_nonneg positive.le (sub_nonneg.mpr (by exact_mod_cast lower s positive moved))
  refine ⟨sub_nonneg.mp (gap.symm ▸ sum_nonneg (fun s _ => each_nonneg s)), ?_⟩
  constructor
  · intro equal s positive moved
    have zero : ∑ s, summand s = 0 := by rw [← gap, equal, sub_self]
    have contribution :=
      (sum_eq_zero_iff_of_nonneg (fun t _ => each_nonneg t)).mp zero s (mem_univ s)
    have product : a s * ((count s : ℝ) - d) = 0 := by
      simpa only [summand, ite_eq_right moved] using contribution
    have value := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left positive.ne')
    exact_mod_cast value
  · intro exact_count
    have zero (s : S) : summand s = 0 := by
      unfold summand
      split
      · rfl
      · next moved =>
        rcases eq_or_lt_of_le (nonneg s) with z | positive
        · simp [← z]
        · have card : count s = d := exact_count s positive moved
          rw [card, sub_self, mul_zero]
    rw [sum_congr rfl (fun s _ => zero s), sum_const_zero] at gap
    exact (sub_eq_zero.mp gap).symm

end D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
