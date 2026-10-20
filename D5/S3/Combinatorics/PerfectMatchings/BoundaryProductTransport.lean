/- GID: D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Transport of the unaffected boundary product. -/
import D5.S3.Combinatorics.PerfectMatchings.DetourLabels
import Mathlib.Tactic.Tauto

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CupCapBridgeProposal

section Products
variable {L : Type*} {n : ℕ}

def openingFactor (q : L → ℝ) (M : NCMatching n)
    (x : Fin (n + 1) → L) (t : Fin n) : ℝ :=
  if t < M.partner t then q (x t.succ) / q (x t.castSucc) else 1

def openingProduct (q : L → ℝ) (M : NCMatching n) (x : Fin (n + 1) → L) : ℝ :=
  ∏ t : Fin n, openingFactor q M x t

theorem boundaryPotential_eq (q : L → ℝ) (M : NCMatching n)
    (x : Fin (n + 1) → L) :
    boundaryPotential q M x = if Compatible M x then openingProduct q M x else 0 := rfl

end Products

section Transport
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))

def Unchanged (t : Fin (m + 2)) : Prop :=
  t ≠ j.castSucc ∧ t ≠ j.succ ∧
    t ≠ M.partner j.castSucc ∧ t ≠ M.partner j.succ

def ShortUnchanged (k : Fin m) : Prop :=
  skipPair j k ≠ M.partner j.castSucc ∧ skipPair j k ≠ M.partner j.succ

theorem unchanged_partner (t : Fin (m + 2)) (ht : Unchanged M j t) :
    reconnectPartner M j t = M.partner t := by
  have hpa : M.partner t ≠ j.castSucc := by
    intro h; apply ht.2.2.1
    simpa only [M.involutive] using congrArg M.partner h
  have hpb : M.partner t ≠ j.succ := by
    intro h; apply ht.2.2.2
    simpa only [M.involutive] using congrArg M.partner h
  simp only [reconnectPartner, hpa, hpb, if_false]

theorem shortUnchanged_iff (k : Fin m) :
    ShortUnchanged M j k ↔ Unchanged M j (skipPair j k) := by
  exact ⟨fun h => ⟨(skipPair_survives j k).1, (skipPair_survives j k).2, h⟩,
    fun h => h.2.2⟩

theorem skipPair_unchanged_partner (k : Fin m) (hk : ShortUnchanged M j k) :
    skipPair j ((capSurgery M j).partner k) = M.partner (skipPair j k) := by
  rw [capSurgery_reconnect, unchanged_partner M j _ ((shortUnchanged_iff M j k).mp hk)]

theorem unchanged_factor {L : Type*} (q : L → ℝ)
    (y : Fin (m + 1) → L) (B : L) (k : Fin m) (hk : ShortUnchanged M j k) :
    openingFactor q (capSurgery M j) y k =
      openingFactor q M (detourLabels j y B) (skipPair j k) := by
  have hp := skipPair_unchanged_partner M j k hk
  have ho : (skipPair j k < M.partner (skipPair j k)) ↔
      k < (capSurgery M j).partner k := by
    rw [← hp]
    exact (skipPair_strictMono j).lt_iff_lt
  simp only [openingFactor, ho, detour_skip_left, detour_skip_right]

/-- All unaffected arcs, including ones far from the cap, occur exactly once.
The proof uses an actual finite-product bijection, not a supplied coefficient. -/
theorem unaffected_opening_product {L : Type*} (q : L → ℝ)
    (y : Fin (m + 1) → L) (B : L) :
    (∏ t ∈ Finset.univ.filter (Unchanged M j),
      openingFactor q M (detourLabels j y B) t) =
    ∏ k ∈ Finset.univ.filter (ShortUnchanged M j),
      openingFactor q (capSurgery M j) y k := by
  classical
  symm
  apply Finset.prod_bij (fun k _ => skipPair j k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact (shortUnchanged_iff M j k).mp hk
  · intro k hk l hl he
    exact skipPair_injective j he
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    let k := unskipPair j t ht.1 ht.2.1
    have hk : skipPair j k = t := skipPair_unskipPair j t ht.1 ht.2.1
    refine ⟨k, ?_, hk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [shortUnchanged_iff, hk]
    exact ht
  · intro k hk
    exact unchanged_factor M j q y B k
      ((Finset.mem_filter.mp hk).2)

/-- The two literal products share precisely the reindexed unaffected factor.
The finite affected products are left visible, with no scalar identity assumed. -/
theorem opening_products_split {L : Type*} (q : L → ℝ)
    (y : Fin (m + 1) → L) (B : L) :
    let U := ∏ k ∈ Finset.univ.filter (ShortUnchanged M j),
      openingFactor q (capSurgery M j) y k
    (openingProduct q M (detourLabels j y B) =
      (∏ t ∈ Finset.univ.filter (fun t => ¬ Unchanged M j t),
        openingFactor q M (detourLabels j y B) t) * U) ∧
    (openingProduct q (capSurgery M j) y =
      (∏ k ∈ Finset.univ.filter (fun k => ¬ ShortUnchanged M j k),
        openingFactor q (capSurgery M j) y k) * U) := by
  classical
  dsimp only
  constructor
  · rw [← unaffected_opening_product M j q y B]
    exact (Finset.prod_filter_not_mul_prod_filter Finset.univ
      (Unchanged M j) (openingFactor q M (detourLabels j y B))).symm
  · exact (Finset.prod_filter_not_mul_prod_filter Finset.univ
      (ShortUnchanged M j) (openingFactor q (capSurgery M j) y)).symm
end Transport

/-- Exact endpoint deletion formula, valid for any commutative monoid. -/
theorem prod_skipPair {K : Type*} [CommMonoid K] {m : ℕ}
    (j : Fin (m + 1)) (f : Fin (m + 2) → K) :
    (∏ t : Fin (m + 2), f t) =
      f j.castSucc * f j.succ * ∏ k : Fin m, f (skipPair j k) := by
  classical
  have himg (t : Fin (m + 2)) :
      t ∈ Finset.univ.image (skipPair j) ↔ t ≠ j.castSucc ∧ t ≠ j.succ := by
    constructor
    · intro ht
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
      exact skipPair_survives j k
    · intro ht
      exact Finset.mem_image.mpr ⟨unskipPair j t ht.1 ht.2,
        Finset.mem_univ _, skipPair_unskipPair j t ht.1 ht.2⟩
  have hab : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; omega
  have ha : j.castSucc ∉ Finset.insert j.succ (Finset.univ.image (skipPair j)) := by
    simp only [Finset.mem_insert, himg]
    tauto
  have hb : j.succ ∉ Finset.univ.image (skipPair j) := by
    rw [himg]
    tauto
  have hu : (Finset.univ : Finset (Fin (m + 2))) =
      Finset.insert j.castSucc (Finset.insert j.succ (Finset.univ.image (skipPair j))) := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, himg]
    tauto
  change (∏ t ∈ (Finset.univ : Finset (Fin (m + 2))), f t) = _
  rw [hu, Finset.prod_insert ha, Finset.prod_insert hb,
    Finset.prod_image (fun k _ l _ h => skipPair_injective j h)]
  exact (mul_assoc _ _ _).symm

end CupCapBridgeProposal
