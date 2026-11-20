/- GID: D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compatible binary suffix on fresh positions costs one half per position. -/

import D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw

open D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw

variable {P V : Type*} [Fintype P] [DecidableEq P]

private def combined (seen : Finset P)
    (earlier later : P → Bool → Option V) (p : P) : Bool → Option V :=
  if p ∈ seen then earlier p else later p

private theorem compatible_combined {choices : P → Bool → V}
    {earlier later : P → Bool → Option V} {seen fresh : Finset P}
    (hDisjoint : Disjoint seen fresh)
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v) :
    Compatible choices (combined seen earlier later) ↔
      Compatible choices earlier ∧ Compatible choices later := by
  constructor
  · intro h
    have he p b v (hv : earlier p b = some v) : combined seen earlier later p b = some v := by
      simp [combined, (hSeen p).mpr ⟨b, v, hv⟩, hv]
    have hl p b v (hv : later p b = some v) : combined seen earlier later p b = some v := by
      have hp : p ∉ seen := fun hS => Finset.disjoint_left.mp hDisjoint hS
        ((hFresh p).mpr ⟨b, v, hv⟩)
      simp [combined, hp, hv]
    exact ⟨⟨fun p b v hv => h.1 p b v (he p b v hv),
      fun p v hf ht => h.2 p v (he p false v hf) (he p true v ht)⟩,
      ⟨fun p b v hv => h.1 p b v (hl p b v hv),
      fun p v hf ht => h.2 p v (hl p false v hf) (hl p true v ht)⟩⟩
  · rintro ⟨he, hl⟩
    constructor
    · intro p b v hb
      by_cases hp : p ∈ seen
      · exact he.1 p b v (by simpa [combined, hp] using hb)
      · exact hl.1 p b v (by simpa [combined, hp] using hb)
    · intro p v hf ht
      by_cases hp : p ∈ seen
      · exact he.2 p v (by simpa [combined, hp] using hf) (by simpa [combined, hp] using ht)
      · exact hl.2 p v (by simpa [combined, hp] using hf) (by simpa [combined, hp] using ht)

private theorem matching_combined {choices : P → Bool → V}
    {earlier later : P → Bool → Option V} {seen fresh : Finset P}
    (hDisjoint : Disjoint seen fresh)
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v)
    (f : P → Equiv.Perm Bool) :
    Matches choices (combined seen earlier later) f ↔
      Matches choices earlier f ∧ Matches choices later f := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro p b v hv
      exact h p b v (by simpa [combined, (hSeen p).mpr ⟨b, v, hv⟩] using hv)
    · intro p b v hv
      have hp : p ∉ seen := fun hs => Finset.disjoint_left.mp hDisjoint hs
        ((hFresh p).mpr ⟨b, v, hv⟩)
      exact h p b v (by simpa [combined, hp] using hv)
  · rintro ⟨he, hl⟩ p b v hv
    by_cases hp : p ∈ seen
    · exact he p b v (by simpa [combined, hp] using hv)
    · exact hl p b v (by simpa [combined, hp] using hv)

private theorem combined_positions {earlier later : P → Bool → Option V}
    {seen fresh : Finset P}
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v) (p : P) :
    p ∈ seen ∪ fresh ↔ ∃ b v, combined seen earlier later p b = some v := by
  by_cases hp : p ∈ seen
  · simpa [combined, hp] using (hSeen p).mp hp
  · simpa [combined, hp] using hFresh p

attribute [local instance] Classical.propDecidable

/-- The conditional likelihood of a slot observation supported on fresh positions. -/
theorem suffix_after_prefix (choices : P → Bool → V)
    (hChoice : ∀ p, Function.Injective (choices p))
    (earlier later : P → Bool → Option V) (seen fresh : Finset P)
    (hDisjoint : Disjoint seen fresh)
    (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v)
    (hCompatible : Compatible choices earlier) :
    let μ := uniformPmf (P → Equiv.Perm Bool)
    let E : Set (P → Equiv.Perm Bool) := {f | Matches choices earlier f}
    let F : Set (P → Equiv.Perm Bool) := {f | Matches choices later f}
    let freshCount := fresh.card
    μ.toOuterMeasure (E ∩ F) / μ.toOuterMeasure E =
      if Compatible choices later then ((2 ^ freshCount : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  intro μ E F freshCount
  dsimp only [freshCount]
  have hEvent : E ∩ F = {f | Matches choices (combined seen earlier later) f} := by
    ext f
    exact (matching_combined hDisjoint hSeen hFresh f).symm
  change μ.toOuterMeasure _ / μ.toOuterMeasure {f | Matches choices earlier f} = _
  rw [hEvent]
  dsimp only [μ]
  rw [partial_forward_order_likelihood choices hChoice (combined seen earlier later)
      (seen ∪ fresh) (combined_positions hSeen hFresh),
    partial_forward_order_likelihood choices hChoice earlier seen hSeen, ite_eq_left hCompatible,
    compatible_combined hDisjoint hSeen hFresh]
  simp only [hCompatible, true_and]
  by_cases h : Compatible choices later
  · rw [ite_eq_left h, ite_eq_left h, Finset.card_union_of_disjoint hDisjoint, pow_add,
      Nat.cast_mul]
    let m : ℝ≥0∞ := (↑(2 ^ seen.card : ℕ) : ℝ≥0∞)
    let n : ℝ≥0∞ := (↑(2 ^ fresh.card : ℕ) : ℝ≥0∞)
    change (m * n)⁻¹ / m⁻¹ = n⁻¹
    have hm0 : m ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))
    have hmt : m ≠ ⊤ := ENNReal.natCast_ne_top _
    have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [div_eq_mul_inv, inv_inv, ENNReal.mul_inv (a := m) (b := n) (Or.inr hnt) (Or.inl hmt),
      mul_comm m⁻¹ n⁻¹, mul_assoc, ENNReal.inv_mul_cancel hm0 hmt, mul_one]
  · simp [h]

end D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
