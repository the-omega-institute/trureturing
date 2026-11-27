/- GID: D5/S3/Combinatorics/Probability/OrderedNamingReply
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/OrderedNamingReply
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Ordered replies from a uniform injective naming are uniform on the replies consistent with the fixed names and the requested equality pattern. -/

import D5.S3.Combinatorics.Probability.NamingRestrictionLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Probability.NamingRestrictionLaw
open D5.S3.Combinatorics.Probability.PartialNameAssignment
open scoped ENNReal

namespace D5.S3.Combinatorics.Probability.OrderedNamingReply

variable {I V N : Type*} [DecidableEq V]

/-- The distinct requested vertices outside the already named set. -/
abbrev FreshVertices (K : Finset V) (read : I → V) :=
  {v : V // v ∉ K ∧ v ∈ Set.range read}

private def residualInclusion (K : Finset V) (read : I → V) :
    FreshVertices K read ↪ {v // v ∉ K} where
  toFun v := ⟨v.1, v.2.1⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun v : {v : V // v ∉ K} => v.1) h)

private def replyEmbedding (K : Finset V) (A : Finset N) (known : K ↪ N) (read : I → V) :
    (FreshVertices K read ↪ A) ↪ (I → N) where
  toFun fresh i :=
    if hi : read i ∈ K then known ⟨read i, hi⟩
    else fresh ⟨read i, hi, ⟨i, rfl⟩⟩
  inj' := by
    intro a b h
    ext v
    obtain ⟨i, hi⟩ := v.2.2
    have hMem : read i ∉ K := hi ▸ v.2.1
    have hv : (⟨read i, hMem, ⟨i, rfl⟩⟩ : FreshVertices K read) = v := Subtype.ext hi
    have he := congrFun h i
    simp only [dite_eq_right hMem, hv] at he
    exact he

/-- A feasible reply agrees on old names, uses available names on every fresh
entry and records exactly the equality pattern of the requested vertices. -/
def IsConsistentReply (K : Finset V) (A : Finset N) (known : K ↪ N)
    (read : I → V) (reply : I → N) : Prop :=
  (∀ i (hi : read i ∈ K), reply i = known ⟨read i, hi⟩) ∧
  (∀ i, read i ∉ K → reply i ∈ A) ∧
  (∀ i j, reply i = reply j ↔ read i = read j)

private theorem in_range_iff_valid (K : Finset V) (A : Finset N) (known : K ↪ N)
    (read : I → V) (hsep : ∀ v, known v ∉ A) (reply : I → N) :
    reply ∈ Set.range (replyEmbedding K A known read) ↔ IsConsistentReply K A known read reply := by
  classical
  constructor
  · rintro ⟨fresh, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change (if h : read i ∈ K then known ⟨read i, h⟩
        else (fresh ⟨read i, h, ⟨i, rfl⟩⟩ : N)) = known ⟨read i, hi⟩
      simp [hi]
    · intro i hi
      change (if h : read i ∈ K then known ⟨read i, h⟩
        else (fresh ⟨read i, h, ⟨i, rfl⟩⟩ : N)) ∈ A
      simp only [dite_eq_right hi]
      exact (fresh ⟨read i, hi, ⟨i, rfl⟩⟩).2
    · intro i j
      change ((if h : read i ∈ K then known ⟨read i, h⟩
          else (fresh ⟨read i, h, ⟨i, rfl⟩⟩ : N)) =
        (if h : read j ∈ K then known ⟨read j, h⟩
          else (fresh ⟨read j, h, ⟨j, rfl⟩⟩ : N))) ↔ read i = read j
      by_cases hi : read i ∈ K <;> by_cases hj : read j ∈ K
      · simp only [dite_eq_left hi, dite_eq_left hj, known.injective.eq_iff, Subtype.mk.injEq]
      · rw [dite_eq_left hi, dite_eq_right hj]
        exact ⟨fun he => (hsep ⟨read i, hi⟩ (he ▸ (fresh ⟨read j, hj, ⟨j, rfl⟩⟩).2)).elim,
          fun he => (hj (he ▸ hi)).elim⟩
      · rw [dite_eq_right hi, dite_eq_left hj]
        exact ⟨fun he => (hsep ⟨read j, hj⟩ (he ▸ (fresh ⟨read i, hi, ⟨i, rfl⟩⟩).2)).elim,
          fun he => (hi (he.symm ▸ hj)).elim⟩
      · simp only [dite_eq_right hi, dite_eq_right hj, Subtype.coe_inj, fresh.injective.eq_iff, Subtype.mk.injEq]
  · rintro ⟨hOld, hNew, hEq⟩
    let slot (v : FreshVertices K read) : I := v.2.2.choose
    have hSlot (v : FreshVertices K read) : read (slot v) = v.1 := v.2.2.choose_spec
    let fresh : FreshVertices K read ↪ A := {
      toFun := fun v => ⟨reply (slot v), hNew (slot v) ((hSlot v).symm ▸ v.2.1)⟩
      inj' := fun u v h => Subtype.ext
        ((hSlot u).symm.trans (((hEq _ _).mp (congrArg Subtype.val h)).trans (hSlot v))) }
    refine ⟨fresh, funext fun i => ?_⟩
    change (if h : read i ∈ K then known ⟨read i, h⟩ else
      (fresh ⟨read i, h, ⟨i, rfl⟩⟩ : N)) = reply i
    by_cases hi : read i ∈ K
    · simpa only [dite_eq_left hi] using (hOld i hi).symm
    · rw [dite_eq_right hi]
      exact (hEq _ i).mpr (hSlot ⟨read i, hi, ⟨i, rfl⟩⟩)

private theorem reveal_composition (K : Finset V) (A : Finset N) (known : K ↪ N)
    (read : I → V) (hsep : ∀ v, known v ∉ A) (f : Candidates K A known) :
    (fun i => f.1 (read i)) = replyEmbedding K A known read
      ((residualInclusion K read).trans (residualEmbedding K A known hsep f)) := by
  funext i
  change f.1 (read i) = if h : read i ∈ K then known ⟨read i, h⟩ else _
  by_cases hi : read i ∈ K
  · simpa only [dite_eq_left hi] using f.2.1 ⟨read i, hi⟩
  · rw [dite_eq_right hi]
    rfl

/-- Observing an ordered reply gives equal mass to each consistent reply. -/
theorem ordered_reply_mass [Finite V] [Finite N]
    (K : Finset V) (A : Finset N) (known : K ↪ N) (hsep : ∀ v, known v ∉ A)
    (h : Nonempty (Candidates K A known)) (read : I → V) :
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h
    let mass := namingMass (Nat.card (FreshVertices K read ↪ A))
    ∀ reply : I → N,
      ((uniformPmf (Candidates K A known)).map (fun f i => f.1 (read i))) reply =
        @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _)
          mass 0 := by
  classical
  intro _ _ mass reply
  let restrict (f : Candidates K A known) :=
    (residualInclusion K read).trans (residualEmbedding K A known hsep f)
  have hMap : (uniformPmf (Candidates K A known)).map (fun f i => f.1 (read i)) =
      ((uniformPmf (Candidates K A known)).map restrict).map (replyEmbedding K A known read) := by
    rw [PMF.map_comp]
    congr 1
    funext f
    exact reveal_composition K A known read hsep f
  rw [hMap, PMF.map_apply]
  by_cases hConsistent : IsConsistentReply K A known read reply
  · obtain ⟨fresh, rfl⟩ := (in_range_iff_valid K A known read hsep reply).mpr hConsistent
    simp only [(replyEmbedding K A known read).injective.eq_iff, tsum_ite_eq', ite_eq_left hConsistent]
    exact uniform_residual_restriction K A known hsep h (residualInclusion K read) fresh
  · have hNot := mt (in_range_iff_valid K A known read hsep reply).mp hConsistent
    have hNot' (fresh : FreshVertices K read ↪ A) : reply ≠ replyEmbedding K A known read fresh :=
      fun he => hNot ⟨fresh, he.symm⟩
    simp [hNot', hConsistent]

end D5.S3.Combinatorics.Probability.OrderedNamingReply
