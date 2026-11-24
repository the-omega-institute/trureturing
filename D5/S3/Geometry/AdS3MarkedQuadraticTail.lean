import D5.S3.Arith.ModularForms.RademacherQuadraticTail
import D5.S3.Geometry.AdS3MarkedFillingCharacter

/-!
# The quadratic tail of the marked AdS₃ filling sum

The polar filling contributes only to the polar seed. The quadratic error is
compact-uniform and the exact character error also contains the linear term.
-/

set_option autoImplicit false

open scoped UpperHalfPlane

namespace D5.S3.Geometry.AdS3MarkedFillingCharacter

open AdS3RademacherFilling
open D5.S3.Arith.ModularForms.RademacherVacuum
  (mem_cutoffPairs vacuumSummand linearSummand quadraticRemainder linearCutoff remainderCutoff
    rademacherCutoff_eq)
open D5.S3.Arith.ModularForms.RademacherRectangularConvergence
  (PrimitiveRow remainderLimit rademacherLimit norm_remainderLimit_sub_remainderCutoff_le)
open D5.S3.Arith.ModularForms.RademacherLinearTailConvergence (linearPrincipalValueQTailLimit)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries (character)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldRademacherCharacter (rademacherLimit_eq_character)

noncomputable section

private def fillingQuadraticSummand (τ : ℍ) (p : FillingIndex) : ℂ :=
  if p = polarIndex then 0 else quadraticRemainder p.c p.d τ

/-- The quadratic part on the actual marked meridians, with zero polar term. -/
def markedFillingQuadraticSummand (τ : ℍ) (m : MarkedFilling τ) : ℂ :=
  fillingQuadraticSummand τ ((markedFillingEquiv τ).symm m)

/-- The actual geometric summand is the polar Boltzmann term at the polar
filling, and the sum of the linear and quadratic terms elsewhere. -/
theorem markedFillingVacuumSummand_eq_polar_or_linear_add_quadratic
    (τ : ℍ) (m : MarkedFilling τ) :
    markedFillingVacuumSummand τ m =
      if (markedFillingEquiv τ).symm m = polarIndex then rawBoltzmann 1 τ else
        linearSummand ((markedFillingEquiv τ).symm m).c
          ((markedFillingEquiv τ).symm m).d τ + markedFillingQuadraticSummand τ m := by
  obtain ⟨p, rfl⟩ := (markedFillingEquiv τ).surjective m
  simp only [markedFillingVacuumSummand, markedFillingQuadraticSummand,
    Equiv.symm_apply_apply, fillingQuadraticSummand]
  split_ifs with hp
  · subst p
    simp [completedVacuumSummand, cuspSubtraction]
  · have hc : 0 < p.c := p.normalized.resolve_right fun h => hp ((eq_polarIndex_iff p).mpr h.1)
    have hv := vacuumSummand_eq p.completion τ p.completion_c p.completion_d hc
    rw [completedVacuumSummand, rawBoltzmann_eq_exp, cuspSubtraction, p.completion_c,
      ite_eq_right hc.ne', ← hv]
    unfold vacuumSummand linearSummand quadraticRemainder
    ring

private def primitiveRowEquivNonpolar : PrimitiveRow ≃ {p : FillingIndex // p ≠ polarIndex} where
  toFun p :=
    ⟨⟨p.val.1, p.val.2, p.property.2, Or.inl p.property.1⟩,
      fun h => p.property.1.ne' (congrArg FillingIndex.c h)⟩
  invFun p := ⟨(p.val.c, p.val.d),
    p.val.normalized.resolve_right fun h => p.property ((eq_polarIndex_iff _).mpr h.1),
    p.val.primitive⟩
  left_inv := by rintro ⟨⟨c, d⟩, h⟩; rfl
  right_inv := by intro p; exact Subtype.ext (FillingIndex.ext rfl rfl)

/-- The marked infinite quadratic sum is the primitive-row limit. -/
theorem tsum_markedFillingQuadraticSummand_eq_remainderLimit (τ : ℍ) :
    (∑' m : MarkedFilling τ, markedFillingQuadraticSummand τ m) = remainderLimit τ := by
  have hs : Function.support (fillingQuadraticSummand τ) ⊆ {p | p ≠ polarIndex} := by
    intro p hp he
    subst p
    exact hp (by simp [fillingQuadraticSummand])
  calc
    _ = ∑' p : FillingIndex, fillingQuadraticSummand τ p := by
      simpa only [markedFillingQuadraticSummand, Equiv.symm_apply_apply] using
        ((markedFillingEquiv τ).tsum_eq (markedFillingQuadraticSummand τ)).symm
    _ = ∑' p : {p : FillingIndex // p ≠ polarIndex}, fillingQuadraticSummand τ p :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = _ := by
      unfold remainderLimit
      symm
      rw [← primitiveRowEquivNonpolar.tsum_eq
        (fun p : {p : FillingIndex // p ≠ polarIndex} => fillingQuadraticSummand τ p)]
      apply tsum_congr
      intro p
      let q := primitiveRowEquivNonpolar p
      change quadraticRemainder q.val.c q.val.d τ = fillingQuadraticSummand τ q
      exact (ite_eq_right q.property).symm

/-- Reindexing the actual marked cutoff gives the literal quadratic cutoff. -/
theorem sum_markedFillingCutoff_quadratic_eq_remainderCutoff (N : ℕ) (τ : ℍ) :
    (∑ m ∈ markedFillingCutoff τ N, markedFillingQuadraticSummand τ m) = remainderCutoff N τ := by
  have hp : polarIndex ∉ fillingCutoff N := by simp [polarIndex]
  rw [markedFillingCutoff, Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, markedFillingQuadraticSummand, Equiv.symm_apply_apply]
  rw [Finset.sum_insert hp]
  simp only [fillingQuadraticSummand, ite_true, zero_add, remainderCutoff]
  apply Finset.sum_bij (fun p _ => (p.c, p.d))
  · intro p h
    obtain ⟨hc, hN, hd⟩ := mem_fillingCutoff.mp h
    exact mem_cutoffPairs.mpr ⟨hc, hN, hd, p.primitive⟩
  · rintro p _ q _ h
    exact FillingIndex.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · rintro ⟨c, d⟩ h
    obtain ⟨hc, hN, hd, hprim⟩ := mem_cutoffPairs.mp h
    exact ⟨⟨c, d, hprim, Or.inl hc⟩, mem_fillingCutoff.mpr ⟨hc, hN, hd⟩, rfl⟩
  · intro p h
    have hne : p ≠ polarIndex := fun he => hp (he ▸ h)
    simp [hne]

/-- Compact-uniform inverse-square error for the quadratic contribution on
the actual marked meridians and the original geometric cutoff. -/
theorem norm_markedFillingQuadratic_tsum_sub_cutoff_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ∀ N : ℕ, 1 ≤ N →
      ‖(∑' m : MarkedFilling τ, markedFillingQuadraticSummand τ m) -
        (∑ m ∈ markedFillingCutoff τ N, markedFillingQuadraticSummand τ m)‖ ≤
        C / (N : ℝ) ^ 2 := by
  simpa only [tsum_markedFillingQuadraticSummand_eq_remainderLimit,
    sum_markedFillingCutoff_quadratic_eq_remainderCutoff] using
    norm_remainderLimit_sub_remainderCutoff_le hK

/-- The exact error of the marked filling approximation to the Leech torus
character. The same polar seed occurs in the limit and at every cutoff. -/
theorem character_sub_markedFillingCutoff_sub_twelve (N : ℕ) (τ : ℍ) :
    character τ - ((∑ m ∈ markedFillingCutoff τ N, markedFillingVacuumSummand τ m) - 12) =
      (linearPrincipalValueQTailLimit τ - (linearCutoff N τ - 12)) +
        ((∑' m : MarkedFilling τ, markedFillingQuadraticSummand τ m) -
          ∑ m ∈ markedFillingCutoff τ N, markedFillingQuadraticSummand τ m) := by
  rw [← rademacherLimit_eq_character, sum_markedFillingCutoff_eq_rademacherCutoff,
    rademacherLimit, ← rawBoltzmann_one, rawBoltzmann_eq_exp, rademacherCutoff_eq,
    tsum_markedFillingQuadraticSummand_eq_remainderLimit,
    sum_markedFillingCutoff_quadratic_eq_remainderCutoff]
  simp only [one_smul, neg_mul]
  abel

end

end D5.S3.Geometry.AdS3MarkedFillingCharacter
