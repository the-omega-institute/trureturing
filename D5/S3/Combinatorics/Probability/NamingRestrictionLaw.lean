/- GID: D5/S3/Combinatorics/Probability/NamingRestrictionLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/NamingRestrictionLaw
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Restricting a uniform partial naming completion gives a uniform injection. -/

import D5.S3.Combinatorics.Probability.PartialNameAssignment
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.CardEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal
open D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates residualEmbedding)
open D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion (uniform_equiv)

namespace D5.S3.Combinatorics.Probability.NamingRestrictionLaw

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

private noncomputable def relabel (σ : Equiv.Perm Y) : (X ↪ Y) ≃ (X ↪ Y) where
  toFun f := f.trans σ.toEmbedding
  invFun f := f.trans σ.symm.toEmbedding
  left_inv f := Function.Embedding.ext fun x => σ.symm_apply_apply (f x)
  right_inv f := Function.Embedding.ext fun x => σ.apply_symm_apply (f x)

private theorem uniform_restriction (ι : Z ↪ X) [Nonempty (X ↪ Y)] :
    let _ : Nonempty (Z ↪ Y) := ‹Nonempty (X ↪ Y)›.map (fun f => ι.trans f)
    (uniformPmf (X ↪ Y)).map (fun f => ι.trans f) = uniformPmf (Z ↪ Y) := by
  classical
  let _ : Nonempty (Z ↪ Y) := ‹Nonempty (X ↪ Y)›.map (fun f => ι.trans f)
  let restrict (f : X ↪ Y) := ι.trans f
  let μ := uniformPmf (X ↪ Y)
  let ν := μ.map restrict
  change ν = uniformPmf (Z ↪ Y)
  have hEqual (a b : Z ↪ Y) : ν a = ν b := by
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair a b a.injective b.injective
    let e : (↑({f | restrict f = a} : Set (X ↪ Y))) ≃
        (↑({f | restrict f = b} : Set (X ↪ Y))) :=
      (relabel σ).subtypeEquiv fun f => by
        constructor
        · intro he
          apply Function.Embedding.ext
          intro z
          change σ (f (ι z)) = b z
          rw [show f (ι z) = a z from congrArg (fun g : Z ↪ Y => g z) he, hσ]
        · intro he
          apply Function.Embedding.ext
          intro z
          apply σ.injective
          exact (congrArg (fun g : Z ↪ Y => g z) he).trans (hσ z).symm
    rw [← ν.toOuterMeasure_apply_singleton a, ← ν.toOuterMeasure_apply_singleton b]
    simp only [ν, PMF.toOuterMeasure_map_apply]
    rw [show restrict ⁻¹' {a} = {f | restrict f = a} by rfl,
      show restrict ⁻¹' {b} = {f | restrict f = b} by rfl]
    rw [uniformPmf_toOuterMeasure_apply, uniformPmf_toOuterMeasure_apply]
    congr 2
    exact Fintype.card_congr e
  apply PMF.ext
  intro b
  have hSum := ν.tsum_coe
  rw [tsum_fintype] at hSum
  simp only [hEqual _ b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hSum
  have h₀ : (Fintype.card (Z ↪ Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hTop : (Fintype.card (Z ↪ Y) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  change ν b = (Fintype.card (Z ↪ Y) : ℝ≥0∞)⁻¹
  calc
    ν b = (Fintype.card (Z ↪ Y) : ℝ≥0∞)⁻¹ * ((Fintype.card (Z ↪ Y) : ℝ≥0∞) * ν b) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h₀ hTop, one_mul]
    _ = _ := by rw [hSum, mul_one]


private theorem residual_restriction_eq_uniform {V N Z : Type*}
    [DecidableEq V] [Fintype V] [Fintype N] [Fintype Z]
    (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) (h : Nonempty (Candidates K A knownNames))
    (ι : Z ↪ {v // v ∉ K}) :
    let _ : Fintype (Candidates K A knownNames) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A knownNames) := h
    let _ : Nonempty (Z ↪ A) := h.map (fun f => ι.trans (residualEmbedding K A knownNames hsep f))
    (uniformPmf (Candidates K A knownNames)).map
      (fun f => ι.trans (residualEmbedding K A knownNames hsep f)) = uniformPmf (Z ↪ A) := by
  intro _ _ _
  let residual := residualEmbedding K A knownNames hsep
  let _ : Nonempty ({v // v ∉ K} ↪ A) := h.map residual
  calc
    _ = ((uniformPmf (Candidates K A knownNames)).map residual).map
        (fun f => ι.trans f) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [uniform_equiv residual]
      exact uniform_restriction ι


/-- Each injection in the restricted naming space has the reciprocal of its cardinality as mass. -/
noncomputable def namingMass (size : ℕ) : ℝ≥0∞ := (size : ℝ≥0∞)⁻¹

/-- The joint names on any fixed subcollection of the remaining vertices are uniform
over injections of that subcollection into the available name set. -/
theorem uniform_residual_restriction {V N Z : Type*}
    [DecidableEq V] [Finite V] [Finite N] [Finite Z]
    (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) (h : Nonempty (Candidates K A knownNames))
    (ι : Z ↪ {v // v ∉ K}) :
    let _ : Fintype (Candidates K A knownNames) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A knownNames) := h
    let mass := namingMass (Nat.card (Z ↪ A))
    ∀ g : Z ↪ A, ((uniformPmf (Candidates K A knownNames)).map
      (fun f => ι.trans (residualEmbedding K A knownNames hsep f))) g = mass := by
  intro _ _ mass g
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype N := Fintype.ofFinite N
  let _ : Fintype Z := Fintype.ofFinite Z
  let _ : Nonempty (Z ↪ A) := h.map (fun f => ι.trans (residualEmbedding K A knownNames hsep f))
  rw [residual_restriction_eq_uniform K A knownNames hsep h ι]
  simp [uniformPmf, mass, namingMass, Nat.card_eq_fintype_card]

end D5.S3.Combinatorics.Probability.NamingRestrictionLaw
