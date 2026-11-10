/- GID: D5/S3/FiniteGroups/Semilinear/ChartFieldDegree
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/ChartFieldDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual generated coordinate field controls full semilinear isotropy and orbit size. -/

import D5.S3.FiniteGroups.Semilinear.WeightOneChart
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! The chart stabilizer is the fixing subgroup of the actual coordinate-generated field. -/

set_option autoImplicit false

namespace WeightedSemilinear

universe u
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {J : Type u} (w : J → ℕ)

private theorem tuple_stabilizer (b : J → K) :
    MulAction.stabilizer Gal(K/F) b =
      (IntermediateField.adjoin F (Set.range b)).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.forall_mem_adjoin_smul_eq_self_iff F σ]
  simp only [MulAction.mem_stabilizer_iff, funext_iff, Pi.smul_apply,
    AlgEquiv.smul_def, Set.forall_mem_range]

local instance : MulAction (Group F K) (Option J → K) := weightedAction (chartWeights w)
local instance : MulAction (Group F K) (Chart (K := K) (J := J) w) := chartAction w

private theorem ambient_stabilizer (A : Chart (K := K) (J := J) w) :
    MulAction.stabilizer (Group F K) A.val = MulAction.stabilizer (Group F K) A := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  exact Subtype.ext_iff.symm

/-- The generated normalized-coordinate field controls the stabilizer and the full ambient
weighted-semilinear orbit. There is no finiteness or nonvanishing hypothesis on the residual tuple. -/
theorem chart_field_degree (p n : ℕ) [Fact p.Prime]
    {K : Type} [Field K] [Fintype K] [Algebra (ZMod p) K]
    (A : Chart (K := K) (J := J) w) (hK : Fintype.card K = p ^ n) :
    let L := IntermediateField.adjoin (ZMod p) (Set.range (normalize w A))
    let e := Module.finrank (ZMod p) L
    MulAction.stabilizer Gal(K/ZMod p) (normalize w A) = L.fixingSubgroup ∧
      e ∣ n ∧
      Nat.card (MulAction.stabilizer (Group (ZMod p) K) A.val) = n / e ∧
      Nat.card (MulAction.orbit (Group (ZMod p) K) A.val) = (p ^ n - 1) * e := by
  classical
  let L := IntermediateField.adjoin (ZMod p) (Set.range (normalize w A))
  let e := Module.finrank (ZMod p) L
  have hL : MulAction.stabilizer Gal(K/ZMod p) (normalize w A) = L.fixingSubgroup :=
    tuple_stabilizer (normalize w A)
  have hn : Module.finrank (ZMod p) K = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    exact (FiniteField.pow_finrank_eq_card p K).trans hK
  have ht : e * Module.finrank L K = n :=
    (Module.finrank_mul_finrank (ZMod p) L K).trans hn
  have hs : Nat.card (MulAction.stabilizer (Group (ZMod p) K) A.val) =
      Module.finrank L K := by
    rw [ambient_stabilizer w A,
      Nat.card_congr (chartStabilizerEquiv (F := ZMod p) w A).toEquiv, hL]
    exact IsGalois.card_fixingSubgroup_eq_finrank L
  have hg : Nat.card (Group (ZMod p) K) = (p ^ n - 1) * n := by
    rw [SemidirectProduct.card, Nat.card_units, IsGalois.card_aut_eq_finrank,
      Nat.card_eq_fintype_card, hK, hn]
  have ho := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Group (ZMod p) K) A.val)
  rw [Nat.card_prod, hs, hg, ← ht, ← Nat.mul_assoc] at ho
  have hd : Module.finrank L K ≠ 0 := Module.finrank_pos.ne'
  refine ⟨hL, ⟨Module.finrank L K, ht.symm⟩, ?_, ?_⟩
  · rw [hs, ← hn]
    exact (Module.finrank_div_finrank_cancel_left (ZMod p) L K
      Module.finrank_pos.ne').symm
  · exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) ho

#print axioms chart_field_degree

end WeightedSemilinear
