/- GID: D5/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample.claim; result=D5/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample.result; claim=D5/S3/Combinatorics/CayleySumCodes/AffineExhaustivenessCounterexample.claim
   digest: The connected affine F3 graph refutes the old total-code exhaustiveness. -/

import D5.S3.Combinatorics.CayleySumCodes.AffineExamples

/-!
The two actual examples of Ma--Nikandish--Zhang, revised correction,
Examples 3.4 and 3.5. `listed` is the complete multiplier-transversal
total-code construction retained from Zhang's Theorem 5.13. No new
exhaustive classification is asserted.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.AffineExhaustivenessCounterexample

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.AffineExamples

/-- The actual retained affine total-code family: the unique internal
multiplier is a nonsquare of H, and all its affine conjugates are included. -/
def listed {F : Type*} [Field F] (H : Subgroup Fˣ) (Y : Set (Affine1 F)) : Prop :=
  ∃ T : Set Fˣ, ∃ a0 : Fˣ,
    Subgroup.IsComplement T (H : Set Fˣ) ∧ a0 ∈ T ∧ a0 ∈ H ∧
      a0 ∉ squares H ∧ Y = transversalConnection T

private theorem identity_not_mem_listed {F : Type*} [Field F]
    (H : Subgroup Fˣ) (Y : Set (Affine1 F)) (hy : listed H Y) :
    (1 : Affine1 F) ∉ Y := by
  rintro hi
  obtain ⟨T, a0, ht, haT, haH, hns, rfl⟩ := hy
  have h1T : (1 : Fˣ) ∈ T := hi
  obtain ⟨u, _, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht 1
  have ha1 : a0 = 1 := congrArg Subtype.val
    ((hu ⟨a0, haT⟩ (by simpa using H.inv_mem haH)).trans
      (hu ⟨1, h1T⟩ (by simp)).symm)
  exact hns ⟨1, H.one_mem, by simp [ha1]⟩

/-- The old exhaustiveness assertion, already at its q=3 instance and
the full multiplicative complement. Connectedness is included. -/
def claim : Prop :=
  ∀ Y : Set (Affine1 (ZMod 3)), ∀ hn : NormalSubset Y,
    IsTotalPerfectCode (sumGraph Y hn) (complement (F := ZMod 3)) →
      (sumGraph Y hn).Connected → listed (⊤ : Subgroup (ZMod 3)ˣ) Y

/-- The old connected affine total-code exhaustiveness fails already for
q=3, at its complete order-two multiplicative complement. The separate
q=5 application is given by `AffineExamples.total_code` and `connected_iff`;
its complete parameter correspondence and derivation are given in the affine exposition. -/
theorem result : ¬ claim := by
  have hc3 : (1 : ZMod 3) ≠ -1 := by decide +kernel
  have hs3 : ∀ a : (ZMod 3)ˣ, a * a = 1 ∨ a * a = -1 := by decide +kernel
  have hcon3 : (sumGraph (connection (F := ZMod 3)) connection_normal).Connected :=
    (connected_iff hc3).mpr (by decide +kernel)
  intro hall
  exact identity_not_mem_listed _ _
    (hall _ connection_normal (total_code hc3 hs3) hcon3) (Or.inl rfl)

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.AffineExhaustivenessCounterexample
