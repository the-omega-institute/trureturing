/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed polar sum for the actual Bose-adapted DPS cone. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The application in Haobo Ma and Wenlin Zhang's note retains the closure
in Britz--Laurent's dual-sum question. It does not prove that the sum itself
is closed, nor does it give unrestricted exact dual-certificate lifting. -/

open scoped BigOperators ComplexOrder Pointwise RealInnerProductSpace
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDual

noncomputable section
set_option backward.isDefEq.respectTransparency false

private lemma polar_inter_subspace {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (C : ProperCone ℝ V) (L : Submodule ℝ V) :
    (ProperCone.dual (innerₗ V) ((C : Set V) ∩ (L : Set V)) : Set V) =
      closure ((ProperCone.dual (innerₗ V) (C : Set V) : Set V) +
        (L.orthogonal : Set V)) := by
  let K : PointedCone ℝ V :=
    (ProperCone.dual (innerₗ V) (C : Set V)).toPointedCone ⊔
      L.orthogonal.restrictScalars (Nonneg ℝ)
  let Q : ProperCone ℝ V := ⟨K.closure, isClosed_closure⟩
  have hflip : (innerₗ V).flip = innerₗ V := by
    exact flip_innerₗ V
  have hdual : (ProperCone.dual (innerₗ V) (Q : Set V) : Set V) =
      (C : Set V) ∩ (L : Set V) := by
    ext x
    constructor
    · intro hx
      have hc : x ∈ ProperCone.dual (innerₗ V).flip
          (ProperCone.dual (innerₗ V) (C : Set V) : Set V) := by
        intro y hy
        rw [hflip]
        exact hx (subset_closure (Submodule.mem_sup_left hy))
      rw [ProperCone.dual_flip_dual] at hc
      have hl : x ∈ L.orthogonal.orthogonal := by
        apply (Submodule.mem_orthogonal _ _).mpr
        intro y hy
        have hp : 0 ≤ inner ℝ y x :=
          hx (subset_closure (Submodule.mem_sup_right hy))
        have hn : 0 ≤ inner ℝ (-y) x :=
          hx (subset_closure (Submodule.mem_sup_right (L.orthogonal.neg_mem hy)))
        rw [inner_neg_left] at hn
        linarith
      rw [Submodule.orthogonal_orthogonal] at hl
      exact ⟨hc,hl⟩
    · rintro ⟨hc,hl⟩ y hy
      have hclosed : IsClosed {z : V | 0 ≤ inner ℝ z x} :=
        isClosed_le continuous_const (by fun_prop)
      apply closure_minimal (t := {z : V | 0 ≤ inner ℝ z x}) ?_ hclosed hy
      intro z hz
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hz
      change 0 ≤ inner ℝ (a + b) x
      have ha' : 0 ≤ inner ℝ a x := by
        simpa only [innerₗ_apply_apply, real_inner_comm] using ha hc
      have hb' : inner ℝ b x = 0 := by
        simpa only [real_inner_comm] using (Submodule.mem_orthogonal _ _).mp hb x hl
      simpa only [inner_add_left, hb', add_zero] using ha'
  calc
    _ = (ProperCone.dual (innerₗ V)
        (ProperCone.dual (innerₗ V) (Q : Set V) : Set V) : Set V) := by rw [hdual]
    _ = (Q : Set V) := by
      simpa only [flip_innerₗ] using congrArg (fun R : ProperCone ℝ V => (R : Set V))
        (ProperCone.dual_flip_dual (innerₗ V) Q)
    _ = _ := by
      change closure (K : Set V) = _
      rw [show (K : Set V) =
        (ProperCone.dual (innerₗ V) (C : Set V) : Set V) +
          (L.orthogonal : Set V) from Submodule.coe_sup _ _]

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

open private ordinary_pos from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS

private lemma ordinary_add (root leaf : I) (hne : root ≠ leaf)
    {ρ τ : Matrix (L × L) (L × L) ℂ}
    (hρ : ρ ∈ ordinaryDPS root leaf hne) (hτ : τ ∈ ordinaryDPS root leaf hne) :
    ρ + τ ∈ ordinaryDPS root leaf hne := by
  obtain ⟨E,hE⟩ := hρ
  obtain ⟨F,hF⟩ := hτ
  refine ⟨E+F,?_,?_,?_⟩
  · simp only [Matrix.mul_add, Matrix.add_mul, hE.1, hF.1]
  · have hm : edgeMarginal root leaf hne (E+F) =
        edgeMarginal root leaf hne E + edgeMarginal root leaf hne F := by
      ext x y
      simp [edgeMarginal,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        Finset.sum_add_distrib]
    rw [hm, hE.2.1, hF.2.1]
  · intro S hr
    have ht : partialTransposeOn S (E+F) = partialTransposeOn S E +
        partialTransposeOn S F := rfl
    rw [ht]
    exact (hE.2.2 S hr).add (hF.2.2 S hr)

private lemma ordinary_smul (root leaf : I) (hne : root ≠ leaf)
    {ρ : Matrix (L × L) (L × L) ℂ} (hρ : ρ ∈ ordinaryDPS root leaf hne)
    (c : ℝ) (hc : 0 ≤ c) : c • ρ ∈ ordinaryDPS root leaf hne := by
  obtain ⟨E,hE⟩ := hρ
  refine ⟨c • E,?_,?_,?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, hE.1]
  · have hm : edgeMarginal root leaf hne (c • E) =
        c • edgeMarginal root leaf hne E := by
      ext x y
      simp [edgeMarginal,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        Finset.smul_sum]
    rw [hm,hE.2.1]
  · intro S hr
    exact (hE.2.2 S hr).smul hc

/-- The ordinary DPS cone in the real Hermitian space, with its actual tensor
lift and unnormalized marginal. Closedness is proved by bounded PSD lifts. -/
def ordinaryCone (root leaf : I) (hne : root ≠ leaf) :
    ProperCone ℝ (HermitianMat (L × L) ℂ) where
  carrier := {ρ | ρ.mat ∈ ordinaryDPS root leaf hne}
  zero_mem' := by
    refine ⟨0,?_,?_,?_⟩
    · simp
    · ext x y
      simp [edgeMarginal,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight]
    · intro S hr
      exact Matrix.PosSemidef.zero
  add_mem' := by
    intro ρ τ hρ hτ
    exact ordinary_add root leaf hne hρ hτ
  smul_mem' := by
    intro c ρ hρ
    exact ordinary_smul root leaf hne hρ c.val c.property
  isClosed' := (ordinary_closed root leaf hne).preimage HermitianMat.continuous_mat

/-- The full real linear space of pair-Bose-supported Hermitian operators.
Positivity is supplied by the DPS cone, not built into this subspace. -/
def boseSubspace : Submodule ℝ (HermitianMat (L × L) ℂ) where
  carrier := {ρ | pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat}
  zero_mem' := by simp
  add_mem' := by
    intro ρ τ hρ hτ
    change pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat at hρ
    change pairSymmetricProjector * τ.mat * pairSymmetricProjector = τ.mat at hτ
    change pairSymmetricProjector * (ρ + τ).mat * pairSymmetricProjector = (ρ + τ).mat
    simpa only [HermitianMat.mat_add, Matrix.mul_add, Matrix.add_mul, hρ, hτ]
  smul_mem' := by
    intro c ρ hρ
    change pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat at hρ
    change pairSymmetricProjector * (c • ρ).mat * pairSymmetricProjector = (c • ρ).mat
    simpa only [HermitianMat.mat_smul, Matrix.mul_smul, Matrix.smul_mul, hρ]

private lemma ordinary_input_pos (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (hρ : ρ ∈ ordinaryDPS root leaf hne) :
    ρ.PosSemidef := by
  obtain ⟨E,hE⟩ := hρ
  rw [← hE.2.1]
  exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
    ((ordinary_pos root leaf hne ρ E hE).submatrix (edgeSplit root leaf hne).symm)

/-- The polar of the actual adapted DPS cone is the closure of the ordinary
DPS polar plus the orthogonal complement of the Bose support subspace.
The closure bar is essential to the scope of this theorem. -/
theorem closed_dual_identity (root leaf : I) (hne : root ≠ leaf) :
    (ProperCone.dual (innerₗ (HermitianMat (L × L) ℂ))
      {ρ : HermitianMat (L × L) ℂ | ρ.mat ∈ adaptedDPS root leaf hne} :
        Set (HermitianMat (L × L) ℂ)) =
      closure ((ProperCone.dual (innerₗ (HermitianMat (L × L) ℂ))
        (ordinaryCone (L := L) root leaf hne : Set (HermitianMat (L × L) ℂ)) :
          Set (HermitianMat (L × L) ℂ)) +
        ((boseSubspace (L := L)).orthogonal : Set (HermitianMat (L × L) ℂ))) := by
  have he : {ρ : HermitianMat (L × L) ℂ | ρ.mat ∈ adaptedDPS root leaf hne} =
      (ordinaryCone (L := L) root leaf hne : Set (HermitianMat (L × L) ℂ)) ∩
        (boseSubspace (L := L) : Set (HermitianMat (L × L) ℂ)) := by
    ext ρ
    rw [adapted_eq_inter]
    change (ρ.mat ∈ ordinaryDPS root leaf hne ∧ ρ.mat.PosSemidef ∧
      pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat) ↔
        ρ.mat ∈ ordinaryDPS root leaf hne ∧
          pairSymmetricProjector * ρ.mat * pairSymmetricProjector = ρ.mat
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h =>
      ⟨h.1,ordinary_input_pos root leaf hne ρ.mat h.1,h.2⟩⟩
  rw [he]
  exact polar_inter_subspace _ _

#print axioms closed_dual_identity

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDual
