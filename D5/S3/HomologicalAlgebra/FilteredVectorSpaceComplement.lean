/- GID: D5/S3/HomologicalAlgebra/FilteredVectorSpaceComplement
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FilteredVectorSpaceComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite increasing subspace chain admits a complement splitting every layer. -/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.FilteredVectorSpaceComplement

/-- A single ambient complement splits every layer of a finite increasing chain.
The chain may be empty, repeat layers, and have arbitrary endpoints; the ambient
module need not be finite-dimensional, and the division ring need not be commutative. -/
theorem exists_common_complement_of_monotone
    {k : Type*} [DivisionRing k] {V : Type*} [AddCommGroup V] [Module k V]
    {n : ℕ} (F : Fin n → Submodule k V) (hF : Monotone F) (K : Submodule k V) :
    ∃ L : Submodule k V, IsCompl K L ∧
      ∀ i, F i = (F i ⊓ K) ⊔ (F i ⊓ L) := by
  classical
  -- Build a partial complement inside any upper bound of the chain.
  have build : ∀ m (G : Fin m → Submodule k V), Monotone G →
      ∀ B : Submodule k V, (∀ i, G i ≤ B) →
        ∃ C : Submodule k V, C ≤ B ∧ Disjoint C K ∧
          ∀ i, G i = (G i ⊓ K) ⊔ (G i ⊓ C) := by
    intro m
    induction m with
    | zero =>
        intro G _ B _
        exact ⟨⊥, bot_le, disjoint_bot_left, fun i => Fin.elim0 i⟩
    | succ m ih =>
        intro G hG B hGB
        let A := G (Fin.last m)
        obtain ⟨C, hCA, hCK, hC⟩ := ih (fun i => G i.castSucc)
          (fun i j hij => hG hij) A (fun i => hG (Fin.le_last i.castSucc))
        -- Extend the old partial complement inside the new last layer.
        have hdis : Disjoint (⟨C, hCA⟩ : Set.Iic A)
            (⟨A ⊓ K, show A ⊓ K ≤ A from inf_le_left⟩ : Set.Iic A) :=
          Set.Iic.disjoint_iff.mpr (hCK.mono_right inf_le_right)
        obtain ⟨D, hCD, hD⟩ := hdis.exists_isCompl
        have hCD' : C ≤ (D : Submodule k V) := hCD
        have hDA : (D : Submodule k V) ≤ A := D.property
        obtain ⟨hDK, hsum⟩ := Set.Iic.isCompl_iff.mp hD
        have hDK' : Disjoint (D : Submodule k V) K := by
          rw [disjoint_iff] at hDK ⊢
          simpa only [← inf_assoc, inf_of_le_left hDA] using hDK
        refine ⟨D, hDA.trans (hGB (Fin.last m)), hDK', ?_⟩
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · change A = (A ⊓ K) ⊔ (A ⊓ (D : Submodule k V))
          rw [inf_of_le_right hDA, sup_comm]
          exact hsum.symm
        · apply le_antisymm
          · calc
              G i.castSucc = (G i.castSucc ⊓ K) ⊔ (G i.castSucc ⊓ C) := hC i
              _ ≤ (G i.castSucc ⊓ K) ⊔ (G i.castSucc ⊓ (D : Submodule k V)) :=
                sup_le_sup_left (inf_le_inf_left _ hCD') _
          · exact sup_le inf_le_left inf_le_left
  obtain ⟨C, _, hCK, hC⟩ := build n F hF ⊤ (fun _ => le_top)
  -- One ambient enlargement preserves all previously established splittings.
  obtain ⟨L, hCL, hL⟩ := hCK.exists_isCompl
  refine ⟨L, hL.symm, fun i => le_antisymm ?_ (sup_le inf_le_left inf_le_left)⟩
  calc
    F i = (F i ⊓ K) ⊔ (F i ⊓ C) := hC i
    _ ≤ (F i ⊓ K) ⊔ (F i ⊓ L) :=
      sup_le_sup_left (inf_le_inf_left _ hCL) _

end D5.S3.HomologicalAlgebra.FilteredVectorSpaceComplement
