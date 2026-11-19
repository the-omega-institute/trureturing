import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Assign the three attachment labels in the cubical search to the actual
vertices attached in pairs to the six-cycle. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels

open Finset SimpleGraph
open private cycleLabel pairingModel from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
open private attachment from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private def representative (opposite : Bool) : Fin 3 → Fin 6 :=
  if opposite then ![0, 1, 2] else ![0, 1, 3]

private def rootIndex (i : Fin 3) : Fin 10 := ⟨i.val + 1, by omega⟩

private theorem pair_labels :
    ∀ (opposite : Bool) (j : Fin 3) (i : Fin 6),
      (i = representative opposite j ∨ i = pairingModel opposite (representative opposite j)) ↔
        attachment opposite i = rootIndex j := by
  decide +kernel

private theorem representative_label :
    ∀ (opposite : Bool) (j : Fin 3), attachment opposite (representative opposite j) = rootIndex j := by
  decide

private theorem cycleLabel_injective (shift : Fin 6) (reverse : Bool) :
    Function.Injective (cycleLabel shift reverse) := by
  exact (show ∀ (t : Fin 6) (b : Bool) (i j : Fin 6), cycleLabel t b i = cycleLabel t b j → i = j
    by decide +kernel) shift reverse

/-- The three attachment vertices can be labeled so that their incidences
to the cycle vertices agree exactly with the model used by the search. -/
theorem label_attachments {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : Finset V) (hA : A.card = 3)
    (cyc : Fin 6 ↪ V) (opposite : Bool)
    (hpair : ∀ i : Fin 6, ∃ x ∈ A, H.neighborFinset x = {cyc i, cyc (pairingModel opposite i)}) :
    ∃ roots : Fin 3 ↪ V, Finset.univ.image roots = A ∧
      ∀ j i, H.Adj (roots j) (cyc i) ↔ attachment opposite i = rootIndex j := by
  choose r hr hrN using fun j : Fin 3 => hpair (representative opposite j)
  have hlink (j : Fin 3) (i : Fin 6) :
      H.Adj (r j) (cyc i) ↔ attachment opposite i = rootIndex j := by
    rw [← H.mem_neighborFinset, hrN]
    simpa only [Finset.mem_insert, Finset.mem_singleton, cyc.injective.eq_iff] using
      pair_labels opposite j i
  have hinj : Function.Injective r := by
    intro j k h
    have hj := (hlink j (representative opposite j)).mpr (representative_label opposite j)
    rw [h] at hj
    have he := (hlink k (representative opposite j)).mp hj
    rw [representative_label] at he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change j.val + 1 = k.val + 1 at hv
    omega
  let roots : Fin 3 ↪ V := ⟨r, hinj⟩
  refine ⟨roots, Finset.eq_of_subset_of_card_le ?_ ?_, hlink⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hr j
  · rw [hA, Finset.card_image_of_injective _ roots.injective, Finset.card_univ, Fintype.card_fin]

/-- Apply the labeling to the cycle isomorphism and the dihedral relabeling
produced by the actual compression. -/
theorem label_paired_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V) (hA : A.card = 3)
    (e : cycleGraph 6 ≃g H.induce (B : Set V)) (shift : Fin 6) (reverse opposite : Bool)
    (hpair : ∀ i : Fin 6, ∃ x ∈ A, H.neighborFinset x =
      {(e (cycleLabel shift reverse i)).val,
        (e (cycleLabel shift reverse (pairingModel opposite i))).val}) :
    ∃ roots : Fin 3 ↪ V, Finset.univ.image roots = A ∧
      ∀ j i, H.Adj (roots j) (e (cycleLabel shift reverse i)).val ↔
        attachment opposite i = rootIndex j := by
  let c : Fin 6 ↪ V := ⟨fun i => (e (cycleLabel shift reverse i)).val,
    fun _ _ h => cycleLabel_injective shift reverse (e.injective (Subtype.ext h))⟩
  exact label_attachments H A hA c opposite hpair

#print axioms label_paired_cycle

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels
