/- GID: D5/S1/Dynamics/ProfiniteIntegers
   generality: I
   mirror-B: D5/B/S1/Dynamics/ProfiniteIntegers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Natural numbers embed densely in the compatible-residue profinite integers. -/

import Mathlib

namespace D5.S1.Dynamics

/-- One residue reading for every positive modulus. -/
abbrev ResidueFamily := (m : ℕ) → ZMod (m + 1)

/-- The profinite integers as compatible residue readings over all positive moduli. -/
abbrev ProfiniteIntegers :=
  {x : ResidueFamily //
    ∀ {m n : ℕ} (h : m + 1 ∣ n + 1), ZMod.castHom h (ZMod (m + 1)) (x n) = x m}

namespace ProfiniteIntegers

/-- The compatible residue family represented by a natural number. -/
def natEmbedding (n : ℕ) : ProfiniteIntegers :=
  ⟨fun m => (n : ZMod (m + 1)), by
    intro m k h
    simp⟩

instance : TopologicalSpace ProfiniteIntegers :=
  TopologicalSpace.induced Subtype.val inferInstance

private def commonModulus (indices : Finset ℕ) : ℕ :=
  indices.prod (fun m => m + 1)

private theorem commonModulus_pos (indices : Finset ℕ) : 0 < commonModulus indices := by
  exact Finset.prod_pos fun m _ => Nat.zero_lt_succ m

private def commonIndex (indices : Finset ℕ) : ℕ :=
  commonModulus indices - 1

private theorem commonIndex_succ (indices : Finset ℕ) :
    commonIndex indices + 1 = commonModulus indices := by
  exact Nat.sub_add_cancel (commonModulus_pos indices)

private theorem divides_commonIndex {indices : Finset ℕ} {m : ℕ}
    (hm : m ∈ indices) : m + 1 ∣ commonIndex indices + 1 := by
  rw [commonIndex_succ]
  exact Finset.dvd_prod_of_mem (fun k : ℕ => k + 1) hm

/-- Every finite window of a compatible residue family has one simultaneous
natural-number representative. -/
theorem exists_nat_eq_on_finset (x : ProfiniteIntegers) (indices : Finset ℕ) :
    ∃ n : ℕ, ∀ m ∈ indices, (natEmbedding n).1 m = x.1 m := by
  refine ⟨(x.1 (commonIndex indices)).val, ?_⟩
  intro m hm
  change ((x.1 (commonIndex indices)).val : ZMod (m + 1)) = x.1 m
  simpa [ZMod.castHom_apply] using x.2 (divides_commonIndex hm)

/-- Distinct natural numbers have distinct compatible residue families. -/
theorem natEmbedding_injective : Function.Injective natEmbedding := by
  intro a b hab
  let m := max a b
  have hcoord : (a : ZMod (m + 1)) = (b : ZMod (m + 1)) := by
    exact congrFun (congrArg Subtype.val hab) m
  have ha : a < m + 1 := Nat.lt_succ_of_le (Nat.le_max_left a b)
  have hb : b < m + 1 := Nat.lt_succ_of_le (Nat.le_max_right a b)
  have hval := congrArg ZMod.val hcoord
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hval

/-- The natural-number residue families meet every neighborhood in the
profinite product topology. -/
theorem denseRange_natEmbedding : DenseRange natEmbedding := by
  rw [DenseRange]
  intro x
  rw [mem_closure_iff_nhds']
  intro neighborhood hneighborhood
  change neighborhood ∈ @nhds ProfiniteIntegers
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace ResidueFamily)) x at hneighborhood
  rw [mem_nhds_induced] at hneighborhood
  rcases hneighborhood with ⟨ambient, hambient, hsubset⟩
  classical
  simp only [nhds_pi, Filter.mem_pi'] at hambient
  rcases hambient with ⟨indices, coordinateSets, hx, hcoordinateSets⟩
  rcases exists_nat_eq_on_finset x indices with ⟨n, hn⟩
  refine ⟨⟨natEmbedding n, ⟨n, rfl⟩⟩, hsubset ?_⟩
  apply hcoordinateSets
  intro m hm
  rw [hn m hm]
  exact mem_of_mem_nhds (hx m)

/-- Natural numbers inject into the profinite integers and are dense there. -/
theorem nat_embedding_injective_and_dense :
    Function.Injective natEmbedding ∧ DenseRange natEmbedding := by
  exact ⟨natEmbedding_injective, denseRange_natEmbedding⟩

end ProfiniteIntegers

end D5.S1.Dynamics
