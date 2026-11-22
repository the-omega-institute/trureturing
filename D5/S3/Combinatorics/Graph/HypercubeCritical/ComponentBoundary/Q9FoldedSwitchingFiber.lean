/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSwitchingFiber
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSwitchingFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity and frozen edges jointly determine the affine family for exact signed rows. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

/-! Joint switching fibers for parity and specified edge coordinates. -/

set_option autoImplicit false

open scoped Matrix
open LinearMap

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber

open Q9FoldedCycleRank
open private cast_negativeDegree signedRow_eq_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

/-- Adjoin the selected edge coordinates to the binary incidence rows. -/
abbrev jointMap {V : Type*} {E : Type*} [Fintype E] (B : Matrix V E (ZMod 2))
    (F : Set E) : (E → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) × (F → ZMod 2) :=
  B.mulVecLin.prod (funLeft (ZMod 2) (ZMod 2) (Subtype.val : F → E))

/-- Joint compatibility determines the affine family of switched edge signings. Its direction
space has two rank descriptions and suffices for the exact integer signed-row test. -/
theorem joint_switching_fiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Set G.edgeSet)
    (s : G.edgeSet → ZMod 2) (q : V → ℤ) (f : F → ZMod 2) :
    let B := incidence G
    let T := Bᵀ.mulVecLin
    let J := jointMap B F
    let b := ((fun v => (q v : ZMod 2)), f)
    let S := ker J
    let D := S ⊓ range T
    let R := (bicycles B).mkQ.domRestrict (S.comap (Cycles B).subtype)
    let W : Set (G.edgeSet → ZMod 2) := {w | (∃ z, w = s + T z) ∧ J w = b}
    (W.Nonempty ↔ b - J s ∈ range (J.comp T)) ∧
    (∀ w₀ ∈ W, ∀ w, w ∈ W ↔ ∃ d : D, w = w₀ + d.val) ∧
    (Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range (J.comp T)) = B.rank) ∧
    (Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range R) =
      Module.finrank (ZMod 2) S) ∧
    ((∀ w, negativeDegree G w = q → (fun e : F => w e.val) = f) →
      ((∃ z, signedRow G (s + T z) = fun v => (G.degree v : ℤ) - 2 * q v) ↔
        ∃ w ∈ W, negativeDegree G w = q)) := by
  dsimp only
  let B := incidence G
  let T := Bᵀ.mulVecLin
  let J := jointMap B F
  let b := ((fun v => (q v : ZMod 2)), f)
  let S := ker J
  let D := S ⊓ range T
  let W : Set (G.edgeSet → ZMod 2) := {w | (∃ z, w = s + T z) ∧ J w = b}
  have hS : S ≤ Cycles B := by
    intro w hw
    exact mem_ker.mpr (congrArg Prod.fst (mem_ker.mp hw))
  have hswitch (z : V → ZMod 2) : J (s + T z) = b ↔ (J.comp T) z = b - J s := by
    rw [map_add, add_comm, eq_sub_iff_add_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change W.Nonempty ↔ _
    constructor
    · rintro ⟨w, ⟨z, rfl⟩, hz⟩
      exact ⟨z, (hswitch z).mp hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨s + T z, ⟨z, rfl⟩, (hswitch z).mpr hz⟩
  · change ∀ w₀ ∈ W, ∀ w, w ∈ W ↔ ∃ d : D, w = w₀ + d.val
    rintro w₀ ⟨⟨z₀, rfl⟩, hz₀⟩ w
    constructor
    · rintro ⟨⟨z, rfl⟩, hz⟩
      refine ⟨⟨T (z - z₀), ?_, ⟨z - z₀, rfl⟩⟩, ?_⟩
      · apply mem_ker.mpr
        rw [map_sub, map_sub, ((hswitch z).mp hz : J (T z) = b - J s),
          ((hswitch z₀).mp hz₀ : J (T z₀) = b - J s), sub_self]
      · change s + T z = s + T z₀ + T (z - z₀)
        rw [map_sub]
        abel
    · rintro ⟨d, rfl⟩
      obtain ⟨t, ht⟩ := d.property.2
      refine ⟨⟨z₀ + t, ?_⟩, ?_⟩
      · rw [map_add, ht, add_assoc]
      · change J (s + T z₀ + d.val) = b
        rw [map_add, hz₀, mem_ker.mp d.property.1, add_zero]
  · change Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range (J.comp T)) = B.rank
    have h := finrank_range_add_finrank_ker (J.domRestrict (range T))
    rw [range_domRestrict, ← range_comp, ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq (range T), Submodule.map_comap_subtype, inf_comm (range T)] at h
    change _ + Module.finrank (ZMod 2) D = Bᵀ.rank at h
    rw [Matrix.rank_transpose, add_comm] at h
    exact h
  · let C := Cycles B
    let S' := S.comap C.subtype
    let R := (bicycles B).mkQ.domRestrict S'
    change Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range R) =
      Module.finrank (ZMod 2) S
    have h := finrank_range_add_finrank_ker R
    change _ + Module.finrank (ZMod 2) (ker ((bicycles B).mkQ.domRestrict S')) = _
      at h
    rw [ker_domRestrict, Submodule.ker_mkQ,
      ← Submodule.finrank_map_subtype_eq S', Submodule.map_comap_subtype,
      ← Submodule.finrank_map_subtype_eq C (S' ⊓ bicycles B),
      ← Submodule.finrank_map_subtype_eq C S',
      Submodule.map_inf _ C.injective_subtype] at h
    dsimp only [S', bicycles] at h
    rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      inf_eq_right.mpr hS, inf_eq_right.mpr inf_le_left, ← inf_assoc,
      inf_eq_left.mpr hS, add_comm] at h
    exact h
  · change (∀ w, negativeDegree G w = q → (fun e : F => w e.val) = f) → (_ ↔ ∃ w ∈ W, _)
    intro frozen
    constructor
    · rintro ⟨z, hz⟩
      have hq := (signedRow_eq_iff G _ q).mp hz
      have hp := cast_negativeDegree G (s + T z)
      rw [hq] at hp
      exact ⟨s + T z, ⟨⟨z, rfl⟩, Prod.ext hp.symm (frozen _ hq)⟩, hq⟩
    · rintro ⟨w, ⟨⟨z, rfl⟩, _⟩, hq⟩
      exact ⟨z, (signedRow_eq_iff G _ q).mpr hq⟩

#print axioms joint_switching_fiber

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber
