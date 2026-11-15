/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every eight actual coordinate Lagrangians have a unique actual ninth completion. -/

import D5.S3.Combinatorics.Orthogonality.SevenBitSpreadCompletion

/-! Exact finite-point/coordinate correspondence for arbitrary actual
Submodules, followed by the full original unique ninth completion theorem.
No incidence counts or expected answer are assumed of the actual input. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.SevenDimensional.ActualSpreadCompletion
open SevenBitGeometry

/-- Every nonzero point of the entire actual Submodule. -/
def pointsOf (U : Submodule (ZMod 2) Coordinates) : Finset Vector := by
  classical
  exact (Finset.univ.filter (fun v => bits v ∈ U)).erase 0

private theorem mem_points (U : Submodule (ZMod 2) Coordinates) (v : Vector) :
    v ∈ pointsOf U ↔ v ≠ 0 ∧ bits v ∈ U := by
  classical
  simp [pointsOf]

/-- Complete carrier equality, including zero. -/
theorem carrier (U : Submodule (ZMod 2) Coordinates) :
    (U : Set Coordinates) = bits '' ((insert 0 (pointsOf U) : Finset Vector) : Set Vector) := by
  ext w
  obtain ⟨v,rfl⟩ := bits_bijective.2 w
  constructor
  · intro hv
    refine ⟨v,?_,rfl⟩
    by_cases hz : v = 0
    · simp [hz]
    · exact Finset.mem_insert_of_mem ((mem_points U v).mpr ⟨hz,hv⟩)
  · rintro ⟨u,hu,huv⟩
    have heq : u = v := bits_bijective.1 huv
    subst u
    rcases Finset.mem_insert.mp hu with rfl | hv
    · change bits 0 ∈ U
      rw [bits_zero]
      exact U.zero_mem
    · exact ((mem_points U v).mp hv).2

private theorem points_injective : Function.Injective pointsOf := by
  intro U W h
  apply SetLike.coe_injective
  rw [carrier U,carrier W,h]

/-- Derive all finite Lagrangian data from the actual full-dimensional
isotropic Submodule. Incidence and closure are conclusions. -/
theorem actual_data (U : Submodule (ZMod 2) Coordinates)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (horth : ∀ u ∈ U, ∀ v ∈ U, dotProduct u v = 0) :
    LagrangianData (pointsOf U) := by
  classical
  let Z : Finset Vector := Finset.univ.filter (fun v => bits v ∈ U)
  let f : {v : Vector // v ∈ Z} → U := fun v =>
    ⟨bits v,(Finset.mem_filter.mp v.property).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (bits_bijective.1 (congrArg Subtype.val h))
    · rintro ⟨u,hu⟩
      obtain ⟨v,rfl⟩ := bits_bijective.2 u
      exact ⟨⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩⟩,rfl⟩
  have hn : Nat.card U = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,
      Nat.card_eq_fintype_card,ZMod.card]
    norm_num
  have hzcard : Z.card = 8 := by
    have h := Nat.card_congr (Equiv.ofBijective f hf)
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,hn] at h
    exact h
  have hzero : (0 : Vector) ∈ Z := by simp [Z,bits_zero]
  have hcard : (pointsOf U).card = 7 := by
    have h := Finset.card_erase_add_one hzero
    change (Z.erase 0).card = 7
    omega
  have hsub : pointsOf U ⊆ evenPoints := by
    intro v hv
    have hh := (mem_points U v).mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,
      (bits_dot v v).mp (horth _ hh.2 _ hh.2)⟩
  have hp : ∀ x ∈ pointsOf U, ∀ y ∈ pointsOf U, dot x y = 0 := by
    intro x hx y hy
    exact (bits_dot x y).mp
      (horth _ ((mem_points U x).mp hx).2 _ ((mem_points U y).mp hy).2)
  exact SevenBitSpreadCompletion.orthogonal_seven _ hsub hcard hp

private theorem points_disjoint (U W : Submodule (ZMod 2) Coordinates)
    (h : Disjoint U W) : Disjoint (pointsOf U) (pointsOf W) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hv' := (mem_points U v).mp hv
  have hw' := (mem_points W v).mp hw
  have hz : bits v = 0 := (Submodule.disjoint_def.mp h) _ hv'.2 hw'.2
  exact hv'.1 (bits_bijective.1 (hz.trans bits_zero.symm))

private theorem disjoint_of_points (U W : Submodule (ZMod 2) Coordinates)
    (h : Disjoint (pointsOf U) (pointsOf W)) : Disjoint U W := by
  apply Submodule.disjoint_def.mpr
  intro w hwU hwW
  obtain ⟨v,rfl⟩ := bits_bijective.2 w
  by_cases hz : v = 0
  · simpa only [hz,bits_zero]
  · exact (Finset.disjoint_left.mp h ((mem_points U v).mpr ⟨hz,hwU⟩)
      ((mem_points W v).mpr ⟨hz,hwW⟩)).elim

/-- Every eight actual three-dimensional totally isotropic Submodules,
with pairwise zero intersection, have exactly one actual ninth completion
of the full original even hyperplane. -/
theorem result (U : Fin 8 → Submodule (ZMod 2) Coordinates)
    (hdim : ∀ i, Module.finrank (ZMod 2) (U i) = 3)
    (horth : ∀ i, ∀ u ∈ U i, ∀ v ∈ U i, dotProduct u v = 0)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    ∃! M : Submodule (ZMod 2) Coordinates,
      Module.finrank (ZMod 2) M = 3 ∧
      (∀ u ∈ M, ∀ v ∈ M, dotProduct u v = 0) ∧
      (∀ i, Disjoint M (U i)) ∧
      pointsOf M ∪ Finset.univ.biUnion (fun i => pointsOf (U i)) = evenPoints := by
  classical
  let L : Fin 8 → Finset Vector := fun i => pointsOf (U i)
  obtain ⟨R,hR,hunique⟩ := SevenBitSpreadCompletion.result L
    (fun i => actual_data (U i) (hdim i) (horth i))
    (fun i j hij => points_disjoint _ _ (hdisjoint i j hij))
  obtain ⟨M,hdM,hoM,hcar⟩ := hR.2.2.2
  have hpM : pointsOf M = R := by
    ext v
    rw [mem_points]
    constructor
    · rintro ⟨hv,hvM⟩
      change bits v ∈ (M : Set Coordinates) at hvM
      rw [hcar] at hvM
      obtain ⟨x,hx,hxv⟩ := hvM
      have hxv' : x = v := bits_bijective.1 hxv
      subst x
      exact (Finset.mem_insert.mp hx).resolve_left hv
    · intro hv
      have hn : v ≠ 0 := (Finset.mem_filter.mp (hR.1.1 hv)).2.1
      exact ⟨hn,by
        change bits v ∈ (M : Set Coordinates)
        rw [hcar]
        exact ⟨v,Finset.mem_insert_of_mem hv,rfl⟩⟩
  refine ⟨M,⟨hdM,hoM,?_,?_⟩,?_⟩
  · intro i
    apply disjoint_of_points
    simpa only [hpM] using hR.2.1 i
  · simpa only [hpM] using hR.2.2.1
  · intro M' hM'
    have hp : pointsOf M' = R := hunique _ ⟨actual_data M' hM'.1 hM'.2.1,
      (fun i => points_disjoint _ _ (hM'.2.2.1 i)),hM'.2.2.2,
      ⟨M',hM'.1,hM'.2.1,carrier M'⟩⟩
    exact points_injective (hp.trans hpM.symm)

#print axioms result
end D5.S3.Combinatorics.Orthogonality.SevenDimensional.ActualSpreadCompletion
