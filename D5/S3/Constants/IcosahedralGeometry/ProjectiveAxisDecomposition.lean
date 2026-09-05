/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit F5 icosahedral action has projective axis orbits of sizes 6, 10, and 15. -/

/- Library-search audit trail (2026-08-28):
   * No D5 declaration covers the concrete 31-point action or its three orbits.
   * Pinned Mathlib supplies the generic projectivization and orbit-stabilizer APIs,
     but no declaration contains the source matrices or this finite computation.
   * Loogle and LeanSearch returned only those generic APIs; no exact third-party
     theorem was found. The detailed receipt is `/tmp/SEARCH-ob3.md`. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

/-- Finite icosahedral axis decomposition of the actual projective plane over
`F₅`: the concrete quadratic classes are the three orbits of sizes 6, 10,
and 15, with stabilizer orders 10, 6, and 4. -/
theorem finite_icosahedral_axis_decomposition :
    Disjoint fivefoldAxes threefoldAxes ∧
      Disjoint fivefoldAxes twofoldAxes ∧
      Disjoint threefoldAxes twofoldAxes ∧
      fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes =
        (Finset.univ : Finset (Projectivization F5 Vector)) ∧
      fivefoldAxes.card = 6 ∧
      threefoldAxes.card = 10 ∧
      twofoldAxes.card = 15 ∧
      (∀ p ∈ fivefoldAxes, axisOrbit p = fivefoldAxes) ∧
      (∀ p ∈ threefoldAxes, axisOrbit p = threefoldAxes) ∧
      (∀ p ∈ twofoldAxes, axisOrbit p = twofoldAxes) ∧
      (∀ p ∈ fivefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10) ∧
      (∀ p ∈ threefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 6) ∧
      (∀ p ∈ twofoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 4) ∧
      (∀ p : FivefoldAxis,
        Fintype.card (fiveCycleSubgroup p) = 5 ∧
          IsCyclic (fiveCycleSubgroup p) ∧
          MulAction.stabilizer IcosahedralGroup p.1 =
            Subgroup.normalizer (fiveCycleSubgroup p : Set IcosahedralGroup)) := by
  classical
  rcases chartFiniteAxisCertificate with
    ⟨h53Inter, h52Inter, h32Inter, hunion, hcard5, hcard3, hcard2,
      horbit5, horbit3, horbit2, hstab5, hstab3, hstab2⟩
  have h53Chart : Disjoint chartFivefoldAxes chartThreefoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h53Inter
  have h52Chart : Disjoint chartFivefoldAxes chartTwofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h52Inter
  have h32Chart : Disjoint chartThreefoldAxes chartTwofoldAxes :=
    Finset.disjoint_iff_inter_eq_empty.mpr h32Inter
  have h53 : Disjoint fivefoldAxes threefoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp5 hp3
    exact Finset.disjoint_left.mp h53Chart
      ((mem_mappedAxes p chartFivefoldAxes).mp hp5)
      ((mem_mappedAxes p chartThreefoldAxes).mp hp3)
  have h52 : Disjoint fivefoldAxes twofoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp5 hp2
    exact Finset.disjoint_left.mp h52Chart
      ((mem_mappedAxes p chartFivefoldAxes).mp hp5)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp2)
  have h32 : Disjoint threefoldAxes twofoldAxes := by
    rw [Finset.disjoint_left]
    intro p hp3 hp2
    exact Finset.disjoint_left.mp h32Chart
      ((mem_mappedAxes p chartThreefoldAxes).mp hp3)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp2)
  have hactualUnion : fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes = Finset.univ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rw [fivefoldAxes, threefoldAxes, twofoldAxes,
      mem_mappedAxes, mem_mappedAxes, mem_mappedAxes]
    have hp : projectiveChart p ∈
        chartFivefoldAxes ∪ chartThreefoldAxes ∪ chartTwofoldAxes := by
      rw [hunion]
      exact Finset.mem_univ _
    simpa only [Finset.mem_union] using hp
  refine ⟨h53, h52, h32, hactualUnion, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fivefoldAxes] using hcard5
  · simpa [threefoldAxes] using hcard3
  · simpa [twofoldAxes] using hcard2
  · intro p hp
    rw [axisOrbit_eq_map, fivefoldAxes, horbit5 (projectiveChart p)
      ((mem_mappedAxes p chartFivefoldAxes).mp hp)]
  · intro p hp
    rw [axisOrbit_eq_map, threefoldAxes, horbit3 (projectiveChart p)
      ((mem_mappedAxes p chartThreefoldAxes).mp hp)]
  · intro p hp
    rw [axisOrbit_eq_map, twofoldAxes, horbit2 (projectiveChart p)
      ((mem_mappedAxes p chartTwofoldAxes).mp hp)]
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 10 := hstab5 (projectiveChart p)
        ((mem_mappedAxes p chartFivefoldAxes).mp hp)
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 6 := hstab3 (projectiveChart p)
        ((mem_mappedAxes p chartThreefoldAxes).mp hp)
  · intro p hp
    calc
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
          Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
        stabilizer_card_eq_chart p
      _ = 4 := hstab2 (projectiveChart p)
        ((mem_mappedAxes p chartTwofoldAxes).mp hp)
  · intro p
    obtain ⟨hcycleCard, hnormalizerMem⟩ :=
      chartFivefoldNormalizerCertificate (toChartFivefoldAxis p)
    have hNatCard : Nat.card (fiveCycleSubgroup p) = 5 := by
      simpa [Nat.card_eq_fintype_card, fiveCycleSubgroup] using hcycleCard
    refine ⟨?_, isCyclic_of_prime_card hNatCard, ?_⟩
    · calc
        Fintype.card (fiveCycleSubgroup p) = Nat.card (fiveCycleSubgroup p) :=
          Nat.card_eq_fintype_card.symm
        _ = 5 := hNatCard
    ext g
    rw [stabilizer_eq_chart]
    exact hnormalizerMem g

#print axioms icosahedralGroup_card
#print axioms finite_icosahedral_axis_decomposition

section FidelityProbes

/-- Quotient discrimination probe: the first two coordinate lines remain
distinct in Mathlib's projectivization. -/
theorem projective_coordinate_axes_ne :
    Projectivization.mk F5 (![1, 0, 0] : Vector) (by decide) ≠
      Projectivization.mk F5 (![0, 1, 0] : Vector) (by decide) := by
  intro h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  simpa [Pi.smul_apply] using h0

/-- Reverse probe: the public theorem forces every isotropic axis to lie in the
claimed partition and to have stabilizer order ten. -/
example (p : ProjectiveAxis) (hp : p ∈ fivefoldAxes) :
    p ∈ fivefoldAxes ∪ threefoldAxes ∪ twofoldAxes ∧
      Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10 := by
  rcases finite_icosahedral_axis_decomposition with
    ⟨_, _, _, _, _, _, _, _, _, _, hstab5, _, _, _⟩
  exact ⟨by simp [hp], hstab5 p hp⟩

/-- Trivialization probe: a one-element action cannot have the source's three
different nonzero stabilizer orders. -/
example {X : Type*} [Fintype X] [DecidableEq X] [MulAction Unit X] :
    ¬ ((∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 10) ∧
       (∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 6) ∧
       (∃ x : X, Fintype.card (MulAction.stabilizer Unit x) = 4)) := by
  rintro ⟨⟨x, hx⟩, _⟩
  let e : MulAction.stabilizer Unit x ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨(), by exact one_smul Unit x⟩
      left_inv := by
        intro g
        apply Subtype.ext
        cases g.1
        rfl
      right_inv := by intro u; cases u; rfl }
  have hcard : Fintype.card (MulAction.stabilizer Unit x) = 1 := by
    calc
      Fintype.card (MulAction.stabilizer Unit x) = Fintype.card Unit :=
        Fintype.card_congr e
      _ = 1 := Fintype.card_unit
  omega

end FidelityProbes

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
