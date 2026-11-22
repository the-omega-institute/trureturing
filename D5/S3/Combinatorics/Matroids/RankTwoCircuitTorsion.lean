/- GID: D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankTwoCircuitTorsion
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Class potentials for the rank-two joint circuit lifting obstruction. -/

module

public import D5.S3.Combinatorics.Matroids.RationalJointCircuitImage

/-! # Joint circuit lifting obstructions in rank two -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.RankTwoCircuitTorsion

open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open CircuitPairInnerProduct (rationalTopCycles rationalAggregate)
open CircuitCycleDecomposition (restrictionSign)
open OrderedCycleFactorization (shuffleSign)
open RationalJointCircuitImage (RationalResidue rationalResidue rationalResidue_eq_zero
  rationalIntegralReadoutCycles integralCycleInRational rationalJointRestriction_equiv)
open CircuitPairInnerProduct (castChain mem_rationalTopCycles_iff)
open CircuitCycleDecomposition (topCycles)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

variable {V ι A : Type*} [AddCommGroup A]

/-- The class potentials are uniquely determined once their value at the pivot is fixed. -/
private theorem exists_normalized_class_potentials
    (part : V → ι) (hsurj : Function.Surjective part) (pivot : ι)
    (edge : V → V → A)
    (hzero : ∀ u v, part u = part v → edge u v = 0)
    (hrow : ∀ u v w, part u = part v → edge u w = edge v w)
    (hskew : ∀ u v, edge v u = -edge u v)
    (htriangle : ∀ u v w, part u ≠ part v → part v ≠ part w → part u ≠ part w →
      edge u v + edge v w = edge u w) :
    ∃! potential : ι → A,
      potential pivot = 0 ∧
        ∀ u v, edge u v = potential (part u) - potential (part v) := by
  classical
  choose representative hpart using hsurj
  let anchor := representative pivot
  let potential : ι → A := fun i => edge (representative i) anchor
  have hanchor : part anchor = pivot := hpart pivot
  have htriangleAll (u v w : V) : edge u v + edge v w = edge u w := by
    by_cases huv : part u = part v
    · rw [hzero u v huv, hrow u v w huv, zero_add]
    by_cases hvw : part v = part w
    · have hcol : edge u v = edge u w := by
        rw [hskew v u, hskew w u, hrow v w u hvw]
      rw [hzero v w hvw, add_zero, hcol]
    by_cases huw : part u = part w
    · rw [hzero u w huw, hskew w v, hrow u w v huw, add_neg_cancel]
    · exact htriangle u v w huv hvw huw
  refine ⟨potential, ⟨hzero anchor anchor rfl, ?_⟩, ?_⟩
  · intro u v
    have hu : edge u anchor = potential (part u) :=
      hrow u (representative (part u)) anchor (hpart (part u)).symm
    have hv : edge v anchor = potential (part v) :=
      hrow v (representative (part v)) anchor (hpart (part v)).symm
    exact eq_sub_of_add_eq (by simpa only [hu, hv] using htriangleAll u v anchor)
  · rintro other ⟨hother, hedge⟩
    funext i
    simpa only [potential, hpart i, hanchor, hother, sub_zero] using
      (hedge (representative i) anchor).symm

/-- Vanishing vertex boundary is equivalent to two conditions on the normalized
potentials: every potential is killed by the ground size, and their weighted sum vanishes. -/
private theorem normalized_boundary_iff [Fintype V] [Fintype ι] [DecidableEq ι]
    (part : V → ι) (hsurj : Function.Surjective part) {pivot : ι}
    (potential : ι → A) (hpivot : potential pivot = 0) :
    (∀ u : V, ∑ v : V, (potential (part u) - potential (part v)) = 0) ↔
      (∀ i, Fintype.card V • potential i = 0) ∧
        ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i = 0 := by
  classical
  have hmass : (∑ v : V, potential (part v)) =
      ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i := by
    rw [← sum_fiberwise univ part (fun v : V => potential (part v))]
    apply sum_congr rfl
    intro i _
    calc
      (∑ v ∈ univ.filter (fun v => part v = i), potential (part v)) =
          ∑ _v ∈ univ.filter (fun v => part v = i), potential i := by
        apply sum_congr rfl
        intro v hv
        rw [(mem_filter.mp hv).2]
      _ = _ := sum_const _
  simp only [sum_sub_distrib, sum_const, card_univ, hmass, sub_eq_zero]
  constructor
  · intro h
    obtain ⟨anchor, hanchor⟩ := hsurj pivot
    have hweighted : ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i = 0 := by
      simpa only [hanchor, hpivot, nsmul_zero] using (h anchor).symm
    refine ⟨fun i => ?_, hweighted⟩
    obtain ⟨u, rfl⟩ := hsurj i
    exact (h u).trans hweighted
  · rintro ⟨hannihilate, hweighted⟩ u
    exact (hannihilate (part u)).trans hweighted.symm

private def oriented_edge [DecidableEq V] (start finish : V) (value : A) (u v : V) : A :=
  (if u = start then if v = finish then value else 0 else 0) -
    (if u = finish then if v = start then value else 0 else 0)

private lemma oriented_edge_reverse [DecidableEq V] (start finish : V) (value : A)
    (u v : V) : oriented_edge start finish value v u = -oriented_edge start finish value u v := by
  simp only [oriented_edge, neg_sub]
  congr 1 <;> split_ifs <;> simp_all

private lemma oriented_edge_boundary [Fintype V] [DecidableEq V]
    (start finish : V) (value : A) (u : V) :
    ∑ v : V, oriented_edge start finish value u v =
      (if u = start then value else 0) - (if u = finish then value else 0) := by
  by_cases hs : u = start <;> by_cases hf : u = finish <;>
    simp [oriented_edge, hs, hf, sum_sub_distrib]

private lemma oriented_edge_same_class [DecidableEq V]
    (part : V → ι) {start finish : V} (h : part start ≠ part finish)
    (value : A) (u v : V) (huv : part u = part v) :
    oriented_edge start finish value u v = 0 := by
  unfold oriented_edge
  split_ifs <;> simp_all

/-- Route a zero-sum boundary to an anchor through edges joining distinct classes. -/
private theorem exists_multipartite_boundary_lift [Fintype V] (part : V → ι)
    (anchor bridge : V) (hbridge : part bridge ≠ part anchor)
    (boundary : V → A) (hboundary : ∑ u, boundary u = 0) :
    ∃ flow : V → V → A,
      (∀ u v, flow v u = -flow u v) ∧
      (∀ u v, part u = part v → flow u v = 0) ∧
      (∀ u, ∑ v, flow u v = boundary u) := by
  classical
  let route := fun source u v =>
    if part source = part anchor then
      oriented_edge source bridge (boundary source) u v +
        oriented_edge bridge anchor (boundary source) u v
    else oriented_edge source anchor (boundary source) u v
  let flow := fun u v => ∑ source : V, route source u v
  refine ⟨flow, ?_, ?_, ?_⟩
  · intro u v
    dsimp only [flow]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro source _
    by_cases hs : part source = part anchor <;>
      simp [route, hs, oriented_edge_reverse source bridge _ u v,
        oriented_edge_reverse bridge anchor _ u v,
        oriented_edge_reverse source anchor _ u v, add_comm]
  · intro u v huv
    dsimp only [flow]
    apply sum_eq_zero
    intro source _
    by_cases hs : part source = part anchor
    · simp only [route, hs, ite_true,
        oriented_edge_same_class part (hs.trans_ne hbridge.symm) _ u v huv,
        oriented_edge_same_class part hbridge _ u v huv, add_zero]
    · simpa only [route, hs, ite_false] using
        oriented_edge_same_class part hs (boundary source) u v huv
  · intro u
    have hroute (source : V) : ∑ v, route source u v =
        (if u = source then boundary source else 0) -
          (if u = anchor then boundary source else 0) := by
      by_cases hs : part source = part anchor
      · simp only [route, hs, ite_true, sum_add_distrib, oriented_edge_boundary]
        abel
      · simp only [route, hs, ite_false, oriented_edge_boundary]
    change ∑ v : V, ∑ source : V, route source u v = boundary u
    rw [sum_comm]
    simp [hroute, sum_sub_distrib, sum_ite_irrel, hboundary]

/-- Correct the integral boundary of rational edge representatives while preserving
every edge residue. -/
private theorem exists_rational_circulation_lift [Fintype V] (part : V → ι)
    (anchor bridge : V) (hbridge : part bridge ≠ part anchor)
    (edge : V → V → ℚ) (hskew : ∀ u v, edge v u = -edge u v)
    (hsame : ∀ u v, part u = part v → edge u v = 0)
    (hboundary : ∀ u, ∑ v, rationalResidue (edge u v) = 0) :
    ∃ lift : V → V → ℚ,
      (∀ u v, lift v u = -lift u v) ∧
      (∀ u v, part u = part v → lift u v = 0) ∧
      (∀ u, ∑ v, lift u v = 0) ∧
      (∀ u v, rationalResidue (lift u v) = rationalResidue (edge u v)) := by
  classical
  have htotal : ∑ u : V, ∑ v : V, edge u v = 0 := by
    have hneg : ∑ u : V, ∑ v : V, edge u v = -(∑ u : V, ∑ v : V, edge u v) := by
      calc
        ∑ u : V, ∑ v : V, edge u v = ∑ v : V, ∑ u : V, edge u v := sum_comm
        _ = ∑ v : V, ∑ u : V, -edge v u :=
          sum_congr rfl fun v _ => sum_congr rfl fun u _ => hskew v u
        _ = _ := by simp only [sum_neg_distrib]
    linarith
  have hint (u : V) : ∃ n : ℤ, (n : ℚ) = ∑ v, edge u v :=
    rationalResidue_eq_zero.mp (by rw [map_sum, hboundary])
  choose boundary hboundary' using hint
  have hzero : ∑ u, boundary u = 0 := by
    exact_mod_cast (show (∑ u : V, (boundary u : ℚ)) = 0 by simp only [hboundary', htotal])
  obtain ⟨correction, hreverse, hsupport, hsum⟩ :=
    exists_multipartite_boundary_lift part anchor bridge hbridge boundary hzero
  refine ⟨fun u v => edge u v - correction u v, ?_, ?_, ?_, ?_⟩
  · intro u v
    change edge v u - (correction v u : ℚ) = -(edge u v - (correction u v : ℚ))
    rw [hskew, hreverse, Int.cast_neg]
    abel
  · intro u v huv
    simp only [hsame u v huv, hsupport u v huv, Int.cast_zero, sub_zero]
  · intro u
    rw [sum_sub_distrib, ← Int.cast_sum, hsum, hboundary', sub_self]
  · intro u v
    rw [map_sub, (rationalResidue_eq_zero).mpr ⟨correction u v, rfl⟩, sub_zero]

/-- Normalized class potentials with the weighted boundary relations admit rational
circulation representatives. -/
private theorem exists_circulation_of_potentials [Fintype V] [Fintype ι] [DecidableEq ι]
    (part : V → ι) (hsurj : Function.Surjective part) {pivot : ι}
    (anchor bridge : V) (hbridge : part bridge ≠ part anchor)
    (potential : ι → RationalResidue) (hpivot : potential pivot = 0)
    (hannihilate : ∀ i, Fintype.card V • potential i = 0)
    (hweighted : ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i = 0) :
    ∃ lift : V → V → ℚ,
      (∀ u v, lift v u = -lift u v) ∧
      (∀ u v, part u = part v → lift u v = 0) ∧
      (∀ u, ∑ v, lift u v = 0) ∧
      (∀ u v, rationalResidue (lift u v) = potential (part u) - potential (part v)) := by
  classical
  have hsurjResidue : Function.Surjective rationalResidue := QuotientAddGroup.mk'_surjective _
  choose representative hrepresentative using fun i => hsurjResidue (potential i)
  let edge := fun u v => representative (part u) - representative (part v)
  have hskew (u v : V) : edge v u = -edge u v := by
    dsimp only [edge]
    abel
  have hsupport (u v : V) (huv : part u = part v) : edge u v = 0 := by
    simp only [edge, huv, sub_self]
  have hresidue (u v : V) :
      rationalResidue (edge u v) = potential (part u) - potential (part v) := by
    simp only [edge, map_sub, hrepresentative]
  have hboundary (u : V) : ∑ v, rationalResidue (edge u v) = 0 := by
    simp only [hresidue]
    exact (normalized_boundary_iff part hsurj potential hpivot).mpr
      ⟨hannihilate, hweighted⟩ u
  obtain ⟨lift, hlift, hsame, hzero, hmod⟩ :=
    exists_rational_circulation_lift part anchor bridge hbridge edge hskew hsupport hboundary
  exact ⟨lift, hlift, hsame, hzero, fun u v => (hmod u v).trans (hresidue u v)⟩

/-- The signed edge coefficient in the boundary at its first vertex. -/
def flowOfChain [LinearOrder V] (chain : Finset V → ℚ) (u v : V) : ℚ :=
  if u = v then 0 else (insertionSign {u} v : ℚ) * chain {u, v}

private lemma flowOfChain_of_lt [LinearOrder V] (chain : Finset V → ℚ)
    {u v : V} (huv : u < v) : flowOfChain chain u v = -chain {u, v} := by
  simp [flowOfChain, huv.ne, insertionSign, filter_singleton, huv]

private lemma flowOfChain_reverse [LinearOrder V] (chain : Finset V → ℚ) (u v : V) :
    flowOfChain chain v u = -flowOfChain chain u v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [flowOfChain, huv.ne, huv.ne', insertionSign, filter_singleton, huv,
      huv.not_gt, pair_comm]
  · simp [flowOfChain]
  · simp [flowOfChain, hvu.ne, hvu.ne', insertionSign, filter_singleton, hvu,
      hvu.not_gt, pair_comm]

private lemma flowOfChain_sum [Fintype V] [LinearOrder V] (chain : Finset V → ℚ) (u : V) :
    ∑ v : V, flowOfChain chain u v =
      ∑ v ∈ univ \ {u}, (insertionSign {u} v : ℚ) * chain (insert v {u}) := by
  rw [← sum_sdiff (singleton_subset_iff.mpr (mem_univ u))]
  simp only [sum_singleton, flowOfChain, ite_true, add_zero]
  apply sum_congr rfl
  intro v hv
  have hne : u ≠ v := by simpa [eq_comm] using (mem_sdiff.mp hv).2
  rw [ite_eq_right hne, pair_comm]

private def chainOfFlow [LinearOrder V] (flow : V → V → ℚ) (face : Finset V) : ℚ :=
  if h : face.card = 2 then
    -flow (face.min' (card_pos.mp (by omega))) (face.max' (card_pos.mp (by omega)))
  else 0

private lemma chainOfFlow_pair [LinearOrder V] (flow : V → V → ℚ) {u v : V} (huv : u < v) :
    chainOfFlow flow {u, v} = -flow u v := by
  rw [chainOfFlow, dite_eq_left (card_eq_two.mpr ⟨u, v, huv.ne, rfl⟩)]
  simp [min_eq_left huv.le, max_eq_right huv.le]

private lemma flowOfChain_chainOfFlow [LinearOrder V] (flow : V → V → ℚ)
    (hskew : ∀ u v, flow v u = -flow u v) (hdiag : ∀ u, flow u u = 0) (u v : V) :
    flowOfChain (chainOfFlow flow) u v = flow u v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · rw [flowOfChain_of_lt _ huv, chainOfFlow_pair _ huv, neg_neg]
  · simp [flowOfChain, hdiag]
  · rw [flowOfChain_reverse _ v u, flowOfChain_of_lt _ hvu, chainOfFlow_pair _ hvu,
      neg_neg, hskew v u]

private lemma chainOfFlow_mem_rationalTopCycles [Fintype V] [LinearOrder V] {M : Matroid V}
    (part : V → ι) (hbase : ∀ F : Finset V,
      M.IsBase (F : Set V) ↔ ∃ u v : V, part u ≠ part v ∧ F = {u, v})
    (flow : V → V → ℚ) (hskew : ∀ u v, flow v u = -flow u v)
    (hsame : ∀ u v, part u = part v → flow u v = 0)
    (hboundary : ∀ u, ∑ v, flow u v = 0) :
    chainOfFlow flow ∈ rationalTopCycles M := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · by_cases hc : F.card = 2
    · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hc
      have hs : part u = part v := not_ne_iff.mp fun h => hF ((hbase _).mpr ⟨u, v, h, rfl⟩)
      rcases huv.lt_or_gt with h | h
      · rw [chainOfFlow_pair flow h, hsame u v hs, neg_zero]
      · rw [pair_comm, chainOfFlow_pair flow h, hsame v u hs.symm, neg_zero]
    · simp [chainOfFlow, hc]
  · by_cases hc : R.card = 1
    · obtain ⟨u, rfl⟩ := card_eq_one.mp hc
      rw [← flowOfChain_sum]
      simpa only [flowOfChain_chainOfFlow flow hskew (fun u => hsame u u rfl)] using hboundary u
    · apply sum_eq_zero
      intro v hv
      have hnot : v ∉ R := (mem_sdiff.mp hv).2
      have hi : (insert v R).card ≠ 2 := by
        rw [card_insert_of_notMem hnot]
        omega
      simp [chainOfFlow, hi]

/-- Bases are the pairs whose vertices lie in different classes. -/
def HasClassBases [DecidableEq V] (M : Matroid V) (part : V → ι) : Prop :=
  ∀ F : Finset V, M.IsBase (F : Set V) ↔ ∃ u v : V, part u ≠ part v ∧ F = {u, v}

private lemma pair_ground [DecidableEq V] [Nontrivial ι] {M : Matroid V}
    {part : V → ι} (hbases : HasClassBases M part) (hsurj : Function.Surjective part) (u : V) :
    u ∈ M.E := by
  obtain ⟨j, hj⟩ := exists_ne (part u)
  obtain ⟨v, hv⟩ := hsurj j
  exact ((hbases {u, v}).mpr ⟨u, v, (hv ▸ hj).symm, rfl⟩).subset_ground (by simp)

private lemma indep_iff_class_injective [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (F : Finset V) :
    M.Indep (F : Set V) ↔ F.card ≤ 2 ∧ Set.InjOn part (F : Set V) := by
  classical
  constructor
  · intro h
    obtain ⟨B, hB, hFB⟩ := h.exists_isBase_superset
    have hB' : M.IsBase ((B.toFinite.toFinset : Finset V) : Set V) := by simpa using hB
    obtain ⟨u, v, huv, heq⟩ := (hbases _).mp hB'
    have hsub : F ⊆ {u, v} := by
      rw [← heq, ← coe_subset, Set.Finite.coe_toFinset]
      exact hFB
    refine ⟨(card_le_card hsub).trans card_le_two, ?_⟩
    intro a ha b hb hab
    have ha' : a = u ∨ a = v := by simpa using hsub ha
    have hb' : b = u ∨ b = v := by simpa using hsub hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> tauto
  · rintro ⟨hc, hinj⟩
    rcases (show F.card = 0 ∨ F.card = 1 ∨ F.card = 2 by omega) with hc | hc | hc
    · simp [card_eq_zero.mp hc]
    · obtain ⟨u, rfl⟩ := card_eq_one.mp hc
      obtain ⟨j, hj⟩ := exists_ne (part u)
      obtain ⟨v, hv⟩ := hsurj j
      have hB : M.IsBase (↑({u, v} : Finset V) : Set V) :=
        (hbases _).mpr ⟨u, v, (hv ▸ hj).symm, rfl⟩
      apply hB.indep.subset
      simp
    · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hc
      exact ((hbases _).mpr ⟨u, v, fun h => huv (hinj (by simp) (by simp) h), rfl⟩).indep

private lemma exists_pair_or_triple_circuit [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (C : Finset V) (hC : M.IsCircuit (C : Set V)) :
    (∃ u v, u ≠ v ∧ part u = part v ∧ C = {u, v}) ∨
    (∃ u v w, part u ≠ part v ∧ part v ≠ part w ∧ part u ≠ part w ∧ C = {u, v, w}) := by
  obtain ⟨u, hu⟩ := hC.nonempty
  change u ∈ C at hu
  have hproper {S : Finset V} (hS : S ⊂ C) : M.Indep (S : Set V) :=
    (Matroid.isCircuit_iff_forall_ssubset.mp hC).2 (coe_ssubset.mpr hS)
  have hcard : C.card ≤ 3 := by
    have hsm := (indep_iff_class_injective hbases hsurj _).mp
      (hproper (erase_ssubset hu))
    have hc := card_erase_add_one hu
    omega
  have hmin : 2 ≤ C.card := by
    by_contra! hc
    apply hC.not_indep
    refine (indep_iff_class_injective hbases hsurj _).mpr ⟨by omega, ?_⟩
    intro a ha b hb _
    exact card_le_one.mp (by omega) a ha b hb
  rcases (show C.card = 2 ∨ C.card = 3 by omega) with hc | hc
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
    refine Or.inl ⟨a, b, hab, ?_, rfl⟩
    by_contra h
    exact hC.not_indep ((hbases _).mpr ⟨a, b, h, rfl⟩).indep
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hc
    have hpair {x y : V} (hxy : x ≠ y) (hsub : {x, y} ⊆ ({a, b, c} : Finset V)) :
        part x ≠ part y := by
      have hss : ({x, y} : Finset V) ⊂ {a, b, c} := by
        refine ssubset_of_subset_of_ne hsub fun heq => ?_
        have hp := card_eq_two.mpr ⟨x, y, hxy, rfl⟩
        rw [heq, hc] at hp
        contradiction
      have hinj := ((indep_iff_class_injective hbases hsurj _).mp (hproper hss)).2
      exact fun h => hxy (hinj (by simp) (by simp) h)
    exact Or.inr ⟨a, b, c, hpair hab (by simp), hpair hbc (by simp),
      hpair hac (by simp), rfl⟩

private lemma same_class_isCircuit [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v : V} (huv : u ≠ v) (hsame : part u = part v) :
    M.IsCircuit (↑({u, v} : Finset V) : Set V) := by
  have hsubset : (↑({u, v} : Finset V) : Set V) ⊆ M.E := by
    intro a ha
    have ha' : a = u ∨ a = v := by simpa using ha
    rcases ha' with rfl | rfl <;> apply pair_ground hbases hsurj
  rw [Matroid.isCircuit_iff_forall_ssubset]
  refine ⟨(Matroid.not_indep_iff hsubset).mp ?_, ?_⟩
  · intro h
    exact huv (((indep_iff_class_injective hbases hsurj _).mp h).2 (by simp) (by simp) hsame)
  · intro B hB
    have hB' : B.toFinite.toFinset ⊂ ({u, v} : Finset V) :=
      coe_ssubset.mp (by simpa using hB)
    have hc : B.toFinite.toFinset.card ≤ 1 :=
      Nat.le_of_lt_succ ((card_lt_card hB').trans_le card_le_two)
    have hI : M.Indep (↑(B.toFinite.toFinset : Finset V) : Set V) :=
      (indep_iff_class_injective hbases hsurj _).mpr
        ⟨hc.trans (by decide), fun _ ha _ hb _ => card_le_one.mp hc _ ha _ hb⟩
    simpa using hI

private lemma distinct_classes_isCircuit [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v w : V}
    (huv : part u ≠ part v) (hvw : part v ≠ part w) (huw : part u ≠ part w) :
    M.IsCircuit (↑({u, v, w} : Finset V) : Set V) := by
  have hsubset : (↑({u, v, w} : Finset V) : Set V) ⊆ M.E := by
    intro a ha
    have ha' : a = u ∨ a = v ∨ a = w := by simpa using ha
    rcases ha' with rfl | rfl | rfl <;> apply pair_ground hbases hsurj
  have hc : ({u, v, w} : Finset V).card = 3 := card_eq_three.mpr
    ⟨u, v, w, huv ∘ congrArg part, huw ∘ congrArg part, hvw ∘ congrArg part, rfl⟩
  have hinj : Set.InjOn part (↑({u, v, w} : Finset V) : Set V) := by
    intro a ha b hb heq
    have ha' : a = u ∨ a = v ∨ a = w := by simpa using ha
    have hb' : b = u ∨ b = v ∨ b = w := by simpa using hb
    rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> tauto
  rw [Matroid.isCircuit_iff_forall_ssubset]
  refine ⟨(Matroid.not_indep_iff hsubset).mp ?_, ?_⟩
  · intro h
    have hd := ((indep_iff_class_injective hbases hsurj _).mp h).1
    omega
  · intro B hB
    have hB' : B.toFinite.toFinset ⊂ ({u, v, w} : Finset V) :=
      coe_ssubset.mp (by simpa using hB)
    have hcB := card_lt_card hB'
    have hI : M.Indep (↑(B.toFinite.toFinset : Finset V) : Set V) :=
      (indep_iff_class_injective hbases hsurj _).mpr
        ⟨by omega, hinj.mono (by simpa using hB.subset)⟩
    simpa using hI

private lemma contract_same_class_bases [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v : V} (huv : u ≠ v) (hsame : part u = part v)
    (F : Finset V) :
    (M ／ (↑({u, v} : Finset V) : Set V)).IsBase (F : Set V) ↔
      ∃ w, part w ≠ part u ∧ F = {w} := by
  classical
  let P := M ／ (↑({u, v} : Finset V) : Set V)
  have hC := same_class_isCircuit hbases hsurj huv hsame
  have hI : M.IsBasis ({u} : Set V) (↑({u, v} : Finset V) : Set V) := by
    simpa [huv, huv.symm] using hC.sdiff_singleton_isBasis (e := v) (by simp)
  have hsize (S : Finset V) (hS : P.Indep (S : Set V)) : S.card ≤ 1 := by
    obtain ⟨hunion, hdisj⟩ := hI.contract_indep_iff.mp hS
    have hnot : u ∉ S := fun hu => Set.disjoint_left.mp hdisj (by simp) hu
    have hcoef : (↑(insert u S) : Set V) = (S : Set V) ∪ {u} := by
      rw [coe_insert, Set.union_comm, Set.singleton_union]
    have hbound := ((indep_iff_class_injective hbases hsurj (insert u S)).mp
      (hcoef.symm ▸ hunion)).1
    rw [card_insert_of_notMem hnot] at hbound
    omega
  have hsingle (w : V) : P.Indep ({w} : Set V) ↔ part w ≠ part u := by
    rw [show P.Indep ({w} : Set V) ↔ _ from hI.contract_indep_iff]
    constructor
    · rintro ⟨h, hd⟩ heq
      have hne : w ≠ u := by
        intro hwu
        have hwC : w ∈ (↑({u, v} : Finset V) : Set V) := by simp [hwu]
        exact Set.disjoint_left.mp hd hwC (Set.mem_singleton w)
      have h' : M.Indep (↑({w, u} : Finset V) : Set V) := by
        simpa only [coe_insert, coe_singleton, Set.singleton_union] using h
      exact hne (((indep_iff_class_injective hbases hsurj _).mp h').2 (by simp) (by simp) heq)
    · intro h
      refine ⟨?_, Set.disjoint_right.mpr ?_⟩
      · simpa only [coe_insert, coe_singleton, Set.singleton_union] using
          ((hbases {w, u}).mpr ⟨w, u, h, rfl⟩).indep
      · intro a ha hc
        have ha' : a = w := by simpa using ha
        subst a
        have hc' : w = u ∨ w = v := by simpa using hc
        rcases hc' with rfl | rfl
        · exact h rfl
        · exact h hsame.symm
  change P.IsBase (F : Set V) ↔ _
  constructor
  · intro hF
    have hc := hsize F hF.indep
    have hne : F.card ≠ 0 := by
      intro hz
      obtain ⟨j, hj⟩ := exists_ne (part u)
      obtain ⟨w, hw⟩ := hsurj j
      have hs := (hsingle w).mpr (hw ▸ hj)
      have he := hF.eq_of_subset_indep hs (by simp [card_eq_zero.mp hz])
      have hw' : w ∈ (F : Set V) := by rw [he]; simp
      simp [card_eq_zero.mp hz] at hw'
    obtain ⟨w, rfl⟩ := card_eq_one.mp (by omega : F.card = 1)
    exact ⟨w, (hsingle w).mp (by simpa using hF.indep), rfl⟩
  · rintro ⟨w, hw, rfl⟩
    apply (show P.Indep (↑({w} : Finset V) : Set V) by simpa using (hsingle w).mpr hw)
      |>.isBase_of_maximal
    intro J hJ hsub
    have hJ' : P.Indep (↑(J.toFinite.toFinset : Finset V) : Set V) := by simpa using hJ
    have hcard := hsize J.toFinite.toFinset hJ'
    have hwJ : w ∈ J.toFinite.toFinset := by simpa using hsub (by simp)
    have heq : J.toFinite.toFinset = {w} := by
      apply Subset.antisymm
      · intro a ha
        simpa using card_le_one.mp hcard a ha w hwJ
      · exact singleton_subset_iff.mpr hwJ
    have he := congrArg (fun S : Finset V => (S : Set V)) heq
    simpa using he.symm

private lemma contract_distinct_classes_bases [Finite V] [DecidableEq V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v w : V}
    (huv : part u ≠ part v) (hvw : part v ≠ part w) (huw : part u ≠ part w)
    (F : Finset V) :
    (M ／ (↑({u, v, w} : Finset V) : Set V)).IsBase (F : Set V) ↔ F = ∅ := by
  classical
  let P := M ／ (↑({u, v, w} : Finset V) : Set V)
  have hC := distinct_classes_isCircuit hbases hsurj huv hvw huw
  have hB := (hbases {u, v}).mpr ⟨u, v, huv, rfl⟩
  have hsubset : (↑({u, v} : Finset V) : Set V) ⊆ (↑({u, v, w} : Finset V) : Set V) :=
    coe_subset.mpr (by simp)
  have hI := hB.isBasis_of_subset hC.subset_ground hsubset
  have hempty (S : Set V) (hS : P.Indep S) : S = ∅ := by
    obtain ⟨hunion, hdisj⟩ := hI.contract_indep_iff.mp hS
    have he := hB.eq_of_subset_indep hunion Set.subset_union_right
    have hsub : S ⊆ (↑({u, v} : Finset V) : Set V) := by
      rw [he]
      exact Set.subset_union_left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact Set.disjoint_left.mp hdisj (hsubset (hsub ha)) ha
  change P.IsBase (F : Set V) ↔ _
  refine ⟨fun h => coe_eq_empty.mp (hempty _ h.indep), ?_⟩
  rintro rfl
  simpa using (P.empty_indep).isBase_of_maximal (fun _ hJ _ => (hempty _ hJ).symm)

private lemma rationalAggregate_pair [LinearOrder V] {M : Matroid V} {u v w : V}
    (huv : u < v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hbase : (M ／ (↑({u, v} : Finset V) : Set V)).IsBase (↑({w} : Finset V) : Set V))
    (chain : Finset V → ℚ) :
    rationalAggregate M {u, v} chain {w} = flowOfChain chain w v - flowOfChain chain w u := by
  classical
  have he₁ : ({u, v} : Finset V).erase u = {v} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  have he₂ : ({u, v} : Finset V).erase v = {u} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hbase,
    sum_insert (notMem_singleton.mpr huv.ne), sum_singleton,
    he₁, he₂, singleton_union, restrictionSign]
  have hshuffle (x : V) : shuffleSign {x} {w} = insertionSign {w} x := by
    simp [shuffleSign, insertionSign]
  simp [hshuffle, flowOfChain, hwu, hwv, insertionSign, filter_singleton, huv, huv.not_gt,
    sub_eq_add_neg]

private lemma rationalAggregate_triple [LinearOrder V] {M : Matroid V} {u v w : V}
    (huv : u < v) (hvw : v < w)
    (hbase : (M ／ (↑({u, v, w} : Finset V) : Set V)).IsBase (↑(∅ : Finset V) : Set V))
    (chain : Finset V → ℚ) :
    rationalAggregate M {u, v, w} chain ∅ =
      -(flowOfChain chain u v + flowOfChain chain v w - flowOfChain chain u w) := by
  classical
  have huw := huv.trans hvw
  have hu : u ∉ ({v, w} : Finset V) := by simp [huv.ne, huw.ne]
  have hv : v ∉ ({w} : Finset V) := notMem_singleton.mpr hvw.ne
  have he₁ : ({u, v, w} : Finset V).erase u = {v, w} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  have he₂ : ({u, v, w} : Finset V).erase v = {u, w} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  have he₃ : ({u, v, w} : Finset V).erase w = {u, v} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    grind
  rw [flowOfChain_of_lt _ huv, flowOfChain_of_lt _ hvw, flowOfChain_of_lt _ huw]
  simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hbase,
    sum_insert hu, sum_insert hv, sum_singleton, he₁, he₂, he₃, restrictionSign, empty_union]
  simp [shuffleSign, insertionSign, filter_insert, filter_singleton,
    huv, hvw, huw, huv.not_gt, hvw.not_gt, huw.not_gt, huv.ne]
  ring

/-- Take the residue of the signed edge coefficient in the vertex boundary convention. -/
def edgeResidue [LinearOrder V] (chain : Finset V → ℚ) (u v : V) : RationalResidue :=
  rationalResidue (flowOfChain chain u v)

private lemma edgeResidue_reverse [LinearOrder V] (chain : Finset V → ℚ) (u v : V) :
    edgeResidue chain v u = -edgeResidue chain u v := by
  simp only [edgeResidue, flowOfChain_reverse chain u v, map_neg]

private lemma pair_readout_residue_iff [Finite V] [LinearOrder V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v w : V} (huv : u ≠ v)
    (hsame : part u = part v) (houtside : part w ≠ part u) (chain : Finset V → ℚ) :
    rationalResidue (rationalAggregate M {u, v} chain {w}) = 0 ↔
      edgeResidue chain u w = edgeResidue chain v w := by
  wlog hord : u < v generalizing u v
  · rw [pair_comm u v]
    exact (this huv.symm hsame.symm (hsame ▸ houtside)
      (lt_of_le_of_ne (le_of_not_gt hord) huv.symm)).trans eq_comm
  have hwv : part w ≠ part v := hsame ▸ houtside
  have hbase := (contract_same_class_bases hbases hsurj huv hsame {w}).mpr ⟨w, houtside, rfl⟩
  rw [rationalAggregate_pair hord (houtside ∘ congrArg part) (hwv ∘ congrArg part) hbase]
  change rationalResidue (flowOfChain chain w v - flowOfChain chain w u) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  change edgeResidue chain w v = edgeResidue chain w u ↔ _
  rw [edgeResidue_reverse chain v w, edgeResidue_reverse chain u w, neg_inj, eq_comm]

private def triangleSum (edge : V → V → A) (u v w : V) : A :=
  edge u v + edge v w + edge w u

private lemma triangleSum_rotate (edge : V → V → A) (u v w : V) :
    triangleSum edge v w u = triangleSum edge u v w := by
  unfold triangleSum
  abel

private lemma triangleSum_swap (edge : V → V → A)
    (hskew : ∀ u v, edge v u = -edge u v) (u v w : V) :
    triangleSum edge v u w = -triangleSum edge u v w := by
  unfold triangleSum
  rw [hskew u v, hskew w u, hskew v w]
  abel

private lemma triple_readout_residue_iff [Finite V] [LinearOrder V] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) {u v w : V}
    (huv : part u ≠ part v) (hvw : part v ≠ part w) (huw : part u ≠ part w)
    (chain : Finset V → ℚ) :
    rationalResidue (rationalAggregate M {u, v, w} chain ∅) = 0 ↔
      triangleSum (edgeResidue chain) u v w = 0 := by
  have hsorted (a b c : V) (hab : a < b) (hbc : b < c) (h₁ : part a ≠ part b)
      (h₂ : part b ≠ part c) (h₃ : part a ≠ part c) :
      rationalResidue (rationalAggregate M {a, b, c} chain ∅) = 0 ↔
        triangleSum (edgeResidue chain) a b c = 0 := by
    have hb := (contract_distinct_classes_bases hbases hsurj h₁ h₂ h₃ ∅).mpr rfl
    rw [rationalAggregate_triple hab hbc hb, map_neg, neg_eq_zero, map_sub, map_add]
    change edgeResidue chain a b + edgeResidue chain b c - edgeResidue chain a c = 0 ↔ _
    rw [triangleSum, edgeResidue_reverse chain a c, sub_eq_add_neg]
  have hset (a b c : V) : ({a, b, c} : Finset V) = {b, c, a} := by
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have hswap (a b c : V) :
      triangleSum (edgeResidue chain) b a c = -triangleSum (edgeResidue chain) a b c :=
    triangleSum_swap _ (edgeResidue_reverse chain) a b c
  have hrotate (a b c : V) :
      triangleSum (edgeResidue chain) b c a = triangleSum (edgeResidue chain) a b c :=
    triangleSum_rotate _ a b c
  rcases (show u ≠ v from huv ∘ congrArg part).lt_or_gt with h₁ | h₁
  · rcases (show v ≠ w from hvw ∘ congrArg part).lt_or_gt with h₂ | h₂
    · exact hsorted u v w h₁ h₂ huv hvw huw
    · rcases (show u ≠ w from huw ∘ congrArg part).lt_or_gt with h₃ | h₃
      · have hs : ({u, v, w} : Finset V) = {u, w, v} := by ext x; simp; tauto
        rw [hs]
        simpa only [hswap w u v, hrotate w u v, neg_eq_zero] using
          hsorted u w v h₃ h₂ huw hvw.symm huv
      · rw [← hset w u v, hrotate w u v]
        exact hsorted w u v h₃ h₁ huw.symm huv hvw.symm
  · rcases (show u ≠ w from huw ∘ congrArg part).lt_or_gt with h₃ | h₃
    · rw [insert_comm u v]
      simpa only [hswap u v w, neg_eq_zero] using hsorted v u w h₁ h₃ huv.symm huw hvw
    · rcases (show v ≠ w from hvw ∘ congrArg part).lt_or_gt with h₂ | h₂
      · rw [hset u v w]
        simpa only [hrotate u v w] using
          hsorted v w u h₂ h₃ hvw huw.symm huv.symm
      · have hs : ({u, v, w} : Finset V) = {w, v, u} := by ext x; simp; tauto
        rw [hs]
        simpa only [hrotate u w v, hswap w u v, hrotate w u v, neg_eq_zero] using
          hsorted w v u h₂ h₁ hvw.symm huv.symm huw.symm

private lemma edgeResidue_same_class [Fintype V] [LinearOrder V] {M : Matroid V}
    {part : V → ι} (hbases : HasClassBases M part) (chain : rationalTopCycles M)
    (u v : V) (heq : part u = part v) : edgeResidue chain.val u v = 0 := by
  by_cases huv : u = v
  · subst v
    simp [edgeResidue, flowOfChain]
  have hnot : ¬ M.IsBase (↑({u, v} : Finset V) : Set V) := by
    intro h
    obtain ⟨a, b, hab, hp⟩ := (hbases _).mp h
    have ha : a ∈ ({u, v} : Finset V) := by rw [hp]; simp
    have hb : b ∈ ({u, v} : Finset V) := by rw [hp]; simp
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto
  simp [edgeResidue, flowOfChain, huv, chain.prop.1 _ hnot]

private theorem readout_residues_iff [Fintype V] [LinearOrder V] [Nontrivial ι] {M : Matroid V}
    {part : V → ι} (hbases : HasClassBases M part) (hsurj : Function.Surjective part)
    (chain : rationalTopCycles M) :
    (∀ (C : Finset V), M.IsCircuit (C : Set V) → ∀ F : Finset V,
      rationalResidue (rationalAggregate M C chain.val F) = 0) ↔
      (∀ u v w, part u = part v →
        edgeResidue chain.val u w = edgeResidue chain.val v w) ∧
      (∀ u v w, part u ≠ part v → part v ≠ part w → part u ≠ part w →
        triangleSum (edgeResidue chain.val) u v w = 0) := by
  classical
  constructor
  · intro h
    constructor
    · intro u v w hs
      by_cases huv : u = v
      · rw [huv]
      by_cases hw : part w = part u
      · rw [edgeResidue_same_class hbases chain u w hw.symm,
          edgeResidue_same_class hbases chain v w (hs.symm.trans hw.symm)]
      have hC := same_class_isCircuit hbases hsurj huv hs
      exact (pair_readout_residue_iff hbases hsurj huv hs hw chain.val).mp (h _ hC _)
    · intro u v w huv hvw huw
      have hC := distinct_classes_isCircuit hbases hsurj huv hvw huw
      exact (triple_readout_residue_iff hbases hsurj huv hvw huw chain.val).mp (h _ hC ∅)
  · rintro ⟨hpair, htriangle⟩ C hC F
    by_cases hbase : (M ／ (C : Set V)).IsBase (F : Set V)
    · rcases exists_pair_or_triple_circuit hbases hsurj C hC with
        ⟨u, v, huv, hs, rfl⟩ | ⟨u, v, w, huv, hvw, huw, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := (contract_same_class_bases hbases hsurj huv hs F).mp hbase
        exact (pair_readout_residue_iff hbases hsurj huv hs hw chain.val).mpr (hpair _ _ _ hs)
      · obtain rfl := (contract_distinct_classes_bases hbases hsurj huv hvw huw F).mp hbase
        exact (triple_readout_residue_iff hbases hsurj huv hvw huw chain.val).mpr
          (htriangle _ _ _ huv hvw huw)
    · simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk,
        ite_eq_right hbase, map_zero]

/-- Integral circuit readouts of a rational cycle determine unique normalized potentials. -/
theorem exists_potentials_of_integral_readouts
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι] {M : Matroid V}
    {part : V → ι} (hbases : HasClassBases M part) (hsurj : Function.Surjective part)
    (pivot : ι) (chain : rationalTopCycles M)
    (hintegral : ∀ (C : Finset V), M.IsCircuit (C : Set V) → ∀ F : Finset V,
      rationalResidue (rationalAggregate M C chain.val F) = 0) :
    ∃! potential : ι → RationalResidue,
      potential pivot = 0 ∧
      (∀ u v, edgeResidue chain.val u v = potential (part u) - potential (part v)) ∧
      (∀ i, Fintype.card V • potential i = 0) ∧
        ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i = 0 := by
  obtain ⟨hpair, htriangle⟩ := (readout_residues_iff hbases hsurj chain).mp hintegral
  have htriangle' (u v w : V) (huv : part u ≠ part v) (hvw : part v ≠ part w)
      (huw : part u ≠ part w) :
      edgeResidue chain.val u v + edgeResidue chain.val v w = edgeResidue chain.val u w := by
    have h := htriangle u v w huv hvw huw
    rwa [triangleSum, edgeResidue_reverse chain.val u w, ← sub_eq_add_neg, sub_eq_zero] at h
  obtain ⟨potential, ⟨hpivot, hedge⟩, hunique⟩ :=
    exists_normalized_class_potentials part hsurj pivot (edgeResidue chain.val)
      (edgeResidue_same_class hbases chain) hpair (edgeResidue_reverse chain.val) htriangle'
  have hsum (u : V) : ∑ v : V, (potential (part u) - potential (part v)) = 0 := by
    simp only [← hedge, edgeResidue, ← map_sum, flowOfChain_sum, chain.prop.2, map_zero]
  obtain ⟨hsize, hmass⟩ := (normalized_boundary_iff part hsurj potential hpivot).mp hsum
  exact ⟨potential, ⟨hpivot, hedge, hsize, hmass⟩, fun _ h => hunique _ ⟨h.1, h.2.1⟩⟩

/-- Realize normalized potentials satisfying the boundary relations by a single rational top
cycle with integral circuit readouts. -/
theorem exists_integral_readouts_of_potentials
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι] {M : Matroid V}
    {part : V → ι} (hbases : HasClassBases M part) (hsurj : Function.Surjective part)
    {pivot : ι} (potential : ι → RationalResidue) (hpivot : potential pivot = 0)
    (hsize : ∀ i, Fintype.card V • potential i = 0)
    (hmass : ∑ i : ι, (univ.filter (fun v => part v = i)).card • potential i = 0) :
    ∃ chain : rationalTopCycles M,
      (∀ (C : Finset V), M.IsCircuit (C : Set V) → ∀ F : Finset V,
        rationalResidue (rationalAggregate M C chain.val F) = 0) ∧
      ∀ u v, edgeResidue chain.val u v = potential (part u) - potential (part v) := by
  obtain ⟨j, hj⟩ := exists_ne pivot
  obtain ⟨anchor, hanchor⟩ := hsurj pivot
  obtain ⟨bridge, hbridge⟩ := hsurj j
  have hdiff : part bridge ≠ part anchor := by rwa [hbridge, hanchor]
  obtain ⟨flow, hskew, hsame, hboundary, hresidue⟩ :=
    exists_circulation_of_potentials part hsurj anchor bridge hdiff potential hpivot hsize hmass
  let chain : rationalTopCycles M :=
    ⟨chainOfFlow flow, chainOfFlow_mem_rationalTopCycles part hbases flow hskew hsame hboundary⟩
  have hedge (u v : V) : edgeResidue chain.val u v = potential (part u) - potential (part v) := by
    simpa only [chain, edgeResidue, flowOfChain_chainOfFlow flow hskew (fun u => hsame u u rfl)]
      using hresidue u v
  refine ⟨chain, (readout_residues_iff hbases hsurj chain).mpr ⟨?_, ?_⟩, hedge⟩
  · intro u v w hs
    rw [hedge, hedge, hs]
  · intro u v w _ _ _
    simp only [triangleSum, hedge]
    abel

/-- One class value is fixed to zero. The vertex equations impose ground-size torsion
and a single relation weighted by the class sizes. -/
def normalizedClassPotentials [Fintype V] [Fintype ι] [DecidableEq ι]
    (part : V → ι) (pivot : ι) : Submodule ℤ (ι → RationalResidue) where
  carrier := {f | f pivot = 0 ∧ (∀ i, Fintype.card V • f i = 0) ∧
    ∑ i : ι, (univ.filter (fun v => part v = i)).card • f i = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    refine ⟨by simp [hf.1, hg.1], fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, smul_add, hf.2.1 i, hg.2.1 i, add_zero]
    · simp only [Pi.add_apply, smul_add, sum_add_distrib, hf.2.2, hg.2.2, add_zero]
  smul_mem' n f hf := by
    refine ⟨by simp [hf.1], fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_comm (Fintype.card V) n, hf.2.1 i, smul_zero]
    · simp only [Pi.smul_apply, smul_comm _ n, ← smul_sum, hf.2.2, smul_zero]

private lemma edgeResidue_add [LinearOrder V] (c d : Finset V → ℚ) (u v : V) :
    edgeResidue (c + d) u v = edgeResidue c u v + edgeResidue d u v := by
  by_cases h : u = v <;> simp [edgeResidue, flowOfChain, h, mul_add, map_add]

private lemma edgeResidue_smul [LinearOrder V] (n : ℤ) (c : Finset V → ℚ) (u v : V) :
    edgeResidue (n • c) u v = n • edgeResidue c u v := by
  by_cases h : u = v
  · simp [edgeResidue, flowOfChain, h]
  · unfold edgeResidue flowOfChain
    simp only [ite_eq_right h, Pi.smul_apply, ← map_zsmul, zsmul_eq_mul]
    ring

private noncomputable def potentialReadout
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (pivot : ι) :
    rationalIntegralReadoutCycles M →ₗ[ℤ] normalizedClassPotentials part pivot := by
  classical
  let representative := Function.surjInv hsurj
  have hp : Function.RightInverse representative part := Function.rightInverse_surjInv hsurj
  refine
    { toFun := fun z => ⟨fun i => edgeResidue z.val (representative i) (representative pivot), ?_⟩
      map_add' := fun z w => Subtype.ext (funext fun i => edgeResidue_add z.val w.val _ _)
      map_smul' := fun n z => Subtype.ext (funext fun i => edgeResidue_smul n z.val _ _) }
  obtain ⟨f, ⟨hzero, he, hsize, hmass⟩, _⟩ :=
    exists_potentials_of_integral_readouts hbases hsurj pivot ⟨z.val, z.prop.1⟩
      (fun C hC F => z.prop.2 ⟨C, hC⟩ F)
  have he' (i : ι) : edgeResidue z.val (representative i) (representative pivot) = f i := by
    simpa only [hp i, hp pivot, hzero, sub_zero] using he (representative i) (representative pivot)
  change edgeResidue z.val (representative pivot) (representative pivot) = 0 ∧
    (∀ i, Fintype.card V • edgeResidue z.val (representative i) (representative pivot) = 0) ∧
      ∑ i : ι, (univ.filter (fun v => part v = i)).card •
        edgeResidue z.val (representative i) (representative pivot) = 0
  simp [he', hzero, hsize, hmass]

private lemma potentialReadout_spec
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (pivot : ι)
    (z : rationalIntegralReadoutCycles M) (u v : V) :
    edgeResidue z.val u v =
      (potentialReadout hbases hsurj pivot z).val (part u) -
        (potentialReadout hbases hsurj pivot z).val (part v) := by
  obtain ⟨f, ⟨hzero, he, _, _⟩, _⟩ :=
    exists_potentials_of_integral_readouts hbases hsurj pivot ⟨z.val, z.prop.1⟩
      (fun C hC F => z.prop.2 ⟨C, hC⟩ F)
  have hp (i : ι) : part (Function.surjInv hsurj i) = i :=
    Function.rightInverse_surjInv hsurj i
  have he' (i : ι) :
      (potentialReadout hbases hsurj pivot z).val i = f i := by
    change edgeResidue z.val (Function.surjInv hsurj i) (Function.surjInv hsurj pivot) = f i
    simpa only [hp i, hp pivot, hzero, sub_zero] using
      he (Function.surjInv hsurj i) (Function.surjInv hsurj pivot)
  simpa only [he'] using he u v

private lemma potentialReadout_surj
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (pivot : ι) :
    Function.Surjective (potentialReadout hbases hsurj pivot) := by
  intro f
  obtain ⟨chain, hread, hedge⟩ :=
    exists_integral_readouts_of_potentials hbases hsurj f.val f.prop.1 f.prop.2.1 f.prop.2.2
  let z : rationalIntegralReadoutCycles M :=
    ⟨chain.val, chain.prop, fun C F => hread C.val C.prop F⟩
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  have hp (j : ι) : part (Function.surjInv hsurj j) = j :=
    Function.rightInverse_surjInv hsurj j
  change edgeResidue chain.val (Function.surjInv hsurj i) (Function.surjInv hsurj pivot) = f.val i
  rw [hedge, hp, hp, f.prop.1, sub_zero]

private lemma potentialReadout_ker
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (pivot : ι) :
    (potentialReadout hbases hsurj pivot).ker = (integralCycleInRational M).range := by
  ext z
  change potentialReadout hbases hsurj pivot z = 0 ↔ _
  constructor
  · intro hz
    have hedge (u v : V) : edgeResidue z.val u v = 0 := by
      rw [potentialReadout_spec hbases hsurj pivot z u v, hz]
      simp
    have hpair (u v : V) (h : u < v) : rationalResidue (z.val {u, v}) = 0 := by
      simpa only [edgeResidue, flowOfChain_of_lt _ h, map_neg, neg_eq_zero] using hedge u v
    have hintegral (F : Finset V) : ∃ n : ℤ, (n : ℚ) = z.val F := by
      apply rationalResidue_eq_zero.mp
      by_cases hF : M.IsBase (F : Set V)
      · obtain ⟨u, v, huv, rfl⟩ := (hbases F).mp hF
        rcases (show u ≠ v from huv ∘ congrArg part).lt_or_gt with h | h
        · exact hpair u v h
        · rw [pair_comm]
          exact hpair v u h
      · rw [z.prop.1.1 F hF, map_zero]
    choose x hx using hintegral
    have hx' : castChain x = z.val := funext hx
    let integral : topCycles M := ⟨x, mem_rationalTopCycles_iff.mp (hx'.symm ▸ z.prop.1)⟩
    exact ⟨integral, Subtype.ext hx'⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    funext i
    change edgeResidue (castChain x.val) (Function.surjInv hsurj i)
      (Function.surjInv hsurj pivot) = 0
    generalize Function.surjInv hsurj i = u
    generalize Function.surjInv hsurj pivot = v
    by_cases h : u = v
    · simp [edgeResidue, flowOfChain, h]
    · rw [edgeResidue, flowOfChain, ite_eq_right h]
      exact rationalResidue_eq_zero.mpr
        ⟨insertionSign {u} v * x.val {u, v}, by simp only [Int.cast_mul, castChain]⟩

/-- The integral lifting obstruction in rank two is the group of normalized class
potentials satisfying the weighted boundary relation. -/
theorem rank_two_lifting_obstruction_potentials
    [Fintype V] [LinearOrder V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {M : Matroid V} {part : V → ι} (hbases : HasClassBases M part)
    (hsurj : Function.Surjective part) (pivot : ι) :
    Nonempty ((JointSaturatedImage M ⧸ JointImageInSaturation M) ≃ₗ[ℤ]
      normalizedClassPotentials part pivot) := by
  obtain ⟨e, _⟩ := hsurj pivot
  obtain ⟨_, _, _, ⟨comparison⟩⟩ :=
    rationalJointRestriction_equiv M (pair_ground hbases hsurj e)
  let readout := potentialReadout hbases hsurj pivot
  refine ⟨comparison.symm.trans (?_ : _ ≃ₗ[ℤ] normalizedClassPotentials part pivot)⟩
  exact (Submodule.quotEquivOfEq _ _ (potentialReadout_ker hbases hsurj pivot).symm).trans
    (readout.quotKerEquivOfSurjective (potentialReadout_surj hbases hsurj pivot))

end D5.S3.Combinatorics.Matroids.RankTwoCircuitTorsion
