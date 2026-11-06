/- GID: D5/S3/FiniteGroups/TransversalProbabilityMonotone
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/TransversalProbabilityMonotone
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Common transversal probability increases under a normal extension. -/

/-
admission_basis: open-problem-resolution (#22474; Proved)
Direct frozen dependencies: none (all upstream declarations are from pinned Mathlib).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23087 (result).
The probability counts actual two-sided transversal subsets with the source denominator
|H|^[G:H]. The join H ⊔ N equals HN when N is normal. The equality classification
and a separate homomorphism theorem are not asserted here.
The equal-index argument restricts the probability to the source's specified domain;
its value is the literal cardinality quotient and is independent of that proof.
All rows below have escape_witness: none and Direct frozen dependencies: none.
The proof shapes are semantic classifications; the module uses the settlement basis.
TransversalCounting.Bisections | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivBlocks, TransversalCounting.bisectionsEquivMatchings
TransversalCounting.Matchings | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivBlocks, TransversalCounting.bisectionsEquivMatchings
TransversalCounting.matchings_ext | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivMatchings, TransversalCounting.matchingsEquivBlocks
TransversalCounting.bisectionsEquivMatchings | proof_shape: content | consumer: TransversalCounting.bisectionsEquivBlocks, TransversalCounting.card_bisections
TransversalCounting.card_bisections | proof_shape: content | consumer: TransversalCounting.card_bisections_uniform
TransversalCounting.card_bisections_uniform | proof_shape: content | consumer: block_count
DT | proof_shape: bind-only | consumer: card_dt_cells, card_dt_orbit_factorial
commonTransversalProbability | proof_shape: bind-only | consumer: P, probability_eq_orbit_product
P | proof_shape: bind-only | consumer: claim, probability_eq_orbit_product
claim | proof_shape: bind-only | consumer: result
TransversalCounting.blockP | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivBlocks, TransversalCounting.blocksMatching
TransversalCounting.blockQ | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivBlocks, TransversalCounting.blocksMatching
TransversalCounting.matching_label | proof_shape: bind-only | consumer: TransversalCounting.matchingBlock
TransversalCounting.matchingBlock | proof_shape: bind-only | consumer: TransversalCounting.matchingsEquivBlocks
TransversalCounting.blocksMatching | proof_shape: bind-only | consumer: TransversalCounting.matchingsEquivBlocks
TransversalCounting.matchingsEquivBlocks | proof_shape: bind-only | consumer: TransversalCounting.bisectionsEquivBlocks
TransversalCounting.bisectionsEquivBlocks | proof_shape: content | consumer: TransversalCounting.card_bisections_blocks
TransversalCounting.card_bisections_blocks | proof_shape: content | consumer: card_dt_orbit_factorial
TransversalCounting.card_leftFiber | proof_shape: bind-only | consumer: component_sides_card
TransversalCounting.card_rightFiber | proof_shape: bind-only | consumer: component_size_mul_cell_size
leftComponent | proof_shape: bind-only | consumer: block_cell_card, block_count
rightComponent | proof_shape: bind-only | consumer: block_cell_card, block_count
leftComponent_mk | proof_shape: bind-only | consumer: normal_extension_component_surjective
cell_nonempty | proof_shape: content | consumer: componentCellEquiv
cellMulEquiv | proof_shape: bind-only | consumer: componentCellEquiv
componentCellEquiv | proof_shape: content | consumer: block_cell_card
componentsFintype | proof_shape: bind-only | consumer: card_dt_cells, card_dt_orbit_factorial
componentSize | proof_shape: bind-only | consumer: block_count, card_dt_cells
cellSize | proof_shape: bind-only | consumer: block_cell_card, block_count
component_size_pos | proof_shape: bind-only | consumer: cell_size_eq_div, probability_eq_orbit_product
cell_size_pos | proof_shape: bind-only | consumer: component_sides_card, probability_eq_orbit_product
block_cell_card | proof_shape: content | consumer: block_count, component_sides_card
block_left_fiber_card | proof_shape: bind-only | consumer: component_sides_card
block_right_fiber_card | proof_shape: bind-only | consumer: component_size_mul_cell_size
component_size_mul_cell_size | proof_shape: content | consumer: cell_size_eq_div, component_sides_card
component_sides_card | proof_shape: content | consumer: block_count
cell_size_eq_div | proof_shape: content | consumer: block_count, card_dt_cells
block_count | proof_shape: content | consumer: card_dt_orbit_factorial
card_dt_orbit_factorial | proof_shape: content | consumer: card_dt_cells
sum_component_size | proof_shape: bind-only | consumer: probability_eq_orbit_product
orbitWeight | proof_shape: bind-only | consumer: component_probability, orbit_weight_antitone
orbit_weight_nonneg | proof_shape: bind-only | consumer: orbit_weight_antitone, weight_product_le
orbit_weight_le_one | proof_shape: bind-only | consumer: weight_product_le
orbit_weight_succ | proof_shape: bind-only | consumer: orbit_weight_antitone
orbit_weight_antitone | proof_shape: bind-only | consumer: weight_product_le
component_probability | proof_shape: bind-only | consumer: probability_eq_orbit_product
componentMap | proof_shape: bind-only | consumer: componentCosetMap, componentMap_mk
componentMap_mk | proof_shape: bind-only | consumer: normal_extension_component_surjective
componentMap_surjective | proof_shape: bind-only | consumer: result
coset_map_component | proof_shape: bind-only | consumer: componentCosetMap
componentCosetMap | proof_shape: bind-only | consumer: normal_extension_component_surjective, normal_extension_size_le
normal_extension_component_surjective | proof_shape: content | consumer: normal_extension_size_le
normal_extension_size_le | proof_shape: content | consumer: result
card_dt_cells | proof_shape: content | consumer: probability_eq_orbit_product
probability_eq_orbit_product | proof_shape: content | consumer: result
finset_prod_le_target | proof_shape: bind-only | consumer: weight_product_le
weight_product_le | proof_shape: bind-only | consumer: result
result | proof_shape: content | consumer: external Problem 5.2
-/

import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm

open Function
open scoped Pointwise

attribute [local instance] Classical.propDecidable

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting

variable {E X Y : Type*}

private def Bisections (p : E → X) (q : E → Y) :=
  {T : Set E // Bijective (fun t : T => p t) ∧ Bijective (fun t : T => q t)}

private def Matchings (p : E → X) (q : E → Y) :=
  Σ e : X ≃ Y, ∀ x : X, {g : E // p g = x ∧ q g = e x}

private theorem matchings_ext {p : E → X} {q : E → Y} {A B : Matchings p q}
    (h : ∀ x, (A.2 x).1 = (B.2 x).1) : A = B := by
  rcases A with ⟨e, f⟩
  rcases B with ⟨e', f'⟩
  have he : e = e' := Equiv.ext (fun x =>
    (f x).2.2.symm.trans ((congrArg q (h x)).trans (f' x).2.2))
  subst e'
  congr 1
  funext x
  exact Subtype.ext (h x)

private noncomputable def bisectionsEquivMatchings (p : E → X) (q : E → Y) :
    Bisections p q ≃ Matchings p q where
  toFun T :=
    let ep := Equiv.ofBijective (fun t : T.1 => p t) T.2.1
    let eq := Equiv.ofBijective (fun t : T.1 => q t) T.2.2
    ⟨ep.symm.trans eq, fun x => ⟨(ep.symm x).1, ep.apply_symm_apply x, rfl⟩⟩
  invFun M := by
    let f : X → E := fun x => (M.2 x).1
    have hp : ∀ x, p (f x) = x := fun x => (M.2 x).2.1
    have hq : ∀ x, q (f x) = M.1 x := fun x => (M.2 x).2.2
    refine ⟨Set.range f, ?_, ?_⟩
    · constructor
      · rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ hab
        apply Subtype.ext
        exact congrArg f ((hp x).symm.trans (hab.trans (hp y)))
      · intro x
        exact ⟨⟨f x, ⟨x, rfl⟩⟩, hp x⟩
    · constructor
      · rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ hab
        apply Subtype.ext
        exact congrArg f (M.1.injective ((hq x).symm.trans (hab.trans (hq y))))
      · intro y
        exact ⟨⟨f (M.1.symm y), ⟨_, rfl⟩⟩,
          (hq _).trans (M.1.apply_symm_apply y)⟩
  left_inv T := by
    apply Subtype.ext
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ((Equiv.ofBijective (fun t : T.1 => p t) T.2.1).symm x).2
    · intro hg
      refine ⟨p g, ?_⟩
      exact congrArg Subtype.val
        ((Equiv.ofBijective (fun t : T.1 => p t) T.2.1).symm_apply_apply ⟨g, hg⟩)
  right_inv M := by
    apply matchings_ext
    intro x
    let T : Bisections p q := by
      let f : X → E := fun x => (M.2 x).1
      have hp : ∀ x, p (f x) = x := fun x => (M.2 x).2.1
      have hq : ∀ x, q (f x) = M.1 x := fun x => (M.2 x).2.2
      refine ⟨Set.range f, ?_, ?_⟩
      · constructor
        · rintro ⟨a, z, rfl⟩ ⟨b, y, rfl⟩ h
          exact Subtype.ext (congrArg f ((hp z).symm.trans (h.trans (hp y))))
        · intro z
          exact ⟨⟨f z, ⟨z, rfl⟩⟩, hp z⟩
      · constructor
        · rintro ⟨a, z, rfl⟩ ⟨b, y, rfl⟩ h
          exact Subtype.ext (congrArg f (M.1.injective ((hq z).symm.trans (h.trans (hq y)))))
        · intro y
          exact ⟨⟨f (M.1.symm y), ⟨_, rfl⟩⟩, (hq _).trans (M.1.apply_symm_apply y)⟩
    let ep := Equiv.ofBijective (fun t : T.1 => p t) T.2.1
    change (ep.symm x).1 = (M.2 x).1
    have hx : p (ep.symm x).1 = x := ep.apply_symm_apply x
    obtain ⟨z, hz⟩ := (ep.symm x).2
    change (M.2 z).1 = (ep.symm x).1 at hz
    rw [← hz, (M.2 z).2.1] at hx
    exact hz.symm.trans (congrArg (fun z => (M.2 z).1) hx)

private theorem card_bisections [Finite E] [Fintype X] [Fintype Y]
    (p : E → X) (q : E → Y) :
    Nat.card (Bisections p q) =
      ∑ e : X ≃ Y, ∏ x : X, Nat.card {g : E // p g = x ∧ q g = e x} := by
  classical
  let := Fintype.ofFinite E
  rw [Nat.card_congr (bisectionsEquivMatchings p q)]
  simp only [Matchings, Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_pi]

private theorem card_bisections_uniform [Finite E] [Fintype X] [Fintype Y]
    (p : E → X) (q : E → Y) (e0 : X ≃ Y) (m : ℕ)
    (hm : ∀ x y, Nat.card {g : E // p g = x ∧ q g = y} = m) :
    Nat.card (Bisections p q) = (Fintype.card X).factorial * m ^ Fintype.card X := by
  classical
  rw [card_bisections]
  simp_rw [hm]
  simp [Fintype.card_equiv e0, mul_comm]

end D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting


namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

/-- Definition 3.1(i): actual subsets that are left H-transversals and right K-transversals.
Mathlib's `IsComplement` is the bijective multiplication map, equivalently unique
representatives in the appropriate cosets; it does not require T to be a subgroup. -/
def DT {G : Type} [Group G] (H K : Subgroup G) : Type :=
  {T : Set G // Subgroup.IsComplement T (H : Set G) ∧
    Subgroup.IsComplement (K : Set G) T}

/-- Definition 3.1(ii), used for equal-index subgroups: |DT_G(H,K)| / |H|^[G:H]. -/
noncomputable def commonTransversalProbability {G : Type} [Group G] [Finite G]
    (H K : Subgroup G) (sameIndex : H.index = K.index) : ℚ :=
  (Nat.card (DT H K) : ℚ) / (Nat.card H : ℚ) ^ H.index

/-- The specified-subgroup quantity P_G(H) := P_G(H,H), not the minimum tp(G). -/
noncomputable def P {G : Type} [Group G] [Finite G] (H : Subgroup G) : ℚ :=
  commonTransversalProbability H H rfl

/-- Problem 5.2: H ⊔ N is the product HN whenever N is normal in G. -/
def claim : Prop :=
  ∀ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G) (N : Subgroup G),
    N.Normal → P H ≤ P (H ⊔ N)

end D5.S3.FiniteGroups.TransversalProbabilityMonotone


namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting

variable {E X Y D : Type*} (p : E → X) (q : E → Y)
    (dx : X → D) (dy : Y → D) (hc : ∀ g, dx (p g) = dy (q g))

private def blockP (d : D) (g : {g : E // dx (p g) = d}) : {x : X // dx x = d} :=
  Subtype.map p (fun _ hg => hg) g

private def blockQ (d : D) (g : {g : E // dx (p g) = d}) : {y : Y // dy y = d} :=
  Subtype.map q (fun e he => (hc e).symm.trans he) g

include hc in
private theorem matching_label (M : Matchings p q) (x : X) : dy (M.1 x) = dx x := by
  rw [← (M.2 x).2.2, ← hc, (M.2 x).2.1]

private noncomputable def matchingBlock (M : Matchings p q) (d : D) :
    Matchings (blockP p dx d) (blockQ p q dx dy hc d) := by
  let e : {x : X // dx x = d} ≃ {y : Y // dy y = d} :=
    M.1.subtypeEquiv (fun x => by rw [matching_label p q dx dy hc M x])
  refine ⟨e, fun x => ⟨⟨(M.2 x.1).1, ?_⟩, ?_, ?_⟩⟩
  · rw [(M.2 x.1).2.1]
    exact x.2
  · exact Subtype.ext (M.2 x.1).2.1
  · exact Subtype.ext (M.2 x.1).2.2

private noncomputable def blocksMatching
    (M : ∀ d, Matchings (blockP p dx d) (blockQ p q dx dy hc d)) : Matchings p q := by
  let e : X ≃ Y := (Equiv.sigmaFiberEquiv dx).symm.trans
    ((Equiv.sigmaCongrRight (fun d => (M d).1)).trans (Equiv.sigmaFiberEquiv dy))
  refine ⟨e, fun x => ⟨((M (dx x)).2 ⟨x, rfl⟩).1.1, ?_, ?_⟩⟩
  · exact congrArg Subtype.val (((M (dx x)).2 ⟨x, rfl⟩).2.1)
  · exact congrArg Subtype.val (((M (dx x)).2 ⟨x, rfl⟩).2.2)

private noncomputable def matchingsEquivBlocks : Matchings p q ≃
    ∀ d, Matchings (blockP p dx d) (blockQ p q dx dy hc d) where
  toFun := matchingBlock p q dx dy hc
  invFun := blocksMatching p q dx dy hc
  left_inv M := by
    apply matchings_ext
    intro x
    rfl
  right_inv M := by
    funext d
    apply matchings_ext
    rintro ⟨x, hx⟩
    subst d
    rfl

private noncomputable def bisectionsEquivBlocks : Bisections p q ≃
    ∀ d, Bisections (blockP p dx d) (blockQ p q dx dy hc d) :=
  (bisectionsEquivMatchings p q).trans
    ((matchingsEquivBlocks p q dx dy hc).trans
      (Equiv.piCongrRight (fun _ => (bisectionsEquivMatchings _ _).symm)))

private theorem card_bisections_blocks [Finite E] [Finite X] [Finite Y] [Fintype D] :
    Nat.card (Bisections p q) =
      ∏ d, Nat.card (Bisections (blockP p dx d) (blockQ p q dx dy hc d)) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  rw [Nat.card_congr (bisectionsEquivBlocks p q dx dy hc)]
  exact Nat.card_pi

end D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting

variable {E X Y : Type*}

private theorem card_leftFiber [Finite E] [Fintype Y] (p : E → X) (q : E → Y) (x : X) :
    Nat.card {g : E // p g = x} =
      ∑ y : Y, Nat.card {g : E // p g = x ∧ q g = y} := by
  classical
  let := Fintype.ofFinite E
  let e := (Equiv.sigmaFiberEquiv (fun g : {g : E // p g = x} => q g.1)).symm.trans
    (Equiv.sigmaCongrRight (fun y =>
      Equiv.subtypeSubtypeEquivSubtypeInter (fun g => p g = x) (fun g => q g = y)))
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

private theorem card_rightFiber [Finite E] [Fintype X] (p : E → X) (q : E → Y) (y : Y) :
    Nat.card {g : E // q g = y} =
      ∑ x : X, Nat.card {g : E // p g = x ∧ q g = y} := by
  classical
  let := Fintype.ofFinite E
  let e := (Equiv.sigmaFiberEquiv (fun g : {g : E // q g = y} => p g.1)).symm.trans
    (Equiv.sigmaCongrRight (fun x =>
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => q g = y) (fun g => p g = x)).trans
        (Equiv.subtypeEquivRight (fun _ => and_comm))))
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

end D5.S3.FiniteGroups.TransversalProbabilityMonotone.TransversalCounting

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

variable {G : Type} [Group G] (H : Subgroup G)

private def leftComponent : (G ⧸ H) → (DoubleCoset.Quotient (H : Set G) (H : Set G)) :=
  Quotient.lift (DoubleCoset.mk H H) (fun a b hab => by
    apply DoubleCoset.eq.mpr
    exact ⟨1, H.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by simp⟩)

private def rightComponent : (Quotient (QuotientGroup.rightRel H)) → (DoubleCoset.Quotient (H : Set G) (H : Set G)) :=
  Quotient.lift (DoubleCoset.mk H H) (fun a b hab => by
    apply DoubleCoset.eq.mpr
    exact ⟨b * a⁻¹, QuotientGroup.rightRel_apply.mp hab, 1, H.one_mem, by simp⟩)

@[simp] private theorem leftComponent_mk (g : G) :
    leftComponent H ((QuotientGroup.mk : G → G ⧸ H) g) = DoubleCoset.mk H H g := rfl


private theorem cell_nonempty (x : (G ⧸ H)) (y : (Quotient (QuotientGroup.rightRel H)))
    (h : leftComponent H x = rightComponent H y) : Nonempty ({g : G // (QuotientGroup.mk : G → G ⧸ H) g = x ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y}) := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  obtain ⟨u, hu, v, hv, hb⟩ := DoubleCoset.eq.mp h
  refine ⟨⟨a * v, QuotientGroup.mk_mul_of_mem a hv, ?_⟩⟩
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [hb, mul_assoc] using hu

private noncomputable def cellMulEquiv (a b : H) (g0 : G) :
    {g : G // (QuotientGroup.mk : G → G ⧸ H) g = ((QuotientGroup.mk : G → G ⧸ H) g0) ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g0)} ≃
      {g : G // (QuotientGroup.mk : G → G ⧸ H) g = ((QuotientGroup.mk : G → G ⧸ H) (a * g0 * b)) ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (a * g0 * b))} :=
  ((Equiv.mulLeft (a : G)).trans (Equiv.mulRight (b : G))).subtypeEquiv (by
    intro g
    constructor
    · intro hg
      constructor
      · apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        have hl := QuotientGroup.leftRel_apply.mp (Quotient.exact hg.1)
        simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem b.2) hl) b.2
      · apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hg.2)
        simpa [mul_assoc] using H.mul_mem (H.mul_mem a.2 hr) (H.inv_mem a.2)
    · intro hg
      constructor
      · apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        have hl := QuotientGroup.leftRel_apply.mp (Quotient.exact hg.1)
        have hh := H.mul_mem (H.mul_mem b.2 hl) (H.inv_mem b.2)
        simpa [mul_assoc] using hh
      · apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hg.2)
        have hh := H.mul_mem (H.mul_mem (H.inv_mem a.2) hr) a.2
        simpa [mul_assoc] using hh)

private noncomputable def componentCellEquiv (d : (DoubleCoset.Quotient (H : Set G) (H : Set G)))
    (x : (G ⧸ H)) (y : (Quotient (QuotientGroup.rightRel H)))
    (hx : leftComponent H x = d) (hy : rightComponent H y = d) :
    {g : G // (QuotientGroup.mk : G → G ⧸ H) g = ((QuotientGroup.mk : G → G ⧸ H) d.out) ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) d.out)} ≃ {g : G // (QuotientGroup.mk : G → G ⧸ H) g = x ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y} := by
  classical
  apply Classical.choice
  obtain ⟨w⟩ := cell_nonempty H x y (hx.trans hy.symm)
  have hdw : DoubleCoset.mk H H w.1 = d := by
    rw [← leftComponent_mk, w.2.1, hx]
  obtain ⟨a, ha, b, hb, hw⟩ := DoubleCoset.eq.mp
    ((DoubleCoset.out_eq' d).trans hdw.symm)
  have hx' : (QuotientGroup.mk : G → G ⧸ H) (a * d.out * b) = x := by simpa [hw] using w.2.1
  have hy' : (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (a * d.out * b) = y := by simpa [hw] using w.2.2
  exact ⟨(cellMulEquiv H ⟨a, ha⟩ ⟨b, hb⟩ d.out).trans
    (Equiv.subtypeEquivRight (fun g => by rw [hx', hy']))⟩

end D5.S3.FiniteGroups.TransversalProbabilityMonotone

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

open TransversalCounting
variable {G : Type} [Group G] [Fintype G] (H : Subgroup G)


private noncomputable instance componentsFintype :
    Fintype (DoubleCoset.Quotient (H : Set G) (H : Set G)) :=
  Quotient.fintype (DoubleCoset.setoid (H : Set G) (H : Set G))

private noncomputable def componentSize (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) : ℕ := Nat.card ({x : G ⧸ H // leftComponent H x = d})
private noncomputable def cellSize (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) : ℕ :=
  Nat.card ({g : G // (QuotientGroup.mk : G → G ⧸ H) g = ((QuotientGroup.mk : G → G ⧸ H) d.out) ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) d.out)})

private theorem component_size_pos (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) : 0 < componentSize H d := by
  have : Nonempty ({x : G ⧸ H // leftComponent H x = d}) := ⟨⟨(QuotientGroup.mk : G → G ⧸ H) d.out, DoubleCoset.out_eq' d⟩⟩
  exact Nat.card_pos

private theorem cell_size_pos (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) : 0 < cellSize H d := by
  have : Nonempty ({g : G // (QuotientGroup.mk : G → G ⧸ H) g = ((QuotientGroup.mk : G → G ⧸ H) d.out) ∧ (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) d.out)}) :=
    cell_nonempty H (QuotientGroup.mk d.out) (Quotient.mk'' d.out) rfl
  exact Nat.card_pos

omit [Fintype G] in
private theorem block_cell_card (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) (x : {x : G ⧸ H // leftComponent H x = d}) (y : {y : Quotient (QuotientGroup.rightRel H) // rightComponent H y = d}) :
    Nat.card {g : {g : G // DoubleCoset.mk H H g = d} // (blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d) g = x ∧ (blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d) g = y} = cellSize H d := by
  let e : {g : {g : G // DoubleCoset.mk H H g = d} //
      blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d g = x ∧
      blockQ (QuotientGroup.mk : G → G ⧸ H)
        (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))
        (leftComponent H) (rightComponent H) (fun _ => rfl) d g = y} ≃
      {g : G // (QuotientGroup.mk : G → G ⧸ H) g = x.1 ∧
        (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y.1} :=
    (Equiv.subtypeEquivRight (fun _ => and_congr Subtype.ext_iff Subtype.ext_iff)).trans
      (Equiv.subtypeSubtypeEquivSubtype
        (p := fun g : G => DoubleCoset.mk H H g = d)
        (q := fun g : G => (QuotientGroup.mk : G → G ⧸ H) g = x.1 ∧
          (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y.1)
        (fun hg => (congrArg (leftComponent H) hg.1).trans x.2))
  exact (Nat.card_congr e).trans
    (Nat.card_congr (componentCellEquiv H d x.1 y.1 x.2 y.2)).symm

omit [Fintype G] in
private theorem block_left_fiber_card (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) (x : {x : G ⧸ H // leftComponent H x = d}) :
    Nat.card {g : {g : G // DoubleCoset.mk H H g = d} // (blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d) g = x} = Nat.card H  := by
  let e : {g : {g : G // DoubleCoset.mk H H g = d} //
      blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d g = x} ≃
      {g : G // (QuotientGroup.mk : G → G ⧸ H) g = x.1} :=
    (Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)).trans
      (Equiv.subtypeSubtypeEquivSubtype
        (p := fun g : G => DoubleCoset.mk H H g = d)
        (q := fun g : G => (QuotientGroup.mk : G → G ⧸ H) g = x.1)
        (fun hg => (congrArg (leftComponent H) hg).trans x.2))
  have hcos : ∀ g : G, (QuotientGroup.mk : G → G ⧸ H) g = x.1 ↔
      g ∈ x.1.out • (H : Set G) := by
    intro g
    simpa only [Set.mem_setOf_eq, Quotient.out_eq'] using
      (Set.ext_iff.mp (QuotientGroup.eq_class_eq_leftCoset H x.1.out) g)
  exact Nat.card_congr (e.trans
    ((Equiv.subtypeEquivRight hcos).trans (Subgroup.leftCosetEquivSubgroup x.1.out)))

omit [Fintype G] in
private theorem block_right_fiber_card (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) (y : {y : Quotient (QuotientGroup.rightRel H) // rightComponent H y = d}) :
    Nat.card {g : {g : G // DoubleCoset.mk H H g = d} // (blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d) g = y} = Nat.card H  := by
  let e : {g : {g : G // DoubleCoset.mk H H g = d} //
      blockQ (QuotientGroup.mk : G → G ⧸ H)
        (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))
        (leftComponent H) (rightComponent H) (fun _ => rfl) d g = y} ≃
      {g : G // (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y.1} :=
    (Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)).trans
      (Equiv.subtypeSubtypeEquivSubtype (fun hg =>
        (show leftComponent H (QuotientGroup.mk _) = rightComponent H (Quotient.mk'' _) from rfl).trans
          ((congrArg (rightComponent H) hg).trans y.2)))
  have hcos : ∀ g : G, (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) g = y.1 ↔
      g ∈ MulOpposite.op y.1.out • (H : Set G) := by
    intro g
    constructor
    · intro hg
      exact (mem_rightCoset_iff _).mpr (QuotientGroup.rightRel_apply.mp
        (Quotient.exact ((Quotient.out_eq' y.1).trans hg.symm)))
    · intro hg
      have he : (Quotient.mk'' y.1.out : Quotient (QuotientGroup.rightRel H)) =
          Quotient.mk'' g := Quotient.sound
        (QuotientGroup.rightRel_apply.mpr ((mem_rightCoset_iff _).mp hg))
      exact he.symm.trans (Quotient.out_eq' y.1)
  exact Nat.card_congr (e.trans
    ((Equiv.subtypeEquivRight hcos).trans (Subgroup.rightCosetEquivSubgroup y.1.out)))

private theorem component_size_mul_cell_size (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    componentSize H d * cellSize H d = Nat.card H := by
  let y : {y : Quotient (QuotientGroup.rightRel H) // rightComponent H y = d} := ⟨(Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) d.out, DoubleCoset.out_eq' d⟩
  have h : Nat.card H = ∑ x : {x : G ⧸ H // leftComponent H x = d},
      Nat.card {g : {g : G // DoubleCoset.mk H H g = d} // (blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d) g = x ∧ (blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d) g = y} :=
    (block_right_fiber_card H d y).symm.trans (card_rightFiber ((blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d)) ((blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d)) y)
  simp_rw [block_cell_card H d] at h
  simpa [componentSize, Nat.card_eq_fintype_card, mul_comm] using h.symm

private theorem component_sides_card (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    Fintype.card ({x : G ⧸ H // leftComponent H x = d}) = Fintype.card ({y : Quotient (QuotientGroup.rightRel H) // rightComponent H y = d}) := by
  let x : {x : G ⧸ H // leftComponent H x = d} := ⟨(QuotientGroup.mk : G → G ⧸ H) d.out, DoubleCoset.out_eq' d⟩
  have h : Nat.card H = ∑ y : {y : Quotient (QuotientGroup.rightRel H) // rightComponent H y = d},
      Nat.card {g : {g : G // DoubleCoset.mk H H g = d} // (blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d) g = x ∧ (blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d) g = y} :=
    (block_left_fiber_card H d x).symm.trans (card_leftFiber ((blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d)) ((blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d)) x)
  simp_rw [block_cell_card H d] at h
  have h' := component_size_mul_cell_size H d
  simp only [componentSize, Nat.card_eq_fintype_card, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at h h'
  exact Nat.eq_of_mul_eq_mul_right (cell_size_pos H d) (h'.trans h)

private theorem cell_size_eq_div (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    cellSize H d = Nat.card H / componentSize H d := by
  rw [← component_size_mul_cell_size H d]
  exact (Nat.mul_div_cancel_left _ (component_size_pos H d)).symm

private theorem block_count (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    Nat.card (Bisections ((blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d)) ((blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d))) =
      (componentSize H d).factorial * (Nat.card H / componentSize H d) ^ componentSize H d := by
  rw [card_bisections_uniform ((blockP (QuotientGroup.mk : G → G ⧸ H) (leftComponent H) d)) ((blockQ (QuotientGroup.mk : G → G ⧸ H) (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)) (leftComponent H) (rightComponent H) (fun _ => rfl) d))
    (Fintype.equivOfCardEq (component_sides_card H d)) (cellSize H d)
    (block_cell_card H d)]
  simp only [componentSize, Nat.card_eq_fintype_card, cell_size_eq_div]

private theorem card_dt_orbit_factorial : Nat.card (DT H H) =
    ∏ d : (DoubleCoset.Quotient (H : Set G) (H : Set G)), (componentSize H d).factorial *
      (Nat.card H / componentSize H d) ^ componentSize H d := by
  let e : DT H H ≃ Bisections ((QuotientGroup.mk : G → G ⧸ H)) ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))) :=
    Equiv.subtypeEquivRight (fun _ => and_congr
      Subgroup.isComplement_subgroup_right_iff_bijective
      Subgroup.isComplement_subgroup_left_iff_bijective)
  rw [Nat.card_congr e, card_bisections_blocks ((QuotientGroup.mk : G → G ⧸ H)) ((Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H)))
    (leftComponent H) (rightComponent H) (fun _ => rfl)]
  apply Finset.prod_congr rfl
  intro d _
  exact block_count H d

private theorem sum_component_size : (∑ d : (DoubleCoset.Quotient (H : Set G) (H : Set G)), componentSize H d) = H.index := by
  change (∑ d : (DoubleCoset.Quotient (H : Set G) (H : Set G)), Nat.card ({x : G ⧸ H // leftComponent H x = d})) = Nat.card ((G ⧸ H))
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (leftComponent H))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

end D5.S3.FiniteGroups.TransversalProbabilityMonotone

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

private noncomputable def orbitWeight (n : ℕ) : ℚ := (n.factorial : ℚ) / (n : ℚ) ^ n

private theorem orbit_weight_nonneg (n : ℕ) : 0 ≤ orbitWeight n :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

private theorem orbit_weight_le_one (n : ℕ) : orbitWeight n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    norm_num [orbitWeight]
  · apply (div_le_one₀ (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) n)).2
    exact_mod_cast Nat.factorial_le_pow n

private theorem orbit_weight_succ (n : ℕ) :
    orbitWeight (n + 1) = orbitWeight n * ((n : ℚ) / (n + 1)) ^ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [orbitWeight]
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hnp : (n : ℚ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    simp only [orbitWeight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ, div_pow]
    field_simp

private theorem orbit_weight_antitone : Antitone orbitWeight := by
  apply antitone_nat_of_succ_le
  intro n
  rw [orbit_weight_succ]
  have hn : 0 ≤ (n : ℚ) / (n + 1) := by positivity
  have hn1 : (n : ℚ) / (n + 1) ≤ 1 := by
    apply (div_le_one₀ (by positivity)).2
    linarith
  exact mul_le_of_le_one_right (orbit_weight_nonneg n) (pow_le_one₀ hn hn1)

private theorem component_probability (h n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hh : n * m = h) :
    ((n.factorial * m ^ n : ℕ) : ℚ) / (h : ℚ) ^ n = orbitWeight n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  subst h
  simp only [Nat.cast_mul, Nat.cast_pow, mul_pow, orbitWeight]
  field_simp

end D5.S3.FiniteGroups.TransversalProbabilityMonotone

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

variable {G : Type} [Group G] {H L : Subgroup G}

private noncomputable def componentMap (h : H ≤ L) : (DoubleCoset.Quotient (H : Set G) (H : Set G)) → (DoubleCoset.Quotient (L : Set G) (L : Set G)) :=
  Quotient.map id (fun a b hab => by
    obtain ⟨u, hu, v, hv, hb⟩ := DoubleCoset.rel_iff.mp hab
    exact DoubleCoset.rel_iff.mpr ⟨u, h hu, v, h hv, hb⟩)

@[simp] private theorem componentMap_mk (h : H ≤ L) (g : G) :
    componentMap h (DoubleCoset.mk H H g) = DoubleCoset.mk L L g := rfl

private theorem componentMap_surjective (h : H ≤ L) :
    Function.Surjective (componentMap h) :=
  Quotient.map_surjective _ Function.surjective_id

private theorem coset_map_component (h : H ≤ L) (x : (G ⧸ H)) :
    leftComponent L (Subgroup.quotientMapOfLE h x) = componentMap h (leftComponent H x) := by
  induction x using Quotient.inductionOn with | h g => rfl

private noncomputable def componentCosetMap (h : H ≤ L) (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    {x : G ⧸ H // leftComponent H x = d} → {x : G ⧸ L // leftComponent L x = (componentMap h d)} :=
  Subtype.map (Subgroup.quotientMapOfLE h) (fun x hx =>
    (coset_map_component h x).trans (congrArg (componentMap h) hx))

private theorem normal_extension_component_surjective (H N : Subgroup G) [N.Normal]
    (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    Function.Surjective (componentCosetMap (show H ≤ H ⊔ N from le_sup_left) d) := by
  let L := H ⊔ N
  let h : H ≤ L := le_sup_left
  intro y
  have hd : DoubleCoset.mk L L d.out = componentMap h d := by
    rw [← componentMap_mk h, DoubleCoset.out_eq']
  have hy : DoubleCoset.mk L L y.1.out = componentMap h d := by
    exact (congrArg (leftComponent L) (Quotient.out_eq' y.1)).trans y.2
  obtain ⟨l, hl, r, hr, hb⟩ := DoubleCoset.eq.mp (hd.trans hy.symm)
  have hl' : l ∈ (H : Set G) * (N : Set G) := by
    rwa [← Subgroup.mul_normal H N]
  obtain ⟨a, ha, n, hn, han⟩ := Set.mem_mul.mp hl'
  let x : {x : G ⧸ H // leftComponent H x = d} := ⟨(QuotientGroup.mk : G → G ⧸ H) (a * d.out), by
    rw [leftComponent_mk]
    exact (DoubleCoset.mk_mem_mul ⟨a, ha⟩ d.out).trans (DoubleCoset.out_eq' d)⟩
  refine ⟨x, Subtype.ext ?_⟩
  change ((QuotientGroup.mk : G → G ⧸ L) (a * d.out)) = y.1
  rw [← Quotient.out_eq' y.1]
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  rw [hb, ← han]
  have hn' : d.out⁻¹ * n * d.out ∈ L :=
    (show N ≤ L from le_sup_right) ((inferInstance : N.Normal).conj_mem' n hn d.out)
  simpa [mul_assoc] using L.mul_mem hn' hr

private theorem normal_extension_size_le [Fintype G] (H N : Subgroup G) [N.Normal]
    (d : (DoubleCoset.Quotient (H : Set G) (H : Set G))) :
    componentSize (H ⊔ N) (componentMap (show H ≤ H ⊔ N from le_sup_left) d) ≤
      componentSize H d :=
  Nat.card_le_card_of_surjective _ (normal_extension_component_surjective H N d)

end D5.S3.FiniteGroups.TransversalProbabilityMonotone

namespace D5.S3.FiniteGroups.TransversalProbabilityMonotone

variable {G : Type} [Group G] [Fintype G] (H : Subgroup G)

private theorem card_dt_cells : Nat.card (DT H H) =
    ∏ d : (DoubleCoset.Quotient (H : Set G) (H : Set G)), (componentSize H d).factorial * (cellSize H d) ^ componentSize H d := by
  rw [card_dt_orbit_factorial]
  simp_rw [cell_size_eq_div]

private theorem probability_eq_orbit_product : P H =
    ∏ d : (DoubleCoset.Quotient (H : Set G) (H : Set G)), orbitWeight (componentSize H d) := by
  unfold P commonTransversalProbability
  rw [card_dt_cells, Finset.prod_natCast, ← sum_component_size H,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro d _
  exact component_probability (Nat.card H) (componentSize H d) (cellSize H d)
    (component_size_pos H d) (cell_size_pos H d) (component_size_mul_cell_size H d)

private theorem finset_prod_le_target {ι : Type*} (s : Finset ι) (f : ι → ℚ) (target : ℚ)
    (hs : s.Nonempty) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1)
    (ht : ∀ i ∈ s, f i ≤ target) :
    ∏ i ∈ s, f i ≤ target := by
  classical
  obtain ⟨i, hi⟩ := hs
  have hp := Finset.prod_le_prod_of_subset_of_le_one₀
    (Finset.singleton_subset_iff.mpr hi) h0 (fun j hj _ => h1 j hj)
  have hp' : ∏ j ∈ s, f j ≤ f i := by
    simpa only [Finset.prod_singleton] using hp
  exact hp'.trans (ht i hi)

private theorem weight_product_le {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Surjective f) (u : I → ℕ) (v : J → ℕ)
    (huv : ∀ i, v (f i) ≤ u i) :
    (∏ i, orbitWeight (u i)) ≤ ∏ j, orbitWeight (v j) := by
  classical
  rw [← Fintype.prod_fiberwise f (fun i => orbitWeight (u i))]
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.prod_nonneg (fun i _ => orbit_weight_nonneg (u i.1))
  · intro j _
    obtain ⟨i, hi⟩ := hf j
    let i0 : {i // f i = j} := ⟨i, hi⟩
    exact finset_prod_le_target Finset.univ
      (fun k : {i // f i = j} => orbitWeight (u k)) (orbitWeight (v j))
      ⟨i0, Finset.mem_univ _⟩
      (fun k _ => orbit_weight_nonneg _) (fun k _ => orbit_weight_le_one _)
      (fun k _ => by
        have hk := orbit_weight_antitone (huv k.1)
        simpa only [k.2] using hk)

theorem result : claim := by
  intro G instGroup instFinite H N hN
  let : Fintype G := Fintype.ofFinite G
  let : N.Normal := hN
  rw [probability_eq_orbit_product, probability_eq_orbit_product]
  exact weight_product_le (componentMap (show H ≤ H ⊔ N from le_sup_left))
    (componentMap_surjective _) (componentSize H) (componentSize (H ⊔ N))
    (normal_extension_size_le H N)

end D5.S3.FiniteGroups.TransversalProbabilityMonotone
