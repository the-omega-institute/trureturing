/- GID: D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Full reachability and switching support for two twisted SSEP models. -/

/-
admission_basis: open-problem-resolution (#30601; Proved)
escape_witness: none; every declaration is bind-only and the settlement is admitted as open-problem-resolution (#30601)
Direct frozen mathematical dependencies: none (pinned Mathlib only).
Utility is none: this is a uniform classification of the external switching
question, rather than a finite certificate or an asserted computational use.
The proof-shape judgments expand all same-delivery definitions and helpers.
Every declaration is judged bind-only: the proofs apply closure induction,
commutator, quotient and orbit-stabilizer results of pinned Mathlib with
normalization. The novelty is the settlement of the external question.
Configuration: proof_shape=bind-only; consumers=adjacentMove, boundaryMove, moveRelation, sector, branchingProbability, overlap, unionMoveRelation, sectorsOf, alternatingSectorReach, switchSupport, alternatingSupport, adjacentMove_involutive, boundary_at_first, boundary_at_last, boundary_at_other, boundaryMove_involutive, sector_nonempty, branchingProbability_pos_iff, sector_overlap_is_positive, alternatingSupport_eq_switchSupport, fullSwitchingReachability, mem_sector_iff, alternatingSupport_step, alternatingSupport_mono, alternatingSupport_union_step, union_path_eventually_supported, supported_in_union_component, siteReachGroup, site_permutation_path, coordinateReachGroup, boundary_pair_path, unionConnected_of_derived_transitive, union_path_invariant, all_in_orbit_move, twist_transitive_of_unionConnected, charge_product_move, twoSiteEquiv, twoSite_move_orbit, unionConnected_two_iff_pair_pretransitive, result
adjacentMove: proof_shape=bind-only; consumers=moveRelation, adjacentMove_involutive, twoSite_move_orbit
lastSite: proof_shape=bind-only; consumers=boundaryMove, lastSite_ne_first, boundary_at_first, boundary_at_last, boundary_at_other, boundaryMove_involutive, boundary_pair_path, exists_site_permutation, pairedCoordinates_mem, all_in_orbit_move, charge_product_move
firstSite: proof_shape=bind-only; consumers=boundaryMove, lastSite_ne_first, boundary_at_first, boundary_at_last, boundary_at_other, boundaryMove_involutive, boundary_pair_path, exists_site_permutation, pairedCoordinates_mem, all_in_orbit_move, twist_transitive_of_unionConnected, charge_product_move, derived_transitive_of_unionConnected
boundaryMove: proof_shape=bind-only; consumers=moveRelation, boundary_at_first, boundary_at_last, boundary_at_other, boundaryMove_involutive, boundary_pair_path, all_in_orbit_move, charge_product_move
moveRelation: proof_shape=bind-only; consumers=sector, unionMoveRelation, moveRelation_symmetric, mem_sector_iff, alternatingSupport_step, alternatingSupport_union_step, supported_in_union_component, all_in_orbit_move, charge_product_move, twoSite_move_orbit
sector: proof_shape=bind-only; consumers=branchingProbability, overlap, sectorsOf, sector_nonempty, branchingProbability_pos_iff, fullSwitchingReachability, mem_sector_iff, alternatingSupport_step, supported_in_union_component, fullSwitchingReachability_iff_unionConnected
branchingProbability: proof_shape=bind-only; consumers=branchingProbability_pos_iff, sector_overlap_is_positive, result
overlap: proof_shape=bind-only; consumers=branchingProbability_pos_iff, sector_overlap_is_positive, result
unionMoveRelation: proof_shape=bind-only; consumers=unionConnected, alternatingSupport_union_step, union_path_eventually_supported, supported_in_union_component, UnionPath, siteReachGroup, coordinateReachGroup, unionConnected_of_derived_transitive, union_path_invariant, twist_transitive_of_unionConnected, unionConnected_two_iff_pair_pretransitive
unionConnected: proof_shape=bind-only; consumers=registeredReachabilityAnswer, fullSwitchingReachability_iff_unionConnected, unionConnected_of_derived_transitive, twist_transitive_of_unionConnected, derived_transitive_of_unionConnected, unionConnected_two_iff_pair_pretransitive, unionConnected_two_iff_lTwoCriterion, unionConnected_iff_lAtLeastThreeCriterion, result
sectorsOf: proof_shape=bind-only; consumers=alternatingSectorReach, alternatingSupport
alternatingSectorReach: proof_shape=bind-only; consumers=switchSupport, alternatingSupport_eq_switchSupport
switchSupport: proof_shape=bind-only; consumers=alternatingSupport_eq_switchSupport, fullSwitchingReachability, result
alternatingSupport: proof_shape=bind-only; consumers=alternatingSupport_eq_switchSupport, alternatingSupport_step, alternatingSupport_mono, alternatingSupport_union_step, union_path_eventually_supported, supported_in_union_component, result
adjacentMove_involutive: proof_shape=bind-only; consumers=moveRelation_symmetric
lastSite_ne_first: proof_shape=bind-only; consumers=boundary_at_last, boundary_pair_path, exists_site_permutation, charge_product_move
boundary_at_first: proof_shape=bind-only; consumers=boundaryMove_involutive, all_in_orbit_move, charge_product_move
boundary_at_last: proof_shape=bind-only; consumers=boundaryMove_involutive, all_in_orbit_move
boundary_at_other: proof_shape=bind-only; consumers=boundaryMove_involutive
boundaryMove_involutive: proof_shape=bind-only; consumers=moveRelation_symmetric
moveRelation_symmetric: proof_shape=bind-only; consumers=union_path_eventually_supported, twist_transitive_of_unionConnected, unionConnected_two_iff_pair_pretransitive
sector_nonempty: proof_shape=bind-only; consumers=branchingProbability_pos_iff
branchingProbability_pos_iff: proof_shape=bind-only; consumers=sector_overlap_is_positive
sector_overlap_is_positive: proof_shape=bind-only; consumers=result
alternatingSupport_eq_switchSupport: proof_shape=bind-only; consumers=fullSwitchingReachability_iff_unionConnected, result
twistGroup: proof_shape=bind-only; consumers=derivedTwistGroup, lTwoCriterion, pairTwistGroup_le_product, twistGroup_le_pair_fst, twist_transitive_of_unionConnected, derived_transitive_of_unionConnected, pairStabilizerEquiv, lTwoCriterion_iff_pair_pretransitive
derivedTwistGroup: proof_shape=bind-only; consumers=lAtLeastThreeCriterion, derived_singleCoordinate_mem, unionConnected_of_derived_transitive
pairTwistGroup: proof_shape=bind-only; consumers=lTwoCriterion, lTwoOrbitCriterion, lTwoOrbitCriterion_iff_pretransitive, pairCoordinate_mem, pairTwistGroup_le_product, twistGroup_le_pair_fst, pair_flip_mem, pair_orbit_swap, twoSite_move_orbit, unionConnected_two_iff_pair_pretransitive, pairStabilizerEquiv, lTwoCriterion_iff_pair_pretransitive
pairPermutationMulAction: proof_shape=bind-only; consumers=lTwoOrbitCriterion, lTwoOrbitCriterion_iff_pretransitive, pair_orbit_swap, twoSite_move_orbit, unionConnected_two_iff_pair_pretransitive, pairStabilizerEquiv, lTwoCriterion_iff_pair_pretransitive
pointStabilizer: proof_shape=bind-only; consumers=pointPairStabilizer
pointPairStabilizer: proof_shape=bind-only; consumers=lTwoCriterion, pairStabilizerEquiv, lTwoCriterion_iff_pair_pretransitive
lTwoCriterion: proof_shape=bind-only; consumers=registeredReachabilityAnswer, lTwoCriterion_iff_pair_pretransitive, unionConnected_two_iff_lTwoCriterion, result
lAtLeastThreeCriterion: proof_shape=bind-only; consumers=registeredReachabilityAnswer, unionConnected_of_derived_transitive, derived_transitive_of_unionConnected, unionConnected_iff_lAtLeastThreeCriterion, result
lTwoOrbitCriterion: proof_shape=bind-only; consumers=lTwoOrbitCriterion_iff_pretransitive, lTwoCriterion_iff_pair_pretransitive
fullSwitchingReachability: proof_shape=bind-only; consumers=registeredReachabilityAnswer, fullSwitchingReachability_iff_unionConnected
registeredReachabilityAnswer: proof_shape=bind-only; consumers=result
lTwoOrbitCriterion_iff_pretransitive: proof_shape=bind-only; consumers=unionConnected_two_iff_pair_pretransitive, lTwoCriterion_iff_pair_pretransitive
mem_sector_iff: proof_shape=bind-only; consumers=alternatingSupport_step, supported_in_union_component, fullSwitchingReachability_iff_unionConnected
alternatingSupport_step: proof_shape=bind-only; consumers=alternatingSupport_mono, alternatingSupport_union_step
alternatingSupport_mono: proof_shape=bind-only; consumers=alternatingSupport_union_step
alternatingSupport_union_step: proof_shape=bind-only; consumers=union_path_eventually_supported
union_path_eventually_supported: proof_shape=bind-only; consumers=fullSwitchingReachability_iff_unionConnected
supported_in_union_component: proof_shape=bind-only; consumers=fullSwitchingReachability_iff_unionConnected
fullSwitchingReachability_iff_unionConnected: proof_shape=bind-only; consumers=result
UnionPath: proof_shape=bind-only; consumers=siteReachGroup, site_permutation_path, coordinateReachGroup, boundary_pair_path, unionConnected_of_derived_transitive
siteReachGroup: proof_shape=bind-only; consumers=siteReachGroup_eq_top, site_permutation_path
siteReachGroup_eq_top: proof_shape=bind-only; consumers=site_permutation_path
site_permutation_path: proof_shape=bind-only; consumers=boundary_pair_path, pairedCoordinates_mem
coordinateReachGroup: proof_shape=bind-only; consumers=pairedCoordinates_mem, pairCoordinate_mem, derived_singleCoordinate_mem
pairedCoordinates: proof_shape=bind-only; consumers=boundary_pair_path, pairedCoordinates_mem, pairCoordinate_mem
boundary_pair_path: proof_shape=bind-only; consumers=pairedCoordinates_mem
exists_site_permutation: proof_shape=bind-only; consumers=pairedCoordinates_mem
pairedCoordinates_mem: proof_shape=bind-only; consumers=pairCoordinate_mem
pairCoordinateHom: proof_shape=bind-only; consumers=pairCoordinate_mem, derived_singleCoordinate_mem, unionConnected_two_iff_pair_pretransitive
pairCoordinate_mem: proof_shape=bind-only; consumers=derived_singleCoordinate_mem, unionConnected_two_iff_pair_pretransitive
pairTwistGroup_le_product: proof_shape=bind-only; consumers=pairStabilizerEquiv
twistGroup_le_pair_fst: proof_shape=bind-only; consumers=derived_singleCoordinate_mem
singleCoordinateHom: proof_shape=bind-only; consumers=derived_singleCoordinate_mem, unionConnected_of_derived_transitive
three_distinct_sites: proof_shape=bind-only; consumers=derived_singleCoordinate_mem
derived_singleCoordinate_mem: proof_shape=bind-only; consumers=unionConnected_of_derived_transitive
unionConnected_of_derived_transitive: proof_shape=bind-only; consumers=unionConnected_iff_lAtLeastThreeCriterion
union_path_invariant: proof_shape=bind-only; consumers=twist_transitive_of_unionConnected, derived_transitive_of_unionConnected
all_in_orbit_move: proof_shape=bind-only; consumers=twist_transitive_of_unionConnected
twist_transitive_of_unionConnected: proof_shape=bind-only; consumers=derived_transitive_of_unionConnected
actionCharge: proof_shape=bind-only; consumers=actionCharge_eval, actionCharge_smul, derived_transitive_of_unionConnected
actionCharge_eval: proof_shape=bind-only; consumers=actionCharge_smul, derived_transitive_of_unionConnected
actionCharge_smul: proof_shape=bind-only; consumers=derived_transitive_of_unionConnected
charge_product_move: proof_shape=bind-only; consumers=derived_transitive_of_unionConnected
derived_transitive_of_unionConnected: proof_shape=bind-only; consumers=unionConnected_iff_lAtLeastThreeCriterion
twoSiteEquiv: proof_shape=bind-only; consumers=twoSite_move_orbit, unionConnected_two_iff_pair_pretransitive
flipPairHom: proof_shape=bind-only; consumers=pair_flip_mem, pair_orbit_swap
pair_flip_mem: proof_shape=bind-only; consumers=pair_orbit_swap
pair_orbit_swap: proof_shape=bind-only; consumers=twoSite_move_orbit
twoSite_move_orbit: proof_shape=bind-only; consumers=unionConnected_two_iff_pair_pretransitive
unionConnected_two_iff_pair_pretransitive: proof_shape=bind-only; consumers=unionConnected_two_iff_lTwoCriterion
pairStabilizerEquiv: proof_shape=bind-only; consumers=lTwoCriterion_iff_pair_pretransitive
lTwoCriterion_iff_pair_pretransitive: proof_shape=bind-only; consumers=unionConnected_two_iff_lTwoCriterion
unionConnected_two_iff_lTwoCriterion: proof_shape=bind-only; consumers=result
unionConnected_iff_lAtLeastThreeCriterion: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=none (designated external-question result)
-/

import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic

/-!
The finite configuration and switching layer for the two-twist SSEP question.

The definitions below keep the source's direction of the boundary move: the last
entry is sent through the inverse twist to the first site, while the first entry
is sent through the twist to the last site.  Sectors are the finite connected
components generated by the involutive elementary moves.  The group-theoretic
classification of the resulting union graph uses site-permutation generation,
isolated coordinate commutators and an abelian quotient charge.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators commutatorElement IsMulCommutative

namespace D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP

abbrev Configuration (L N : ℕ) := Fin L → Fin N

def adjacentMove {L N : ℕ} (i : Fin L) (hi : i.1 + 1 < L)
    (x : Configuration L N) : Configuration L N :=
  x ∘ Equiv.swap i ⟨i.1 + 1, hi⟩

def lastSite {L : ℕ} (hL : 1 < L) : Fin L :=
  ⟨L - 1, Nat.sub_lt (Nat.zero_lt_of_lt hL) (by omega)⟩

def firstSite {L : ℕ} (hL : 1 < L) : Fin L :=
  ⟨0, Nat.zero_lt_of_lt hL⟩

def boundaryMove {L N : ℕ} (hL : 1 < L) (s : Equiv.Perm (Fin N))
    (x : Configuration L N) : Configuration L N := fun i =>
  if i = firstSite hL then s⁻¹ (x (lastSite hL))
  else if i = lastSite hL then s (x (firstSite hL))
  else x i

def moveRelation {L N : ℕ} (hL : 1 < L) (s : Equiv.Perm (Fin N))
    (x y : Configuration L N) : Prop :=
  (∃ i : Fin L, ∃ hi : i.1 + 1 < L, y = adjacentMove i hi x) ∨
    y = boundaryMove hL s x

def sector {L N : ℕ} (hL : 1 < L) (s : Equiv.Perm (Fin N))
    (x : Configuration L N) : Finset (Configuration L N) :=
  by classical exact Finset.univ.filter (fun y => Relation.EqvGen (moveRelation hL s) x y)

def branchingProbability {L N : ℕ} (hL : 1 < L)
    (s t : Equiv.Perm (Fin N)) (x y : Configuration L N) : ℚ :=
  ((sector hL s x ∩ sector hL t y).card : ℚ) / (sector hL s x).card

def overlap {L N : ℕ} (hL : 1 < L)
    (s t : Equiv.Perm (Fin N)) (x y : Configuration L N) : Prop :=
  (sector hL s x ∩ sector hL t y).Nonempty

def unionMoveRelation {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N))
    (x y : Configuration L N) : Prop :=
  moveRelation hL f x y ∨ moveRelation hL g x y

def unionConnected {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) : Prop :=
  ∀ x y, Relation.EqvGen (unionMoveRelation hL f g) x y

def sectorsOf {L N : ℕ} (hL : 1 < L) (s : Equiv.Perm (Fin N)) :
    Set (Finset (Configuration L N)) :=
  Set.range (sector hL s)

def alternatingSectorReach {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool)
    (C : Finset (Configuration L N)) : ℕ → Set (Finset (Configuration L N))
  | 0 => {C}
  | k + 1 =>
      {D | D ∈ sectorsOf hL (if start = (k % 2 == 0) then g else f) ∧
        ∃ E ∈ alternatingSectorReach hL f g start C k, (E ∩ D).Nonempty}

def switchSupport {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool)
    (C : Finset (Configuration L N)) (k : ℕ) : Set (Configuration L N) :=
  ⋃ D ∈ alternatingSectorReach hL f g start C k, (D : Set (Configuration L N))

def alternatingSupport {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool)
    (C : Finset (Configuration L N)) : ℕ → Set (Configuration L N)
  | 0 => C
  | k + 1 =>
      {x | ∃ D ∈ sectorsOf hL (if start = (k % 2 == 0) then g else f),
        x ∈ D ∧ ∃ y ∈ alternatingSupport hL f g start C k, y ∈ D}
private lemma adjacentMove_involutive {L N : ℕ} (i : Fin L) (hi : i.1 + 1 < L)
    (x : Configuration L N) : adjacentMove i hi (adjacentMove i hi x) = x := by
  funext j
  exact congrArg x (Equiv.swap_apply_self i ⟨i.1 + 1, hi⟩ j)
private lemma lastSite_ne_first {L : ℕ} (hL : 1 < L) : lastSite hL ≠ firstSite hL := by
  intro h
  have hv := congrArg Fin.val h
  simp [lastSite, firstSite] at hv
  omega
private lemma boundary_at_first {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) (x : Configuration L N) :
    boundaryMove hL s x (firstSite hL) = s⁻¹ (x (lastSite hL)) := by
  exact Fin.eq_of_val_eq rfl
private lemma boundary_at_last {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) (x : Configuration L N) :
    boundaryMove hL s x (lastSite hL) = s (x (firstSite hL)) := by
  simp [boundaryMove, lastSite_ne_first hL]
private lemma boundary_at_other {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) (x : Configuration L N) {i : Fin L}
    (hi0 : i ≠ firstSite hL) (hil : i ≠ lastSite hL) :
    boundaryMove hL s x i = x i := by
  simp [boundaryMove, hi0, hil]
private lemma boundaryMove_involutive {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) (x : Configuration L N) :
    boundaryMove hL s (boundaryMove hL s x) = x := by
  funext i
  by_cases hi0 : i = firstSite hL
  · subst i
    rw [boundary_at_first, boundary_at_last]
    simp
  · by_cases hil : i = lastSite hL
    · subst i
      rw [boundary_at_last, boundary_at_first]
      simp
    · rw [boundary_at_other hL s _ hi0 hil, boundary_at_other hL s _ hi0 hil]
private lemma moveRelation_symmetric {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) : Symmetric (moveRelation hL s) := by
  intro x y hxy
  cases hxy with
  | inl h =>
    rcases h with ⟨i, hi, h⟩
    left
    refine ⟨i, hi, ?_⟩
    rw [h]
    exact (adjacentMove_involutive i hi x).symm
  | inr h =>
    right
    rw [h]
    exact (boundaryMove_involutive hL s x).symm
private lemma sector_nonempty {L N : ℕ} (hL : 1 < L)
    (s : Equiv.Perm (Fin N)) (x : Configuration L N) :
    (sector hL s x).Nonempty := by
  classical
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.EqvGen.refl _⟩⟩
private theorem branchingProbability_pos_iff {L N : ℕ} (hL : 1 < L)
    (s t : Equiv.Perm (Fin N)) (x y : Configuration L N) :
    0 < branchingProbability hL s t x y ↔ overlap hL s t x y := by
  classical
  unfold branchingProbability overlap
  have hden : 0 < (sector hL s x).card :=
    Finset.card_pos.mpr (sector_nonempty hL s x)
  rw [div_pos_iff_of_pos_right (by exact_mod_cast hden), Nat.cast_pos, Finset.card_pos]
private theorem sector_overlap_is_positive {L N : ℕ} (hL : 1 < L)
    (s t : Equiv.Perm (Fin N)) (x y : Configuration L N) :
    overlap hL s t x y ↔ 0 < branchingProbability hL s t x y := by
  exact (branchingProbability_pos_iff hL s t x y).symm
private theorem alternatingSupport_eq_switchSupport {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool)
    (C : Finset (Configuration L N)) (k : ℕ) :
    alternatingSupport hL f g start C k = switchSupport hL f g start C k := by
  induction k with
  | zero =>
      ext x
      simp [alternatingSupport, switchSupport, alternatingSectorReach]
  | succ k ih =>
      ext x
      simp only [alternatingSupport, switchSupport, alternatingSectorReach, Set.mem_setOf_eq,
        Set.mem_iUnion]
      constructor
      · rintro ⟨D, hD, hxD, y, hy, hyD⟩
        rw [ih] at hy
        simp only [switchSupport, Set.mem_iUnion] at hy
        rcases hy with ⟨E, hE, hyE⟩
        exact ⟨D, ⟨hD, ⟨E, hE, ⟨y, Finset.mem_inter.mpr ⟨hyE, hyD⟩⟩⟩⟩, hxD⟩
      · rintro ⟨D, ⟨hD, ⟨E, hE, hinter⟩⟩, hxD⟩
        rcases hinter with ⟨y, hy⟩
        have hyE : y ∈ E := (Finset.mem_inter.mp hy).1
        have hyD : y ∈ D := (Finset.mem_inter.mp hy).2
        rw [ih]
        simp only [switchSupport, Set.mem_iUnion]
        exact ⟨D, hD, hxD, y, ⟨E, hE, hyE⟩, hyD⟩

def twistGroup {N : ℕ} (f g : Equiv.Perm (Fin N)) : Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {f, g}

def derivedTwistGroup {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.map (Subgroup.subtype (twistGroup f g)) (commutator (twistGroup f g))

def pairTwistGroup {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    Subgroup (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) :=
  Subgroup.closure {(f, f⁻¹), (g, g⁻¹)}
private instance pairPermutationMulAction {N : ℕ} :
    MulAction (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) (Fin N × Fin N) :=
  @Prod.mulAction _ _ _ _
    (MulAction.compHom (Fin N) (MonoidHom.fst _ _))
    (MulAction.compHom (Fin N) (MonoidHom.snd _ _))

def pointStabilizer {N : ℕ} (H : Subgroup (Equiv.Perm (Fin N))) (a : Fin N) :
    Subgroup (Equiv.Perm (Fin N)) :=
  H ⊓ MulAction.stabilizer (Equiv.Perm (Fin N)) a

def pointPairStabilizer {N : ℕ} (H : Subgroup (Equiv.Perm (Fin N))) (a : Fin N) :
    Subgroup (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) :=
  Subgroup.prod (pointStabilizer H a) (pointStabilizer H a)

def lTwoCriterion {N : ℕ} (f g : Equiv.Perm (Fin N)) : Prop :=
  ∀ a : Fin N,
    Nat.card (pairTwistGroup f g) =
      N ^ 2 * Nat.card
        ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a)

def lAtLeastThreeCriterion {N : ℕ} (f g : Equiv.Perm (Fin N)) : Prop :=
  MulAction.IsPretransitive (derivedTwistGroup f g) (Fin N)
private def lTwoOrbitCriterion {N : ℕ} (f g : Equiv.Perm (Fin N)) (a : Fin N) : Prop :=
  MulAction.orbit (pairTwistGroup f g) (a, a) = Set.univ

def fullSwitchingReachability {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) : Prop :=
  ∀ (start : Bool) (x target : Configuration L N),
    ∃ k : ℕ,
      target ∈ switchSupport hL f g start
        (sector hL (if start then f else g) x) k

def registeredReachabilityAnswer {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) : Prop :=
  fullSwitchingReachability hL f g ↔
    (unionConnected hL f g ∧
      (if 3 ≤ L then lAtLeastThreeCriterion f g else lTwoCriterion f g))
private theorem lTwoOrbitCriterion_iff_pretransitive {N : ℕ}
    (f g : Equiv.Perm (Fin N)) (a : Fin N) :
    lTwoOrbitCriterion f g a ↔
      MulAction.IsPretransitive (pairTwistGroup f g) (Fin N × Fin N) := by
  unfold lTwoOrbitCriterion
  exact (MulAction.isPretransitive_iff_orbit_eq_univ (a, a)).symm
private lemma mem_sector_iff {L N : ℕ} (hL : 1 < L) (s : Equiv.Perm (Fin N))
    (x y : Configuration L N) :
    y ∈ sector hL s x ↔ Relation.EqvGen (moveRelation hL s) x y := by
  classical
  simp [sector]
private lemma alternatingSupport_step {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N))
    (start : Bool) (C : Finset (Configuration L N)) (k : ℕ)
    {x y : Configuration L N} (hx : x ∈ alternatingSupport hL f g start C k)
    (hxy : Relation.EqvGen
      (moveRelation hL (if start = (k % 2 == 0) then g else f)) x y) :
    y ∈ alternatingSupport hL f g start C (k + 1) := by
  refine ⟨sector hL (if start = (k % 2 == 0) then g else f) x,
    ⟨x, rfl⟩, (mem_sector_iff _ _ _ _).mpr hxy, x, hx, ?_⟩
  exact (mem_sector_iff _ _ _ _).mpr (.refl x)
private lemma alternatingSupport_mono {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N))
    (start : Bool) (C : Finset (Configuration L N)) (k : ℕ) :
    alternatingSupport hL f g start C k ⊆ alternatingSupport hL f g start C (k + 1) := by
  intro x hx
  exact alternatingSupport_step hL f g start C k hx (.refl x)
private lemma alternatingSupport_union_step {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool) (C : Finset (Configuration L N))
    (k : ℕ) {x y : Configuration L N}
    (hx : x ∈ alternatingSupport hL f g start C k)
    (hxy : unionMoveRelation hL f g x y) :
    y ∈ alternatingSupport hL f g start C (k + 2) := by
  have hs (s : Equiv.Perm (Fin N)) (hs : s = f ∨ s = g)
      (hm : moveRelation hL s x y) :
      y ∈ alternatingSupport hL f g start C (k + 2) := by
    have hp : ((k + 1) % 2 == 0) = (!(k % 2 == 0)) := by
      by_cases hz : k % 2 = 0
      · have ho : (k + 1) % 2 = 1 := by omega
        simp [hz, ho]
      · have ho : (k + 1) % 2 = 0 := by omega
        simp [hz, ho]
    by_cases ht : s = (if start = (k % 2 == 0) then g else f)
    · exact alternatingSupport_mono hL f g start C (k + 1)
        (alternatingSupport_step hL f g start C k hx (.rel _ _ (ht ▸ hm)))
    · have ht' : s = (if start = ((k + 1) % 2 == 0) then g else f) := by
        rw [hp]
        rcases hs with rfl | rfl <;> cases start <;> cases he : (k % 2 == 0) <;>
          simp_all
      exact alternatingSupport_step hL f g start C (k + 1)
        (alternatingSupport_mono hL f g start C k hx) (.rel _ _ (ht' ▸ hm))
  exact hxy.elim (hs f (Or.inl rfl)) (hs g (Or.inr rfl))
private lemma union_path_eventually_supported {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool) (C : Finset (Configuration L N))
    {x y : Configuration L N} (hxy : Relation.EqvGen (unionMoveRelation hL f g) x y) :
    ∀ k, x ∈ alternatingSupport hL f g start C k →
      ∃ l, y ∈ alternatingSupport hL f g start C l := by
  have symm : Symmetric (unionMoveRelation hL f g) := by
    intro a b hab
    exact hab.elim (fun h => Or.inl (moveRelation_symmetric hL f h))
      (fun h => Or.inr (moveRelation_symmetric hL g h))
  letI : Std.Symm (unionMoveRelation hL f g) := ⟨fun _ _ h => symm h⟩
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen] at hxy
  induction hxy with
  | refl => exact fun k hx => ⟨k, hx⟩
  | @tail y z hpath hyz ih =>
      intro k hx
      obtain ⟨l, hy⟩ := ih k hx
      exact ⟨l + 2, alternatingSupport_union_step hL f g start C l hy hyz⟩
private lemma supported_in_union_component {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (start : Bool) (x : Configuration L N) :
    ∀ k y, y ∈ alternatingSupport hL f g start
      (sector hL (if start then f else g) x) k →
      Relation.EqvGen (unionMoveRelation hL f g) x y := by
  intro k
  induction k with
  | zero =>
      intro y hy
      have h := (mem_sector_iff _ _ _ _).mp hy
      apply Relation.EqvGen.eqvGen_mono (r := moveRelation hL (if start then f else g)) _ _ _ h
      intro a b hab
      cases start <;> simp_all [unionMoveRelation]
  | succ k ih =>
      rintro y ⟨D, ⟨z, rfl⟩, hyD, w, hw, hwD⟩
      have hzy := (mem_sector_iff _ _ _ _).mp hyD
      have hzw := (mem_sector_iff _ _ _ _).mp hwD
      have hwy := Relation.EqvGen.trans _ _ _ (.symm _ _ hzw) hzy
      refine .trans _ _ _ (ih w hw) (Relation.EqvGen.eqvGen_mono ?_ _ _ hwy)
      intro a b hab
      by_cases ht : start = (k % 2 == 0) <;> simp_all [unionMoveRelation]
private theorem fullSwitchingReachability_iff_unionConnected {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) :
    fullSwitchingReachability hL f g ↔ unionConnected hL f g := by
  constructor
  · intro h x y
    obtain ⟨k, hk⟩ := h true x y
    rw [← alternatingSupport_eq_switchSupport] at hk
    exact supported_in_union_component hL f g true x k y hk
  · intro h start x y
    obtain ⟨k, hk⟩ := union_path_eventually_supported hL f g start
      (sector hL (if start then f else g) x) (h x y) 0
      ((mem_sector_iff _ _ _ _).mpr (.refl x))
    exact ⟨k, by rwa [← alternatingSupport_eq_switchSupport]⟩


private abbrev UnionPath {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :=
  Relation.EqvGen (unionMoveRelation hL f g)
private def siteReachGroup {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :
    Subgroup (Equiv.Perm (Fin L)) := by
  letI : MulAction (Equiv.Perm (Fin L)) (Configuration L N) := arrowAction
  letI : MulAction (Equiv.Perm (Fin L))
      (Configuration L N → Quot (unionMoveRelation hL f g)) := arrowAction
  let K := MulAction.stabilizer (Equiv.Perm (Fin L)) (Quot.mk (unionMoveRelation hL f g))
  refine K.copy {p | ∀ x, UnionPath hL f g x (x ∘ p)} ?_
  ext p
  change (∀ x, UnionPath hL f g x (x ∘ p)) ↔
    (fun x => Quot.mk (unionMoveRelation hL f g) (x ∘ p)) = Quot.mk (unionMoveRelation hL f g)
  rw [funext_iff]
  exact forall_congr' fun x =>
    ⟨fun h => Quot.eqvGen_sound h.symm, fun h => (Quot.eqvGen_exact h).symm⟩
private lemma siteReachGroup_eq_top {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :
    siteReachGroup hL f g = ⊤ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  apply top_unique
  have hgen : Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤
      (siteReachGroup hL f g).toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩ x
    apply Relation.EqvGen.rel
    left; left
    exact ⟨i.castSucc, by simpa using i.isLt, rfl⟩
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hgen
  exact hgen
private lemma site_permutation_path {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N))
    (p : Equiv.Perm (Fin L)) (x : Configuration L N) :
    UnionPath hL f g x (x ∘ p) := by
  have hp : p ∈ siteReachGroup hL f g := by rw [siteReachGroup_eq_top]; trivial
  exact hp x
private def coordinateReachGroup {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :
    Subgroup (Fin L → Equiv.Perm (Fin N)) := by
  letI : MulAction (Fin L → Equiv.Perm (Fin N)) (Configuration L N) := Pi.mulAction'
  letI : MulAction (Fin L → Equiv.Perm (Fin N))
      (Configuration L N → Quot (unionMoveRelation hL f g)) := arrowAction
  let K := MulAction.stabilizer (Fin L → Equiv.Perm (Fin N))
    (Quot.mk (unionMoveRelation hL f g))
  refine K.copy {p | ∀ x, UnionPath hL f g x (fun i => p i (x i))} ?_
  ext p
  change (∀ x, UnionPath hL f g x (p • x)) ↔
    (fun x => Quot.mk (unionMoveRelation hL f g) (p⁻¹ • x)) = Quot.mk (unionMoveRelation hL f g)
  constructor
  · intro h
    funext x
    simpa only [smul_inv_smul] using Quot.eqvGen_sound (h (p⁻¹ • x))
  · intro h x
    apply Quot.eqvGen_exact
    simpa only [inv_smul_smul] using congrFun h (p • x)
private def pairedCoordinates {L N : ℕ} (i j : Fin L) (s : Equiv.Perm (Fin N)) :
    Fin L → Equiv.Perm (Fin N) :=
  Function.update (Pi.mulSingle j s⁻¹) i s
private lemma boundary_pair_path {L N : ℕ} (hL : 1 < L) (f g s : Equiv.Perm (Fin N))
    (hs : s = f ∨ s = g) (x : Configuration L N) :
    UnionPath hL f g x (fun i => pairedCoordinates (lastSite hL) (firstSite hL) s i (x i)) := by
  have hswap := site_permutation_path hL f g (Equiv.swap (lastSite hL) (firstSite hL)) x
  have hb : UnionPath hL f g
      (x ∘ Equiv.swap (lastSite hL) (firstSite hL))
      (boundaryMove hL s (x ∘ Equiv.swap (lastSite hL) (firstSite hL))) := by
    apply Relation.EqvGen.rel
    rcases hs with rfl | rfl
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inr rfl)
  have he : boundaryMove hL s (x ∘ Equiv.swap (lastSite hL) (firstSite hL)) =
      (fun i => pairedCoordinates (lastSite hL) (firstSite hL) s i (x i)) := by
    funext i
    by_cases h0 : i = firstSite hL
    · subst i
      simp [boundaryMove, pairedCoordinates, (lastSite_ne_first hL).symm]
    · by_cases hl : i = lastSite hL
      · subst i
        simp [boundaryMove, pairedCoordinates, lastSite_ne_first hL]
      · simp [boundaryMove, pairedCoordinates, h0, hl,
          Equiv.swap_apply_of_ne_of_ne hl h0]
  rw [he] at hb
  exact .trans _ _ _ hswap hb
private lemma exists_site_permutation {L : ℕ} (hL : 1 < L) (i j : Fin L) (hij : i ≠ j) :
    ∃ p : Equiv.Perm (Fin L), p i = lastSite hL ∧ p j = firstSite hL := by
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun b : Bool => if b then i else j)
    (fun b : Bool => if b then lastSite hL else firstSite hL)
    (Bool.injective_iff.mpr hij.symm)
    (Bool.injective_iff.mpr (lastSite_ne_first hL).symm)
  exact ⟨p, hp true, hp false⟩
private lemma pairedCoordinates_mem {L N : ℕ} (hL : 1 < L) (f g s : Equiv.Perm (Fin N))
    (hs : s = f ∨ s = g) (i j : Fin L) (hij : i ≠ j) :
    pairedCoordinates i j s ∈ coordinateReachGroup hL f g := by
  obtain ⟨p, hpi, hpj⟩ := exists_site_permutation hL i j hij
  intro x
  have h1 := site_permutation_path hL f g p⁻¹ x
  have h2 := boundary_pair_path hL f g s hs (x ∘ p.symm)
  have h3 := site_permutation_path hL f g p
    (fun k => pairedCoordinates (lastSite hL) (firstSite hL) s k ((x ∘ p.symm) k))
  have he : (fun k => pairedCoordinates (lastSite hL) (firstSite hL) s k
      ((x ∘ p.symm) k)) ∘ p = (fun k => pairedCoordinates i j s k (x k)) := by
    funext k
    have hpki : p k = lastSite hL ↔ k = i := by rw [← hpi]; exact p.injective.eq_iff
    have hpkj : p k = firstSite hL ↔ k = j := by rw [← hpj]; exact p.injective.eq_iff
    simp [pairedCoordinates, Function.update_apply, Pi.mulSingle_apply, hpki, hpkj]
  rw [he] at h3
  exact .trans _ _ _ h1 (.trans _ _ _ h2 h3)
private def pairCoordinateHom {L N : ℕ} (i j : Fin L) :
    (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) →*
      (Fin L → Equiv.Perm (Fin N)) :=
  MonoidHom.pi (fun k => if k = i then MonoidHom.fst _ _
    else if k = j then MonoidHom.snd _ _ else 1)
private lemma pairCoordinate_mem {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N))
    (i j : Fin L) (hij : i ≠ j) :
    pairTwistGroup f g ≤ (coordinateReachGroup hL f g).comap (pairCoordinateHom i j) := by
  have he (s : Equiv.Perm (Fin N)) :
      pairCoordinateHom i j (s, s⁻¹) = pairedCoordinates i j s := by
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairCoordinateHom, pairedCoordinates, hki, hkj, hij, hij.symm]
  apply (Subgroup.closure_le _).mpr
  intro p hp
  rcases hp with rfl | rfl
  · change pairCoordinateHom i j (f, f⁻¹) ∈ coordinateReachGroup hL f g
    rw [he]
    exact pairedCoordinates_mem hL f g f (Or.inl rfl) i j hij
  · change pairCoordinateHom i j (g, g⁻¹) ∈ coordinateReachGroup hL f g
    rw [he]
    exact pairedCoordinates_mem hL f g g (Or.inr rfl) i j hij
private lemma pairTwistGroup_le_product {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    pairTwistGroup f g ≤ (twistGroup f g).prod (twistGroup f g) := by
  apply (Subgroup.closure_le _).mpr
  have hf : f ∈ twistGroup f g := Subgroup.subset_closure (by simp)
  have hg : g ∈ twistGroup f g := Subgroup.subset_closure (by simp)
  rintro p (rfl | rfl)
  · exact ⟨hf, (twistGroup f g).inv_mem hf⟩
  · exact ⟨hg, (twistGroup f g).inv_mem hg⟩
private lemma twistGroup_le_pair_fst {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    twistGroup f g ≤ (pairTwistGroup f g).map (MonoidHom.fst _ _) := by
  apply (Subgroup.closure_le _).mpr
  rintro s (rfl | rfl)
  · exact ⟨(s, s⁻¹), Subgroup.subset_closure (by simp), rfl⟩
  · exact ⟨(s, s⁻¹), Subgroup.subset_closure (by simp), rfl⟩
private def singleCoordinateHom {L N : ℕ} (i : Fin L) :
    Equiv.Perm (Fin N) →* (Fin L → Equiv.Perm (Fin N)) :=
  MonoidHom.mulSingle (fun _ : Fin L => Equiv.Perm (Fin N)) i
private lemma three_distinct_sites {L : ℕ} (hL : 3 ≤ L) (i : Fin L) :
    ∃ j k : Fin L, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  exact ⟨j, k, hji.symm, hki.symm, hkj.symm⟩
private lemma derived_singleCoordinate_mem {L N : ℕ} (hL : 1 < L) (h3 : 3 ≤ L)
    (f g : Equiv.Perm (Fin N)) (i : Fin L) :
    derivedTwistGroup f g ≤ (coordinateReachGroup hL f g).comap (singleCoordinateHom i) := by
  rw [derivedTwistGroup, Subgroup.map_subtype_commutator]
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  obtain ⟨j, k, hij, hik, hjk⟩ := three_distinct_sites h3 i
  obtain ⟨p, hp, hpa⟩ := twistGroup_le_pair_fst f g ha
  obtain ⟨q, hq, hqb⟩ := twistGroup_le_pair_fst f g hb
  have hpc := pairCoordinate_mem hL f g i j hij hp
  have hqc := pairCoordinate_mem hL f g i k hik hq
  have hcomm := (coordinateReachGroup hL f g).mul_mem
    ((coordinateReachGroup hL f g).mul_mem
      ((coordinateReachGroup hL f g).mul_mem hpc hqc)
      ((coordinateReachGroup hL f g).inv_mem hpc))
    ((coordinateReachGroup hL f g).inv_mem hqc)
  have he : pairCoordinateHom i j p * pairCoordinateHom i k q *
      (pairCoordinateHom i j p)⁻¹ * (pairCoordinateHom i k q)⁻¹ =
      singleCoordinateHom i ⁅a, b⁆ := by
    funext t
    by_cases hi : t = i
    · subst t
      simp [pairCoordinateHom, singleCoordinateHom, commutatorElement_def, ← hpa, ← hqb]
    · by_cases hj : t = j
      · subst t
        simp [pairCoordinateHom, singleCoordinateHom, commutatorElement_def, hi, hjk]
      · by_cases hk : t = k
        · subst t
          simp [pairCoordinateHom, singleCoordinateHom, commutatorElement_def, hi, hj]
        · simp [pairCoordinateHom, singleCoordinateHom, commutatorElement_def, hi, hj, hk]
  rw [he] at hcomm
  exact hcomm
private lemma unionConnected_of_derived_transitive {L N : ℕ} (hL : 1 < L) (h3 : 3 ≤ L)
    (f g : Equiv.Perm (Fin N)) (hD : lAtLeastThreeCriterion f g) :
    unionConnected hL f g := by
  classical
  letI : MulAction.IsPretransitive (derivedTwistGroup f g) (Fin N) := hD
  intro x y
  have hu (z : Configuration L N) (i : Fin L) :
      UnionPath hL f g z (Function.update z i (y i)) := by
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (derivedTwistGroup f g) (z i) (y i)
    have h := derived_singleCoordinate_mem hL h3 f g i d.property z
    have he : (fun k => singleCoordinateHom i d.val k (z k)) = Function.update z i (y i) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp only [singleCoordinateHom, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same,
          Function.update_self]
        simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hd
      · simp [singleCoordinateHom, hk]
    rwa [he] at h
  have hfin : ∀ S : Finset (Fin L),
      UnionPath hL f g x (fun i => if i ∈ S then y i else x i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using (Relation.EqvGen.refl (r := unionMoveRelation hL f g) x)
    | @insert i S hi ih =>
        have h := hu (fun k => if k ∈ S then y k else x k) i
        have he : Function.update (fun k => if k ∈ S then y k else x k) i (y i) =
            (fun k => if k ∈ insert i S then y k else x k) := by
          funext k
          by_cases hk : k = i <;> simp [hk, Function.update_of_ne]
        rw [he] at h
        exact .trans _ _ _ ih h
  simpa using hfin Finset.univ


private lemma union_path_invariant {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) {A : Type*} (I : Configuration L N → A)
    (hm : ∀ x y, unionMoveRelation hL f g x y → I x = I y)
    {x y : Configuration L N} (hxy : Relation.EqvGen (unionMoveRelation hL f g) x y) :
    I x = I y := by
  exact Relation.EqvGen.eqvGen_le (r' := (Setoid.ker I).r) hm x y hxy
private lemma all_in_orbit_move {L N : ℕ} (hL : 1 < L)
    (H : Subgroup (Equiv.Perm (Fin N))) (a : Fin N) (s : H)
    {x y : Configuration L N} (hm : moveRelation hL s.val x y)
    (hx : ∀ i, ∃ h : H, h • a = x i) : ∀ i, ∃ h : H, h • a = y i := by
  rcases hm with ⟨i, hi, rfl⟩ | rfl
  · intro k; exact hx _
  · intro k
    by_cases h0 : k = firstSite hL
    · subst k
      obtain ⟨h, hh⟩ := hx (lastSite hL)
      refine ⟨s⁻¹ * h, ?_⟩
      rw [mul_smul, hh, boundary_at_first]
      rfl
    · by_cases hl : k = lastSite hL
      · subst k
        obtain ⟨h, hh⟩ := hx (firstSite hL)
        refine ⟨s * h, ?_⟩
        rw [mul_smul, hh, boundary_at_last]
        rfl
      · simpa [boundaryMove, h0, hl] using hx k
private lemma twist_transitive_of_unionConnected {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (hc : unionConnected hL f g) :
    MulAction.IsPretransitive (twistGroup f g) (Fin N) := by
  constructor
  intro a b
  let P (x : Configuration L N) : Prop := ∀ i, ∃ h : twistGroup f g, h • a = x i
  have hf : f ∈ twistGroup f g := Subgroup.subset_closure (by simp)
  have hg : g ∈ twistGroup f g := Subgroup.subset_closure (by simp)
  have hm (x y : Configuration L N) (hxy : unionMoveRelation hL f g x y) : P x → P y := by
    rcases hxy with h | h
    · exact all_in_orbit_move hL (twistGroup f g) a ⟨f, hf⟩ h
    · exact all_in_orbit_move hL (twistGroup f g) a ⟨g, hg⟩ h
  have hI : P (fun _ => a) = P (fun _ => b) :=
    union_path_invariant hL f g P (fun x y hxy => propext ⟨hm x y hxy, by
      intro hy
      rcases hxy with h | h
      · exact hm y x (Or.inl (moveRelation_symmetric hL f h)) hy
      · exact hm y x (Or.inr (moveRelation_symmetric hL g h)) hy⟩)
      (hc (fun _ => a) (fun _ => b))
  have hstart : P (fun _ => a) := fun _ => ⟨1, one_smul _ _⟩
  rw [hI] at hstart
  exact hstart (firstSite hL)
private def actionCharge {G X : Type*} [Group G] [MulAction G X]
    (a : X) (ht : ∀ b, ∃ h : G, h • a = b) (P : Subgroup G) [P.Normal] : X → G ⧸ P :=
  (QuotientGroup.mk' P) ∘ Function.surjInv ht
private lemma actionCharge_eval {G X : Type*} [Group G] [MulAction G X]
    (a : X) (ht : ∀ b, ∃ h : G, h • a = b) (P : Subgroup G) [P.Normal]
    (hstab : MulAction.stabilizer G a ≤ P) (h : G) :
    actionCharge a ht P (h • a) = (QuotientGroup.mk' P) h := by
  apply QuotientGroup.eq.mpr
  apply hstab
  rw [MulAction.mem_stabilizer_iff (G := G) (α := X), mul_smul]
  exact (congrArg (fun z => (Function.surjInv ht (h • a))⁻¹ • z)
    (Function.surjInv_eq ht (h • a)).symm).trans
      (inv_smul_smul (Function.surjInv ht (h • a)) a)
private lemma actionCharge_smul {G X : Type*} [Group G] [MulAction G X]
    (a : X) (ht : ∀ b, ∃ h : G, h • a = b) (P : Subgroup G) [P.Normal]
    (hstab : MulAction.stabilizer G a ≤ P) (h : G) (b : X) :
    actionCharge a ht P (h • b) = (QuotientGroup.mk' P) h * actionCharge a ht P b := by
  obtain ⟨k, rfl⟩ := ht b
  rw [← mul_smul, actionCharge_eval a ht P hstab (h * k),
    actionCharge_eval a ht P hstab k, map_mul]
private lemma charge_product_move {L N : ℕ} (hL : 1 < L)
    {A : Type*} [CommGroup A] (χ : Fin N → A) (s : Equiv.Perm (Fin N)) (t : A)
    (hχ : ∀ b, χ (s b) = t * χ b) {x y : Configuration L N}
    (hm : moveRelation hL s x y) : (∏ i, χ (x i)) = ∏ i, χ (y i) := by
  classical
  rcases hm with ⟨i, hi, rfl⟩ | rfl
  · exact (Equiv.prod_comp (Equiv.swap i ⟨i.val + 1, hi⟩) (fun i => χ (x i))).symm
  · have hinv (b : Fin N) : χ (s⁻¹ b) = t⁻¹ * χ b := by
      have h := hχ (s⁻¹ b)
      simpa using (congrArg (fun z => t⁻¹ * z) h).symm
    have he (i : Fin L) : χ (boundaryMove hL s x i) =
        ((if i = firstSite hL then t⁻¹ else 1) * (if i = lastSite hL then t else 1)) *
          χ (x (Equiv.swap (firstSite hL) (lastSite hL) i)) := by
      by_cases h0 : i = firstSite hL
      · subst i
        simp only [boundary_at_first, ite_true, (lastSite_ne_first hL).symm, ite_false,
          mul_one, Equiv.swap_apply_left]
        exact hinv _
      · by_cases hl : i = lastSite hL
        · subst i; simp [boundaryMove, lastSite_ne_first hL, hχ]
        · simp [boundaryMove, h0, hl, Equiv.swap_apply_of_ne_of_ne h0 hl]
    simp_rw [he]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, inv_mul_cancel, one_mul]
    exact (Equiv.prod_comp (Equiv.swap (firstSite hL) (lastSite hL)) (fun i => χ (x i))).symm
private lemma derived_transitive_of_unionConnected {L N : ℕ} (hL : 1 < L)
    (f g : Equiv.Perm (Fin N)) (hc : unionConnected hL f g) :
    lAtLeastThreeCriterion f g := by
  classical
  have ht := twist_transitive_of_unionConnected hL f g hc
  letI : MulAction.IsPretransitive (twistGroup f g) (Fin N) := ht
  constructor
  intro a b
  let H := twistGroup f g
  let P : Subgroup H := commutator H ⊔ MulAction.stabilizer H a
  letI : P.Normal := Subgroup.Normal.of_commutator_le H (show commutator H ≤ P from le_sup_left)
  letI : IsMulCommutative (H ⧸ P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_sup_left
  have hbase : ∀ z : Fin N, ∃ h : H, h • a = z :=
    fun z => MulAction.exists_smul_eq H a z
  let χ := actionCharge a hbase P
  have hstab : MulAction.stabilizer H a ≤ P := le_sup_right
  have hχa : χ a = 1 := by
    simpa using actionCharge_eval a hbase P hstab 1
  have hf : f ∈ H := Subgroup.subset_closure (by simp [H, twistGroup])
  have hg : g ∈ H := Subgroup.subset_closure (by simp [H, twistGroup])
  have hinv : (∏ i, χ ((fun _ : Fin L => a) i)) =
      ∏ i, χ ((Function.update (fun _ : Fin L => a) (firstSite hL) b) i) := by
    apply union_path_invariant hL f g (fun x => ∏ i, χ (x i)) _
      (hc (fun _ => a) (Function.update (fun _ => a) (firstSite hL) b))
    intro x y hm
    rcases hm with hm | hm
    · exact charge_product_move hL χ f ((QuotientGroup.mk' P) ⟨f, hf⟩)
        (actionCharge_smul a hbase P hstab ⟨f, hf⟩) hm
    · exact charge_product_move hL χ g ((QuotientGroup.mk' P) ⟨g, hg⟩)
        (actionCharge_smul a hbase P hstab ⟨g, hg⟩) hm
  have hχb : χ b = 1 := by
    simp only [Function.update_apply] at hinv
    simp_rw [apply_ite χ] at hinv
    simpa [hχa] using hinv.symm
  obtain ⟨h, hh⟩ := hbase b
  have hhP : h ∈ P := by
    apply (QuotientGroup.eq_one_iff h).mp
    change (QuotientGroup.mk' P) h = 1
    rw [← actionCharge_eval a hbase P hstab h, hh]
    exact hχb
  obtain ⟨d, hd, s, hs, hds⟩ := Subgroup.mem_sup_of_normal_left.mp hhP
  have hs' : s • a = a := hs
  have hda : d • a = b := by
    rw [← hs', ← mul_smul, hds, hh]
  refine ⟨⟨d.val, ?_⟩, ?_⟩
  · exact ⟨d, hd, rfl⟩
  · exact hda


private def twoSiteEquiv {N : ℕ} : Configuration 2 N ≃ Fin N × Fin N :=
  (finTwoArrowEquiv (Fin N)).trans (Equiv.prodComm _ _)
private def flipPairHom {N : ℕ} :
    (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) →*
      (Equiv.Perm (Fin N) × Equiv.Perm (Fin N)) :=
  MulEquiv.prodComm.toMonoidHom
private lemma pair_flip_mem {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    pairTwistGroup f g ≤ (pairTwistGroup f g).comap flipPairHom := by
  apply (Subgroup.closure_le _).mpr
  rintro p (rfl | rfl)
  · change (f⁻¹, f) ∈ pairTwistGroup f g
    simpa using (pairTwistGroup f g).inv_mem
      (Subgroup.subset_closure (by simp) : (f, f⁻¹) ∈ pairTwistGroup f g)
  · change (g⁻¹, g) ∈ pairTwistGroup f g
    simpa using (pairTwistGroup f g).inv_mem
      (Subgroup.subset_closure (by simp) : (g, g⁻¹) ∈ pairTwistGroup f g)
private lemma pair_orbit_swap {N : ℕ} (f g : Equiv.Perm (Fin N)) (a : Fin N)
    {y : Fin N × Fin N} (hy : y ∈ MulAction.orbit (pairTwistGroup f g) (a, a)) :
    y.swap ∈ MulAction.orbit (pairTwistGroup f g) (a, a) := by
  obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hy
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨⟨flipPairHom p.val, pair_flip_mem f g p.property⟩, ?_⟩
  exact congrArg Prod.swap hp
private lemma twoSite_move_orbit {N : ℕ} (f g s : Equiv.Perm (Fin N))
    (hs : s = f ∨ s = g) (a : Fin N) {x y : Configuration 2 N}
    (hm : moveRelation (by decide) s x y)
    (hx : twoSiteEquiv x ∈ MulAction.orbit (pairTwistGroup f g) (a, a)) :
    twoSiteEquiv y ∈ MulAction.orbit (pairTwistGroup f g) (a, a) := by
  rcases hm with ⟨i, hi, rfl⟩ | rfl
  · have hi0 : i = 0 := Fin.ext (by omega)
    subst i
    have he : twoSiteEquiv (adjacentMove 0 hi x) = (twoSiteEquiv x).swap := by
      apply Prod.ext <;> simp [twoSiteEquiv, adjacentMove, finTwoArrowEquiv]
    rw [he]
    exact pair_orbit_swap f g a hx
  · have hsK : (s, s⁻¹) ∈ pairTwistGroup f g := by
      rcases hs with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp (pair_orbit_swap f g a hx)
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨(s, s⁻¹), hsK⟩ * p, ?_⟩
    rw [mul_smul, hp]
    rfl
private lemma unionConnected_two_iff_pair_pretransitive {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    unionConnected (L := 2) (by decide) f g ↔
      MulAction.IsPretransitive (pairTwistGroup f g) (Fin N × Fin N) := by
  classical
  constructor
  · intro hc
    by_cases hn : Nonempty (Fin N)
    · let a := hn.some
      apply (lTwoOrbitCriterion_iff_pretransitive f g a).mp
      apply Set.eq_univ_of_forall
      intro b
      let P (x : Configuration 2 N) : Prop :=
        twoSiteEquiv x ∈ MulAction.orbit (pairTwistGroup f g) (a, a)
      have hm (x y : Configuration 2 N) (hxy : unionMoveRelation (by decide) f g x y) :
          P x → P y := by
        rcases hxy with h | h
        · exact twoSite_move_orbit f g f (Or.inl rfl) a h
        · exact twoSite_move_orbit f g g (Or.inr rfl) a h
      have he' : ∀ x y, Relation.EqvGen (unionMoveRelation (by decide) f g) x y → (P x ↔ P y) := by
        intro x y hpath
        induction hpath with
        | rel x y hxy =>
            refine ⟨hm x y hxy, ?_⟩
            rcases hxy with h | h
            · exact hm y x (Or.inl (moveRelation_symmetric (by decide) f h))
            · exact hm y x (Or.inr (moveRelation_symmetric (by decide) g h))
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      have ha : P (fun _ => a) := MulAction.mem_orbit_self (a, a)
      simpa [P] using (he' (fun _ => a) (twoSiteEquiv.symm b) (hc _ _)).mp ha
    · constructor
      intro x y
      exact (hn ⟨x.1⟩).elim
  · intro ht x y
    letI := ht
    obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (pairTwistGroup f g)
      (twoSiteEquiv x) (twoSiteEquiv y)
    simp only [MulAction.subgroup_smul_def] at hp
    change (p.val.1 (x 1), p.val.2 (x 0)) = (y 1, y 0) at hp
    have h := pairCoordinate_mem (by decide) f g (1 : Fin 2) 0 (by decide) p.property x
    have he : (fun i => pairCoordinateHom (1 : Fin 2) 0 p.val i (x i)) = y := by
      funext i
      fin_cases i
      · simpa [pairCoordinateHom, twoSiteEquiv, finTwoArrowEquiv] using congrArg Prod.snd hp
      · simpa [pairCoordinateHom, twoSiteEquiv, finTwoArrowEquiv] using congrArg Prod.fst hp
    rwa [he] at h
private def pairStabilizerEquiv {N : ℕ} (f g : Equiv.Perm (Fin N)) (a : Fin N) :
    MulAction.stabilizer (pairTwistGroup f g) (a, a) ≃
      ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a) := by
  let T := pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a
  have he : MulAction.stabilizer (pairTwistGroup f g) (a, a) =
      T.subgroupOf (pairTwistGroup f g) := by
    ext p
    have hpH := pairTwistGroup_le_product f g p.property
    change (p.val.1 a, p.val.2 a) = (a, a) ↔
      p.val ∈ pairTwistGroup f g ∧
        (p.val.1 ∈ twistGroup f g ∧ p.val.1 a = a) ∧
        (p.val.2 ∈ twistGroup f g ∧ p.val.2 a = a)
    rw [Prod.mk.injEq]
    exact ⟨fun h => ⟨p.property, ⟨hpH.1, h.1⟩, ⟨hpH.2, h.2⟩⟩,
      fun h => ⟨h.2.1.2, h.2.2.2⟩⟩
  exact ((MulEquiv.subgroupCongr he).trans
    (Subgroup.subgroupOfEquivOfLe (show T ≤ pairTwistGroup f g from inf_le_left))).toEquiv
private lemma lTwoCriterion_iff_pair_pretransitive {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    lTwoCriterion f g ↔ MulAction.IsPretransitive (pairTwistGroup f g) (Fin N × Fin N) := by
  classical
  have hcard (a : Fin N) : Nat.card (MulAction.orbit (pairTwistGroup f g) (a, a)) *
      Nat.card ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a) =
      Nat.card (pairTwistGroup f g) := by
    rw [← Nat.card_congr (pairStabilizerEquiv f g a)]
    letI := Fintype.ofFinite (MulAction.orbit (pairTwistGroup f g) (a, a))
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (pairTwistGroup f g) (a, a)
  have hiff (a : Fin N) :
      Nat.card (pairTwistGroup f g) = N ^ 2 *
        Nat.card ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a) ↔
      lTwoOrbitCriterion f g a := by
    rw [lTwoOrbitCriterion, Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq,
      Nat.card_prod, Nat.card_fin, ← hcard a]
    have hpos : 0 < Nat.card
        ↥(pairTwistGroup f g ⊓ pointPairStabilizer (twistGroup f g) a) :=
      Nat.card_pos
    rw [Nat.mul_right_cancel_iff hpos]
    simp [pow_two]
  constructor
  · intro hc
    by_cases hn : Nonempty (Fin N)
    · exact (lTwoOrbitCriterion_iff_pretransitive f g hn.some).mp ((hiff hn.some).mp (hc hn.some))
    · constructor; intro x y; exact (hn ⟨x.1⟩).elim
  · intro ht a
    exact (hiff a).mpr ((lTwoOrbitCriterion_iff_pretransitive f g a).mpr ht)
private theorem unionConnected_two_iff_lTwoCriterion {N : ℕ} (f g : Equiv.Perm (Fin N)) :
    unionConnected (L := 2) (by decide) f g ↔ lTwoCriterion f g :=
  (unionConnected_two_iff_pair_pretransitive f g).trans
    (lTwoCriterion_iff_pair_pretransitive f g).symm
private theorem unionConnected_iff_lAtLeastThreeCriterion {L N : ℕ}
    (hL : 1 < L) (h3 : 3 ≤ L) (f g : Equiv.Perm (Fin N)) :
    unionConnected hL f g ↔ lAtLeastThreeCriterion f g :=
  ⟨derived_transitive_of_unionConnected hL f g,
    unionConnected_of_derived_transitive hL h3 f g⟩

/-- The full classification, the equivalent group criterion, and the exact
sector-kernel positivity and alternating-support identifications. -/
theorem result {L N : ℕ} (hL : 1 < L) (f g : Equiv.Perm (Fin N)) :
    registeredReachabilityAnswer hL f g ∧
    ((3 ≤ L → (unionConnected hL f g ↔ lAtLeastThreeCriterion f g)) ∧
      (L = 2 → (unionConnected hL f g ↔ lTwoCriterion f g))) ∧
    (∀ (s t : Equiv.Perm (Fin N)) (x y : Configuration L N),
      overlap hL s t x y ↔ 0 < branchingProbability hL s t x y) ∧
    (∀ (start : Bool) (C : Finset (Configuration L N)) (k : ℕ),
      alternatingSupport hL f g start C k = switchSupport hL f g start C k) := by
  have h3 (h : 3 ≤ L) : unionConnected hL f g ↔ lAtLeastThreeCriterion f g :=
    unionConnected_iff_lAtLeastThreeCriterion hL h f g
  have h2 (h : L = 2) : unionConnected hL f g ↔ lTwoCriterion f g := by
    subst L
    exact unionConnected_two_iff_lTwoCriterion f g
  refine ⟨?_, ⟨h3, h2⟩, sector_overlap_is_positive hL, alternatingSupport_eq_switchSupport hL f g⟩
  unfold registeredReachabilityAnswer
  rw [fullSwitchingReachability_iff_unionConnected]
  refine ⟨fun hc => ⟨hc, ?_⟩, And.left⟩
  split_ifs with h
  · exact (h3 h).mp hc
  · exact (h2 (by omega)).mp hc

end D5.S3.StatisticalMechanics.ParticleProcesses.SwitchedTwistedSSEP
