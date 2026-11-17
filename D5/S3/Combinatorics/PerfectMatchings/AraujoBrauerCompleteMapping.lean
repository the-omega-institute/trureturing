/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: open-problem-resolution (#23706; Proved)
escape_witness: none (settling result)
proof_shape: content — unit_coordinates_full, brauer_small_no_complete, partial_small_no_complete, brauer_rank_transversal, partial_brauer_rank_transversal, brauer_factor_all, partial_factor_all, brauer_large_complete, partial_large_complete, result
proof_shape: bind-only — choose_two_mod_two, choose_three_mod_two, rank_two_odd_index_degrees, rank_three_odd_index_degrees, half_diagram_card, half_diagram_odd_iff, brauer_rank_two_odd_index, brauer_rank_three_odd_index, PartialHalfDiagram, partialHalfPermutation, partialHalfPermutation_involutive, partialHalfMarked, partialHalfMarkedEquiv, involutionRelabelEquiv, partialHalfDiagramEquiv, partial_half_index_card, partial_half_index_even, partial_rank_two_index_even, partial_rank_three_index_even, involution_no_fixed_even, brauer_half_rank_admissible, fullHalf, fullDiagram, fullDiagram_one_partition, fullDiagram_fixed_point_free, coordinates_full_exists, coordinate_units_perm, source_identity_value, partition_coordinates_units, brauer_units_perm, partial_units_perm, reesTransversal_realize, complete_mapping_of_fibre_transversals, upperOne, lowerOne, relation_one, product_cross_one, partition_product_one, partial_one_complete, partition_one_cases, brauer_one_val_top, brauerOneSubsingleton, brauer_one_complete, claim
Direct frozen dependencies (declaration statement_id):
D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping sha256:feb39c68be69503661ae3a788bf2232ca9855f0eaebeaa2ddd409e15b0143e47
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpointPairing sha256:d5fe3010047acb473686bcb77f6a2d93e8abda0a4b57e07f73cd492d884645bb
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_fixed_point_free sha256:f38f799a458169dd8462c2f2d261dd3b31ab484d67cf3072fc90e32441e69122
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_involutive sha256:68a971affeadeb943cd77ab25c00a899390e1744f4dfd8ebba1ee658748ebd3b
D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle sha256:80531d01c5f8e8e12fe05303348e4bb896d99ae17e8b09fcabf422650c76dbe1
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Connected sha256:6d8b0931bcb5ff204447a86b31378e1915c6cc1d8fca5b690ecfbafce8be9e46
D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits sha256:7ad1cdbc41eb6395cdc5d770c9601e3a8cad541996c47297f2c2a9207e7a4cad
D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution sha256:6a2fd619f7f0c220bed4d3b853cca9527379a8bd42cefa9403ca65d4b3210aac
D5.S3.Zeros.Convolution.PerfectMatchingCount.card_fixedPointFreeInvolution_mul sha256:f668778ce789801ae29ef9f459aca650eb978ac4b6ca4160af5447a4367a38a9
D5.S3.Zeros.Convolution.PerfectMatchingCount.instFintypeFixedPointFreeInvolution sha256:662e2e6ff37d64412b2e0ed0ce1cccc25fbfa080efcb06596f49226b5ef90dbc
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/


import D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.LibrarySearch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Lucas
import D5.S3.Zeros.Convolution.PerfectMatchingCount
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
import D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation
import D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCompleteMapping

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

private theorem choose_two_mod_two (n : ℕ) : n.choose 2 % 2 = n / 2 % 2 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := n) (k := 2) (p := 2)
  simpa [Nat.ModEq] using h

private theorem choose_three_mod_two (n : ℕ) :
    n.choose 3 % 2 = (n % 2) * (n / 2 % 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := n) (k := 3) (p := 2)
  have h₂ : n % 2 * (n / 2) % 2 = n % 2 * (n / 2 % 2) := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h₀ | h₁
    · simp [h₀]
    · simp [h₁]
  simpa [Nat.ModEq,h₂] using h

private theorem rank_two_odd_index_degrees (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    Odd (n.choose 2) ↔ ∃ k, n = 6 + 4*k := by
  rw [Nat.odd_iff,choose_two_mod_two]
  constructor
  · intro h
    refine ⟨n / 4 - 1,?_⟩
    omega
  · rintro ⟨k,rfl⟩
    omega

private theorem rank_three_odd_index_degrees (n : ℕ) (hn : 5 ≤ n) (he : n % 2 = 1) :
    Odd (n.choose 3) ↔ ∃ k, n = 7 + 4*k := by
  rw [Nat.odd_iff,choose_three_mod_two,he,one_mul]
  constructor
  · intro h
    refine ⟨n / 4 - 1,?_⟩
    omega
  · rintro ⟨k,rfl⟩
    omega


private theorem half_diagram_card (n r : ℕ) :
    Fintype.card (HalfDiagram n r) =
      n.choose r * Fintype.card (FixedPointFreeInvolution (Fin (n-r))) := by
  rw [Fintype.card_congr (halfDiagramEquiv n r),Fintype.card_prod]
  congr 1
  simp [ThroughSets]

private theorem half_diagram_odd_iff {n r : ℕ} (he : Even (n-r)) :
    Odd (Fintype.card (HalfDiagram n r)) ↔ Odd (n.choose r) := by
  obtain ⟨h,hh⟩ := he
  have hf : Odd (Fintype.card (FixedPointFreeInvolution (Fin (n-r)))) :=
    card_matching_fibre_odd h (by simpa only [Fintype.card_fin,two_mul] using hh)
  rw [half_diagram_card,Nat.odd_mul]
  exact and_iff_left hf

private theorem brauer_rank_two_odd_index {n : ℕ} (hn : 4 ≤ n) (he : n % 2 = 0) :
    Odd (Fintype.card (HalfDiagram n 2)) ↔ ∃ k, n = 6+4*k := by
  have hd : Even (n-2) := by rw [Nat.even_iff]; omega
  rw [half_diagram_odd_iff hd]
  exact rank_two_odd_index_degrees n hn he

private theorem brauer_rank_three_odd_index {n : ℕ} (hn : 5 ≤ n) (he : n % 2 = 1) :
    Odd (Fintype.card (HalfDiagram n 3)) ↔ ∃ k, n = 7+4*k := by
  have hd : Even (n-3) := by rw [Nat.even_iff]; omega
  rw [half_diagram_odd_iff hd]
  exact rank_three_odd_index_degrees n hn he

private abbrev PartialHalfDiagram (n r : ℕ) :=
  (T : ThroughSets n r) × {p : Equiv.Perm {x : Fin n // x ∉ T.val} // Function.Involutive p}

private noncomputable def partialHalfPermutation {n r : ℕ} (D : PartialHalfDiagram n r) :
    Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr (Equiv.refl {x : Fin n // x ∈ D.1.val}) D.2.val

private theorem partialHalfPermutation_involutive {n r : ℕ} (D : PartialHalfDiagram n r) :
    Function.Involutive (partialHalfPermutation D) := by
  classical
  intro x
  by_cases hx : x ∈ D.1.val
  · have h : partialHalfPermutation D x = x := Equiv.Perm.subtypeCongr.left_apply _ _ hx
    rw [h,h]
  · rw [show partialHalfPermutation D x = D.2.val ⟨x,hx⟩ from
      Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rw [show partialHalfPermutation D (D.2.val ⟨x,hx⟩) = D.2.val (D.2.val ⟨x,hx⟩) from
      Equiv.Perm.subtypeCongr.right_apply _ _ (D.2.val ⟨x,hx⟩).property]
    exact congrArg Subtype.val (D.2.property ⟨x,hx⟩)

private noncomputable def partialHalfMarked {n r : ℕ} (D : PartialHalfDiagram n r) :
    RankedHalf (Fin n) r := by
  classical
  let H : MarkedHalf (Fin n) := {
    through := {x | x ∈ D.1.val}
    mate := partialHalfPermutation D
    involutive := partialHalfPermutation_involutive D
    fixes := fun x hx => Equiv.Perm.subtypeCongr.left_apply _ _ hx }
  refine ⟨H,?_⟩
  let e : H.through ≃ Fin r := (D.1.val.orderIsoOfFin D.1.property).toEquiv.symm
  simpa only [Nat.card_fin] using Nat.card_congr e

private noncomputable def partialHalfMarkedEquiv (n r : ℕ) :
    PartialHalfDiagram n r ≃ RankedHalf (Fin n) r := by
  classical
  apply Equiv.ofBijective partialHalfMarked
  constructor
  · rintro ⟨T,p⟩ ⟨U,q⟩ he
    have hv : (partialHalfMarked ⟨T,p⟩).val = (partialHalfMarked ⟨U,q⟩).val := congrArg Subtype.val he
    have ht : T = U := by
      apply Subtype.ext
      apply Finset.coe_injective
      exact congrArg MarkedHalf.through hv
    subst U
    congr 1
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hm := congrArg (fun H : MarkedHalf (Fin n) => H.mate x.val) hv
    simpa only [partialHalfMarked,partialHalfPermutation,
      Equiv.Perm.subtypeCongr.right_apply _ _ x.property] using hm
  · intro H
    let T : ThroughSets n r := ⟨H.val.through.toFinset,by
      simpa only [Set.toFinset_card,Nat.card_eq_fintype_card] using H.property⟩
    have hn (x : {x : Fin n // x ∉ T.val}) : H.val.mate x.val ∉ T.val := by
      have hx : x.val ∉ H.val.through := by simpa [T] using x.property
      have hm := (half_mate_mem H.val x.val).not.mpr hx
      simpa [T] using hm
    let p : Equiv.Perm {x : Fin n // x ∉ T.val} :=
      ⟨fun x => ⟨H.val.mate x,hn x⟩,fun x => ⟨H.val.mate x,hn x⟩,
        fun x => Subtype.ext (H.val.involutive x),fun x => Subtype.ext (H.val.involutive x)⟩
    have hp : Function.Involutive p := fun x => Subtype.ext (H.val.involutive x)
    refine ⟨⟨T,⟨p,hp⟩⟩,?_⟩
    apply Subtype.ext
    change (partialHalfMarked ⟨T,⟨p,hp⟩⟩).val = H.val
    apply markedHalf_ext
    · ext x
      simp [partialHalfMarked,T]
    · apply Equiv.ext
      intro x
      by_cases hx : x ∈ H.val.through
      · have ht : x ∈ T.val := by simpa [T] using hx
        exact (Equiv.Perm.subtypeCongr.left_apply _ _ ht).trans (H.val.fixes x hx).symm
      · have ht : x ∉ T.val := by simpa [T] using hx
        exact Equiv.Perm.subtypeCongr.right_apply _ _ ht

private noncomputable def involutionRelabelEquiv {X Y : Type} (e : X ≃ Y) :
    {p : Equiv.Perm X // Function.Involutive p} ≃ {p : Equiv.Perm Y // Function.Involutive p} where
  toFun p := ⟨(e.symm.trans p.val).trans e,by
    intro y
    change e (p.val (e.symm (e (p.val (e.symm y))))) = y
    rw [e.symm_apply_apply,p.property,e.apply_symm_apply]⟩
  invFun p := ⟨(e.trans p.val).trans e.symm,by
    intro x
    change e.symm (p.val (e (e.symm (p.val (e x))))) = x
    rw [e.apply_symm_apply,p.property,e.symm_apply_apply]⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp
  right_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp

private noncomputable def partialHalfDiagramEquiv (n r : ℕ) :
    PartialHalfDiagram n r ≃ ThroughSets n r × {p : Equiv.Perm (Fin (n-r)) // Function.Involutive p} :=
  (Equiv.sigmaCongrRight fun T => involutionRelabelEquiv
    (Fintype.equivOfCardEq (by rw [complement_card T,Fintype.card_fin]))).trans
      (Equiv.sigmaEquivProd _ _)

private theorem partial_half_index_card (n r : ℕ) :
    Nat.card (RankedHalf (Fin n) r) =
      n.choose r * Nat.card ({p : Equiv.Perm (Fin (n-r)) // Function.Involutive p}) := by
  rw [← Nat.card_congr (partialHalfMarkedEquiv n r),Nat.card_congr (partialHalfDiagramEquiv n r),
    Nat.card_prod]
  congr 1
  simp [ThroughSets,Nat.card_eq_fintype_card]

private theorem partial_half_index_even {n r : ℕ} (h : 2 ≤ n-r) :
    Even (Nat.card (RankedHalf (Fin n) r)) := by
  rw [partial_half_index_card]
  exact (partial_matching_card_even (X := Fin (n-r)) (by simpa using h)).mul_left _

private theorem partial_rank_two_index_even {n : ℕ} (hn : 4 ≤ n) :
    Even (Nat.card (RankedHalf (Fin n) 2)) :=
  partial_half_index_even (by omega)

private theorem partial_rank_three_index_even {n : ℕ} (hn : 4 ≤ n) :
    Even (Nat.card (RankedHalf (Fin n) 3)) := by
  by_cases he : n = 4
  · subst n
    rw [partial_half_index_card]
    have hc : Nat.card ({p : Equiv.Perm (Fin 1) // Function.Involutive p}) = 1 := by
      letI : Unique ({p : Equiv.Perm (Fin 1) // Function.Involutive p}) := {
        default := ⟨1,by intro x; rfl⟩
        uniq := fun x => Subsingleton.elim _ _ }
      exact Nat.card_unique
    change Even (4 * Nat.card ({p : Equiv.Perm (Fin 1) // Function.Involutive p}))
    rw [hc]
    exact ⟨2,rfl⟩
  · exact partial_half_index_even (by omega)

private theorem involution_no_fixed_even {X : Type} [Fintype X]
    (p : Equiv.Perm X) (hp : Function.Involutive p) (hn : ∀ x, p x ≠ x) :
    Even (Fintype.card X) := by
  classical
  let f : Function.End X := fun x => p x
  have h := involution_card_mod_two f hp
  rw [← Fintype.card_eq_nat_card,← Fintype.card_eq_nat_card] at h
  letI : IsEmpty (Function.fixedPoints f) := ⟨fun x => hn x x.property⟩
  have h0 : Fintype.card (Function.fixedPoints f) = 0 := Fintype.card_of_isEmpty
  rw [h0] at h
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp h)

private theorem brauer_half_rank_admissible {n r : ℕ} (D : HalfDiagram n r) :
    r ≤ n ∧ Even (n-r) := by
  constructor
  · simpa only [D.1.property,Fintype.card_fin] using Finset.card_le_univ D.1.val
  · simpa only [complement_card D.1] using
      involution_no_fixed_even D.2.val D.2.property.1 D.2.property.2

open Equiv
open scoped BigOperators
open D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation
open D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
open D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

private noncomputable def fullHalf (n : ℕ) : RankedHalf (Fin n) n :=
  ⟨⟨Set.univ,1,(fun x => rfl),(fun x _ => rfl)⟩,by simp⟩

private noncomputable def fullDiagram {n : ℕ} (g : Equiv.Perm (Fin n)) : DiagramCoordinates (Fin n) :=
  rankedDiagram (fullHalf n) g (fullHalf n)

private theorem fullDiagram_one_partition (n : ℕ) :
    coordinatePartition (fullDiagram (1 : Equiv.Perm (Fin n))) = identityPartition n := by
  ext x y
  rcases x with ⟨b,i⟩
  rcases y with ⟨c,j⟩
  change ((b,i) = (c,j) ∨ coordinatePerm (fullDiagram 1) (b,i) = (c,j)) ↔ i = j
  cases b <;> cases c <;>
    simp [coordinatePerm_apply,coordinateMate,fullDiagram,rankedDiagram,fullHalf,Equiv.Perm.one_def]

private theorem fullDiagram_fixed_point_free {n : ℕ} (g : Equiv.Perm (Fin n)) :
    ∀ x, coordinatePerm (fullDiagram g) x ≠ x := by
  apply (coordinate_fixed_point_free_iff _).mpr
  constructor <;> intro x hx <;> exact (hx (Set.mem_univ x)).elim

private theorem coordinates_full_exists {n : ℕ} (d : DiagramCoordinates (Fin n))
    (hu : ∀ x, x ∈ d.upper.through) (hl : ∀ x, x ∈ d.lower.through) :
    ∃ g : Equiv.Perm (Fin n), d = fullDiagram g := by
  have hU : d.upper = (fullHalf n).val := by
    apply markedHalf_ext (Set.eq_univ_of_forall hu)
    apply Equiv.ext
    intro x
    exact d.upper.fixes x (hu x)
  have hL : d.lower = (fullHalf n).val := by
    apply markedHalf_ext (Set.eq_univ_of_forall hl)
    apply Equiv.ext
    intro x
    exact d.lower.fixes x (hl x)
  have hr : diagramRank d = n := by
    change Nat.card d.upper.through = n
    rw [hU]
    exact (fullHalf n).property
  obtain ⟨⟨A,g,D⟩,he⟩ := (rankedCoordinatesEquiv (Fin n) n).surjective ⟨d,hr⟩
  have hh : rankedDiagram A g D = d := congrArg Subtype.val he
  have hA : A = fullHalf n := Subtype.ext ((congrArg DiagramCoordinates.upper hh).trans hU)
  have hD : D = fullHalf n := Subtype.ext ((congrArg DiagramCoordinates.lower hh).trans hL)
  refine ⟨g,?_⟩
  rw [hA,hD] at hh
  exact hh.symm

private theorem unit_coordinates_full {M : Type} [Monoid M] {n : ℕ}
    (c : M → DiagramCoordinates (Fin n))
    (cm : ∀ x y, c (x*y) = coordinateMul (c x) (c y))
    (c1 : c 1 = fullDiagram (1 : Equiv.Perm (Fin n))) (u : Mˣ) :
    ∃ g : Equiv.Perm (Fin n), c (u : M) = fullDiagram g := by
  have hp : coordinateMul (c (u : M)) (c (↑(u⁻¹) : M)) = fullDiagram 1 :=
    (cm _ _).symm.trans ((congrArg c u.val_inv).trans c1)
  have hq : coordinateMul (c (↑(u⁻¹) : M)) (c (u : M)) = fullDiagram 1 :=
    (cm _ _).symm.trans ((congrArg c u.inv_val).trans c1)
  have hu := coordinate_product_upper_subset (c (u : M)) (c (↑(u⁻¹) : M))
    (fullDiagram 1) ((coordinateMul_spec _ _).trans (congrArg coordinatePartition hp))
  have hl := coordinate_product_lower_subset (c (↑(u⁻¹) : M)) (c (u : M))
    (fullDiagram 1) ((coordinateMul_spec _ _).trans (congrArg coordinatePartition hq))
  exact coordinates_full_exists _ (fun x => hu (Set.mem_univ x)) (fun x => hl (Set.mem_univ x))

private noncomputable def coordinate_units_perm {M : Type} [Monoid M] {n : ℕ}
    (c : M → DiagramCoordinates (Fin n)) (ci : Function.Injective c)
    (cm : ∀ x y, c (x*y) = coordinateMul (c x) (c y))
    (c1 : c 1 = fullDiagram (1 : Equiv.Perm (Fin n)))
    (cs : ∀ g : Equiv.Perm (Fin n), ∃ x, c x = fullDiagram g) :
    Mˣ ≃* Equiv.Perm (Fin n) := by
  classical
  let f : Equiv.Perm (Fin n) → M := fun g => Classical.choose (cs g)
  have hf : ∀ g, c (f g) = fullDiagram g := fun g => Classical.choose_spec (cs g)
  let h : Equiv.Perm (Fin n) →* M := {
    toFun := f
    map_one' := ci ((hf 1).trans c1.symm)
    map_mul' := by
      intro g h
      apply ci
      rw [hf,cm,hf,hf]
      exact (rankedDiagram_mul (fullHalf n) (fullHalf n) (fullHalf n) g h).symm }
  let fU : Equiv.Perm (Fin n) →* Mˣ := (Units.map h).comp toUnits.toMonoidHom
  have hi : Function.Injective fU := by
    intro g h he
    have hh : f g = f h := congrArg (fun u : Mˣ => (u : M)) he
    exact rankedDiagram_group_injective (fullHalf n) (fullHalf n)
      ((hf g).symm.trans ((congrArg c hh).trans (hf h)))
  have hs : Function.Surjective fU := by
    intro u
    obtain ⟨g,hg⟩ := unit_coordinates_full c cm c1 u
    refine ⟨g,Units.ext ?_⟩
    change f g = (u : M)
    exact ci ((hf g).trans hg.symm)
  exact (MulEquiv.ofBijective fU ⟨hi,hs⟩).symm

private theorem source_identity_value {M : Type} [Monoid M] {n : ℕ}
    (v : M → (Setoid (Bool × Fin n)))
    (hm : ∀ x y, v (x*y) = partitionProduct (v x) (v y))
    (he : ∃ e, v e = identityPartition n) : v 1 = identityPartition n := by
  obtain ⟨e,he⟩ := he
  have hh := hm e 1
  rw [mul_one,he,partitionProduct_identity_left] at hh
  exact hh.symm

private noncomputable def partition_coordinates_units {M : Type} [Monoid M] {n : ℕ}
    (v : M → (Setoid (Bool × Fin n))) (vi : Function.Injective v)
    (c : M → DiagramCoordinates (Fin n)) (hc : ∀ x, coordinatePartition (c x) = v x)
    (hm : ∀ x y, v (x*y) = partitionProduct (v x) (v y))
    (he : ∃ e, v e = identityPartition n)
    (hs : ∀ g : Equiv.Perm (Fin n), ∃ x, v x = coordinatePartition (fullDiagram g)) :
    Mˣ ≃* Equiv.Perm (Fin n) := by
  apply coordinate_units_perm c
  · intro x y h
    apply vi
    rw [← hc x,← hc y,h]
  · intro x y
    apply coordinatePartition_injective
    rw [hc,← coordinateMul_spec,hc,hc]
    exact hm x y
  · apply coordinatePartition_injective
    rw [hc,source_identity_value v hm he,fullDiagram_one_partition]
  · intro g
    obtain ⟨x,hx⟩ := hs g
    refine ⟨x,?_⟩
    apply coordinatePartition_injective
    rw [hc,hx]

private noncomputable def brauer_units_perm {n : ℕ} (B : BrauerSourceMonoid n) :
    letI : Monoid (Brauer n) := B.algebra
    (Brauer n)ˣ ≃* Equiv.Perm (Fin n) := by
  letI : Monoid (Brauer n) := B.algebra
  apply partition_coordinates_units (M := Brauer n) Subtype.val Subtype.val_injective
    (fun x => ((brauerCoordinateEquiv n).symm x).val)
  · intro x
    exact congrArg Subtype.val ((brauerCoordinateEquiv n).apply_symm_apply x)
  · exact B.multiplication
  · exact ⟨⟨identityPartition n,identityPartition_brauer n⟩,rfl⟩
  · intro g
    refine ⟨⟨coordinatePartition (fullDiagram g),?_⟩,rfl⟩
    intro x
    exact involutionSetoidBlockTwo _ _ (fullDiagram_fixed_point_free g) x

private noncomputable def partial_units_perm {n : ℕ} (B : PartialBrauerSourceMonoid n) :
    letI : Monoid (PartialBrauer n) := B.algebra
    (PartialBrauer n)ˣ ≃* Equiv.Perm (Fin n) := by
  letI : Monoid (PartialBrauer n) := B.algebra
  apply partition_coordinates_units (M := PartialBrauer n) Subtype.val Subtype.val_injective
    (fun x => (partialBrauerCoordinateEquiv n).symm x)
  · intro x
    exact congrArg Subtype.val ((partialBrauerCoordinateEquiv n).apply_symm_apply x)
  · exact B.multiplication
  · exact ⟨⟨identityPartition n,fun x => (identityPartition_brauer n x).le⟩,rfl⟩
  · intro g
    refine ⟨⟨coordinatePartition (fullDiagram g),?_⟩,rfl⟩
    intro x
    exact involutionSetoidBlockLeTwo _ _ x

private theorem brauer_small_no_complete {n : ℕ} (hn : n = 2 ∨ n = 3) (B : BrauerSourceMonoid n) :
    ¬ ∃ a : Brauer n → Brauer n, @CompleteMapping (Brauer n) B.algebra.toSemigroup a := by
  letI : Monoid (Brauer n) := B.algebra
  rintro ⟨a,ha⟩
  obtain ⟨u,hu⟩ := complete_mapping_restrict_units ha
  let e := brauer_units_perm B
  have h : ∃ b : Equiv.Perm (Fin n) → Equiv.Perm (Fin n), CompleteMapping b :=
    ⟨_,complete_mapping_transport e hu⟩
  rcases hn with rfl | rfl
  · exact symmetric_two_no_complete h
  · exact symmetric_three_no_complete h

private theorem partial_small_no_complete {n : ℕ} (hn : n = 2 ∨ n = 3) (B : PartialBrauerSourceMonoid n) :
    ¬ ∃ a : PartialBrauer n → PartialBrauer n,
      @CompleteMapping (PartialBrauer n) B.algebra.toSemigroup a := by
  letI : Monoid (PartialBrauer n) := B.algebra
  rintro ⟨a,ha⟩
  obtain ⟨u,hu⟩ := complete_mapping_restrict_units ha
  let e := partial_units_perm B
  have h : ∃ b : Equiv.Perm (Fin n) → Equiv.Perm (Fin n), CompleteMapping b :=
    ⟨_,complete_mapping_transport e hu⟩
  rcases hn with rfl | rfl
  · exact symmetric_two_no_complete h
  · exact symmetric_three_no_complete h

open Equiv
open scoped BigOperators
open D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation
open D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCoordinates
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
open D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
open D5.S3.Combinatorics.PerfectMatchings.AraujoSignedFactorLifting

private theorem reesTransversal_realize {I G X S : Type} [Group G] [Mul S]
    (P : I → I → Option G) (w : ReesTransversal P)
    (e : (I × G × I) ≃ X) (embed : X → S)
    (hm : ∀ x y p, P x.2.2 y.1 = some p →
      embed (e x) * embed (e y) = embed (e (x.1,x.2.1*p*y.2.1,y.2.2))) :
    ∃ a t : Equiv.Perm X, ∀ x, embed x * embed (a x) = embed (t x) := by
  let a := (e.symm.trans w.alpha).trans e
  let t := (e.symm.trans w.theta).trans e
  refine ⟨a,t,?_⟩
  intro x
  obtain ⟨z,rfl⟩ := e.surjective x
  dsimp only [a,t,Equiv.trans_apply]
  simp only [e.symm_apply_apply]
  have hw := w.product z
  cases hp : P z.2.2 (w.alpha z).1 with
  | none => simp [reesProduct,hp] at hw
  | some p =>
    have ht : (z.1,z.2.1*p*(w.alpha z).2.1,(w.alpha z).2.2) = w.theta z := by
      exact Option.some.inj (by simpa only [reesProduct,hp,Option.map_some] using hw)
    rw [hm z (w.alpha z) p hp,ht]

private theorem brauer_rank_transversal {n r : ℕ} (B : BrauerSourceMonoid n)
    (O : RankedHalf (Fin n) r) (w : ReesTransversal (halfMatrix O)) :
    letI : Monoid (Brauer n) := B.algebra
    ∃ a t : Equiv.Perm {x : Brauer n // brauerRank x = r},
      ∀ x, x.val * (a x).val = (t x).val := by
  letI : Monoid (Brauer n) := B.algebra
  apply reesTransversal_realize (halfMatrix O) w (brauerRankHalfDiagramEquiv n r) Subtype.val
  rintro ⟨A,g,D⟩ ⟨E,h,F⟩ p hp
  apply Subtype.ext
  refine (B.multiplication _ _).trans ?_
  change partitionProduct (coordinatePartition (rankedDiagram (halfRanked A) g (halfRanked D)))
    (coordinatePartition (rankedDiagram (halfRanked E) h (halfRanked F))) =
      coordinatePartition (rankedDiagram (halfRanked A) (g*p*h) (halfRanked F))
  rw [coordinateMul_spec,coordinateSandwich_product O _ _ _ _ g h p hp]

private theorem partial_brauer_rank_transversal {n r : ℕ} (B : PartialBrauerSourceMonoid n)
    (O : RankedHalf (Fin n) r)
    (w : ReesTransversal (fun D E => coordinateSandwich O D E)) :
    letI : Monoid (PartialBrauer n) := B.algebra
    ∃ a t : Equiv.Perm {x : PartialBrauer n // partialBrauerRank x = r},
      ∀ x, x.val * (a x).val = (t x).val := by
  letI : Monoid (PartialBrauer n) := B.algebra
  apply reesTransversal_realize (fun D E => coordinateSandwich O D E) w
    (partialBrauerRankEquiv n r) Subtype.val
  rintro ⟨A,g,D⟩ ⟨E,h,F⟩ p hp
  apply Subtype.ext
  refine (B.multiplication _ _).trans ?_
  change partitionProduct (coordinatePartition (rankedDiagram A g D))
    (coordinatePartition (rankedDiagram E h F)) =
      coordinatePartition (rankedDiagram A (g*p*h) F)
  rw [coordinateMul_spec,coordinateSandwich_product O A D E F g h p hp]


private theorem complete_mapping_of_fibre_transversals {S I : Type} [Semigroup S]
    (c : S → I)
    (h : ∀ i, ∃ a t : Equiv.Perm {x : S // c x = i},
      ∀ x, x.val * (a x).val = (t x).val) :
    ∃ a : S → S, CompleteMapping a := by
  classical
  choose a t ht using h
  let e := Equiv.sigmaFiberEquiv c
  let A : Equiv.Perm S := (e.symm.trans (Equiv.sigmaCongrRight a)).trans e
  let T : Equiv.Perm S := (e.symm.trans (Equiv.sigmaCongrRight t)).trans e
  refine ⟨A,A.bijective,?_⟩
  have hT : (fun x => x * A x) = T := by
    funext x
    exact ht (c x) ⟨x,rfl⟩
  rw [hT]
  exact T.bijective

private theorem brauer_factor_all {n r : ℕ} (hn : 4 ≤ n) (D : HalfDiagram n r) :
    Nonempty (ReesTransversal (halfMatrix (halfRanked D))) := by
  classical
  letI : Nonempty (HalfDiagram n r) := ⟨D⟩
  by_cases h2 : r = 2
  · subst r
    rcases Nat.even_or_odd (Fintype.card (HalfDiagram n 2)) with he | ho
    · exact diagonalTransversal_rees _ (fun E => coordinateSandwich_diagonal _ _)
        (diagonalTransversalFiniteEven he diagonalTransversalS2)
    · obtain ⟨hr,he⟩ := brauer_half_rank_admissible D
      have hn2 : n % 2 = 0 := by obtain ⟨k,hk⟩ := he; omega
      obtain ⟨k,rfl⟩ := (brauer_rank_two_odd_index hn hn2).mp ho
      exact rank_two_signed_factor k _
  · by_cases h3 : r = 3
    · subst r
      rcases Nat.even_or_odd (Fintype.card (HalfDiagram n 3)) with he | ho
      · exact diagonalTransversal_rees _ (fun E => coordinateSandwich_diagonal _ _)
          (diagonalTransversalFiniteEven he diagonalTransversalS3)
      · obtain ⟨hr,he⟩ := brauer_half_rank_admissible D
        have hn2 : n % 2 = 1 := by obtain ⟨k,hk⟩ := he; omega
        obtain ⟨k,rfl⟩ := (brauer_rank_three_odd_index (by omega) hn2).mp ho
        exact rank_three_signed_factor k _
    · obtain ⟨a,ha⟩ := symmetric_small_or_large r ⟨h2,h3⟩
      exact diagonalTransversal_rees _ (fun E => coordinateSandwich_diagonal _ _)
        (diagonalTransversalFiniteGood a ha)

private theorem partial_factor_all {n r : ℕ} (hn : 4 ≤ n) (D : RankedHalf (Fin n) r) :
    Nonempty (ReesTransversal (fun A B => coordinateSandwich D A B)) := by
  classical
  letI : Fintype (RankedHalf (Fin n) r) := Fintype.ofFinite _
  letI : Nonempty (RankedHalf (Fin n) r) := ⟨D⟩
  by_cases h2 : r = 2
  · subst r
    have he : Even (Fintype.card (RankedHalf (Fin n) 2)) := by
      simpa only [Nat.card_eq_fintype_card] using partial_rank_two_index_even hn
    exact diagonalTransversal_rees _ (coordinateSandwich_diagonal D)
      (diagonalTransversalFiniteEven he diagonalTransversalS2)
  · by_cases h3 : r = 3
    · subst r
      have he : Even (Fintype.card (RankedHalf (Fin n) 3)) := by
        simpa only [Nat.card_eq_fintype_card] using partial_rank_three_index_even hn
      exact diagonalTransversal_rees _ (coordinateSandwich_diagonal D)
        (diagonalTransversalFiniteEven he diagonalTransversalS3)
    · obtain ⟨a,ha⟩ := symmetric_small_or_large r ⟨h2,h3⟩
      exact diagonalTransversal_rees _ (coordinateSandwich_diagonal D)
        (diagonalTransversalFiniteGood a ha)

private theorem brauer_large_complete {n : ℕ} (hn : 4 ≤ n) (B : BrauerSourceMonoid n) :
    ∃ a : Brauer n → Brauer n, @CompleteMapping (Brauer n) B.algebra.toSemigroup a := by
  classical
  letI : Monoid (Brauer n) := B.algebra
  apply complete_mapping_of_fibre_transversals brauerRank
  intro r
  by_cases h : Nonempty {x : Brauer n // brauerRank x = r}
  · obtain ⟨x⟩ := h
    let D := ((brauerRankHalfDiagramEquiv n r).symm x).1
    obtain ⟨w⟩ := brauer_factor_all hn D
    exact brauer_rank_transversal B (halfRanked D) w
  · refine ⟨Equiv.refl _,Equiv.refl _,?_⟩
    intro x
    exact (h ⟨x⟩).elim

private theorem partial_large_complete {n : ℕ} (hn : 4 ≤ n) (B : PartialBrauerSourceMonoid n) :
    ∃ a : PartialBrauer n → PartialBrauer n,
      @CompleteMapping (PartialBrauer n) B.algebra.toSemigroup a := by
  classical
  letI : Monoid (PartialBrauer n) := B.algebra
  apply complete_mapping_of_fibre_transversals partialBrauerRank
  intro r
  by_cases h : Nonempty {x : PartialBrauer n // partialBrauerRank x = r}
  · obtain ⟨x⟩ := h
    let D := ((partialBrauerRankEquiv n r).symm x).1
    obtain ⟨w⟩ := partial_factor_all hn D
    exact partial_brauer_rank_transversal B D w
  · refine ⟨Equiv.refl _,Equiv.refl _,?_⟩
    intro x
    exact (h ⟨x⟩).elim

open Equiv
open scoped BigOperators
open D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids

private def upperOne : (Bool × Fin 1) := (false, 0)
private def lowerOne : (Bool × Fin 1) := (true, 0)

private theorem relation_one (p : (Setoid (Bool × Fin 1))) (x y : (Bool × Fin 1)) :
    p.r x y ↔ x = y ∨ p.r upperOne lowerOne := by
  rcases x with ⟨xb, xi⟩
  rcases y with ⟨yb, yi⟩
  have hxi : xi = 0 := Subsingleton.elim _ _
  have hyi : yi = 0 := Subsingleton.elim _ _
  subst xi; subst yi
  cases xb <;> cases yb
  · simp only [Prod.mk.injEq, and_self, true_or, iff_true]
    exact p.refl _
  · simp only [upperOne, lowerOne, Prod.mk.injEq, Bool.false_eq_true, false_and, false_or]
  · simp only [upperOne, lowerOne, Prod.mk.injEq, Bool.true_eq_false, false_and, false_or]
    exact ⟨p.symm, p.symm⟩
  · simp only [Prod.mk.injEq, and_self, true_or, iff_true]
    exact p.refl _

private theorem product_cross_one (p q : (Setoid (Bool × Fin 1))) :
    (partitionProduct p q).r upperOne lowerOne ↔
      p.r upperOne lowerOne ∧ q.r upperOne lowerOne := by
  constructor
  · intro hc
    constructor
    · by_contra hn
      have hle : Relation.EqvGen.setoid (productGraphEdge p q) ≤
          Setoid.ker (fun u : Fin 3 × Fin 1 => u.1 = 0) := by
        apply Setoid.eqvGen_le
        intro u v he
        rcases he with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
        · have h : x = y := ((relation_one p x y).mp hxy).resolve_right hn
          subst y
          rfl
        · rcases x with ⟨xb,xi⟩; rcases y with ⟨yb,yi⟩
          cases xb <;> cases yb <;> simp [Setoid.ker, secondEmbedding]
      have hh := hle hc
      simpa [exteriorEmbedding, upperOne, lowerOne] using hh
    · by_contra hn
      have hle : Relation.EqvGen.setoid (productGraphEdge p q) ≤
          Setoid.ker (fun u : Fin 3 × Fin 1 => u.1 = 2) := by
        apply Setoid.eqvGen_le
        intro u v he
        rcases he with ⟨x,y,rfl,rfl,hxy⟩ | ⟨x,y,rfl,rfl,hxy⟩
        · rcases x with ⟨xb,xi⟩; rcases y with ⟨yb,yi⟩
          cases xb <;> cases yb <;> simp [Setoid.ker, firstEmbedding]
        · have h : x = y := ((relation_one q x y).mp hxy).resolve_right hn
          subst y
          rfl
      have hh := hle hc
      simpa [exteriorEmbedding, upperOne, lowerOne] using hh
  · rintro ⟨hp,hq⟩
    have h01 : Relation.EqvGen (productGraphEdge p q)
        (firstEmbedding upperOne) (firstEmbedding lowerOne) :=
      .rel _ _ (Or.inl ⟨upperOne,lowerOne,rfl,rfl,hp⟩)
    have h12 : Relation.EqvGen (productGraphEdge p q)
        (secondEmbedding upperOne) (secondEmbedding lowerOne) :=
      .rel _ _ (Or.inr ⟨upperOne,lowerOne,rfl,rfl,hq⟩)
    exact Relation.EqvGen.trans _ _ _ h01 h12

private theorem partition_product_one (p q : (Setoid (Bool × Fin 1))) : partitionProduct p q = p ⊓ q := by
  ext x y
  change (partitionProduct p q).r x y ↔ p.r x y ∧ q.r x y
  constructor
  · intro h
    rcases (relation_one _ x y).mp h with hxy | hc
    · subst y
      exact ⟨p.refl _,q.refl _⟩
    · have hpq := (product_cross_one p q).mp hc
      exact ⟨(relation_one p x y).mpr (Or.inr hpq.1),
        (relation_one q x y).mpr (Or.inr hpq.2)⟩
  · rintro ⟨hp,hq⟩
    by_cases hxy : x = y
    · subst y
      exact (partitionProduct p q).refl _
    · apply (relation_one _ x y).mpr
      apply Or.inr
      exact (product_cross_one p q).mpr
        ⟨((relation_one p x y).mp hp).resolve_left hxy,
          ((relation_one q x y).mp hq).resolve_left hxy⟩

private theorem partial_one_complete (B : PartialBrauerSourceMonoid 1) :
    @D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping
      (PartialBrauer 1) B.algebra.toSemigroup id := by
  have hi : ∀ a : PartialBrauer 1, B.algebra.mul a a = a := by
    intro a
    apply Subtype.ext
    change (B.algebra.mul a a).val = a.val
    rw [B.multiplication, partition_product_one, inf_idem]
  exact @D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings.complete_mapping_of_idempotent
    (PartialBrauer 1) B.algebra.toSemigroup hi

private theorem partition_one_cases (p : (Setoid (Bool × Fin 1))) : p = ⊤ ∨ p = ⊥ := by
  by_cases hc : p.r upperOne lowerOne
  · left
    ext x y
    change p.r x y ↔ True
    exact ⟨fun _ => trivial, fun _ => (relation_one p x y).mpr (Or.inr hc)⟩
  · right
    ext x y
    change p.r x y ↔ x = y
    simpa only [hc, or_false] using relation_one p x y

private theorem brauer_one_val_top (a : Brauer 1) : a.val = ⊤ := by
  rcases partition_one_cases a.val with ht | hb
  · exact ht
  · have hc := a.property upperOne
    rw [hb] at hc
    have hbot : blockSize (⊥ : (Setoid (Bool × Fin 1))) upperOne = 1 := by
      unfold blockSize
      change Nat.card {y : (Bool × Fin 1) // upperOne = y} = 1
      exact Nat.card_unique
    rw [hbot] at hc
    contradiction

private theorem brauerOneSubsingleton : Subsingleton (Brauer 1) := ⟨by
  intro a b
  apply Subtype.ext
  rw [brauer_one_val_top a, brauer_one_val_top b]⟩

private theorem brauer_one_complete (B : BrauerSourceMonoid 1) :
    @D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping
      (Brauer 1) B.algebra.toSemigroup id := by
  letI := brauerOneSubsingleton
  exact ⟨Function.bijective_id, Function.bijective_of_subsingleton _⟩

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∃ _B : BrauerSourceMonoid n, True) ∧
    (∃ _PB : PartialBrauerSourceMonoid n, True) ∧
    (∀ B : BrauerSourceMonoid n,
      (∃ α : Brauer n → Brauer n,
        @D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping
          (Brauer n) B.algebra.toSemigroup α) ↔ (n = 1 ∨ 4 ≤ n)) ∧
    (∀ PB : PartialBrauerSourceMonoid n,
      (∃ α : PartialBrauer n → PartialBrauer n,
        @D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping
          (PartialBrauer n) PB.algebra.toSemigroup α) ↔ (n = 1 ∨ 4 ≤ n))

theorem result : claim := by
  classical
  intro n hn
  refine ⟨(source_monoids_exist n).1, (source_monoids_exist n).2, ?_, ?_⟩
  · intro B
    constructor
    · intro h
      by_contra hh
      have hs : n = 2 ∨ n = 3 := by omega
      exact brauer_small_no_complete hs B h
    · rintro (rfl | h)
      · exact ⟨id,brauer_one_complete B⟩
      · exact brauer_large_complete h B
  · intro B
    constructor
    · intro h
      by_contra hh
      have hs : n = 2 ∨ n = 3 := by omega
      exact partial_small_no_complete hs B h
    · rintro (rfl | h)
      · exact ⟨id,partial_one_complete B⟩
      · exact partial_large_complete h B

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerCompleteMapping
