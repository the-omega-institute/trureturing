/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport.rank_two_signed_half_cycles
proof_shape: content — adjacent_fixed_sets_connected, through_compatible_overlay, signed_half_diagram_triangle, rank_two_signed_half_cycles, rank_three_signed_half_cycles
proof_shape: bind-only — Overlay, overlay_common_fixed, involution_card_mod_two, OverlayTransport, adjacentTransportEquiv, adjacent_overlay_transport, equal_fixed_sets_overlay_transport, halfPermutation, halfPermutationFixed, halfPermutationInvolutive, overlay_transport_common, overlay_transport_exceptional, triangle_transport_holonomy, transport_cycle_sign, halfFixedLabels, halfTransportSign, geometric_triangle_sign, overlay_transport_round_trip, half_transport_sign_target_eq, half_transport_reverse_sign, triangle_family_sign, SignedHalfCycles, OverlayTransport.transport, OverlayTransport.connected, OverlayTransport.unique, SignedHalfCycles.cycles, SignedHalfCycles.transport, SignedHalfCycles.twoSign, SignedHalfCycles.threeSign
Bind-only consumer edge: geometric_triangle_sign → transport_cycle_sign (consumer → prerequisite).
Direct frozen dependencies (declaration statement_id):
D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution sha256:6a2fd619f7f0c220bed4d3b853cca9527379a8bd42cefa9403ca65d4b3210aac
D5.S3.Zeros.Convolution.PerfectMatchingCount.card_fixedPointFreeInvolution_mul sha256:f668778ce789801ae29ef9f459aca650eb978ac4b6ca4160af5447a4367a38a9
D5.S3.Zeros.Convolution.PerfectMatchingCount.instFintypeFixedPointFreeInvolution sha256:662e2e6ff37d64412b2e0ed0ce1cccc25fbfa080efcb06596f49226b5ef90dbc
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/


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
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles

attribute [local instance] Classical.propDecidable

abbrev Overlay {X : Type*} (p q : Equiv.Perm X) : X → X → Prop :=
  Relation.EqvGen (fun u v => p u = v ∨ q u = v)

private theorem overlay_common_fixed {X : Type*} (p q : Equiv.Perm X)
    {c a : X} (hp : p c = c) (hq : q c = c) (h : Overlay p q a c) : a = c := by
  have hguard : ∀ u v : X, Overlay p q u v → (u = c ↔ v = c) := by
    intro u v huv
    induction huv with
    | rel u v he =>
      rcases he with he | he
      · subst v
        exact ⟨fun h => (congrArg p h).trans hp, fun h => p.injective (h.trans hp.symm)⟩
      · subst v
        exact ⟨fun h => (congrArg q h).trans hq, fun h => q.injective (h.trans hq.symm)⟩
    | refl u => exact Iff.rfl
    | symm u v h ih => exact ih.symm
    | trans u v w h1 h2 ih1 ih2 => exact ih1.trans ih2
  exact (hguard a c h).mpr rfl

theorem involution_card_mod_two {X : Type*} [Fintype X] [DecidableEq X]
    (f : Function.End X) (hf : Function.Involutive f) :
    Nat.ModEq 2 (Nat.card X) (Nat.card (Function.fixedPoints f)) := by
  classical
  have hpow : (f : Function.End X) ^ 2 = 1 := by
    funext x
    exact hf x
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (f := f) (by simpa using hpow)
  simpa only [Fintype.card_eq_nat_card] using h

/-- Two involutions whose fixed sets differ by the endpoints join those endpoints.
Common fixed points form isolated components and do not affect the argument. -/
private theorem adjacent_fixed_sets_connected {X : Type*} [Fintype X]
    (p q : Equiv.Perm X) (hp : Function.Involutive p) (hq : Function.Involutive q)
    (a b : X) (hpa : p a = a) (hqa : q a ≠ a)
    (hpf : ∀ x, p x = x → x = a ∨ q x = x)
    (hqf : ∀ x, q x = x → x = b ∨ p x = x) : Overlay p q a b := by
  classical
  let C := {x : X // Overlay p q a x}
  letI : Fintype C := Fintype.ofFinite C
  let pc : C → C := fun x => ⟨p x, Relation.EqvGen.trans _ _ _ x.property
    (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩
  let qc : C → C := fun x => ⟨q x, Relation.EqvGen.trans _ _ _ x.property
    (Relation.EqvGen.rel _ _ (Or.inr rfl))⟩
  let ac : C := ⟨a, Relation.EqvGen.refl a⟩
  have hpc : Function.Involutive pc := fun x => Subtype.ext (hp x)
  have hqc : Function.Involutive qc := fun x => Subtype.ext (hq x)
  have hnocommon : ∀ x : C, ¬ (p x = x ∧ q x = x) := by
    rintro x ⟨hpx, hqx⟩
    have hax : a = (x : X) := overlay_common_fixed p q hpx hqx x.property
    apply hqa
    simpa only [hax] using hqx
  have hpfixed : ∀ x : C, pc x = x ↔ x = ac := by
    intro x
    constructor
    · intro hx
      have hpx : p x = x := congrArg Subtype.val hx
      rcases hpf x hpx with hxa | hqx
      · exact Subtype.ext hxa
      · exact (hnocommon x ⟨hpx,hqx⟩).elim
    · rintro rfl
      exact Subtype.ext hpa
  have hp_card : Nat.card (Function.fixedPoints pc) = 1 := by
    calc
      Nat.card (Function.fixedPoints pc) = Nat.card {x : C // x = ac} :=
        Nat.card_congr (Equiv.subtypeEquivRight hpfixed)
      _ = 1 := Nat.card_unique
  have hpmod := involution_card_mod_two pc hpc
  have hqmod := involution_card_mod_two qc hqc
  rw [hp_card] at hpmod
  by_contra hab
  have hq_card : Nat.card (Function.fixedPoints qc) = 0 := by
    suffices hi : IsEmpty (Function.fixedPoints qc) by
      letI := hi
      simp
    refine ⟨?_⟩
    intro y
    have hqx : q (y.val : X) = (y.val : X) := congrArg Subtype.val y.property
    rcases hqf y.val hqx with hxb | hpx
    · exact hab (hxb ▸ y.val.property)
    · exact hnocommon y.val ⟨hpx,hqx⟩
  rw [hq_card] at hqmod
  exact (by decide : ¬ Nat.ModEq 2 1 0) (hpmod.symm.trans hqmod)

structure OverlayTransport {X : Type*} (p q : Equiv.Perm X) where
  transport : Function.fixedPoints p ≃ Function.fixedPoints q
  connected : ∀ x : Function.fixedPoints p, Overlay p q x (transport x)
  unique : ∀ (x : Function.fixedPoints p) (y : Function.fixedPoints q),
    Overlay p q x y → transport x = y

private noncomputable def adjacentTransportEquiv {X : Type*} (p q : Equiv.Perm X)
    (a b : X) (hpa : p a = a) (hqa : q a ≠ a)
    (hpb : p b ≠ b) (hqb : q b = b)
    (hpf : ∀ x, p x = x → x = a ∨ q x = x)
    (hqf : ∀ x, q x = x → x = b ∨ p x = x) :
    Function.fixedPoints p ≃ Function.fixedPoints q where
  toFun x := if h : (x : X) = a then ⟨b,hqb⟩ else
    ⟨x, (hpf x x.property).resolve_left h⟩
  invFun y := if h : (y : X) = b then ⟨a,hpa⟩ else
    ⟨y, (hqf y y.property).resolve_left h⟩
  left_inv x := by
    by_cases hx : (x : X) = a
    · apply Subtype.ext
      simp [hx]
    · have hxb : (x : X) ≠ b := by
        intro h
        exact hpb (h ▸ x.property)
      apply Subtype.ext
      simp [hx, hxb]
  right_inv y := by
    by_cases hy : (y : X) = b
    · apply Subtype.ext
      simp [hy]
    · have hya : (y : X) ≠ a := by
        intro h
        exact hqa (h ▸ y.property)
      apply Subtype.ext
      simp [hy, hya]

private noncomputable def adjacent_overlay_transport {X : Type*} [Fintype X]
    (p q : Equiv.Perm X) (hp : Function.Involutive p) (hq : Function.Involutive q)
    (a b : X) (hpa : p a = a) (hqa : q a ≠ a)
    (hpb : p b ≠ b) (hqb : q b = b)
    (hpf : ∀ x, p x = x → x = a ∨ q x = x)
    (hqf : ∀ x, q x = x → x = b ∨ p x = x) : OverlayTransport p q where
  transport := adjacentTransportEquiv p q a b hpa hqa hpb hqb hpf hqf
  connected x := by
    by_cases hx : (x : X) = a
    · change Overlay p q x ((adjacentTransportEquiv p q a b hpa hqa hpb hqb hpf hqf) x)
      simpa [adjacentTransportEquiv, hx] using
        adjacent_fixed_sets_connected p q hp hq a b hpa hqa hpf hqf
    · change Overlay p q x ((adjacentTransportEquiv p q a b hpa hqa hpb hqb hpf hqf) x)
      simpa [adjacentTransportEquiv, hx] using Relation.EqvGen.refl (x : X)
  unique x y hxy := by
    apply Subtype.ext
    by_cases hx : (x : X) = a
    · have hyb : (y : X) = b := by
        rcases hqf y y.property with hyb | hpy
        · exact hyb
        · have hay : (x : X) = y := overlay_common_fixed p q hpy y.property hxy
          exact (hqa (hx ▸ hay.symm ▸ y.property)).elim
      simp [adjacentTransportEquiv, hx, hyb]
    · have hqx : q x = x := (hpf x x.property).resolve_left hx
      have hyx : (y : X) = x := overlay_common_fixed p q x.property hqx
        (Relation.EqvGen.symm _ _ hxy)
      simpa [adjacentTransportEquiv, hx] using hyx.symm

private noncomputable def equal_fixed_sets_overlay_transport {X : Type*}
    (p q : Equiv.Perm X) (hfix : ∀ x, p x = x ↔ q x = x) : OverlayTransport p q where
  transport := Equiv.subtypeEquivRight hfix
  connected x := Relation.EqvGen.refl (x : X)
  unique x y hxy := by
    apply Subtype.ext
    exact (overlay_common_fixed p q x.property ((hfix x).mp x.property)
      (Relation.EqvGen.symm _ _ hxy)).symm

noncomputable def halfPermutation {n r : ℕ} (D : HalfDiagram n r) : Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr (Equiv.refl {x : Fin n // x ∈ D.1.val}) D.2.val

theorem halfPermutationFixed {n r : ℕ} (D : HalfDiagram n r) (x : Fin n) :
    halfPermutation D x = x ↔ x ∈ D.1.val := by
  classical
  by_cases hx : x ∈ D.1.val
  · simp [halfPermutation, Equiv.Perm.subtypeCongr.left_apply _ _ hx, hx]
  · constructor
    · intro h
      have he : (D.2.val ⟨x,hx⟩ : Fin n) = x := by
        simpa only [halfPermutation, Equiv.Perm.subtypeCongr.right_apply _ _ hx] using h
      exact (D.2.property.2 ⟨x,hx⟩ (Subtype.ext he)).elim
    · exact fun h => (hx h).elim

theorem halfPermutationInvolutive {n r : ℕ} (D : HalfDiagram n r) :
    Function.Involutive (halfPermutation D) := by
  classical
  intro x
  by_cases hx : x ∈ D.1.val
  · rw [(halfPermutationFixed D x).mpr hx]
    exact (halfPermutationFixed D x).mpr hx
  · rw [show halfPermutation D x = D.2.val ⟨x,hx⟩ from
      Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rw [show halfPermutation D (D.2.val ⟨x,hx⟩) = D.2.val (D.2.val ⟨x,hx⟩) from
      Equiv.Perm.subtypeCongr.right_apply _ _ (D.2.val ⟨x,hx⟩).property]
    exact congrArg Subtype.val (D.2.property.1 ⟨x,hx⟩)

private theorem through_compatible_overlay {n r : ℕ} (D E : HalfDiagram n r)
    (hc : ThroughCompatible D.1 E.1) :
    Nonempty (OverlayTransport (halfPermutation D) (halfPermutation E)) := by
  classical
  rcases hc with he | ha
  · exact ⟨equal_fixed_sets_overlay_transport _ _ (fun x => by
      rw [halfPermutationFixed, halfPermutationFixed, he])⟩
  · have hD : (D.1.val \ E.1.val).card = 1 := by
      have := Finset.card_sdiff_add_card_inter D.1.val E.1.val
      have := D.1.property
      omega
    have hE : (E.1.val \ D.1.val).card = 1 := by
      have := Finset.card_sdiff_add_card_inter E.1.val D.1.val
      rw [Finset.inter_comm] at this
      have := E.1.property
      omega
    obtain ⟨a,hae⟩ := Finset.card_eq_one.mp hD
    obtain ⟨b,hbe⟩ := Finset.card_eq_one.mp hE
    have ha_mem : a ∈ D.1.val ∧ a ∉ E.1.val := Finset.mem_sdiff.mp
      (hae ▸ Finset.mem_singleton_self a)
    have hb_mem : b ∈ E.1.val ∧ b ∉ D.1.val := Finset.mem_sdiff.mp
      (hbe ▸ Finset.mem_singleton_self b)
    refine ⟨adjacent_overlay_transport _ _ (halfPermutationInvolutive D)
      (halfPermutationInvolutive E) a b
      ((halfPermutationFixed D a).mpr ha_mem.1)
      (fun h => ha_mem.2 ((halfPermutationFixed E a).mp h))
      (fun h => hb_mem.2 ((halfPermutationFixed D b).mp h))
      ((halfPermutationFixed E b).mpr hb_mem.1) ?_ ?_⟩
    · intro x hx
      by_cases hxE : x ∈ E.1.val
      · exact Or.inr ((halfPermutationFixed E x).mpr hxE)
      · left
        have hmem : x ∈ D.1.val \ E.1.val := Finset.mem_sdiff.mpr
          ⟨(halfPermutationFixed D x).mp hx,hxE⟩
        rw [hae] at hmem
        exact Finset.mem_singleton.mp hmem
    · intro x hx
      by_cases hxD : x ∈ D.1.val
      · exact Or.inr ((halfPermutationFixed D x).mpr hxD)
      · left
        have hmem : x ∈ E.1.val \ D.1.val := Finset.mem_sdiff.mpr
          ⟨(halfPermutationFixed E x).mp hx,hxD⟩
        rw [hbe] at hmem
        exact Finset.mem_singleton.mp hmem

attribute [local instance] Classical.propDecidable

private theorem overlay_transport_common {X : Type*} (p q : Equiv.Perm X)
    (w : OverlayTransport p q) (x : X) (hp : p x = x) (hq : q x = x) :
    w.transport ⟨x,hp⟩ = ⟨x,hq⟩ :=
  w.unique _ _ (Relation.EqvGen.refl x)

private theorem overlay_transport_exceptional {X : Type*} (p q : Equiv.Perm X)
    (w : OverlayTransport p q) (a b : X) (hpa : p a = a) (hqa : q a ≠ a)
    (hqb : q b = b) (hqf : ∀ x, q x = x → x = b ∨ p x = x) :
    w.transport ⟨a,hpa⟩ = ⟨b,hqb⟩ := by
  apply Subtype.ext
  let y := w.transport ⟨a,hpa⟩
  rcases hqf y y.property with hyb | hpy
  · exact hyb
  · have hay : a = y := overlay_common_fixed p q hpy y.property (w.connected ⟨a,hpa⟩)
    exact (hqa (hay ▸ y.property)).elim

private theorem triangle_transport_holonomy {X : Type*} [DecidableEq X] (p₀ p₁ p₂ : Equiv.Perm X)
    (w₀₁ : OverlayTransport p₀ p₁) (w₁₂ : OverlayTransport p₁ p₂)
    (w₂₀ : OverlayTransport p₂ p₀) (a b c : X)
    (hab : a ≠ b)
    (h₀a : p₀ a = a) (h₀b : p₀ b = b) (h₀c : p₀ c ≠ c)
    (h₁a : p₁ a = a) (h₁c : p₁ c = c) (h₁b : p₁ b ≠ b)
    (h₂b : p₂ b = b) (h₂c : p₂ c = c) (h₂a : p₂ a ≠ a)
    (h₁₀ : ∀ x, p₁ x = x → x = c ∨ p₀ x = x)
    (h₂₁ : ∀ x, p₂ x = x → x = b ∨ p₁ x = x)
    (h₀₂ : ∀ x, p₀ x = x → x = a ∨ p₂ x = x)
    (hrest : ∀ x, p₀ x = x → x ≠ a → x ≠ b → p₁ x = x ∧ p₂ x = x) :
    ((w₀₁.transport.trans w₁₂.transport).trans w₂₀.transport) =
      Equiv.swap (⟨a,h₀a⟩ : Function.fixedPoints p₀) ⟨b,h₀b⟩ := by
  have h01a := overlay_transport_common p₀ p₁ w₀₁ a h₀a h₁a
  have h01b := overlay_transport_exceptional p₀ p₁ w₀₁ b c h₀b h₁b h₁c h₁₀
  have h12a := overlay_transport_exceptional p₁ p₂ w₁₂ a b h₁a h₂a h₂b h₂₁
  have h12c := overlay_transport_common p₁ p₂ w₁₂ c h₁c h₂c
  have h20b := overlay_transport_common p₂ p₀ w₂₀ b h₂b h₀b
  have h20c := overlay_transport_exceptional p₂ p₀ w₂₀ c a h₂c h₀c h₀a h₀₂
  apply Equiv.ext
  intro x
  change w₂₀.transport (w₁₂.transport (w₀₁.transport x)) = _
  by_cases hxa : (x : X) = a
  · have he : x = (⟨a,h₀a⟩ : Function.fixedPoints p₀) := Subtype.ext hxa
    rw [he, h01a, h12a, h20b, Equiv.swap_apply_left]
  · by_cases hxb : (x : X) = b
    · have he : x = (⟨b,h₀b⟩ : Function.fixedPoints p₀) := Subtype.ext hxb
      rw [he, h01b, h12c, h20c, Equiv.swap_apply_right]
    · obtain ⟨h₁x,h₂x⟩ := hrest x x.property hxa hxb
      have h01x := overlay_transport_common p₀ p₁ w₀₁ x x.property h₁x
      have h12x := overlay_transport_common p₁ p₂ w₁₂ x h₁x h₂x
      have h20x := overlay_transport_common p₂ p₀ w₂₀ x h₂x x.property
      rw [h01x, h12x, h20x]
      apply (Equiv.swap_apply_of_ne_of_ne _ _).symm
      · exact fun h => hxa (congrArg Subtype.val h)
      · exact fun h => hxb (congrArg Subtype.val h)

 theorem transport_cycle_sign {A B C : Type*} [Fintype A] [DecidableEq A]
    {r : ℕ} (e₀ : A ≃ Fin r) (e₁ : B ≃ Fin r) (e₂ : C ≃ Fin r)
    (t₀₁ : A ≃ B) (t₁₂ : B ≃ C) (t₂₀ : C ≃ A) :
    Equiv.Perm.sign ((e₀.symm.trans t₀₁).trans e₁) *
      Equiv.Perm.sign ((e₁.symm.trans t₁₂).trans e₂) *
      Equiv.Perm.sign ((e₂.symm.trans t₂₀).trans e₀) =
        Equiv.Perm.sign ((t₀₁.trans t₁₂).trans t₂₀) := by
  let g₀₁ := (e₀.symm.trans t₀₁).trans e₁
  let g₁₂ := (e₁.symm.trans t₁₂).trans e₂
  let g₂₀ := (e₂.symm.trans t₂₀).trans e₀
  have hm : g₂₀ * g₁₂ * g₀₁ =
      (e₀.symm.trans ((t₀₁.trans t₁₂).trans t₂₀)).trans e₀ := by
    ext x
    simp [g₀₁,g₁₂,g₂₀]
  have hs := congrArg Equiv.Perm.sign hm
  rw [map_mul,map_mul, Equiv.Perm.sign_symm_trans_trans] at hs
  simpa only [g₀₁,g₁₂,g₂₀, mul_comm, mul_left_comm, mul_assoc] using hs

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing

attribute [local instance] Classical.propDecidable

private noncomputable def halfFixedLabels {n r : ℕ} (D : HalfDiagram n r) :
    Function.fixedPoints (halfPermutation D) ≃ Fin r :=
  (Equiv.subtypeEquivRight (halfPermutationFixed D)).trans
    (D.1.val.orderIsoOfFin D.1.property).toEquiv.symm

noncomputable def halfTransportSign {n r : ℕ} (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E)) : ℤˣ :=
  Equiv.Perm.sign (((halfFixedLabels D).symm.trans w.transport).trans (halfFixedLabels E))

private theorem geometric_triangle_sign {n r : ℕ} (D₀ D₁ D₂ : HalfDiagram n r)
    (S : Finset (Fin n)) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haS : a ∉ S) (hbS : b ∉ S) (hcS : c ∉ S)
    (hT₀ : D₀.1.val = S ∪ {a,b}) (hT₁ : D₁.1.val = S ∪ {a,c})
    (hT₂ : D₂.1.val = S ∪ {b,c})
    (w₀₁ : OverlayTransport (halfPermutation D₀) (halfPermutation D₁))
    (w₁₂ : OverlayTransport (halfPermutation D₁) (halfPermutation D₂))
    (w₂₀ : OverlayTransport (halfPermutation D₂) (halfPermutation D₀)) :
    halfTransportSign D₀ D₁ w₀₁ * halfTransportSign D₁ D₂ w₁₂ *
      halfTransportSign D₂ D₀ w₂₀ = -1 := by
  let p₀ := halfPermutation D₀
  let p₁ := halfPermutation D₁
  let p₂ := halfPermutation D₂
  have h₀a : p₀ a = a := (halfPermutationFixed D₀ a).mpr (by simp [hT₀])
  have h₀b : p₀ b = b := (halfPermutationFixed D₀ b).mpr (by simp [hT₀])
  have h₀c : p₀ c ≠ c := by
    simpa [p₀,halfPermutationFixed,hT₀,hcS,Ne.symm hac,Ne.symm hbc]
  have h₁a : p₁ a = a := (halfPermutationFixed D₁ a).mpr (by simp [hT₁])
  have h₁c : p₁ c = c := (halfPermutationFixed D₁ c).mpr (by simp [hT₁])
  have h₁b : p₁ b ≠ b := by
    simpa [p₁,halfPermutationFixed,hT₁,hbS,Ne.symm hab,hbc]
  have h₂b : p₂ b = b := (halfPermutationFixed D₂ b).mpr (by simp [hT₂])
  have h₂c : p₂ c = c := (halfPermutationFixed D₂ c).mpr (by simp [hT₂])
  have h₂a : p₂ a ≠ a := by
    simpa [p₂,halfPermutationFixed,hT₂,haS,hab,hac]
  have h₁₀ : ∀ x, p₁ x = x → x = c ∨ p₀ x = x := by
    intro x
    simp only [p₁,p₀,halfPermutationFixed,hT₁,hT₀,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have h₂₁ : ∀ x, p₂ x = x → x = b ∨ p₁ x = x := by
    intro x
    simp only [p₂,p₁,halfPermutationFixed,hT₂,hT₁,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have h₀₂ : ∀ x, p₀ x = x → x = a ∨ p₂ x = x := by
    intro x
    simp only [p₀,p₂,halfPermutationFixed,hT₀,hT₂,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hrest : ∀ x, p₀ x = x → x ≠ a → x ≠ b → p₁ x = x ∧ p₂ x = x := by
    intro x
    simp only [p₀,p₁,p₂,halfPermutationFixed,hT₀,hT₁,hT₂,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hh := triangle_transport_holonomy p₀ p₁ p₂ w₀₁ w₁₂ w₂₀ a b c hab
    h₀a h₀b h₀c h₁a h₁c h₁b h₂b h₂c h₂a h₁₀ h₂₁ h₀₂ hrest
  have hs := transport_cycle_sign (halfFixedLabels D₀) (halfFixedLabels D₁)
    (halfFixedLabels D₂) w₀₁.transport w₁₂.transport w₂₀.transport
  change halfTransportSign D₀ D₁ w₀₁ * halfTransportSign D₁ D₂ w₁₂ *
    halfTransportSign D₂ D₀ w₂₀ = _ at hs
  rw [hs,hh]
  apply Equiv.Perm.sign_swap
  exact fun h => hab (congrArg Subtype.val h)

private theorem overlay_transport_round_trip {X : Type*} (p q : Equiv.Perm X)
    (w : OverlayTransport p q) (v : OverlayTransport q p) (x : Function.fixedPoints p) :
    v.transport (w.transport x) = x := by
  apply v.unique
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.mono (fun u v (h : p u = v ∨ q u = v) => h.elim Or.inr Or.inl) _ _ (w.connected x))

private theorem half_transport_sign_target_eq {n r : ℕ} (D E F : HalfDiagram n r)
    (hEF : E = F) (w : OverlayTransport (halfPermutation D) (halfPermutation E))
    (v : OverlayTransport (halfPermutation D) (halfPermutation F)) :
    halfTransportSign D E w = halfTransportSign D F v := by
  subst F
  have ht : w.transport = v.transport := by
    apply Equiv.ext
    intro x
    exact (v.unique x (w.transport x) (w.connected x)).symm
  unfold halfTransportSign
  rw [ht]

private theorem half_transport_reverse_sign {n r : ℕ} (D E : HalfDiagram n r)
    (w : OverlayTransport (halfPermutation D) (halfPermutation E))
    (v : OverlayTransport (halfPermutation E) (halfPermutation D)) :
    halfTransportSign D E w * halfTransportSign E D v = 1 := by
  let g := ((halfFixedLabels D).symm.trans w.transport).trans (halfFixedLabels E)
  let h := ((halfFixedLabels E).symm.trans v.transport).trans (halfFixedLabels D)
  have hm : h * g = 1 := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.trans_apply, g, h,
      Equiv.symm_apply_apply, overlay_transport_round_trip,
      Equiv.apply_symm_apply, Equiv.Perm.one_apply]
  have hs := congrArg Equiv.Perm.sign hm
  rw [map_mul,map_one] at hs
  simpa only [halfTransportSign,g,h,mul_comm] using hs

private theorem triangle_family_sign {n r : ℕ} (S : Finset (Fin n)) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haS : a ∉ S) (hbS : b ∉ S) (hcS : c ∉ S)
    (D₀ D₁ D₂ : HalfDiagram n r)
    (h₀ : D₀.1.val ∈ ({S ∪ {a,b}, S ∪ {a,c}, S ∪ {b,c}} : Finset (Finset (Fin n))))
    (h₁ : D₁.1.val ∈ ({S ∪ {a,b}, S ∪ {a,c}, S ∪ {b,c}} : Finset (Finset (Fin n))))
    (h₂ : D₂.1.val ∈ ({S ∪ {a,b}, S ∪ {a,c}, S ∪ {b,c}} : Finset (Finset (Fin n))))
    (h₀₁ : D₀.1.val ≠ D₁.1.val) (h₁₂ : D₁.1.val ≠ D₂.1.val)
    (h₂₀ : D₂.1.val ≠ D₀.1.val)
    (w₀₁ : OverlayTransport (halfPermutation D₀) (halfPermutation D₁))
    (w₁₂ : OverlayTransport (halfPermutation D₁) (halfPermutation D₂))
    (w₂₀ : OverlayTransport (halfPermutation D₂) (halfPermutation D₀)) :
    halfTransportSign D₀ D₁ w₀₁ * halfTransportSign D₁ D₂ w₁₂ *
      halfTransportSign D₂ D₀ w₂₀ = -1 := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at h₀ h₁ h₂
  rcases h₀ with h₀ | h₀ | h₀ <;>
    rcases h₁ with h₁ | h₁ | h₁ <;>
      rcases h₂ with h₂ | h₂ | h₂
  all_goals first
    | exact (h₀₁ (h₀.trans h₁.symm)).elim
    | exact (h₁₂ (h₁.trans h₂.symm)).elim
    | exact (h₂₀ (h₂.trans h₀.symm)).elim
    | (apply geometric_triangle_sign D₀ D₁ D₂ S a b c hab hac hbc haS hbS hcS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)
    | (apply geometric_triangle_sign D₀ D₁ D₂ S b a c (Ne.symm hab) hbc hac hbS haS hcS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)
    | (apply geometric_triangle_sign D₀ D₁ D₂ S a c b hac hab (Ne.symm hbc) haS hcS hbS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)
    | (apply geometric_triangle_sign D₀ D₁ D₂ S c a b (Ne.symm hac) (Ne.symm hbc) hab hcS haS hbS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)
    | (apply geometric_triangle_sign D₀ D₁ D₂ S b c a hbc (Ne.symm hab) (Ne.symm hac) hbS hcS haS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)
    | (apply geometric_triangle_sign D₀ D₁ D₂ S c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) hcS hbS haS
        (by simpa only [Finset.pair_comm] using h₀)
        (by simpa only [Finset.pair_comm] using h₁)
        (by simpa only [Finset.pair_comm] using h₂) w₀₁ w₁₂ w₂₀)

structure SignedHalfCycles (n r : ℕ) where
  cycles : OneTrianglePermutation (HalfDiagram n r)
  transport : ∀ D, OverlayTransport (halfPermutation D) (halfPermutation (cycles.perm D))
  twoSign : ∀ D, D ∉ cycles.triangle →
    halfTransportSign D (cycles.perm D) (transport D) *
      halfTransportSign (cycles.perm D) (cycles.perm (cycles.perm D)) (transport (cycles.perm D)) = 1
  threeSign : ∀ D, D ∈ cycles.triangle →
    halfTransportSign D (cycles.perm D) (transport D) *
      halfTransportSign (cycles.perm D) (cycles.perm (cycles.perm D)) (transport (cycles.perm D)) *
      halfTransportSign (cycles.perm (cycles.perm D)) (cycles.perm (cycles.perm (cycles.perm D))) (transport (cycles.perm (cycles.perm D))) = -1

private theorem signed_half_diagram_triangle {n r : ℕ} {tri : Finset (Finset (Fin n))}
    (h : SubsetPairing (Fin n) r tri) (ht : tri.card = 3)
    (hr : ∀ T ∈ tri, T.card = r) (he : Even (n-r))
    (ha : ∀ T ∈ tri, ∀ U ∈ tri, T = U ∨ (T ∩ U).card + 1 = r)
    (S : Finset (Fin n)) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haS : a ∉ S) (hbS : b ∉ S) (hcS : c ∉ S)
    (htri : tri = {S ∪ {a,b}, S ∪ {a,c}, S ∪ {b,c}}) :
    Nonempty (SignedHalfCycles n r) := by
  classical
  obtain ⟨w,hw,htw,hiw⟩ := half_diagram_supported_triangle_structure h ht hr he ha
  let tr := fun D => Classical.choice (through_compatible_overlay D (w.perm D) (hw D))
  refine ⟨{
    cycles := w
    transport := tr
    twoSign := ?_
    threeSign := ?_ }⟩
  · intro D hD
    have h2 := w.outsideSquare D hD
    let v : OverlayTransport (halfPermutation (w.perm D)) (halfPermutation D) := by
      simpa only [h2] using tr (w.perm D)
    have hs := half_transport_reverse_sign D (w.perm D) (tr D) v
    change halfTransportSign D (w.perm D) (tr D) *
      halfTransportSign (w.perm D) (w.perm (w.perm D)) (tr (w.perm D)) = 1
    rw [half_transport_sign_target_eq (w.perm D) _ D h2 (tr (w.perm D)) v]
    exact hs
  · intro D hD
    let D₁ := w.perm D
    let D₂ := w.perm D₁
    have hD₁ : D₁ ∈ w.triangle := (w.triangleInvariant D).mp hD
    have hD₂ : D₂ ∈ w.triangle := (w.triangleInvariant D₁).mp hD₁
    have h3 : w.perm D₂ = D := w.triangleCube D hD
    let v : OverlayTransport (halfPermutation D₂) (halfPermutation D) := by
      simpa only [h3] using tr D₂
    have h₀₁ : D.1.val ≠ D₁.1.val := by
      intro hDE
      exact w.noFixed D (hiw D hD D₁ hD₁ (Subtype.ext hDE)).symm
    have h₁₂ : D₁.1.val ≠ D₂.1.val := by
      intro hDE
      exact w.noFixed D₁ (hiw D₁ hD₁ D₂ hD₂ (Subtype.ext hDE)).symm
    have h₂₀ : D₂.1.val ≠ D.1.val := by
      intro hDE
      have heq := congrArg w.perm (hiw D₂ hD₂ D hD (Subtype.ext hDE))
      rw [h3] at heq
      exact w.noFixed D heq.symm
    have hs := triangle_family_sign S a b c hab hac hbc haS hbS hcS D D₁ D₂
      (by rw [← htri]; exact htw D hD)
      (by rw [← htri]; exact htw D₁ hD₁)
      (by rw [← htri]; exact htw D₂ hD₂)
      h₀₁ h₁₂ h₂₀ (tr D) (tr D₁) v
    change halfTransportSign D D₁ (tr D) * halfTransportSign D₁ D₂ (tr D₁) *
      halfTransportSign D₂ (w.perm D₂) (tr D₂) = -1
    rw [half_transport_sign_target_eq D₂ _ D h3 (tr D₂) v]
    exact hs

theorem rank_two_signed_half_cycles (k : ℕ) :
    Nonempty (SignedHalfCycles (6+4*k) 2) := by
  obtain ⟨e,⟨h⟩⟩ := rank_two_subset_pairing k
  have ht := triangle_image_card_rank baseTwoTriangle e
    baseTwo_triangle_data.1 baseTwo_triangle_data.2.1
  apply signed_half_diagram_triangle h ht.1 ht.2 ⟨2+2*k,by omega⟩
    (triangle_image_adjacent baseTwoTriangle e baseTwo_triangle_data.2.2)
    ∅ (e 0) (e 1) (e 2)
  · exact fun he => (by decide : (0 : Fin 6) ≠ 1) (e.injective he)
  · exact fun he => (by decide : (0 : Fin 6) ≠ 2) (e.injective he)
  · exact fun he => (by decide : (1 : Fin 6) ≠ 2) (e.injective he)
  · simp
  · simp
  · simp
  · simp [baseTwoTriangle]

theorem rank_three_signed_half_cycles (k : ℕ) :
    Nonempty (SignedHalfCycles (7+4*k) 3) := by
  obtain ⟨e,⟨h⟩⟩ := rank_three_subset_pairing k
  have ht := triangle_image_card_rank baseThreeTriangle e
    baseThree_triangle_data.1 baseThree_triangle_data.2.1
  apply signed_half_diagram_triangle h ht.1 ht.2 ⟨2+2*k,by omega⟩
    (triangle_image_adjacent baseThreeTriangle e baseThree_triangle_data.2.2)
    {e 3} (e 0) (e 1) (e 2)
  · exact fun he => (by decide : (0 : Fin 7) ≠ 1) (e.injective he)
  · exact fun he => (by decide : (0 : Fin 7) ≠ 2) (e.injective he)
  · exact fun he => (by decide : (1 : Fin 7) ≠ 2) (e.injective he)
  · simpa only [Finset.mem_singleton] using
      (fun he => (by decide : (0 : Fin 7) ≠ 3) (e.injective he))
  · simpa only [Finset.mem_singleton] using
      (fun he => (by decide : (1 : Fin 7) ≠ 3) (e.injective he))
  · simpa only [Finset.mem_singleton] using
      (fun he => (by decide : (2 : Fin 7) ≠ 3) (e.injective he))
  · have hA : ({e 0,e 1,e 3} : Finset (Fin (7+4*k))) = {e 3} ∪ {e 0,e 1} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
      tauto
    have hB : ({e 0,e 2,e 3} : Finset (Fin (7+4*k))) = {e 3} ∪ {e 0,e 2} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
      tauto
    have hC : ({e 1,e 2,e 3} : Finset (Fin (7+4*k))) = {e 3} ∪ {e 1,e 2} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_union]
      tauto
    simp only [baseThreeTriangle,Finset.image_insert,Finset.image_singleton,
      Finset.map_insert,Finset.map_singleton,hA,hB,hC]

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerOverlayTransport
