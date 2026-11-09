/- GID: D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative finite-pattern estimates and Myhill for strongly irreducible subshifts. -/

import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Group.FoelnerFilter
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite patterns that occur in a closed invariant configuration space. -/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Pointwise
open SymbolicDynamics.FullShift

universe u v
namespace D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
variable {G : Type u} [Group G] {A : Type v} [TopologicalSpace A]

/-- Configurations in the given native subshift. -/
abbrev Cfg (X : MulSubshift A G) := {x : G → A // x ∈ X.carrier}

/-- The left group action in the paper's convention. -/
def paperShift (X : MulSubshift A G) (g : G) (x : Cfg X) : Cfg X :=
  ⟨mulShift g⁻¹ x.val, X.mapsTo g⁻¹ x.property⟩

/-- Two finite patterns can be joined when the first collar misses the second support. -/
def SI (X : MulSubshift A G) (Delta : Finset G) : Prop :=
  ∀ (F K : Finset G), Disjoint ((F : Set G) * (Delta : Set G)⁻¹) (K : Set G) →
    ∀ x y : Cfg X, ∃ z : Cfg X,
      (∀ g ∈ F, z.val g = x.val g) ∧ (∀ g ∈ K, z.val g = y.val g)

/-- Restrictions of complete configurations in the same subshift. -/
def PatX (X : MulSubshift A G) (F : Finset G) : Set (F → A) :=
  Set.range (fun x : Cfg X => fun g : F => x.val g)

/-- Common-exterior realization, with the original possibly nonsymmetric collar. -/
theorem common_exterior [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (Delta F : Finset G) (hSI : SI X Delta)
    (x x0 : Cfg X) : ∃ z : Cfg X,
      (∀ g ∈ F, z.val g = x.val g) ∧
      (∀ g ∉ (F : Set G) * (Delta : Set G)⁻¹, z.val g = x0.val g) := by
  classical
  let B : Set (G → A) := X.carrier ∩ {z | ∀ g ∈ F, z g = x.val g}
  have hBc : IsCompact B := by
    apply IsClosed.isCompact
    apply X.isClosed.inter
    convert (isClosed_biInter fun g (_ : g ∈ F) =>
      isClosed_eq (continuous_apply g) (continuous_const : Continuous (fun _ : G → A => x.val g))) using 1
    ext z
    simp
  let J := {g : G // g ∉ (F : Set G) * (Delta : Set G)⁻¹}
  let D : J → Set (G → A) := fun g => {z | z g.val = x0.val g.val}
  have hDc : ∀ g, IsClosed (D g) := fun g =>
    isClosed_eq (continuous_apply g.val) continuous_const
  have hfin : ∀ t : Finset J, (B ∩ ⋂ g ∈ t, D g).Nonempty := by
    intro t
    let K : Finset G := t.image Subtype.val
    have hsep : Disjoint ((F : Set G) * (Delta : Set G)⁻¹) (K : Set G) := by
      apply Set.disjoint_left.mpr
      intro g hg hgK
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hgK
      exact j.property (hj ▸ hg)
    obtain ⟨z, hzF, hzK⟩ := hSI F K hsep x x0
    refine ⟨z.val, ⟨z.property, hzF⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact hzK j.val (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  obtain ⟨z, hzB, hzD⟩ := hBc.inter_iInter_nonempty D hDc hfin
  refine ⟨⟨z, hzB.1⟩, hzB.2, ?_⟩
  intro g hg
  exact Set.mem_iInter.mp hzD ⟨g, hg⟩


/-- A left translate of a finite window. -/
def tile (t : G) (E : Finset G) : Set G := (fun e => t * e) '' (E : Set G)

/-- Occurring patterns whose complete realizations avoid each assigned local pattern. -/
def AvoidPatX (X : MulSubshift A G) (C F T : Finset G) (w : T → C → A) : Set (F → A) :=
  Set.range (fun x : {x : Cfg X // ∀ t : T, ∃ c : C, x.val (t.val * c.val) ≠ w t c} =>
    fun f : F => x.val.val f)

private theorem fiber_loss {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (B D : Finset P) (f : P → Q) (rho : ℕ) (hDB : D ⊆ B)
    (hcap : ∀ b ∈ B.image f, (B.filter (fun p => f p = b)).card ≤ rho)
    (hhole : ∀ b ∈ B.image f, ∃ p ∈ B, f p = b ∧ p ∉ D) :
    D.card * rho ≤ B.card * (rho - 1) := by
  classical
  have hDmap : (D : Set P).MapsTo f (B.image f) :=
    fun p hp => Finset.mem_image_of_mem f (hDB hp)
  rw [Finset.card_eq_sum_card_fiberwise hDmap, Finset.card_eq_sum_card_image f B,
    Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  have hsub : D.filter (fun p => f p = b) ⊆ B.filter (fun p => f p = b) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hDB (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2⟩
  obtain ⟨p, hpB, hpb, hpD⟩ := hhole b hb
  have hstrict : D.filter (fun p => f p = b) ⊂ B.filter (fun p => f p = b) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hp : p ∈ B.filter (fun p => f p = b) := Finset.mem_filter.mpr ⟨hpB, hpb⟩
    rw [← heq] at hp
    exact hpD (Finset.mem_filter.mp hp).1
  have hlt := Finset.card_lt_card hstrict
  have hle := hcap b hb
  have hrho : 0 < rho := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlt) hle
  have hpred : rho - 1 + 1 = rho := Nat.sub_add_cancel hrho
  have hmul := Nat.mul_le_mul_left rho (show
    (D.filter (fun p => f p = b)).card + 1 ≤
      (B.filter (fun p => f p = b)).card by omega)
  nlinarith

private def avoidIndices (X : MulSubshift A G) (C F : Finset G)
    {I : Type*} (t : I → G) (w : I → C → A) (S : Finset I) : Set (F → A) :=
  Set.range (fun x : {x : Cfg X // ∀ i ∈ S, ∃ c : C, x.val (t i * c.val) ≠ w i c} =>
    fun f : F => x.val.val f)

private theorem avoid_indices_step [Finite A] (X : MulSubshift A G)
    (Delta C E F : Finset G) (hSI : SI X Delta)
    (hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G))
    {I : Type*} [DecidableEq I] (t : I → G) (w : I → C → A) (S : Finset I) (i : I)
    (hC : (C : Set G) ⊆ (E : Set G))
    (hin : ∀ j, tile (t j) E ⊆ (F : Set G))
    (hdis : ∀ j ∈ S, Disjoint (tile (t i) E) (tile (t j) E))
    (hw : ∃ y : Cfg X, ∀ c : C, y.val (t i * c.val) = w i c) :
    Nat.card (avoidIndices X C F t w (insert i S)) * Nat.card (PatX X E) ≤
      Nat.card (avoidIndices X C F t w S) * (Nat.card (PatX X E) - 1) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let B := (Set.toFinite (avoidIndices X C F t w S)).toFinset
  let D := (Set.toFinite (avoidIndices X C F t w (insert i S))).toFinset
  let L := E.image (fun e => t i * e)
  let O := F \ L
  let f : (F → A) → (O → A) := fun p o => p ⟨o, (Finset.mem_sdiff.mp o.property).1⟩
  have hreal (p : B) : ∃ x : Cfg X,
      (∀ g : F, x.val g = p.val g) ∧ ∀ j ∈ S, ∃ c : C, x.val (t j * c.val) ≠ w j c := by
    have hp : p.val ∈ avoidIndices X C F t w S := by simpa [B] using p.property
    obtain ⟨⟨x, hx⟩, heq⟩ := hp
    exact ⟨x, fun g => congrFun heq g, hx⟩
  choose rep hrep havoid using hreal
  have hDB : D ⊆ B := by
    intro p hp
    have hp' : p ∈ avoidIndices X C F t w (insert i S) := by simpa [D] using hp
    obtain ⟨⟨x, hx⟩, rfl⟩ := hp'
    have : (fun g : F => x.val g) ∈ avoidIndices X C F t w S :=
      ⟨⟨x, fun j hj => hx j (Finset.mem_insert_of_mem hj)⟩, rfl⟩
    simpa [B] using this
  have hcap (b : O → A) (_hb : b ∈ B.image f) :
      (B.filter (fun p => f p = b)).card ≤ Nat.card (PatX X E) := by
    let key : (B.filter (fun p => f p = b)) → PatX X E := fun p =>
      ⟨fun e : E => (rep ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).val (t i * e.val),
        ⟨⟨mulShift (t i) (rep ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).val,
          X.mapsTo (t i) (rep ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).property⟩, rfl⟩⟩
    have hk : Injective key := by
      intro p q heq
      apply Subtype.ext
      funext g
      by_cases hg : g.val ∈ L
      · obtain ⟨e, he, heg⟩ := Finset.mem_image.mp hg
        have h := congrFun (congrArg Subtype.val heq) ⟨e, he⟩
        change (rep ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).val (t i * e) =
          (rep ⟨q.val, (Finset.mem_filter.mp q.property).1⟩).val (t i * e) at h
        rw [heg] at h
        exact (hrep _ g).symm.trans (h.trans (hrep _ g))
      · have hgo : g.val ∈ O := Finset.mem_sdiff.mpr ⟨g.property, hg⟩
        have hp := congrFun (Finset.mem_filter.mp p.property).2 ⟨g.val, hgo⟩
        have hq := congrFun (Finset.mem_filter.mp q.property).2 ⟨g.val, hgo⟩
        exact hp.trans hq.symm
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective key hk
  have hhole (b : O → A) (hb : b ∈ B.image f) :
      ∃ p ∈ B, f p = b ∧ p ∉ D := by
    obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp hb
    let x := rep ⟨p, hp⟩
    obtain ⟨y, hy⟩ := hw
    let C' := C.image (fun c => t i * c)
    have hsep : Disjoint ((C' : Set G) * (Delta : Set G)⁻¹) (O : Set G) := by
      apply Set.disjoint_left.mpr
      intro a ha hao
      obtain ⟨c', hc', d, hd, rfl⟩ := ha
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      have hcd : c * d ∈ E := hCE (Set.mul_mem_mul hc hd)
      have hL : t i * c * d ∈ L := by
        rw [mul_assoc]
        exact Finset.mem_image.mpr ⟨c * d, hcd, rfl⟩
      exact (Finset.mem_sdiff.mp hao).2 hL
    obtain ⟨z, hzC, hzO⟩ := hSI C' O hsep y x
    have hzold : ∀ j ∈ S, ∃ c : C, z.val (t j * c.val) ≠ w j c := by
      intro j hj
      obtain ⟨c, hc⟩ := havoid ⟨p, hp⟩ j hj
      refine ⟨c, ?_⟩
      have hcE : t j * c.val ∈ tile (t j) E := ⟨c.val, hC c.property, rfl⟩
      have hnot : t j * c.val ∉ L := by
        intro hh
        have hh' : t j * c.val ∈ tile (t i) E := by simpa [tile, L] using hh
        exact Set.disjoint_left.mp (hdis j hj) hh' hcE
      have hO : t j * c.val ∈ O := Finset.mem_sdiff.mpr ⟨hin j hcE, hnot⟩
      rw [hzO _ hO]
      exact hc
    let q : F → A := fun g => z.val g
    have hqB : q ∈ B := by
      have : q ∈ avoidIndices X C F t w S := ⟨⟨z, hzold⟩, rfl⟩
      simpa [B] using this
    refine ⟨q, hqB, ?_, ?_⟩
    · have hqp : f q = f p := by
        funext o
        exact (hzO o o.property).trans (hrep ⟨p, hp⟩ ⟨o, (Finset.mem_sdiff.mp o.property).1⟩)
      exact hqp.trans hpb
    · intro hqD
      have hqD' : q ∈ avoidIndices X C F t w (insert i S) := by simpa [D] using hqD
      obtain ⟨⟨z', hz'⟩, heq⟩ := hqD'
      obtain ⟨c, hc⟩ := hz' i (Finset.mem_insert_self _ _)
      have hcF : t i * c.val ∈ F := hin i ⟨c.val, hC c.property, rfl⟩
      have hh := congrFun heq ⟨t i * c.val, hcF⟩
      apply hc
      exact hh.trans ((hzC _ (Finset.mem_image.mpr ⟨c.val, c.property, rfl⟩)).trans (hy c))
  have hh := fiber_loss B D f (Nat.card (PatX X E)) hDB hcap hhole
  simpa only [B, D, ← Nat.card_eq_card_finite_toFinset] using hh

/-- Strict relative loss from excluding occurring patterns on disjoint collared tiles. -/
theorem relative_pattern_bound [Finite A] (X : MulSubshift A G)
    (Delta C E F T : Finset G) (w : T → C → A)
    (hX : X.carrier.Nonempty) (h1 : 1 ∈ Delta) (hSI : SI X Delta)
    (hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G))
    (hin : ∀ t ∈ T, tile t E ⊆ (F : Set G))
    (hdis : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t E) (tile s E))
    (hw : ∀ t : T, ∃ x : Cfg X, ∀ c : C, x.val (t.val * c.val) = w t c) :
    Nat.card (AvoidPatX X C F T w) * Nat.card (PatX X E) ^ T.card ≤
      Nat.card (PatX X F) * (Nat.card (PatX X E) - 1) ^ T.card := by
  classical
  let rho := Nat.card (PatX X E)
  have hrho : 0 < rho := by
    obtain ⟨x, hx⟩ := hX
    letI : Nonempty (PatX X E) := ⟨⟨_, ⟨⟨x, hx⟩, rfl⟩⟩⟩
    exact Nat.card_pos
  have hC : (C : Set G) ⊆ (E : Set G) := by
    intro c hc
    apply hCE
    simpa only [inv_one, mul_one] using Set.mul_mem_mul hc (show (1 : G) ∈ (Delta : Set G)⁻¹ by simpa)
  let t : T → G := Subtype.val
  have hbound (S : Finset T) :
      Nat.card (avoidIndices X C F t w S) * rho ^ S.card ≤
        Nat.card (PatX X F) * (rho - 1) ^ S.card := by
    induction S using Finset.induction_on with
    | empty =>
      have he : avoidIndices X C F t w ∅ = PatX X F := by
        ext p
        constructor
        · rintro ⟨⟨x, _⟩, rfl⟩
          exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨⟨x, by simp⟩, rfl⟩
      simp [he]
    | @insert i S hi ih =>
      have hs := avoid_indices_step X Delta C E F hSI hCE t w S i hC
        (fun j => hin j.val j.property)
        (fun j hj => hdis i.val i.property j.val j.property
          (fun heq => hi (Subtype.ext heq ▸ hj))) (hw i)
      change Nat.card (avoidIndices X C F t w (insert i S)) * rho ≤
        Nat.card (avoidIndices X C F t w S) * (rho - 1) at hs
      have hm := Nat.mul_le_mul_right (rho ^ S.card) hs
      have hm' := Nat.mul_le_mul_right (rho - 1) ih
      rw [Finset.card_insert_of_notMem hi, pow_succ, pow_succ]
      calc
        _ ≤ Nat.card (avoidIndices X C F t w S) * rho ^ S.card * (rho - 1) := by
          nlinarith [pow_pos hrho S.card]
        _ ≤ _ := by nlinarith
  have he : avoidIndices X C F t w Finset.univ = AvoidPatX X C F T w := by
    ext p
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨⟨x, fun i => hx i (Finset.mem_univ i)⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨⟨x, fun i _ => hx i⟩, rfl⟩
  simpa only [he, Finset.card_univ, Fintype.card_coe] using hbound Finset.univ

end D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
