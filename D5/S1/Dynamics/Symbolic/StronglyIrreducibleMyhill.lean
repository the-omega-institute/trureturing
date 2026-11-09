/- GID: D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative finite-pattern estimates and Myhill for strongly irreducible subshifts. -/

import D5.S1.Dynamics.Symbolic.AmenableGardenOfEden
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Group.FoelnerFilter
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite patterns that occur in a closed invariant configuration space. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Function MeasureTheory Filter
open scoped Pointwise Topology
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

/-- A finite input window determines the output at the identity on the actual subshift. -/
def HasMemory (X : MulSubshift A G) (tau : Cfg X → Cfg X) (M : Finset G) : Prop :=
  ∀ x y : Cfg X, (∀ m ∈ M, x.val m = y.val m) → (tau x).val 1 = (tau y).val 1

/-- Continuity on a closed finite-alphabet subshift supplies a finite memory window. -/
theorem finite_memory [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (tau : Cfg X → Cfg X) (htau : Continuous tau) :
    ∃ M : Finset G, HasMemory X tau M := by
  classical
  letI : CompactSpace (Cfg X) := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  let f : Cfg X → A := fun x => (tau x).val 1
  have hf : Continuous f :=
    (continuous_apply 1).comp (continuous_subtype_val.comp htau)
  let K : Set (Cfg X × Cfg X) := {p | f p.1 ≠ f p.2}
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    exact (isClosed_discrete {q : A × A | q.1 ≠ q.2}).preimage
      ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))
  let U : G → Set (Cfg X × Cfg X) := fun g => {p | p.1.val g ≠ p.2.val g}
  have hU : ∀ g, IsOpen (U g) := by
    intro g
    have heval : Continuous (fun x : Cfg X => x.val g) :=
      (continuous_apply g).comp continuous_subtype_val
    have hc : Continuous (fun p : Cfg X × Cfg X => (p.1.val g, p.2.val g)) :=
      (heval.comp continuous_fst).prodMk (heval.comp continuous_snd)
    exact (isOpen_discrete {q : A × A | q.1 ≠ q.2}).preimage hc
  have hcover : K ⊆ ⋃ g, U g := by
    intro p hp
    apply Set.mem_iUnion.mpr
    by_contra hn
    have heq : p.1 = p.2 := by
      apply Subtype.ext
      funext g
      by_contra hg
      exact hn ⟨g, hg⟩
    exact hp (congrArg f heq)
  obtain ⟨M, hM⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨M, ?_⟩
  intro x y hxy
  by_contra hout
  have h := hM (show (x, y) ∈ K from hout)
  obtain ⟨g, hg, hne⟩ := Set.mem_iUnion₂.mp h
  exact hne (hxy g hg)

theorem memory_at (X : MulSubshift A G) (tau : Cfg X → Cfg X)
    (M : Finset G) (hmem : HasMemory X tau M)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (g : G) (x y : Cfg X) (hxy : ∀ m ∈ M, x.val (g * m) = y.val (g * m)) :
    (tau x).val g = (tau y).val g := by
  have hh := hmem (paperShift X g⁻¹ x) (paperShift X g⁻¹ y) (by
    intro m hm
    simpa [paperShift, mulShift] using hxy m hm)
  rw [hequiv, hequiv] at hh
  simpa [paperShift, mulShift] using hh

/-- Finite restrictions of complete images under the given endomorphism of X. -/
def ImagePat (X : MulSubshift A G) (tau : Cfg X → Cfg X) (F : Finset G) : Set (F → A) :=
  Set.range (fun x : Cfg X => fun f : F => (tau x).val f)

/-- Preinjectivity compares occurring source patterns with actual image patterns. -/
theorem preinjective_pattern_lower [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (Delta F M U : Finset G) (hSI : SI X Delta)
    (x0 : Cfg X) (tau : Cfg X → Cfg X) (hmem : HasMemory X tau M)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (hpre : ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite → tau x = tau y → x = y)
    (hU : (F * Delta⁻¹) * M⁻¹ ⊆ U) :
    Nat.card (PatX X F) ≤ Nat.card (ImagePat X tau U) := by
  classical
  have hreal (p : PatX X F) : ∃ z : Cfg X,
      (∀ f : F, z.val f = p.val f) ∧
      (∀ g ∉ (F : Set G) * (Delta : Set G)⁻¹, z.val g = x0.val g) := by
    obtain ⟨x, hx⟩ := p.property
    obtain ⟨z, hzF, hzout⟩ := common_exterior X Delta F hSI x x0
    exact ⟨z, fun f => (hzF f f.property).trans (congrFun hx f), hzout⟩
  choose z hzF hzout using hreal
  let key : PatX X F → ImagePat X tau U := fun p => ⟨_, ⟨z p, rfl⟩⟩
  have hkey : Injective key := by
    intro p q heq
    have hout : tau (z p) = tau (z q) := by
      apply Subtype.ext
      funext g
      by_cases hg : g ∈ U
      · exact congrFun (congrArg Subtype.val heq) ⟨g, hg⟩
      · apply memory_at X tau M hmem hequiv g (z p) (z q)
        intro m hm
        have hnot : g * m ∉ (F : Set G) * (Delta : Set G)⁻¹ := by
          intro hgm
          have hgm' : g * m ∈ F * Delta⁻¹ := by
            change g * m ∈ (↑(F * Delta⁻¹) : Set G)
            simpa only [Finset.coe_mul, Finset.coe_inv] using hgm
          have hg' : g ∈ (F * Delta⁻¹) * M⁻¹ := by
            simpa only [mul_inv_cancel_right] using
              Finset.mul_mem_mul hgm' (show m⁻¹ ∈ M⁻¹ from Finset.inv_mem_inv hm)
          exact hg (hU hg')
        exact (hzout p _ hnot).trans (hzout q _ hnot).symm
    have hfinite : {g | (z p).val g ≠ (z q).val g}.Finite := by
      apply ((F * Delta⁻¹).finite_toSet).subset
      intro g hg
      by_contra hn
      have hn' : g ∉ (F : Set G) * (Delta : Set G)⁻¹ := by
        simpa only [Finset.coe_mul, Finset.coe_inv] using hn
      exact hg ((hzout p g hn').trans (hzout q g hn').symm)
    have hz := hpre (z p) (z q) hfinite hout
    apply Subtype.ext
    funext f
    exact (hzF p f).symm.trans ((congrArg (fun x : Cfg X => x.val f) hz).trans (hzF q f))
  exact Nat.card_le_card_of_injective key hkey

theorem pattern_padding [Finite A] (X : MulSubshift A G)
    (F U : Finset G) (hFU : F ⊆ U) :
    Nat.card (PatX X U) ≤ Nat.card (PatX X F) * Nat.card A ^ (U \ F).card := by
  classical
  let key : PatX X U → PatX X F × ((U \ F : Finset G) → A) := fun p =>
    (⟨fun f : F => p.val ⟨f, hFU f.property⟩, by
        obtain ⟨x, hx⟩ := p.property
        refine ⟨x, ?_⟩
        funext f
        exact congrFun hx ⟨f, hFU f.property⟩⟩,
      fun g => p.val ⟨g, (Finset.mem_sdiff.mp g.property).1⟩)
  have hk : Injective key := by
    intro p q heq
    apply Subtype.ext
    funext g
    by_cases hg : g.val ∈ F
    · exact congrFun (congrArg (fun r : PatX X F × ((U \ F : Finset G) → A) => r.1.val) heq) ⟨g.val, hg⟩
    · exact congrFun (congrArg Prod.snd heq) ⟨g.val, Finset.mem_sdiff.mpr ⟨g.property, hg⟩⟩
  have hh := Nat.card_le_card_of_injective key hk
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using hh

private theorem missing_pattern [Finite A] [DiscreteTopology A]
    (X : MulSubshift A G) (tau : Cfg X → Cfg X) (htau : Continuous tau)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (hns : ¬ Surjective tau) :
    ∃ C : Finset G, C.Nonempty ∧ ∃ p : PatX X C,
      ∀ (x : Cfg X) (t : G), (fun c : C => (tau x).val (t * c.val)) ≠ p.val := by
  classical
  letI : CompactSpace (Cfg X) := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  let f : Cfg X → (G → A) := fun x => (tau x).val
  have hf : Continuous f := continuous_subtype_val.comp htau
  have hclosed : IsClosed (range f) := (isCompact_range hf).isClosed
  obtain ⟨y, hy⟩ : ∃ y : Cfg X, y ∉ range tau := by
    simpa only [Surjective, mem_range, not_forall] using hns
  have hy' : y.val ∉ range f := by
    rintro ⟨x, hx⟩
    exact hy ⟨x, Subtype.ext hx⟩
  obtain ⟨C, U, hU, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl y.val hy'
  have hC : C.Nonempty := by
    by_contra hn
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : f y ∈ (C : Set G).pi U := by simp [he]
    exact hsub hm ⟨y, rfl⟩
  refine ⟨C, hC, ⟨_, ⟨y, rfl⟩⟩, ?_⟩
  intro x t heq
  let x' := paperShift X t⁻¹ x
  have hm : f x' ∈ (C : Set G).pi U := by
    intro c hc
    have he := congrFun heq ⟨c, hc⟩
    have hh : f x' c = (tau x).val (t * c) := by
      change (tau (paperShift X t⁻¹ x)).val c = (tau x).val (t * c)
      rw [hequiv]
      simp [paperShift, mulShift]
    rw [hh, he]
    exact (hU c hc).2
  exact hsub hm ⟨x', rfl⟩

private theorem image_avoidance_bound [Finite A]
    (X : MulSubshift A G) (Delta C E U T : Finset G) (p : PatX X C)
    (tau : Cfg X → Cfg X) (hX : X.carrier.Nonempty) (h1 : 1 ∈ Delta) (hSI : SI X Delta)
    (hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G))
    (hin : ∀ t ∈ T, tile t E ⊆ (U : Set G))
    (hdis : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint (tile t E) (tile s E))
    (hmissing : ∀ (x : Cfg X) (t : G), (fun c : C => (tau x).val (t * c.val)) ≠ p.val) :
    Nat.card (ImagePat X tau U) * Nat.card (PatX X E) ^ T.card ≤
      Nat.card (PatX X U) * (Nat.card (PatX X E) - 1) ^ T.card := by
  classical
  let w : T → C → A := fun _ => p.val
  have hw (t : T) : ∃ x : Cfg X, ∀ c : C, x.val (t.val * c.val) = w t c := by
    obtain ⟨x, hx⟩ := p.property
    refine ⟨paperShift X t.val x, ?_⟩
    intro c
    simpa [paperShift, mulShift, w] using congrFun hx c
  have hsub : ImagePat X tau U ⊆ AvoidPatX X C U T w := by
    rintro q ⟨x, rfl⟩
    refine ⟨⟨tau x, ?_⟩, rfl⟩
    intro t
    have hh := hmissing x t.val
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hh
    exact ⟨c, hc⟩
  have hcard := Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  exact (Nat.mul_le_mul_right _ hcard).trans
    (relative_pattern_bound X Delta C E U T w hX h1 hSI hCE hin hdis hw)

theorem relative_limit_contradiction {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {a rho b : ℕ} (ha : 0 < a) (hrho : 0 < rho) (hb : 0 < b)
    (vol extra tiles : ι → ℕ)
    (hdata : ∀ᶠ i in l, 0 < vol i ∧ vol i ≤ tiles i * b ^ 2 ∧
      rho ^ tiles i ≤ a ^ extra i * (rho - 1) ^ tiles i)
    (hboundary : Filter.Tendsto (fun i => (extra i : ℝ) / vol i) l (nhds 0)) : False := by
  by_cases hr : rho = 1
  · obtain ⟨i, hv, hd, hc⟩ := hdata.exists
    have hk : tiles i ≠ 0 := by intro hk; simp [hk] at hd; omega
    simp [hr, zero_pow hk] at hc
  have hr2 : 2 ≤ rho := by omega
  have hr0 : (0 : ℝ) < rho := by exact_mod_cast hrho
  have hrm : (0 : ℝ) < (rho - 1 : ℕ) := by exact_mod_cast (show 0 < rho - 1 by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  let d := Real.log (rho : ℝ) - Real.log (rho - 1 : ℕ)
  have hd : 0 < d := by
    have hlt : ((rho - 1 : ℕ) : ℝ) < rho := by exact_mod_cast (show rho - 1 < rho by omega)
    exact sub_pos.mpr (Real.log_lt_log hrm hlt)
  let delta := d / (b : ℝ) ^ 2
  have hdelta : 0 < delta := div_pos hd (sq_pos_of_pos hb0)
  have hbound : ∀ᶠ i in l, delta ≤ (extra i : ℝ) / vol i * Real.log (a : ℝ) := by
    filter_upwards [hdata] with i hi
    obtain ⟨hv, hdense, hcount⟩ := hi
    have hv0 : (0 : ℝ) < vol i := by exact_mod_cast hv
    have hlog := Real.log_le_log (pow_pos hr0 (tiles i))
      (show (rho : ℝ) ^ tiles i ≤ (a : ℝ) ^ extra i * ((rho - 1 : ℕ) : ℝ) ^ tiles i by
        exact_mod_cast hcount)
    rw [Real.log_mul (pow_ne_zero _ ha0.ne') (pow_ne_zero _ hrm.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    have hlog' : (tiles i : ℝ) * d ≤ (extra i : ℝ) * Real.log (a : ℝ) := by
      dsimp [d]
      nlinarith only [hlog]
    have hdense' : (vol i : ℝ) ≤ (tiles i : ℝ) * (b : ℝ) ^ 2 := by exact_mod_cast hdense
    have hcharge : (vol i : ℝ) * delta ≤ (tiles i : ℝ) * d := by
      dsimp [delta]
      rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hb0)]
      nlinarith only [mul_le_mul_of_nonneg_right hdense' hd.le]
    calc
      delta ≤ ((extra i : ℝ) * Real.log (a : ℝ)) / vol i :=
        (le_div_iff₀ hv0).mpr (by nlinarith only [hcharge, hlog'])
      _ = (extra i : ℝ) / vol i * Real.log (a : ℝ) := by ring
  have hlim : Filter.Tendsto (fun i => (extra i : ℝ) / vol i * Real.log (a : ℝ)) l (nhds 0) := by
    simpa using hboundary.mul_const (Real.log (a : ℝ))
  have hle : delta ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
  exact (not_le_of_gt hdelta) hle

/-- Myhill's theorem on arbitrary nonempty strongly irreducible subshifts over a
right-counting amenable group, with no countability or finite-type hypothesis. -/
theorem myhill [Finite A] [DiscreteTopology A]
    (ham : letI : MeasurableSpace G := ⊤
      NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)))
    (X : MulSubshift A G) (hX : X.carrier.Nonempty)
    (hSI0 : ∃ Delta : Finset G, SI X Delta)
    (tau : Cfg X → Cfg X) (htau : Continuous tau)
    (hequiv : ∀ g x, tau (paperShift X g x) = paperShift X g (tau x))
    (hpre : ∀ x y : Cfg X, {g | x.val g ≠ y.val g}.Finite → tau x = tau y → x = y) :
    Surjective tau := by
  classical
  obtain ⟨Delta0, hSI0⟩ := hSI0
  let Delta := insert 1 Delta0
  have h1 : 1 ∈ Delta := Finset.mem_insert_self _ _
  have hSI : SI X Delta := by
    intro F K hsep x y
    apply hSI0 F K (hsep.mono_left ?_) x y
    rintro g ⟨f, hf, d, hd, rfl⟩
    refine Set.mul_mem_mul hf ?_
    change d⁻¹ ∈ Delta
    exact Finset.mem_insert_of_mem hd
  obtain ⟨M, hmem⟩ := finite_memory X tau htau
  by_contra hns
  obtain ⟨C, hC, p, hmissing⟩ := missing_pattern X tau htau hequiv hns
  obtain ⟨x0, hx0⟩ := hX
  let xbase : Cfg X := ⟨x0, hx0⟩
  letI : Nonempty A := ⟨x0 1⟩
  let E := C * Delta⁻¹
  have hE : E.Nonempty := by
    obtain ⟨c, hc⟩ := hC
    refine ⟨c, ?_⟩
    simpa using Finset.mul_mem_mul hc (Finset.inv_mem_inv h1)
  have hCE : (C : Set G) * (Delta : Set G)⁻¹ ⊆ (E : Set G) := by
    intro g hg
    simpa only [E, Finset.coe_mul, Finset.coe_inv] using hg
  let K := insert 1 (E ∪ (Delta⁻¹ * M⁻¹))
  have hK : 1 ∈ K := Finset.mem_insert_self _ _
  letI : MeasurableSpace G := ⊤
  letI : NeBot (maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)) := ham
  let l := maxFoelner Gᵐᵒᵖ (Measure.count : Measure G)
  let B : Set G → Finset G := AmenableGardenOfEden.finiteShape
  obtain ⟨hpos, hboundary⟩ := AmenableGardenOfEden.maximal_shapes (G := G)
  let U : Set G → Finset G := fun i => B i * K
  have hBU (i : Set G) : B i ⊆ U i := by
    intro g hg
    simpa only [mul_one] using Finset.mul_mem_mul hg hK
  have hMU (i : Set G) : (B i * Delta⁻¹) * M⁻¹ ⊆ U i := by
    rw [mul_assoc]
    apply Finset.mul_subset_mul_left
    intro k hk
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hk)
  have hpack (i : Set G) := AmenableGardenOfEden.exists_dense_packing E (B i) hE
  choose T hTF hdisjoint hdense using hpack
  have hin (i : Set G) : ∀ t ∈ T i, tile t E ⊆ (U i : Set G) := by
    intro t ht g hg
    obtain ⟨e, he, rfl⟩ := hg
    exact Finset.mul_mem_mul (hTF i ht)
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ he))
  have hdis (i : Set G) : ∀ t ∈ T i, ∀ s ∈ T i, t ≠ s →
      Disjoint (tile t E) (tile s E) := by
    intro t ht s hs hne
    apply Set.disjoint_left.mpr
    rintro g ⟨e, he, rfl⟩ ⟨d, hd, hed⟩
    exact hdisjoint i t ht s hs hne ⟨e, he⟩ ⟨d, hd⟩ hed.symm
  have hcardpos (F : Finset G) : 0 < Nat.card (PatX X F) := by
    letI : Nonempty (PatX X F) := ⟨⟨_, ⟨xbase, rfl⟩⟩⟩
    exact Nat.card_pos
  have hcount (i : Set G) : Nat.card (PatX X E) ^ (T i).card ≤
      Nat.card A ^ (U i \ B i).card * (Nat.card (PatX X E) - 1) ^ (T i).card := by
    have hlower := preinjective_pattern_lower X Delta (B i) M (U i) hSI
      xbase tau hmem hequiv hpre (hMU i)
    have hupper := image_avoidance_bound X Delta C E (U i) (T i) p tau
      ⟨x0, hx0⟩ h1 hSI hCE (hin i) (hdis i) hmissing
    have hpad := pattern_padding X (B i) (U i) (hBU i)
    have hh : Nat.card (PatX X (B i)) * Nat.card (PatX X E) ^ (T i).card ≤
        Nat.card (PatX X (B i)) * (Nat.card A ^ (U i \ B i).card *
          (Nat.card (PatX X E) - 1) ^ (T i).card) := by
      calc
        _ ≤ Nat.card (ImagePat X tau (U i)) * Nat.card (PatX X E) ^ (T i).card :=
          Nat.mul_le_mul_right _ hlower
        _ ≤ Nat.card (PatX X (U i)) * (Nat.card (PatX X E) - 1) ^ (T i).card := hupper
        _ ≤ (Nat.card (PatX X (B i)) * Nat.card A ^ (U i \ B i).card) *
            (Nat.card (PatX X E) - 1) ^ (T i).card := Nat.mul_le_mul_right _ hpad
        _ = _ := by ring
    nlinarith only [hh, hcardpos (B i)]
  have hratio := AmenableGardenOfEden.mul_ratio_tendsto B hpos hboundary K hK
  have hextra : Tendsto (fun i => ((U i \ B i).card : ℝ) / (B i).card) l (𝓝 0) := by
    have hz : Tendsto (fun i => ((U i).card : ℝ) / (B i).card - 1) l (𝓝 0) := by
      simpa only [sub_self, U] using hratio.sub_const 1
    apply hz.congr'
    filter_upwards [hpos] with i hi
    have hv : (0 : ℝ) < (B i).card := by exact_mod_cast hi.card_pos
    rw [Finset.card_sdiff_of_subset (hBU i), Nat.cast_sub (Finset.card_le_card (hBU i)),
      sub_div, div_self hv.ne']
  apply relative_limit_contradiction (l := l) (a := Nat.card A)
    (rho := Nat.card (PatX X E)) (b := E.card) Nat.card_pos (hcardpos E) hE.card_pos
    (fun i => (B i).card) (fun i => (U i \ B i).card) (fun i => (T i).card) ?_ hextra
  filter_upwards [hpos] with i hi
  exact ⟨hi.card_pos, hdense i, hcount i⟩

end D5.S1.Dynamics.Symbolic.StronglyIrreducibleMyhill
