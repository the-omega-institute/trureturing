/- GID: D5/S3/Geometry/CompactWedgeFiniteFactor
   generality: G
   mirror-B: D5/B/S3/Geometry/CompactWedgeFiniteFactor
   mirror-E: none(waiver:compact-wedge-finite-factor)
   anchors: [mathlib/module/Mathlib.Topology.Compactness.Compact, mathlib/module/Mathlib.Topology.Homotopy.Equiv]
   utility: none
   digest: Compact sources in ordinary coproducts of pointed T1 wedges admit actual finite selected-family models. -/
import D5.S3.Geometry.FiniteConeUnionWedge
import Mathlib.Topology.Compactness.Compact

/-!
# Compact finite-factor reduction for ordinary wedges

All wedges have the quotient topology of a disjoint sum with an additional
distinguished point. Empty families therefore give a point. The finite model
retains the selected factors themselves, including zero-dimensional spheres.
-/

noncomputable section
open Set Topology
open scoped ContinuousMap

namespace D5.S3.Geometry.CompactWedgeFiniteFactor

open FiniteConeUnionWedge (subsetSetoid)

universe u v w

/-- The distinguished point and all factor basepoints in the ordinary coproduct. -/
def basePoints {J : Type u} {Z : J → Type v} (b : ∀ j, Z j) :
    Set (Unit ⊕ (Σ j, Z j)) :=
  {x | x = Sum.inl () ∨ ∃ j, x = Sum.inr ⟨j, b j⟩}

/-- The ordinary family wedge with the quotient topology, including the empty family. -/
abbrev FamilyWedge {J : Type u} {Z : J → Type v} (b : ∀ j, Z j) :=
  Quotient (subsetSetoid (basePoints b))

/-- The distinguished class in a family wedge. -/
def base {J : Type u} {Z : J → Type v} (b : ∀ j, Z j) : FamilyWedge b :=
  Quotient.mk _ (Sum.inl ())

section OneWedge

variable {J : Type u} {Z : J → Type v} [∀ j, TopologicalSpace (Z j)]
    (b : ∀ j, Z j)

/-- The continuous map from an original factor to the quotient wedge. -/
def point (j : J) : C(Z j, FamilyWedge b) :=
  ⟨fun z => Quotient.mk _ (Sum.inr ⟨j, z⟩),
    continuous_quotient_mk'.comp (continuous_inr.comp continuous_sigmaMk)⟩

private theorem point_base (j : J) : point b j (b j) = base b :=
  Quotient.sound (Or.inr ⟨Or.inr ⟨j, rfl⟩, Or.inl rfl⟩)

private theorem raw_eq_point {j : J} {z : Z j} (hz : z ≠ b j)
    (x : Unit ⊕ (Σ j, Z j)) :
    Quotient.mk (subsetSetoid (basePoints b)) x = point b j z ↔
      x = Sum.inr ⟨j, z⟩ := by
  have hn : Sum.inr (Sigma.mk j z) ∉ basePoints b := by
    rintro (h | ⟨k, h⟩)
    · cases h
    · have hk : j = k := congrArg Sigma.fst (Sum.inr.inj h)
      subst k
      exact hz (sigma_mk_injective (Sum.inr.inj h))
  change (Quotient.mk (subsetSetoid (basePoints b)) x =
    Quotient.mk (subsetSetoid (basePoints b)) (Sum.inr ⟨j, z⟩)) ↔ _
  rw [Quotient.eq]
  exact ⟨fun h => h.elim id (fun h => (hn h.2).elim), Or.inl⟩

/-- Factors meeting a subset away from the common basepoint. -/
def support (K : Set (FamilyWedge b)) : Set J :=
  {j | ∃ z : Z j, z ≠ b j ∧ point b j z ∈ K}

/-- A compact subset of the ordinary quotient wedge has finite nonbasepoint support.
Only the T1 property of the individual factors is used. -/
theorem compact_support [∀ j, T1Space (Z j)] {K : Set (FamilyWedge b)}
    (hK : IsCompact K) : (support b K).Finite := by
  classical
  let S := support b K
  choose z hz hmem using (fun j : S => j.property)
  let p : S → FamilyWedge b := fun j => point b j.val (z j)
  have pinj : Function.Injective p := by
    intro j k h
    have hraw := (raw_eq_point b (hz k) (Sum.inr ⟨j.val, z j⟩)).mp h
    exact Subtype.ext (congrArg Sigma.fst (Sum.inr.inj hraw))
  have closed : ∀ E : Set S, IsClosed (p '' E) := by
    intro E
    apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    constructor
    · have he : (fun x : Unit => Quotient.mk (subsetSetoid (basePoints b))
          (Sum.inl x)) ⁻¹' (p '' E) = ∅ := by
        ext x
        constructor
        · rintro ⟨j, _, hj⟩
          have hh := (raw_eq_point b (hz j) (Sum.inl x)).mp hj.symm
          cases hh
        · exact False.elim
      change IsClosed ((fun x : Unit => Quotient.mk (subsetSetoid (basePoints b))
        (Sum.inl x)) ⁻¹' (p '' E))
      rw [he]
      exact isClosed_empty
    · apply isClosed_sigma_iff.mpr
      intro k
      apply Set.Subsingleton.isClosed
      intro x hx y hy
      rcases hx with ⟨j, _, hj⟩
      rcases hy with ⟨l, _, hl⟩
      have ex := Sum.inr.inj ((raw_eq_point b (hz j) (Sum.inr ⟨k, x⟩)).mp hj.symm)
      have ey := Sum.inr.inj ((raw_eq_point b (hz l) (Sum.inr ⟨k, y⟩)).mp hl.symm)
      have hjl : j = l := Subtype.ext
        ((congrArg Sigma.fst ex).symm.trans (congrArg Sigma.fst ey))
      subst l
      exact sigma_mk_injective (ex.trans ey.symm)
  by_cases hn : Nonempty S
  · let j₀ : S := Classical.choice hn
    let U : S → Set (FamilyWedge b) := fun j => (p '' {k | k ≠ j})ᶜ
    have cover : K ⊆ ⋃ j, U j := by
      intro x _
      by_cases hx : ∃ j, p j = x
      · obtain ⟨j, rfl⟩ := hx
        refine mem_iUnion.mpr ⟨j, ?_⟩
        rintro ⟨k, hk, he⟩
        exact hk (pinj he)
      · refine mem_iUnion.mpr ⟨j₀, ?_⟩
        rintro ⟨k, _, he⟩
        exact hx ⟨k, he⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun j => (closed _).isOpen_compl) cover
    have hall : ∀ j : S, j ∈ t := by
      intro j
      obtain ⟨k, hk⟩ := mem_iUnion.mp (ht (hmem j))
      obtain ⟨hkt, hU⟩ := mem_iUnion.mp hk
      by_contra hj
      exact hU ⟨j, (fun he => hj (he.symm ▸ hkt)), rfl⟩
    exact (t.finite_toSet.image Subtype.val).subset (by
      intro j hj
      exact ⟨⟨j, hj⟩, hall ⟨j, hj⟩, rfl⟩)
  · have he : S = ∅ := by
      ext j
      exact ⟨fun hj => (hn ⟨⟨j, hj⟩⟩).elim, False.elim⟩
    change S.Finite
    rw [he]
    exact finite_empty

private def descend {T : Type*} [TopologicalSpace T] (c : T)
    (maps : ∀ j, C(Z j, T)) (hb : ∀ j, maps j (b j) = c) : C(FamilyWedge b, T) := by
  let raw : Unit ⊕ (Σ j, Z j) → T := Sum.elim (fun _ => c) (fun z => maps z.1 z.2)
  have hbase : ∀ x ∈ basePoints b, raw x = c := by
    rintro x (rfl | ⟨j, rfl⟩)
    · rfl
    · exact hb j
  have respects : ∀ x y, (subsetSetoid (basePoints b)).r x y → raw x = raw y := by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact (hbase x hx).trans (hbase y hy).symm
  exact ⟨Quotient.lift raw respects,
    (continuous_const.sumElim (continuous_sigma_iff.mpr
      (fun j => (maps j).continuous))).quotient_lift respects⟩

/-- The selected-family wedge is a fresh ordinary quotient, even when F is empty. -/
abbrev Subwedge (F : Finset J) := FamilyWedge (fun j : F => b j.val)

/-- The actual continuous inclusion of a selected-family quotient wedge. -/
def inclusionMap (F : Finset J) : C(Subwedge b F, FamilyWedge b) :=
  descend (fun j : F => b j.val) (base b) (fun j => point b j.val)
    (fun j => point_base b j.val)

/-- The actual retraction, constant on each omitted factor. -/
def retract (F : Finset J) : C(FamilyWedge b, Subwedge b F) := by
  classical
  let maps : ∀ j, C(Z j, Subwedge b F) := fun j =>
    if h : j ∈ F then point (fun j : F => b j.val) ⟨j, h⟩
    else ContinuousMap.const _ (base (fun j : F => b j.val))
  exact descend b (base _) maps (by
    intro j
    dsimp [maps]
    split_ifs with h
    · exact point_base (fun j : F => b j.val) ⟨j, h⟩
    · rfl)

private theorem retract_include (F : Finset J) (x : Subwedge b F) :
    retract b F (inclusionMap b F x) = x := by
  classical
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with x | ⟨⟨j, hj⟩, z⟩
    · cases x
      rfl
    · change (if h : j ∈ F then point (fun j : F => b j.val) ⟨j, h⟩
        else ContinuousMap.const _ (base (fun j : F => b j.val))) z =
          Quotient.mk _ (Sum.inr ⟨⟨j, hj⟩, z⟩)
      rw [dif_pos hj]
      rfl

private theorem include_retract_of_support (F : Finset J) {K : Set (FamilyWedge b)}
    (hF : support b K ⊆ (F : Set J)) {x : FamilyWedge b} (hx : x ∈ K) :
    inclusionMap b F (retract b F x) = x := by
  classical
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with x | ⟨j, z⟩
    · cases x
      rfl
    · by_cases hz : z = b j
      · subst z
        change inclusionMap b F (retract b F (point b j (b j))) = point b j (b j)
        rw [point_base]
        rfl
      · have hj : j ∈ F := hF ⟨z, hz, hx⟩
        change inclusionMap b F
          ((if h : j ∈ F then point (fun j : F => b j.val) ⟨j, h⟩
            else ContinuousMap.const _ (base (fun j : F => b j.val))) z) = _
        rw [dif_pos hj]
        rfl

end OneWedge

section Coproduct

variable {A : Type u} {I : A → Type v} {Z : ∀ a, I a → Type w}
    [∀ a j, TopologicalSpace (Z a j)] (b : ∀ a j, Z a j)

/-- The original arbitrary coproduct of ordinary quotient wedges. -/
abbrev WedgeSum := Σ a, FamilyWedge (b a)

/-- The concrete finite selected-family quotient model. No factors are replaced. -/
abbrev SelectedModel (A₀ : Finset A) (F : ∀ a : A₀, Finset (I a.val)) :=
  Σ a : A₀, Subwedge (b a.val) (F a)

variable {X : Type*} [TopologicalSpace X]

/-- Actual maps and identities for a finite selected-family model of a compact map. -/
structure FiniteFactor (f : C(X, WedgeSum b)) where
  outer : Finset A
  outer_nonempty : outer.Nonempty
  inner : ∀ a : outer, Finset (I a.val)
  inclusion : C(SelectedModel b outer inner, WedgeSum b)
  retraction : C(WedgeSum b, SelectedModel b outer inner)
  retract_inclusion : ∀ m, retraction (inclusion m) = m
  fixes : ∀ x, inclusion (retraction (f x)) = f x

/-- Construct finite nonempty outer and finite inner selections from compactness alone. -/
def finiteFactor [∀ a j, T1Space (Z a j)] [CompactSpace X] [Nonempty X]
    (f : C(X, WedgeSum b)) : FiniteFactor b f := by
  classical
  let K : Set (WedgeSum b) := range f
  have hK : IsCompact K := isCompact_range f.continuous
  have decomposition := IsCompact.sigma_exists_finite_sigma_eq K hK
  let s := decomposition.choose
  let t := decomposition.choose_spec.choose
  have hs : s.Finite := decomposition.choose_spec.choose_spec.1
  have he : s.sigma t = K := decomposition.choose_spec.choose_spec.2.2
  let A₀ := hs.toFinset
  have outer_mem : ∀ x : X, (f x).1 ∈ A₀ := by
    intro x
    have hh : f x ∈ s.sigma t := he.symm ▸ (mem_range_self x)
    exact hs.mem_toFinset.mpr hh.1
  have hA : A₀.Nonempty := ⟨(f (Classical.choice inferInstance)).1, outer_mem _⟩
  let Kₐ : ∀ a, Set (FamilyWedge (b a)) := fun a =>
    (@Sigma.mk A (fun a => FamilyWedge (b a)) a) ⁻¹' K
  have hKa : ∀ a, IsCompact (Kₐ a) := fun _ =>
    Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hK
  let F : ∀ a : A₀, Finset (I a.val) := fun a =>
    (compact_support (b a.val) (hKa a.val)).toFinset
  have hF : ∀ a : A₀, support (b a.val) (Kₐ a.val) ⊆ (F a : Set (I a.val)) := by
    intro a j hj
    exact (compact_support (b a.val) (hKa a.val)).mem_toFinset.mpr hj
  let inc : C(SelectedModel b A₀ F, WedgeSum b) :=
    ⟨fun m => ⟨m.1.val, inclusionMap (b m.1.val) (F m.1) m.2⟩,
      continuous_sigma_iff.mpr (by
        intro a
        change Continuous ((@Sigma.mk A (fun a => FamilyWedge (b a)) a.val) ∘
          inclusionMap (b a.val) (F a))
        exact continuous_sigmaMk.comp (inclusionMap _ _).continuous)⟩
  let a₀ : A₀ := ⟨hA.choose, hA.choose_spec⟩
  let m₀ : SelectedModel b A₀ F := ⟨a₀, base _⟩
  let ret : C(WedgeSum b, SelectedModel b A₀ F) :=
    ⟨fun y => if h : y.1 ∈ A₀ then ⟨⟨y.1, h⟩, retract (b y.1) (F ⟨y.1, h⟩) y.2⟩
      else m₀,
      continuous_sigma_iff.mpr (by
        intro a
        by_cases h : a ∈ A₀
        · simp only [h, dite_true]
          change Continuous ((@Sigma.mk A₀ (fun a => Subwedge (b a.val) (F a))
            ⟨a, h⟩) ∘ retract (b a) (F ⟨a, h⟩))
          exact continuous_sigmaMk.comp (retract _ _).continuous
        · simp only [h, dite_false]
          exact continuous_const)⟩
  refine ⟨A₀, hA, F, inc, ret, ?_, ?_⟩
  · rintro ⟨a, z⟩
    dsimp [ret, inc]
    simp only [a.property, dite_true]
    exact congrArg (Sigma.mk a) (retract_include (b a.val) (F a) z)
  · intro x
    have hr : ret (f x) =
        ⟨⟨(f x).1, outer_mem x⟩, retract (b (f x).1)
          (F ⟨(f x).1, outer_mem x⟩) (f x).2⟩ := by
      change (if h : (f x).1 ∈ A₀ then _ else _) = _
      rw [dif_pos (outer_mem x)]
    rw [hr]
    change (⟨(f x).1, inclusionMap (b (f x).1) (F ⟨(f x).1, outer_mem x⟩)
      (retract (b (f x).1) (F ⟨(f x).1, outer_mem x⟩) (f x).2)⟩ : WedgeSum b) = f x
    exact congrArg (Sigma.mk (f x).1)
      (include_retract_of_support (b (f x).1) (F ⟨(f x).1, outer_mem x⟩)
        (hF ⟨(f x).1, outer_mem x⟩)
        (show (f x).2 ∈ Kₐ (f x).1 from mem_range_self x))

/-- An actual finite selected-family homotopy model. The right homotopy is r H i,
so the original homotopy need not preserve the finite submodel. -/
def finiteFactorHomotopyEquiv [∀ a j, T1Space (Z a j)] [CompactSpace X] [Nonempty X]
    (e : X ≃ₕ WedgeSum b) :
    X ≃ₕ SelectedModel b (finiteFactor b e.toFun).outer (finiteFactor b e.toFun).inner := by
  let R := finiteFactor b e.toFun
  refine { toFun := R.retraction.comp e.toFun
           invFun := e.invFun.comp R.inclusion
           left_inv := ?_
           right_inv := ?_ }
  · have he : (e.invFun.comp R.inclusion).comp (R.retraction.comp e.toFun) =
        e.invFun.comp e.toFun := by
      ext x
      exact congrArg e.invFun (R.fixes x)
    rw [he]
    exact e.left_inv
  · obtain ⟨H⟩ := e.right_inv
    exact ⟨{
      toFun := fun z => R.retraction (H (z.1, R.inclusion z.2))
      continuous_toFun := R.retraction.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk
          (R.inclusion.continuous.comp continuous_snd)))
      map_zero_left := by
        intro m
        exact congrArg R.retraction (H.apply_zero (R.inclusion m))
      map_one_left := by
        intro m
        exact (congrArg R.retraction (H.apply_one (R.inclusion m))).trans
          (R.retract_inclusion m) }⟩

/-- An empty source has the separate empty outer model. Nonempty outer selection
is asserted only by the nonempty compact-source construction. -/
def emptySourceHomotopyEquiv [IsEmpty X] :
    X ≃ₕ SelectedModel b ∅ (fun _ => ∅) := by
  classical
  letI : IsEmpty (SelectedModel b ∅ (fun _ => ∅)) :=
    ⟨fun m => (Finset.notMem_empty m.1.val) m.1.property⟩
  exact (show X ≃ₜ SelectedModel b ∅ (fun _ => ∅) from {
    toEquiv := Equiv.equivOfIsEmpty _ _
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }).toHomotopyEquiv

end Coproduct

end D5.S3.Geometry.CompactWedgeFiniteFactor
