/- GID: D5/S3/Geometry/SphereWedgePositiveNormalization
   generality: G
   mirror-B: D5/B/S3/Geometry/SphereWedgePositiveNormalization
   mirror-E: none(waiver:sphere-wedge-normalization)
   anchors: [D5/S3/Geometry/CompactWedgeFiniteFactor, D5/S3/Geometry/EuclideanSphereJoin, mathlib/module/Mathlib.Analysis.InnerProductSpace.Projection.Reflection]
   utility: none
   digest: Actual pointed sphere wedges split as positive bouquets and isolated zero-sphere points. -/
import D5.S3.Geometry.CompactWedgeFiniteFactor
import D5.S3.Geometry.EuclideanSphereJoin
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.Homeomorph.Quotient

/-! Ordinary quotient wedges and coproducts retain every zero-sphere pole and
all empty-family basepoints. No finiteness or connectedness hypothesis is used. -/

noncomputable section
open Set Topology
open scoped ContinuousMap
attribute [local instance] Classical.propDecidable

namespace D5.S3.Geometry.SphereWedgePositiveNormalization

open CompactWedgeFiniteFactor (FamilyWedge base point basePoints)
open EuclideanSphereJoin (StdSphere coordinatePoint)
open FiniteConeUnionWedge (subsetSetoid)

universe u v

private def spherePointHomeomorph (n : ℕ) (b : StdSphere n) :
    {e : StdSphere n ≃ₜ StdSphere n // e b = coordinatePoint n} := by
  let R := (ℝ ∙ (b.val - (coordinatePoint n).val))ᗮ.reflection
  let e : StdSphere n ≃ₜ StdSphere n := R.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map])
  refine ⟨e, Subtype.ext ?_⟩
  exact Submodule.reflection_sub (by
    rw [mem_sphere_zero_iff_norm.mp b.property,
      mem_sphere_zero_iff_norm.mp (coordinatePoint n).property])

private def negativePoint (n : ℕ) : StdSphere n :=
  ⟨-(coordinatePoint n).val, by
    simpa only [mem_sphere_zero_iff_norm, norm_neg] using (coordinatePoint n).property⟩

private theorem zero_poles (x : StdSphere 0) :
    x = coordinatePoint 0 ∨ x = negativePoint 0 := by
  have hx := x.property
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hx
  have hs : x.val 0 ^ 2 = 1 := by simpa using hx
  have he : x.val 0 = 1 ∨ x.val 0 = -1 := sq_eq_one_iff.mp hs
  rcases he with h | h
  · left
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [coordinatePoint, EuclideanSpace.single] using h
  · right
    apply Subtype.ext
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [negativePoint, coordinatePoint, EuclideanSpace.single] using h

private instance zeroSphereFinite : Finite (StdSphere 0) := by
  classical
  have h : (Set.univ : Set (StdSphere 0)).Finite :=
    (Set.toFinite {coordinatePoint 0, negativePoint 0}).subset (by
      intro x _
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using zero_poles x)
  exact Set.finite_univ_iff.mp h

private theorem negative_ne (n : ℕ) : negativePoint n ≠ coordinatePoint n := by
  intro h
  have hh := congrArg (fun x : StdSphere n => x.val 0) h
  norm_num [negativePoint, coordinatePoint, EuclideanSpace.single] at hh

/-- Indices of positive-dimensional spheres. -/
abbrev PositiveIndex {J : Type u} (n : J → ℕ) := {j // 0 < n j}

/-- Each zero-dimensional factor supplies one isolated point. -/
def ZeroIndex {J : Type u} (n : J → ℕ) := {j // n j = 0}

instance {J : Type u} (n : J → ℕ) : TopologicalSpace (ZeroIndex n) := ⊥
instance {J : Type u} (n : J → ℕ) : DiscreteTopology (ZeroIndex n) := ⟨rfl⟩

/-- The positive bouquet is the actual ordinary quotient, also for an empty index type. -/
abbrev PositiveWedge {J : Type u} (n : J → ℕ) :=
  FamilyWedge (fun j : PositiveIndex n => coordinatePoint (n j.val))

private theorem point_base {J : Type*} {Z : J → Type*}
    [∀ j, TopologicalSpace (Z j)] (b : ∀ j, Z j) (j : J) :
    point b j (b j) = base b :=
  Quotient.sound (Or.inr ⟨Or.inr ⟨j, rfl⟩, Or.inl rfl⟩)

variable {J : Type u} (n : J → ℕ) (b : ∀ j, StdSphere (n j))

private abbrev c := fun j : PositiveIndex n => coordinatePoint (n j.val)
private abbrev E (j : J) := (spherePointHomeomorph (n j) (b j)).val
private theorem E_base (j : J) : E n b j (b j) = coordinatePoint (n j) :=
  (spherePointHomeomorph (n j) (b j)).property

private def factorForward (j : J) : StdSphere (n j) → PositiveWedge n ⊕ ZeroIndex n :=
  fun x => if hp : 0 < n j then Sum.inl (point (c n) ⟨j, hp⟩ (E n b j x))
    else if E n b j x = coordinatePoint (n j) then Sum.inl (base (c n))
    else Sum.inr ⟨j, Nat.eq_zero_of_not_pos hp⟩

private theorem continuous_factorForward (j : J) : Continuous (factorForward n b j) := by
  classical
  by_cases hp : 0 < n j
  · simpa only [factorForward, dif_pos hp] using
      continuous_inl.comp ((point (c n) ⟨j, hp⟩).continuous.comp (E n b j).continuous)
  · have hz : n j = 0 := Nat.eq_zero_of_not_pos hp
    haveI : Finite (StdSphere (n j)) := hz ▸ zeroSphereFinite
    exact continuous_of_discreteTopology

private theorem factorForward_base (j : J) :
    factorForward n b j (b j) = Sum.inl (base (c n)) := by
  classical
  unfold factorForward
  split_ifs with hp
  · rw [E_base, point_base]
  · simp [E_base]

private def forward : FamilyWedge b → PositiveWedge n ⊕ ZeroIndex n := by
  let raw : Unit ⊕ (Σ j, StdSphere (n j)) → PositiveWedge n ⊕ ZeroIndex n :=
    Sum.elim (fun _ => Sum.inl (base (c n))) (fun z => factorForward n b z.1 z.2)
  have hb : ∀ x ∈ basePoints b, raw x = Sum.inl (base (c n)) := by
    rintro x (rfl | ⟨j, rfl⟩)
    · rfl
    · exact factorForward_base n b j
  exact Quotient.lift raw (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact (hb x hx).trans (hb y hy).symm)

private theorem continuous_forward : Continuous (forward n b) := by
  apply Continuous.quotient_lift
  exact continuous_const.sumElim (continuous_sigma_iff.mpr
    (fun j => continuous_factorForward n b j))

private def positiveInverse : PositiveWedge n → FamilyWedge b := by
  let raw : Unit ⊕ (Σ j : PositiveIndex n, StdSphere (n j.val)) → FamilyWedge b :=
    Sum.elim (fun _ => base b) (fun z => point b z.1.val ((E n b z.1.val).symm z.2))
  have hb : ∀ x ∈ basePoints (c n), raw x = base b := by
    rintro x (rfl | ⟨j, rfl⟩)
    · rfl
    · change point b j.val ((E n b j.val).symm (coordinatePoint (n j.val))) = base b
      rw [← E_base n b j.val, Homeomorph.symm_apply_apply, point_base]
  exact Quotient.lift raw (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact (hb x hx).trans (hb y hy).symm)

private def inverse : PositiveWedge n ⊕ ZeroIndex n → FamilyWedge b :=
  Sum.elim (positiveInverse n b)
    (fun j => point b j.val ((E n b j.val).symm (negativePoint (n j.val))))

private theorem continuous_inverse : Continuous (inverse n b) := by
  apply Continuous.sumElim
  · apply Continuous.quotient_lift
    exact continuous_const.sumElim (continuous_sigma_iff.mpr (fun j =>
      (point b j.val).continuous.comp (E n b j.val).symm.continuous))
  · exact continuous_of_discreteTopology

private theorem inverse_forward (x : FamilyWedge b) : inverse n b (forward n b x) = x := by
  classical
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with x | ⟨j, x⟩
    · cases x
      rfl
    · change inverse n b (factorForward n b j x) = point b j x
      unfold factorForward
      split_ifs with hp hx
      · change point b j ((E n b j).symm (E n b j x)) = point b j x
        rw [Homeomorph.symm_apply_apply]
      · have he : x = b j := (E n b j).injective (hx.trans (E_base n b j).symm)
        subst x
        exact (point_base b j).symm
      · have hz : n j = 0 := Nat.eq_zero_of_not_pos hp
        have hn : E n b j x = negativePoint (n j) := by
          have poles : ∀ y : StdSphere (n j),
              y = coordinatePoint (n j) ∨ y = negativePoint (n j) := hz ▸ zero_poles
          exact (poles _).resolve_left hx
        change point b j ((E n b j).symm (negativePoint (n j))) = point b j x
        rw [← hn, Homeomorph.symm_apply_apply]

private theorem forward_inverse (x : PositiveWedge n ⊕ ZeroIndex n) :
    forward n b (inverse n b x) = x := by
  classical
  rcases x with x | j
  · induction x using Quotient.inductionOn with
    | h x =>
      rcases x with x | ⟨j, x⟩
      · cases x
        rfl
      · change factorForward n b j.val ((E n b j.val).symm x) = Sum.inl (point (c n) j x)
        simp only [factorForward, dif_pos j.property, Homeomorph.apply_symm_apply]
  · change factorForward n b j.val ((E n b j.val).symm (negativePoint (n j.val))) = Sum.inr j
    have hp : ¬ 0 < n j.val := by rw [j.property]; omega
    simp only [factorForward, dif_neg hp, Homeomorph.apply_symm_apply, negative_ne, if_false]

/-- The actual pointed normalization, for arbitrary index families and arbitrary sphere basepoints. -/
def normalizationHomeomorph : FamilyWedge b ≃ₜ PositiveWedge n ⊕ ZeroIndex n where
  toFun := forward n b
  invFun := inverse n b
  left_inv := inverse_forward n b
  right_inv := forward_inverse n b
  continuous_toFun := continuous_forward n b
  continuous_invFun := continuous_inverse n b

/-- The common basepoint stays in the positive bouquet, including when that bouquet is a point. -/
theorem normalization_base : normalizationHomeomorph n b (base b) = Sum.inl (base (c n)) := rfl

/-- Dependent outer coproduct normalization. Every original outer block retains
its positive bouquet, and each zero factor contributes a separate isolated point. -/
def coproductNormalizationHomeomorph {A : Type u} {I : A → Type v}
    (d : ∀ a, I a → ℕ) (q : ∀ a j, StdSphere (d a j)) :
    {e : (Σ a, FamilyWedge (q a)) ≃ₜ
      (Σ a, PositiveWedge (d a)) ⊕ (Σ a, ZeroIndex (d a)) //
      ∀ a, e ⟨a, base (q a)⟩ = Sum.inl ⟨a, base (c (d a))⟩} := by
  let fiberwise : (Σ a, FamilyWedge (q a)) ≃ₜ
      (Σ a, PositiveWedge (d a) ⊕ ZeroIndex (d a)) := {
    toEquiv := Equiv.sigmaCongrRight (fun a => (normalizationHomeomorph (d a) (q a)).toEquiv)
    continuous_toFun := continuous_sigma_iff.mpr (fun a =>
      continuous_sigmaMk.comp (normalizationHomeomorph (d a) (q a)).continuous)
    continuous_invFun := continuous_sigma_iff.mpr (fun a =>
      continuous_sigmaMk.comp (normalizationHomeomorph (d a) (q a)).symm.continuous) }
  let distribute : (Σ a, PositiveWedge (d a) ⊕ ZeroIndex (d a)) ≃ₜ
      (Σ a, PositiveWedge (d a)) ⊕ (Σ a, ZeroIndex (d a)) := {
    toEquiv := Equiv.sigmaSumDistrib (fun a => PositiveWedge (d a)) (fun a => ZeroIndex (d a))
    continuous_toFun := continuous_sigma_iff.mpr (fun a =>
      (continuous_inl.comp continuous_sigmaMk).sumElim
        (continuous_inr.comp continuous_sigmaMk))
    continuous_invFun := (continuous_sigma_iff.mpr (fun a =>
      continuous_sigmaMk.comp continuous_inl)).sumElim
        (continuous_sigma_iff.mpr (fun a => continuous_sigmaMk.comp continuous_inr)) }
  refine ⟨fiberwise.trans distribute, ?_⟩
  intro a
  change (Equiv.sigmaSumDistrib (fun a => PositiveWedge (d a))
    (fun a => ZeroIndex (d a))) ⟨a, normalizationHomeomorph (d a) (q a) (base (q a))⟩ = _
  rw [normalization_base]
  rfl

#print axioms normalizationHomeomorph
#print axioms normalization_base
#print axioms coproductNormalizationHomeomorph

end D5.S3.Geometry.SphereWedgePositiveNormalization
