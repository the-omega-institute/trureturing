/- GID: D5/S3/Geometry/FiniteFamilyWedgeSplit
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteFamilyWedgeSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Split an actual family wedge at a distinguished factor while retaining its inclusions. -/
import D5.S3.Geometry.CompactWedgeFiniteFactor

open Set Topology
open scoped ContinuousMap
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.CompactWedgeFiniteFactor

namespace D5.S3.Geometry.FiniteFamilyWedgeSplit

noncomputable section

variable {J : Type*} {Z : J → Type*} [∀ j, TopologicalSpace (Z j)]

/-- A distinguished factor and the wedge of the remaining factors form the
original family wedge. The homeomorphism preserves the base class and agrees
with the original factor inclusion on each side. -/
def split (b : ∀ j, Z j) (i : J) :
    {e : FamilyWedge b ≃ₜ Wedge (b i) (base (fun j : {j // j ≠ i} => b j.val)) //
      e (base b) = Quotient.mk _ (Sum.inl (b i)) ∧
      (∀ x, e (point b i x) = Quotient.mk _ (Sum.inl x)) ∧
      ∀ (j : {j // j ≠ i}) x,
        e (point b j.val x) =
          Quotient.mk _ (Sum.inr (point (fun k : {k // k ≠ i} => b k.val) j x))} := by
  classical
  let r := fun j : {j // j ≠ i} => b j.val
  let a : Z i ⊕ FamilyWedge r := Sum.inl (b i)
  have ha : (Quotient.mk (subsetSetoid (wedgePoints (b i) (base r)))
      (Sum.inr (base r))) = Quotient.mk _ a := Quotient.sound
    (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
  let left : C(Z i, Z i ⊕ FamilyWedge r) := ⟨Sum.inl, continuous_inl⟩
  let right : C(FamilyWedge r, Z i ⊕ FamilyWedge r) := ⟨Sum.inr, continuous_inr⟩
  let piece (j : J) : C(Z j, Z i ⊕ FamilyWedge r) :=
    if h : j = i then h ▸ left else right.comp (point r ⟨j, h⟩)
  let rawForward : Unit ⊕ (Σ j, Z j) → Z i ⊕ FamilyWedge r :=
    Sum.elim (fun _ => a) (fun j => piece j.1 j.2)
  have forwardBase : ∀ x ∈ basePoints b, rawForward x ∈ wedgePoints (b i) (base r) := by
    rintro x (rfl | ⟨j, rfl⟩)
    · exact Or.inl rfl
    · by_cases hj : j = i
      · subst j
        exact Or.inl (by simp [rawForward, piece, a])
      · apply Or.inr
        simp [rawForward, piece, hj, right, show b j = r ⟨j, hj⟩ from rfl, point_base]
  have forwardRel : ∀ x y, (subsetSetoid (basePoints b)).r x y →
      (subsetSetoid (wedgePoints (b i) (base r))).r (rawForward x) (rawForward y) := by
    rintro _ _ (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨forwardBase _ hx, forwardBase _ hy⟩
  let f : C(FamilyWedge b, Wedge (b i) (base r)) :=
    ⟨Quotient.map' rawForward forwardRel,
      (continuous_const.sumElim (continuous_sigma_iff.mpr
        (fun j => (piece j).continuous))).quotient_map' forwardRel⟩
  let rawRemain : Unit ⊕ (Σ j : {j // j ≠ i}, Z j.val) → Unit ⊕ (Σ j, Z j) :=
    Sum.map id (fun j => ⟨j.1.val, j.2⟩)
  have remainBase : ∀ x ∈ basePoints r, rawRemain x ∈ basePoints b := by
    rintro x (rfl | ⟨j, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨j.val, rfl⟩
  have remainRel : ∀ x y, (subsetSetoid (basePoints r)).r x y →
      (subsetSetoid (basePoints b)).r (rawRemain x) (rawRemain y) := by
    rintro _ _ (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨remainBase _ hx, remainBase _ hy⟩
  have continuousRemain : Continuous rawRemain := by
    apply continuous_sum_dom.mpr
    exact ⟨continuous_inl, continuous_inr.comp
      (continuous_sigma_iff.mpr (fun j => continuous_sigmaMk))⟩
  let remain : C(FamilyWedge r, FamilyWedge b) :=
    ⟨Quotient.map' rawRemain remainRel, continuousRemain.quotient_map' remainRel⟩
  let raw : C(Z i ⊕ FamilyWedge r, FamilyWedge b) :=
    ⟨Sum.elim (point b i) remain, (point b i).continuous.sumElim remain.continuous⟩
  have compatible (x y : Z i ⊕ FamilyWedge r) :
      (subsetSetoid (wedgePoints (b i) (base r))).r x y → raw x = raw y := by
    rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · have hbase (z : Z i ⊕ FamilyWedge r) (hz : z ∈ wedgePoints (b i) (base r)) :
          raw z = base b := by
        rcases hz with rfl | rfl
        · exact point_base b i
        · rfl
      exact (hbase x hx).trans (hbase y hy).symm
  let g : C(Wedge (b i) (base r), FamilyWedge b) :=
    ⟨Quotient.lift raw compatible, raw.continuous.quotient_lift compatible⟩
  refine ⟨⟨⟨f, g, ?_, ?_⟩, f.continuous, g.continuous⟩, rfl, ?_, ?_⟩
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (u | ⟨j, x⟩)
    · cases u
      exact point_base b i
    · change g (Quotient.mk _ (piece j x)) = point b j x
      by_cases hj : j = i
      · subst j
        rw [show piece i = left from dite_eq_left rfl]
        rfl
      · rw [show piece j = right.comp (point r ⟨j, hj⟩) from dite_eq_right hj]
        rfl
  · intro y
    refine Quotient.inductionOn y ?_
    rintro (x | y)
    · change Quotient.mk _ (piece i x) = Quotient.mk _ (left x)
      rw [show piece i = left from dite_eq_left rfl]
    · refine Quotient.inductionOn y ?_
      rintro (u | ⟨j, x⟩)
      · cases u
        exact ha.symm
      · change Quotient.mk _ (piece j.val x) = Quotient.mk _ (right (point r j x))
        rw [show piece j.val = right.comp (point r j) from dite_eq_right j.property]
        rfl
  · intro x
    change Quotient.mk _ (piece i x) = Quotient.mk _ (left x)
    rw [show piece i = left from dite_eq_left rfl]
  · intro j x
    change Quotient.mk _ (piece j.val x) = Quotient.mk _ (right (point r j x))
    rw [show piece j.val = right.comp (point r j) from dite_eq_right j.property]
    rfl

#print axioms split

end
end D5.S3.Geometry.FiniteFamilyWedgeSplit
