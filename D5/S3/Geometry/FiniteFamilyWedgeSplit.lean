/- GID: D5/S3/Geometry/FiniteFamilyWedgeSplit
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteFamilyWedgeSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Split an actual family wedge at a distinguished factor while retaining its inclusions. -/
import D5.S3.Geometry.CompactWedgeFiniteFactor
import Batteries.Tactic.OpenPrivate

open Set Topology
open scoped ContinuousMap
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.CompactWedgeFiniteFactor

namespace D5.S3.Geometry.FiniteFamilyWedgeSplit

noncomputable section

open private descend from D5.S3.Geometry.CompactWedgeFiniteFactor

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
  let l := collapseMap (wedgePoints (b i) (base r))
  let a := l (Sum.inl (b i))
  have ha : l (Sum.inr (base r)) = a := Quotient.sound
    (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
  let left : C(Z i, Wedge (b i) (base r)) := ⟨l ∘ Sum.inl, l.continuous.comp continuous_inl⟩
  let right : C(FamilyWedge r, Wedge (b i) (base r)) :=
    ⟨l ∘ Sum.inr, l.continuous.comp continuous_inr⟩
  let piece (j : J) : C(Z j, Wedge (b i) (base r)) :=
    if h : j = i then h ▸ left else right.comp (point r ⟨j, h⟩)
  let f := descend b a piece (by
    intro j
    dsimp only [piece]
    split_ifs with hj
    · subst j
      rfl
    · change right (point r ⟨j, hj⟩ (b j)) = a
      rw [show b j = r ⟨j, hj⟩ from rfl, point_base]
      exact ha)
  let remain : C(FamilyWedge r, FamilyWedge b) :=
    descend r (base b) (fun j => point b j.val) (fun j => point_base b j.val)
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
    · change g (piece j x) = point b j x
      by_cases hj : j = i
      · subst j
        rw [show piece i = left from dite_eq_left rfl]
        rfl
      · rw [show piece j = right.comp (point r ⟨j, hj⟩) from dite_eq_right hj]
        rfl
  · intro y
    refine Quotient.inductionOn y ?_
    rintro (x | y)
    · change piece i x = left x
      rw [show piece i = left from dite_eq_left rfl]
    · refine Quotient.inductionOn y ?_
      rintro (u | ⟨j, x⟩)
      · cases u
        exact ha.symm
      · change piece j.val x = right (point r j x)
        rw [show piece j.val = right.comp (point r j) from dite_eq_right j.property]
        rfl
  · intro x
    change piece i x = left x
    rw [show piece i = left from dite_eq_left rfl]
  · intro j x
    change piece j.val x = right (point r j x)
    rw [show piece j.val = right.comp (point r j) from dite_eq_right j.property]
    rfl

#print axioms split

end
end D5.S3.Geometry.FiniteFamilyWedgeSplit
