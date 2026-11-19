/- GID: D5/S3/Topology/PositiveBilinearUnitInterior
   generality: G
   mirror-B: D5/B/S3/Topology/PositiveBilinearUnitInterior
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.LocallyConvex.Separation]
   utility: none
   digest: Positive spanning bilinear maps have interior unit output before zero relations. -/

module

public import D5.S3.Topology.OrderUnitNorm

/-! The same positive readback is called twice. No orthogonality law or
Jordan classification is an input to the two interior conclusions. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.PositiveBilinearUnitInterior

open OrderUnitNorm Set

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The bilinear image spans the whole real target; no positive-generation
claim about product inputs is made. -/
def Spans (f : X →ₗ[ℝ] Y →ₗ[ℝ] Z) : Prop :=
  Submodule.span ℝ (Set.range (fun xy : X × Y => f xy.1 xy.2)) = ⊤

/-- Whole-cone positivity and real spanning force the unit output to be an
interior point, independently of orthogonality preservation. -/
theorem unit_image_interior [FiniteDimensional ℝ Z]
    (A : Data X) (B : Data Y) (C : Data Z) (f : X →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hpos : ∀ a ∈ A.cone, ∀ b ∈ B.cone, f a b ∈ C.cone)
    (hspan : Spans f) : f A.unit B.unit ∈ interior (C.cone : Set Z) := by
  have hA : A.unit ∈ A.cone := interior_subset A.interior_unit
  have hB : B.unit ∈ B.cone := interior_subset B.interior_unit
  by_contra hnot
  obtain ⟨β, hβ, hmass, hβunit⟩ :=
    C.boundary_support (f A.unit B.unit) (hpos A.unit hA B.unit hB) hnot
  have hfirst (a : X) : β (f a B.unit) = 0 := by
    have hb := A.positive_bound (β.toLinearMap.comp (f.flip B.unit))
      (fun x hx => hβ _ (hpos x hx B.unit hB)) a
    change |β (f a B.unit)| ≤ β (f A.unit B.unit) * A.orderNorm a at hb
    rw [hmass, zero_mul] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have hsecond (a : X) (ha : a ∈ A.cone) (b : Y) : β (f a b) = 0 := by
    have hb := B.positive_bound (β.toLinearMap.comp (f a))
      (fun y hy => hβ _ (hpos a ha y hy)) b
    change |β (f a b)| ≤ β (f a B.unit) * B.orderNorm b at hb
    rw [hfirst, zero_mul] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have hall (a : X) (b : Y) : β (f a b) = 0 := by
    have hb := A.positive_bound (β.toLinearMap.comp (f.flip b))
      (fun x hx => (hsecond x hx b).ge) a
    change |β (f a b)| ≤ β (f A.unit b) * A.orderNorm a at hb
    rw [hsecond A.unit hA b, zero_mul] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have hker : Submodule.span ℝ (Set.range (fun xy : X × Y => f xy.1 xy.2)) ≤
      LinearMap.ker β.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact hall a b
  have hu : C.unit ∈ LinearMap.ker β.toLinearMap :=
    hker (by rw [hspan]; trivial)
  exact hβunit.ne' hu

/-- The original reference and the same readback p are used in both calls. -/
def twiceReadback (L : Y →ₗ[ℝ] X →ₗ[ℝ] Z) (p : Z →ₗ[ℝ] Y) (ω : Y) :
    X →ₗ[ℝ] X →ₗ[ℝ] Y where
  toFun a := p.comp (L (p (L ω a)))
  map_add' a b := by ext c; simp
  map_smul' r a := by ext c; simp

/-- Both actual PRE unit outputs are interior before DJ, DH or C13.
The only hypotheses used are the original whole-cone positivity, reference
positivity and the two original real spanning equalities. -/
theorem original_two_call_units_interior
    [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    (A : Data X) (D : Data Y) (E : Data Z)
    (L : Y →ₗ[ℝ] X →ₗ[ℝ] Z) (p : Z →ₗ[ℝ] Y) (ω : Y)
    (hω : ω ∈ D.cone)
    (hL : ∀ d ∈ D.cone, ∀ a ∈ A.cone, L d a ∈ E.cone)
    (hp : ∀ z ∈ E.cone, p z ∈ D.cone)
    (hMspan : Spans (twiceReadback L p ω)) (hLspan : Spans L) :
    twiceReadback L p ω A.unit A.unit ∈ interior (D.cone : Set Y) ∧
      L D.unit A.unit ∈ interior (E.cone : Set Z) := by
  constructor
  · apply unit_image_interior A A D (twiceReadback L p ω) _ hMspan
    intro a ha b hb
    exact hp _ (hL _ (hp _ (hL ω hω a ha)) b hb)
  · exact unit_image_interior D A E L hL hLspan

#print axioms original_two_call_units_interior

end D5.S3.Topology.PositiveBilinearUnitInterior
