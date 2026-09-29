/- GID: D5/S3/Geometry/MostowPrasadRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/MostowPrasadRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: Dense uniqueness and the group-conjugacy interface for the Mostow--Prasad endpoint.
 -/

import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.MostowPrasadRigidity

/-!
This is the metric and group-theoretic interface needed by the Mostow--Prasad
endpoint. It does not encode hyperbolic curvature, finite volume, or the
existence part of Mostow--Prasad rigidity. Those geometric inputs remain
separate obligations.
-/

/-- Two isometric bijections with the same values on a dense subset are equal. -/
theorem isometry_equiv_eq_of_eqOn_dense
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (s : Set X) (hs : Dense s) (f g : X ≃ᵢ Y)
    (hfg : Set.EqOn f g s) :
    f = g := by
  apply IsometryEquiv.ext
  have hfun : (f : X → Y) = g :=
    hs.denseRange_val.equalizer f.continuous g.continuous (by
      funext x
      exact hfg x.2)
  exact fun x => congrFun hfun x

/- A pointwise form is convenient when the dense set is supplied by a subtype. -/
theorem isometry_equiv_eq_of_dense_range
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
    [MetricSpace Z] (e : Z → X) (he : DenseRange e)
    (f g : X ≃ᵢ Y) (hfg : f ∘ e = g ∘ e) :
    f = g := by
  apply IsometryEquiv.ext
  have hfun : (f : X → Y) = g :=
    he.equalizer f.continuous g.continuous hfg
  exact fun x => congrFun hfun x

/-!
The group-theoretic form of Mostow--Prasad compares holonomy representations
through an abstract group isomorphism.  The following definition isolates the
ambient conjugacy statement without assuming any geometric rigidity theorem.
-/

section GroupConjugacy

variable {G H L K : Type*} [Group G] [Group H] [Group L] [Group K]

/-- An abstract group isomorphism is realized by conjugacy in an ambient group. -/
def GroupConjugacy (e : G ≃* H) (ρ : G →* K) (σ : H →* K) : Prop :=
  ∃ a : K, ∀ g : G, σ (e g) = a * ρ g * a⁻¹

theorem groupConjugacy_symm
    (e : G ≃* H) (ρ : G →* K) (σ : H →* K)
    (h : GroupConjugacy e ρ σ) :
    GroupConjugacy e.symm σ ρ := by
  rcases h with ⟨a, ha⟩
  refine ⟨a⁻¹, ?_⟩
  intro h'
  obtain ⟨g, rfl⟩ := e.surjective h'
  rw [ha]
  simp [mul_assoc]

theorem groupConjugacy_trans
    (e₁ : G ≃* H) (e₂ : H ≃* L)
    (ρ : G →* K) (σ : H →* K) (τ : L →* K)
    (h₁ : GroupConjugacy e₁ ρ σ)
    (h₂ : GroupConjugacy e₂ σ τ) :
    GroupConjugacy (e₁.trans e₂) ρ τ := by
  rcases h₁ with ⟨a, ha⟩
  rcases h₂ with ⟨b, hb⟩
  refine ⟨b * a, ?_⟩
  intro g
  change τ (e₂ (e₁ g)) = (b * a) * ρ g * (b * a)⁻¹
  rw [hb, ha]
  simp [mul_assoc]

/-- The centralizer of the holonomy image is trivial. -/
def RangeCentralizerTrivial (ρ : G →* K) : Prop :=
  ∀ z : K, (∀ g : G, z * ρ g = ρ g * z) → z = 1

theorem groupConjugacy_conjugator_unique
    (e : G ≃* H) (ρ : G →* K) (σ : H →* K)
    {a b : K}
    (ha : ∀ g : G, σ (e g) = a * ρ g * a⁻¹)
    (hb : ∀ g : G, σ (e g) = b * ρ g * b⁻¹)
    (hcentral : RangeCentralizerTrivial ρ) :
    a = b := by
  have hcomm : ∀ g : G, (b⁻¹ * a) * ρ g = ρ g * (b⁻¹ * a) := by
    intro g
    calc
      (b⁻¹ * a) * ρ g = b⁻¹ * (a * ρ g * a⁻¹) * a := by
        simp [mul_assoc]
      _ = b⁻¹ * σ (e g) * a := by rw [ha g]
      _ = b⁻¹ * (b * ρ g * b⁻¹) * a := by rw [hb g]
      _ = ρ g * (b⁻¹ * a) := by simp [mul_assoc]
  have hba : b⁻¹ * a = 1 := hcentral (b⁻¹ * a) hcomm
  exact (inv_mul_eq_one.mp hba).symm

end GroupConjugacy

#print axioms isometry_equiv_eq_of_eqOn_dense
#print axioms isometry_equiv_eq_of_dense_range
#print axioms groupConjugacy_symm
#print axioms groupConjugacy_trans
#print axioms groupConjugacy_conjugator_unique

end D5.S3.Geometry.MostowPrasadRigidity
