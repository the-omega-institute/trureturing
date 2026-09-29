/- GID: D5/S3/Geometry/MostowPrasadRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/MostowPrasadRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: Dense uniqueness and the group-conjugacy interface for the Mostow--Prasad endpoint.
 -/

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ContinuousMap

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
The target theorem quantifies over homotopy equivalences, while the geometric
construction produces isometries.  These predicates keep the existence and
uniqueness obligations separate and make their exact combination explicit.
-/

def HasIsometryRepresentative
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (h : X ≃ₕ Y) : Prop :=
  ∃ e : X ≃ᵢ Y, ContinuousMap.Homotopic (e.toHomeomorph : C(X, Y)) h.toFun

def UniqueIsometryRepresentative
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (h : X ≃ₕ Y) : Prop :=
  ∀ e₁ e₂ : X ≃ᵢ Y,
    ContinuousMap.Homotopic (e₁.toHomeomorph : C(X, Y)) h.toFun →
    ContinuousMap.Homotopic (e₂.toHomeomorph : C(X, Y)) h.toFun →
    e₁ = e₂

/-- The exact `∃!` endpoint for one pair of metric spaces. -/
def MostowPrasadRigidityEndpoint
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] : Prop :=
  ∀ h : X ≃ₕ Y, ∃! e : X ≃ᵢ Y,
    ContinuousMap.Homotopic (e.toHomeomorph : C(X, Y)) h.toFun

theorem hasIsometryRepresentative_of_isometry
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (e : X ≃ᵢ Y) :
    HasIsometryRepresentative e.toHomeomorph.toHomotopyEquiv := by
  refine ⟨e, ?_⟩
  exact ContinuousMap.Homotopic.refl (e.toHomeomorph : C(X, Y))

theorem uniqueIsometryRepresentative_of_eqOn_dense
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (h : X ≃ₕ Y)
    (s : Set X) (hs : Dense s)
    (hboundary : ∀ e₁ e₂ : X ≃ᵢ Y,
      ContinuousMap.Homotopic (e₁.toHomeomorph : C(X, Y)) h.toFun →
      ContinuousMap.Homotopic (e₂.toHomeomorph : C(X, Y)) h.toFun →
      Set.EqOn e₁ e₂ s) :
    UniqueIsometryRepresentative h := by
  intro e₁ e₂ h₁ h₂
  exact isometry_equiv_eq_of_eqOn_dense s hs e₁ e₂ (hboundary e₁ e₂ h₁ h₂)

theorem existsUnique_isometryRepresentative_of_parts
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (h : X ≃ₕ Y)
    (hex : HasIsometryRepresentative h)
    (huniq : UniqueIsometryRepresentative h) :
    ∃! e : X ≃ᵢ Y,
      ContinuousMap.Homotopic (e.toHomeomorph : C(X, Y)) h.toFun := by
  rcases hex with ⟨e, he⟩
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact huniq e' e he' he

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

/-- The orbit of a point under a representation is dense. -/
def DenseOrbit {X : Type*} [MetricSpace X] (ρ : G →* (X ≃ᵢ X)) (x₀ : X) : Prop :=
  Dense (Set.range fun g : G => ρ g x₀)

theorem rangeCentralizerTrivial_of_dense_orbit
    {X : Type*} [MetricSpace X] (ρ : G →* (X ≃ᵢ X)) (x₀ : X)
    (horbit : DenseOrbit ρ x₀)
    (hbase : ∀ z : X ≃ᵢ X,
      (∀ g : G, z * ρ g = ρ g * z) → z x₀ = x₀) :
    RangeCentralizerTrivial ρ := by
  intro z hz
  refine isometry_equiv_eq_of_eqOn_dense (Set.range fun g : G => ρ g x₀) horbit z 1 ?_
  intro y hy
  obtain ⟨g, rfl⟩ := hy
  calc
    z (ρ g x₀) = (z * ρ g) x₀ := rfl
    _ = (ρ g * z) x₀ := by rw [hz g]
    _ = ρ g (z x₀) := rfl
    _ = ρ g x₀ := by rw [hbase z hz]
    _ = (1 : X ≃ᵢ X) (ρ g x₀) := rfl

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
#print axioms hasIsometryRepresentative_of_isometry
#print axioms uniqueIsometryRepresentative_of_eqOn_dense
#print axioms existsUnique_isometryRepresentative_of_parts
#print axioms groupConjugacy_symm
#print axioms groupConjugacy_trans
#print axioms groupConjugacy_conjugator_unique
#print axioms rangeCentralizerTrivial_of_dense_orbit

end D5.S3.Geometry.MostowPrasadRigidity
