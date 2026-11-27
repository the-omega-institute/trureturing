/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48mNormalizerObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48mNormalizerObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48m normalizer supplies two independent fixed lattice states of weight two. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.RepresentationTheory.Invariants
import OmegaBuild.Commands

/-!
Nebe, arXiv:1312.3780v2, Section 2 and Theorem 3.2 identify P48m as a
rank-48 lattice with an order-five isometry of type `5-(8,16)-8`, hence
with a rational fixed space of dimension 16. Remark 3.3 gives the order
1200 of the normalizer of its cyclic subgroup, which implies divisibility
by 1200 for the full automorphism group. The Nebe–Sloane Catalogue of Lattices,
P48m entry `GROUP_ORDER`, gives 1200 for the full automorphism group.

* <https://arxiv.org/html/1312.3780v2#S3.Thmtheorem2>
* <https://arxiv.org/html/1312.3780v2#S3.Thmtheorem3>
* <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/P48m.html#GROUP_ORDER>
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48mNormalizerObstruction

open LatticeGeneratingFieldLocality (LatticeData Carrier)
open LatticePositiveEnergy (grade)
open LatticeAllStateReconstruction (mu)
open P48qInvariantQuadratics
  (RationalCartan rationalGram rationalCurrent blockQuadratic invariant_block_quadratics)
open scoped Matrix

/-- A normal subgroup with a proper nonzero fixed Cartan space gives two
independent actual weight-two states fixed by any compatible lifted action.
The homomorphism `π` can be the identity or a subgroup inclusion. -/
theorem normal_subgroup_fixed_weight_two (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {G H : Type*} [Group G] [Group H]
    (ρ : Representation ℚ G (RationalCartan D)) (π : H →* G)
    (A : Representation ℂ H (Carrier D))
    (hGram : ∀ g x y, rationalGram D (ρ g x) (ρ g y) = rationalGram D x y)
    (hCurrent : ∀ h x, A h (rationalCurrent D x) = rationalCurrent D (ρ (π h) x))
    (hMode : ∀ h u n v, A h (mu D u n v) = mu D (A h u) n (A h v))
    (N : Subgroup G) [N.Normal]
    (hFixedPos : 0 < Module.finrank ℚ (Representation.invariants (ρ.comp N.subtype)))
    (hFixedProper : Module.finrank ℚ (Representation.invariants (ρ.comp N.subtype)) < D.rank) :
    ∃ q : Fin 2 → Carrier D,
      (∀ i, q i ∈ grade D 2) ∧ (∀ h i, A h (q i) = q i) ∧ LinearIndependent ℂ q := by
  let W := Representation.invariants (ρ.comp N.subtype)
  change 0 < Module.finrank ℚ W at hFixedPos
  change Module.finrank ℚ W < D.rank at hFixedProper
  have hBot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hFixedPos
    exact (Nat.lt_irrefl 0) hFixedPos
  have hTop : W ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hFixedProper
    exact (Nat.lt_irrefl D.rank) hFixedProper
  -- Mathlib's conjugation proof uses that g⁻¹ * n * g belongs to N.
  have hW (h : H) : W ≤ W.comap ((ρ.comp π) h) :=
    Representation.le_comap_invariants ρ N (π h)
  exact ⟨![blockQuadratic D hPos W, blockQuadratic D hPos ((rationalGram D).orthogonal W)],
    invariant_block_quadratics D hPos (ρ.comp π) A (fun h => hGram (π h))
      hCurrent hMode W hBot hTop hW⟩

/-- The P48m order and rank inputs give two independent invariant quadratics
for every action with the specified Cartan projection and current transport. -/
theorem p48m_fixed_weight_two (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {G H : Type*} [Group G] [Group H]
    (ρ : Representation ℚ G (RationalCartan D)) (π : H →* G)
    (A : Representation ℂ H (Carrier D))
    (hGram : ∀ g x y, rationalGram D (ρ g x) (ρ g y) = rationalGram D x y)
    (hCurrent : ∀ h x, A h (rationalCurrent D x) = rationalCurrent D (ρ (π h) x))
    (hMode : ∀ h u n v, A h (mu D u n v) = mu D (A h u) n (A h v))
    (s : G) (hGroupOrder : Nat.card G = 1200)
    (hNormalizerOrder : Nat.card (Subgroup.normalizer (Subgroup.zpowers s : Set G)) = 1200)
    (hFixedRank :
      Module.finrank ℚ (Representation.invariants (ρ.comp (Subgroup.zpowers s).subtype)) = 16) :
    ∃ q : Fin 2 → Carrier D,
      (∀ i, q i ∈ grade D 2) ∧ (∀ h i, A h (q i) = q i) ∧ LinearIndependent ℂ q := by
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [hGroupOrder]; decide)
  let : (Subgroup.zpowers s).Normal := Subgroup.normalizer_eq_top_iff.mp
    (Subgroup.eq_top_of_card_eq _ (hNormalizerOrder.trans hGroupOrder.symm))
  apply normal_subgroup_fixed_weight_two D hPos ρ π A hGram hCurrent hMode (Subgroup.zpowers s)
  · rw [hFixedRank]
    decide
  · rw [hFixedRank, hRank]
    decide

/-- A conformal inclusion of the actual fixed states carries the two P48m
quadratics into the target's weight-two eigenspace. -/
theorem p48m_weight_two_finrank (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {G H : Type*} [Group G] [Group H]
    (ρ : Representation ℚ G (RationalCartan D)) (π : H →* G)
    (A : Representation ℂ H (Carrier D))
    (hGram : ∀ g x y, rationalGram D (ρ g x) (ρ g y) = rationalGram D x y)
    (hCurrent : ∀ h x, A h (rationalCurrent D x) = rationalCurrent D (ρ (π h) x))
    (hMode : ∀ h u n v, A h (mu D u n v) = mu D (A h u) n (A h v))
    (s : G) (hGroupOrder : Nat.card G = 1200)
    (hNormalizerOrder : Nat.card (Subgroup.normalizer (Subgroup.zpowers s : Set G)) = 1200)
    (hFixedRank :
      Module.finrank ℚ (Representation.invariants (ρ.comp (Subgroup.zpowers s).subtype)) = 16)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V)
    [FiniteDimensional ℂ (L.eigenspace (2 : ℂ))]
    (inclusion : A.invariants →ₗ[ℂ] V) (hInjective : Function.Injective inclusion)
    (hWeight : ∀ x : A.invariants, (x : Carrier D) ∈ grade D 2 →
      inclusion x ∈ L.eigenspace (2 : ℂ)) :
    2 ≤ Module.finrank ℂ (L.eigenspace (2 : ℂ)) := by
  obtain ⟨q, hGrade, hFixed, hIndependent⟩ := p48m_fixed_weight_two D hRank hPos ρ π A
    hGram hCurrent hMode s hGroupOrder hNormalizerOrder hFixedRank
  let qFixed (i : Fin 2) : A.invariants := ⟨q i, fun h => hFixed h i⟩
  have hFixedIndependent : LinearIndependent ℂ qFixed :=
    LinearIndependent.of_comp A.invariants.subtype hIndependent
  let qImage (i : Fin 2) : L.eigenspace (2 : ℂ) :=
    ⟨inclusion (qFixed i), hWeight (qFixed i) (hGrade i)⟩
  have hImageIndependent : LinearIndependent ℂ qImage := by
    apply LinearIndependent.of_comp (L.eigenspace (2 : ℂ)).subtype
    exact hFixedIndependent.map' inclusion (LinearMap.ker_eq_bot.mpr hInjective)
  simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank

#print axioms p48m_weight_two_finrank

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48mNormalizerObstruction
