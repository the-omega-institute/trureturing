/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite middle-collision residues with coefficient-local cutoffs. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldInnerIterate
import D5.S3.VertexAlgebra.FormalSeries.SupportedCollisionSlice

/-! The fixed middle coefficient uses a finite interval of actual intermediate
modes. Canonical truncation on that interval supplies the outer cutoff for
the original all-integer Borcherds residue. Bakalov--Kac, Matsuo--Nagatomo
and Carnahan attribution is retained in the imported suppliers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorSecondCollisionSlice
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open SupportedChannelSeries SupportedThreeFieldCollision SupportedCollisionSlice
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- The actual middle bracketing, with signed s,y,z exponents. -/
def middleIterate (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (s y z : ℤ) : Oscillator D :=
  iterate D α (β + γ) δ u (canonical D β γ v (-y - 1) t) w s z

/-- Full fixed clearing on this middle channel. The h index expands
(y+z)^a1; the p index expands (s-y)^k. Thus its intermediate exponent is
b-k-p-h, independently of all later auxiliary cutoffs and inverse indices. -/
def clearedMiddleSlice (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b s z : ℤ) : Oscillator D :=
  ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      (((a 1).choose h : ℂ) •
        clearIterate (2 * k - p) (a 0) (a 2 + a 1 - h)
          (fun x y => middleIterate D α β γ δ u v t w x (b - k - p - h) y)
          s z)

/-- A literal product term of the original Jacobi law for u and the actual
state v_{-(b-k-p-h)-1}t, not a supplied common-product certificate. -/
def sliceResidueTerm (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b s z : ℤ) (p h i : ℕ) : Oscillator D :=
  (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
    (((a 1).choose h : ℂ) •
      ((((-1 : ℂ) ^ i) * integerBinomial (((2 * k - p : ℕ) : ℤ) - s - 1) i) •
        product D α (β + γ) δ u (canonical D β γ v (-(b - k - p - h) - 1) t) w
          (s - a 0 - (2 * k - p : ℕ) + i) (z - (a 2 + a 1 - h : ℕ) - i)))

private theorem slice_cutoffs (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k A : ℕ) (b : ℤ) :
    ∃ B : ℕ,
      ∀ r : ℤ, r ∈ modeFiber k A b → ∀ n : ℤ, (B : ℤ) ≤ n →
        canonical D (β + γ) δ (canonical D β γ v r t) n w = 0 := by
  classical
  let nz : ℤ → ℕ := fun r =>
    (Classical.choose (canonical_truncation D (β + γ) δ
      (canonical D β γ v r t) w)).toNat
  let B : ℕ := (modeFiber k A b).sup nz
  refine ⟨B, ?_⟩
  · intro r hr n hn
    have hmax : nz r ≤ B := Finset.le_sup hr
    have original := Classical.choose_spec
      (canonical_truncation D (β + γ) δ (canonical D β γ v r t) w)
    apply original n
    dsimp only [nz] at hmax
    omega

private theorem slice_borcherds_finite (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (b : ℤ) (B : ℕ)
    (hA : ∀ n : ℤ, (a 0 : ℤ) ≤ n → canonical D α δ u n w = 0)
    (hB : ∀ r : ℤ, r ∈ modeFiber k (a 1) b →
      ∀ n : ℤ, (B : ℤ) ≤ n →
        canonical D (β + γ) δ (canonical D β γ v r t) n w = 0)
    (p h : ℕ) (hp : p ≤ k) (hh : h ≤ a 1) (s z : ℤ) :
    clearIterate (2 * k - p) (a 0) (a 2 + a 1 - h)
        (fun x y => middleIterate D α β γ δ u v t w x (b - k - p - h) y) s z =
      ∑ i ∈ Finset.range ((z + B).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial (((2 * k - p : ℕ) : ℤ) - s - 1) i) •
          product D α (β + γ) δ u (canonical D β γ v (-(b - k - p - h) - 1) t) w
            (s - a 0 - (2 * k - p : ℕ) + i) (z - (a 2 + a 1 - h : ℕ) - i) := by
  classical
  let r : ℤ := -(b - k - p - h) - 1
  have member : r ∈ modeFiber k (a 1) b :=
    (mem_modeFiber_iff k (a 1) b r).2 ⟨p, hp, h, hh, by dsimp only [r]; omega⟩
  have bor := iterate_borcherds D α (β + γ) δ u (canonical D β γ v r t) w
    (2 * k - p) (a 0) (a 2 + a 1 - h) hA s z
  change clearIterate (2 * k - p) (a 0) (a 2 + a 1 - h)
    (iterate D α (β + γ) δ u (canonical D β γ v r t) w) s z = _
  rw [bor.2]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hout
  apply hi
  have bound : z + B < i := by
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
    omega
  have inner := hB r member (-(z - (a 2 + a 1 - h : ℕ) - i) - 1) (by omega)
  change (((-1 : ℂ) ^ i) * integerBinomial (((2 * k - p : ℕ) : ℤ) - s - 1) i) •
    canonical D α ((β + γ) + δ) u (-(s - a 0 - (2 * k - p : ℕ) + i) - 1)
      (canonical D (β + γ) δ (canonical D β γ v r t)
        (-(z - (a 2 + a 1 - h : ℕ) - i) - 1) w) = 0
  rw [inner, map_zero, smul_zero]

/-- The actual finite residue, using only the fixed mode interval. -/
theorem actual_collision_slice_finite_residue (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ)
    (hA : ∀ n : ℤ, (a 0 : ℤ) ≤ n → canonical D α δ u n w = 0)
    (b : ℤ) :
    ∃ B : ℕ,
      (∀ r : ℤ, r ∈ modeFiber k (a 1) b → ∀ n : ℤ, (B : ℤ) ≤ n →
        canonical D (β + γ) δ (canonical D β γ v r t) n w = 0) ∧
      ∀ s z : ℤ, clearedMiddleSlice D α β γ δ u v t w k a b s z =
        ∑ i ∈ Finset.range ((z + B).toNat + 1),
          ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
            sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
  classical
  obtain ⟨B, hB⟩ := slice_cutoffs D α β γ δ u v t w k (a 1) b
  refine ⟨B, hB, ?_⟩
  intro s z
  have first : clearedMiddleSlice D α β γ δ u v t w k a b s z =
      ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
        ∑ i ∈ Finset.range ((z + B).toNat + 1),
          sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
    unfold clearedMiddleSlice
    apply Finset.sum_congr rfl
    intro p hp
    have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
    apply Finset.sum_congr rfl
    intro h hh
    have hhA : h ≤ a 1 := by simpa using Finset.mem_range.mp hh
    rw [slice_borcherds_finite D α β γ δ u v t w k a b B hA hB p h hpk hhA s z]
    simp only [Finset.smul_sum, sliceResidueTerm]
  rw [first]
  calc
    _ = ∑ p ∈ Finset.range (k + 1), ∑ i ∈ Finset.range ((z + B).toNat + 1),
        ∑ h ∈ Finset.range (a 1 + 1),
          sliceResidueTerm D α β γ δ u v t w k a b s z p h i := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

end
end D5.S3.VertexAlgebra.LatticeSectorSecondCollisionSlice
