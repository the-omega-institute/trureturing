/- GID: D5/S3/Arith/Lattices/Golay/RealLeech
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Golay/RealLeech
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Golay integer construction is a real even selfdual lattice with positive unimodular integral charge Gram data. -/

import D5.S3.Arith.Lattices.Golay.IntegerLeech
import D5.S3.Arith.Lattices.Golay.DirectLeechDuality
import D5.S3.Arith.Lattices.Golay.RealLatticeGram

open scoped BigOperators
open D5.S3.Arith.Lattices.Golay.GolayEncoder
open D5.S3.Arith.Lattices.Golay.IntegerLeech
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

namespace D5.S3.Arith.Lattices.Golay.RealLeech
noncomputable section

abbrev Space := Fin 24 → ℝ
abbrev pairing := DirectLeechDuality.B

/-- Coordinate inclusion of the actual integral construction, without rescaling. -/
def castLinear : IntVector →ₗ[ℤ] Space where
  toFun := fun x i => (x i : ℝ)
  map_add' := by intros; ext i; simp
  map_smul' := by intros; ext i; simp

/-- The real image of precisely the original additive subgroup. -/
def lattice : Submodule ℤ Space :=
  ((integerLattice code all_ones_mem).toIntSubmodule).map castLinear

theorem mem_lattice (x : Space) :
    x ∈ lattice ↔ ∃ a : IntVector, Admissible code a ∧ castLinear a = x := Iff.rfl

private theorem raw_membership (x : Space) :
    x ∈ lattice ↔ DirectLeechDuality.RawMembership code x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨m, hm, z, hz, hc, hs⟩ := (representation code a).mp ha
    refine ⟨m, hm, z, ?_, hc, (∑ i, a i) / 8, ?_⟩
    · intro i; change (a i : ℝ) = _; rw [hz i]; push_cast; ring
    · have he := Int.emod_add_mul_ediv (∑ i, a i) 8
      rw [hs] at he
      convert he.symm using 1
      exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  · rintro ⟨m, hm, z, hx, hc, q, hs⟩
    let a : IntVector := fun i => m + 2 * z i
    refine (mem_lattice x).mpr ⟨a, ?_, ?_⟩
    · apply (representation code a).mpr
      refine ⟨m, hm, z, fun _ => rfl, hc, ?_⟩
      change (∑ i, m + 2 * z i) % 8 = 4 * m
      rw [hs]; rcases hm with rfl | rfl <;> omega
    · ext i
      change ((m + 2 * z i : ℤ) : ℝ) = x i
      rw [hx i]; push_cast; ring

theorem even_norm (x : Space) (hx : x ∈ lattice) :
    ∃ k : ℤ, pairing x x = 2 * (k : ℝ) := by
  obtain ⟨a, ha, rfl⟩ := (mem_lattice x).mp hx
  obtain ⟨k, hk⟩ := squareSum_div_sixteen code doubly_even ha
  refine ⟨k, ?_⟩
  have he : pairing (castLinear a) (castLinear a) = (squareSum a : ℝ) / 8 := by
    simp [pairing, DirectLeechDuality.B, castLinear, squareSum, pow_two, dotProduct]
    ring
  rw [he, hk]; push_cast; ring

theorem integral_pairing (x y : Space) (hx : x ∈ lattice) (hy : y ∈ lattice) :
    ∃ k : ℤ, pairing x y = (k : ℝ) := by
  obtain ⟨a, ha, rfl⟩ := (mem_lattice x).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_lattice y).mp hy
  obtain ⟨k, hk⟩ := pairing_integral code all_ones_mem doubly_even ha hb
  refine ⟨k, ?_⟩
  change (1 / 8 : ℝ) * ∑ i, (a i : ℝ) * (b i : ℝ) = _
  rw [← Int.cast_sum, ← hk]
  push_cast; ring

/-- Real selfduality of the actual code and original integer congruences. -/
theorem self_dual : pairing.dualSubmodule lattice = lattice := by
  apply DirectLeechDuality.raw_integer_construction_dual_eq code lattice
  · intro w
    rw [← GolayEncoder.self_dual, LinearMap.BilinForm.mem_orthogonal_iff]
    apply forall₂_congr
    intro c hc
    change dotProduct c w = 0 ↔ dotProduct w c = 0
    rw [dotProduct_comm]
  · intro c hc
    have h := doubly_even c hc
    simpa [weight, Finset.sum_boole] using h
  · exact raw_membership
  · exact even_norm

private theorem eight_mem (i : Fin 24) :
    DirectLeechDuality.castVector (DirectLeechDuality.spike i 8) ∈ lattice :=
  DirectLeechDuality.eight_mem raw_membership i

instance : DiscreteTopology lattice := by
  let J := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 24)))
  have hle : lattice ≤ J := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_lattice x).mp hx
    apply ((Pi.basisFun ℝ (Fin 24)).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨a i, rfl⟩
  let f : lattice → J := fun x => ⟨x, hle x.property⟩
  exact DiscreteTopology.of_continuous_injective
    (continuous_subtype_val.subtype_mk (fun x => hle x.property))
    (fun x y h => Subtype.ext (congrArg Subtype.val h))

instance : IsZLattice ℝ lattice where
  span_top := by
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin 24)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := (Submodule.span ℝ (lattice : Set Space)).smul_mem (1 / 8 : ℝ)
      (Submodule.subset_span (eight_mem i))
    convert h using 1
    ext j
    by_cases hj : j = i <;>
      simp [DirectLeechDuality.castVector, DirectLeechDuality.spike, Pi.basisFun_apply, hj]

private theorem positive (x : Space) (hx : x ≠ 0) : 0 < pairing x x := by
  have hi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hi
  have hs : 0 < ∑ j, x j ^ 2 :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  change 0 < (1 / 8 : ℝ) * ∑ i, x i * x i
  simpa only [← pow_two] using mul_pos (by norm_num : (0:ℝ) < 1/8) hs

/-- Actual integral charge coordinates preserve the full scaled pairing. -/
theorem exists_positive_even_unimodular_gram :
    ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] lattice),
      D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      (∀ a c : Charge D, (bilinear D a c : ℝ) =
        pairing (e a : Space) (e c : Space)) := by
  have hsym : pairing.IsSymm := by
    intro x y
    change (1 / 8 : ℝ) * dotProduct x y = (1 / 8 : ℝ) * dotProduct y x
    rw [dotProduct_comm]
  have hB : pairing.Nondegenerate := by
    intro x hx
    by_contra hn
    have hp := positive x hn
    have hz := hx x
    linarith
  obtain ⟨D, b, e, hrank, hunit, hpos, he, hgram, hcoord, hpair⟩ :=
    exists_latticeData_of_real_selfdual lattice pairing hB hsym positive self_dual
      (fun x => even_norm x x.property)
  exact ⟨D, e, hrank, hunit, hpos, hpair⟩

#print axioms self_dual
#print axioms exists_positive_even_unimodular_gram
end D5.S3.Arith.Lattices.Golay.RealLeech
