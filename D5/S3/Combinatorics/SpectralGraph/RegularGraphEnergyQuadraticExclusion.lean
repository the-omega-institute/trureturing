/- GID: D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No regular graph has adjacency energy 2k times square root 2. -/

/-
proof_shape: claim: definition; theorem classification after same-delivery expansion:
| Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.degree_root` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.positive_energy` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_flip` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_irreducible` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_flip` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_invariant` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.spectrum_roots` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.submultiset_lower` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` | bind-only | none | external named settlement |
escape_witness: none
admission_basis: open-problem-resolution (#18578; Proved)
Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/20305
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation (module statement_id sha256:ec0d7832a821ce3739753e61d592f651e43de567141c71cd6277d155fa9cb8f1)
-/

import Mathlib.Algebra.Order.Field.Subfield
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion

open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
  (graphEnergy graphSpectrum MatrixKind)

/-- Conjecture 3.11: no regular graph has adjacency energy `2k√2` for a positive integer `k`.
`graphEnergy G .adjacency` is the sum of the absolute values of the eigenvalues of the real
adjacency matrix, counted with multiplicity. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
    G.IsRegularOfDegree r → ∀ k : ℕ, 0 < k →
      graphEnergy G MatrixKind.adjacency ≠ 2 * (k : ℝ) * Real.sqrt 2

/-! Fidelity checks (not part of the conventions). -/

/-- The adjacency energy has center zero: it is the plain sum of `|λ|` over the spectrum. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    graphEnergy G MatrixKind.adjacency =
      ((graphSpectrum G MatrixKind.adjacency).map fun x => |x - 0|).sum := rfl

/-- The spectrum has one entry per vertex (multiplicities retained). -/
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    Multiset.card (graphSpectrum G MatrixKind.adjacency) = Fintype.card V := by
  classical
  simp [graphSpectrum]

end D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion

open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
  (graphEnergy graphSpectrum MatrixKind)

private lemma quadratic_irreducible : Irreducible (X ^ 2 - C (2 : ℚ)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [Polynomial.natDegree_X_pow_sub_C]
  · intro q hq
    have hq' : q ^ 2 = 2 := by simpa [Polynomial.IsRoot, sub_eq_zero] using hq
    have hqR : (q : ℝ) ^ 2 = 2 := by exact_mod_cast hq'
    have hs : Real.sqrt 2 = |(q : ℝ)| := by
      rw [← hqR, Real.sqrt_sq_eq_abs]
    exact irrational_sqrt_two ⟨|q|, by simpa using hs.symm⟩

private lemma quadratic_flip (K : IntermediateField ℚ ℝ) [Normal ℚ K]
    (a : K) (ha : a ^ 2 = 2) : ∃ σ : K ≃ₐ[ℚ] K, σ a = -a := by
  have hm : X ^ 2 - C (2 : ℚ) = minpoly ℚ a :=
    minpoly.eq_of_irreducible_of_monic quadratic_irreducible (by simp [ha])
      (Polynomial.monic_X_pow_sub_C _ (by decide))
  apply minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic a)
  rw [← hm]
  simp [ha]

private lemma submultiset_lower {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s t : Multiset K) (hs : s.sum = 0) (ht : t ≤ s) :
    -(s.map (fun x => |x|)).sum ≤ 2 * t.sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp ht
  have hts := Multiset.abs_sum_le_sum_abs (s := t)
  have hus := Multiset.abs_sum_le_sum_abs (s := u)
  have ht' := neg_abs_le t.sum
  have hu' := le_abs_self u.sum
  simp only [Multiset.sum_add] at hs
  simp only [Multiset.map_add, Multiset.sum_add]
  linarith

private lemma positive_energy {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s : Multiset K) (hs : s.sum = 0) :
    (s.map (fun x => |x|)).sum = 2 * (s.filter (fun x => 0 < x)).sum := by
  classical
  have h : (s.map (fun x => |x|)).sum =
      2 * (s.filter (fun x => 0 < x)).sum - s.sum := by
    clear hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      by_cases ha : 0 < a
      · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons_of_pos s ha]
        rw [abs_of_pos ha, ih]
        ring
      · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons_of_neg s ha]
        rw [abs_of_nonpos (le_of_not_gt ha), ih]
        ring
  simpa [hs] using h

private lemma roots_invariant (K : IntermediateField ℚ ℝ) (p : ℚ[X])
    (hp : (p.map (algebraMap ℚ K)).Splits) (σ : K ≃ₐ[ℚ] K) :
    ((p.map (algebraMap ℚ K)).roots).map σ = (p.map (algebraMap ℚ K)).roots := by
  have h := hp.roots_map σ.toRingHom
  have hc : σ.toRingHom.comp (algebraMap ℚ K) = algebraMap ℚ K :=
    σ.toAlgHom.comp_algebraMap
  rw [Polynomial.map_map, hc] at h
  exact h.symm

private lemma roots_energy_exclusion (K : IntermediateField ℚ ℝ) [Normal ℚ K]
    (p : ℚ[X]) (hp : (p.map (algebraMap ℚ K)).Splits)
    (hz : (p.map (algebraMap ℚ K)).roots.sum = 0)
    (r : ℕ) (hr : 0 < r) (hrm : (r : K) ∈ (p.map (algebraMap ℚ K)).roots)
    (k : ℕ) (hk : 0 < k) :
    (((p.map (algebraMap ℚ K)).roots.map (fun x => |x|)).sum : ℝ) ≠
      2 * (k : ℝ) * Real.sqrt 2 := by
  classical
  letI : IsStrictOrderedRing K := Subfield.toIsStrictOrderedRing K.toSubfield
  let s := (p.map (algebraMap ℚ K)).roots
  let P := s.filter (fun x => 0 < x)
  let S := P.sum
  let E := (s.map (fun x => |x|)).sum
  have hES : E = 2 * S := positive_energy s hz
  intro hE
  have hkK : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  let a : K := E / (2 * (k : K))
  have haR : (a : ℝ) = Real.sqrt 2 := by
    change (E : ℝ) / (2 * (k : ℝ)) = Real.sqrt 2
    rw [hE]
    field_simp
  have ha : a ^ 2 = 2 := by
    apply Subtype.val_injective
    change (a : ℝ) ^ 2 = 2
    rw [haR, Real.sq_sqrt (by norm_num)]
  obtain ⟨σ, hσ⟩ := quadratic_flip K a ha
  have hSa : S = (k : K) * a := by
    dsimp [a]
    field_simp
    linarith
  have hσS : σ S = -S := by
    rw [hSa, map_mul, hσ]
    simp
  let T := P.map σ
  have hT : T ≤ s := by
    have h := Multiset.map_le_map (f := ⇑σ) (Multiset.filter_le (fun x => 0 < x) s)
    exact h.trans_eq (roots_invariant K p hp σ)
  have hrP : (r : K) ∈ P := by
    exact Multiset.mem_filter.mpr ⟨hrm, by exact_mod_cast hr⟩
  have hrT : (r : K) ∈ T := by
    apply Multiset.mem_map.mpr
    exact ⟨(r : K), hrP, by simp⟩
  have hsumT : T.sum = -S := by
    change (P.map σ).sum = -S
    rw [← map_multiset_sum]
    exact hσS
  have he := Multiset.sum_erase hrT
  have hb := submultiset_lower s (T.erase (r : K)) hz
    (le_trans (Multiset.erase_le _ _) hT)
  have hrK : (0 : K) < r := Nat.cast_pos'.mpr hr
  change -E ≤ 2 * (T.erase (r : K)).sum at hb
  rw [hsumT] at he
  linarith

private lemma spectrum_roots {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (((G.adjMatrix ℚ).charpoly).map (algebraMap ℚ ℝ)).roots =
      graphSpectrum G .adjacency := by
  have hmap : (G.adjMatrix ℚ).map (algebraMap ℚ ℝ) = G.adjMatrix ℝ := by
    ext i j
    simp [SimpleGraph.adjMatrix]
  rw [← Matrix.charpoly_map, hmap]
  let A := D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.sourceMatrix
    G .adjacency
  have hA : A = G.adjMatrix ℝ := by
    ext i j
    by_cases h : G.Adj i j <;>
      simp [A,
        D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.sourceMatrix,
        SimpleGraph.adjMatrix, h]
  have hHerm : A.IsHermitian := hA.symm ▸ G.isHermitian_adjMatrix ℝ
  have hs : A.charpoly.roots = graphSpectrum G .adjacency :=
    hHerm.roots_charpoly_eq_eigenvalues
  simpa only [hA] using hs

private lemma degree_root {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : G.IsRegularOfDegree r) :
    (G.adjMatrix ℝ).charpoly.IsRoot (r : ℝ) := by
  rw [← Matrix.charpoly_toLin']
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly (G.adjMatrix ℝ).toLin' (r : ℝ)).mp
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Function.const V (1 : ℝ))
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    ext v
    simpa using SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hr (v := v)
  · intro h
    have := congrFun h (Classical.choice ‹Nonempty V›)
    simpa using this

 theorem result : claim := by
  classical
  intro V _ _ G _ r hr k hk hE
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hkR : (0 : ℝ) < k := Nat.cast_pos'.mpr hk
  have henergypos : 0 < graphEnergy G .adjacency := by rw [hE]; positivity
  have hnonzero : G ≠ ⊥ := by
    intro hG
    subst G
    have hz : graphSpectrum (⊥ : SimpleGraph V) .adjacency =
        Multiset.replicate (Fintype.card V) (0 : ℝ) := by
      have hm : (⊥ : SimpleGraph V).adjMatrix ℚ = 0 := by
        ext i j
        simp [SimpleGraph.adjMatrix]
      rw [← spectrum_roots, hm, Matrix.charpoly_zero]
      simp [Polynomial.roots_X_pow, Multiset.nsmul_singleton]
    simpa [graphEnergy, hz] using henergypos
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    apply hnonzero
    ext v w
    simp only [SimpleGraph.bot_adj, iff_false]
    intro hvw
    have := hvw.degree_pos_left
    rw [hr v, hr0] at this
    omega
  have hv : Nonempty V := by
    by_contra h
    haveI : IsEmpty V := not_nonempty_iff.mp h
    apply hnonzero
    ext v
    exact isEmptyElim v
  letI := hv
  let p : ℚ[X] := (G.adjMatrix ℚ).charpoly
  have hmap : (G.adjMatrix ℚ).map (algebraMap ℚ ℝ) = G.adjMatrix ℝ := by
    ext i j
    simp [SimpleGraph.adjMatrix]
  have hpR : p.map (algebraMap ℚ ℝ) = (G.adjMatrix ℝ).charpoly := by
    rw [← Matrix.charpoly_map, hmap]
  have hsplitR : (p.map (algebraMap ℚ ℝ)).Splits := by
    rw [hpR]
    exact (G.isHermitian_adjMatrix ℝ).splits_charpoly
  let K := IntermediateField.adjoin ℚ (p.rootSet ℝ)
  letI : p.IsSplittingField ℚ K := IntermediateField.adjoin_rootSet_isSplittingField hsplitR
  letI : Normal ℚ K := Normal.of_isSplittingField p
  have hsplitK := Polynomial.IsSplittingField.splits K p
  let s := (p.map (algebraMap ℚ K)).roots
  have hroots : s.map (algebraMap K ℝ) = graphSpectrum G .adjacency := by
    rw [← hsplitK.roots_map, Polynomial.map_map]
    exact spectrum_roots G
  have hz : s.sum = 0 := by
    apply (algebraMap K ℝ).injective
    rw [map_zero, map_multiset_sum, hroots, ← spectrum_roots G, hpR]
    rw [← Matrix.trace_eq_sum_roots_charpoly_of_splits
      (G.isHermitian_adjMatrix ℝ).splits_charpoly]
    exact SimpleGraph.trace_adjMatrix (α := ℝ) (G := G)
  have hrm : (r : K) ∈ s := by
    have hrR : (r : ℝ) ∈ s.map (algebraMap K ℝ) := by
      rw [hroots, ← spectrum_roots G, hpR]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr (degree_root G r hr)
    obtain ⟨a, ha, har⟩ := Multiset.mem_map.mp hrR
    have : a = (r : K) := SetLike.coe_eq_coe.mp har
    simpa [this] using ha
  apply roots_energy_exclusion K p hsplitK hz r hrpos hrm k hk
  change ((s.map (fun x => |x|)).sum : ℝ) = _
  calc
    ((s.map (fun x => |x|)).sum : ℝ) =
        ((s.map (algebraMap K ℝ)).map (fun x => |x|)).sum := by
      change (algebraMap K ℝ) _ = _
      rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
      rfl
    _ = graphEnergy G .adjacency := by rw [hroots]; simp [graphEnergy]
    _ = _ := hE

end D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion
