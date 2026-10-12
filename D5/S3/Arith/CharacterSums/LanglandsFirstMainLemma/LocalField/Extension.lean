/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream finite-extension support for norm and trace. -/
/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/LocalField/Extension.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/
import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.ResidueField
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite extensions of nonarchimedean local fields
This file exposes Mathlib's trace and norm, their continuous forms, conjugate multisets, and the
elementary symmetric coefficients used in the manuscript's exact norm expansion.  It also proves
that the upper valuation ring is finite over the lower valuation ring and derives the normalized
ramification, residue-degree, norm, and Galois-conjugation laws.
-/

noncomputable section
namespace LanglandsFirstMainLemma

open scoped BigOperators
open scoped Topology
open Polynomial
open Filter
section Trace

variable (F K : Type*) [CommRing F] [CommRing K] [Algebra F K]
/-- The field trace of a finite extension. -/
noncomputable abbrev trace : K →ₗ[F] F := Algebra.trace F K

@[simp]
theorem trace_apply (x : K) : trace F K x = Algebra.trace F K x := rfl
end Trace

section Norm
variable (F K : Type*) [CommRing F] [Ring K] [Algebra F K]

/-- The field norm of a finite extension. -/
noncomputable abbrev norm : K →* F := Algebra.norm F
/-- The field norm restricted to unit groups. -/
noncomputable abbrev normUnits : Kˣ →* Fˣ := Units.map (norm F K)

@[simp]
theorem norm_apply (x : K) : norm F K x = Algebra.norm F x := rfl
@[simp]
theorem coe_normUnits (u : Kˣ) : (normUnits F K u : F) = norm F K (u : K) := rfl

end Norm
section TraceNorm

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K]
omit [Module.Finite F K] in
@[simp]
theorem trace_algebraMap (x : F) :
    trace F K (algebraMap F K x) = Module.finrank F K • x :=
  Algebra.trace_algebraMap x

omit [Module.Finite F K] in
@[simp]
theorem norm_algebraMap (x : F) :
    norm F K (algebraMap F K x) = x ^ Module.finrank F K :=
  Algebra.norm_algebraMap x
end TraceNorm

section TraceNormTower
variable (F K L : Type*) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
  [Module.Free F K] [Module.Finite F K]
  [Module.Free K L] [Module.Finite K L]

/-- Field traces compose in a finite tower. -/
theorem trace_trans (x : L) : trace F K (trace K L x) = trace F L x :=
  Algebra.trace_trace x
omit [Module.Finite F K] [Module.Finite K L] in
/-- Field norms compose in a finite tower. -/
theorem norm_trans (x : L) : norm F K (norm K L x) = norm F L x :=
  Algebra.norm_norm

end TraceNormTower
section Conjugates

/-- The conjugate of `x` selected by an embedding into an overfield. -/
def conjugate {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] (σ : K →ₐ[F] E) (x : K) : E := σ x
/-- The multiset of all conjugates of `x` in an overfield, counted by embeddings. -/
noncomputable def embeddingConjugates (F K E : Type*)
    [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    [FiniteDimensional F K] (x : K) : Multiset E :=
  (Finset.univ : Finset (K →ₐ[F] E)).val.map fun σ => conjugate σ x

variable (F K E : Type*) [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F K]
  [Algebra.IsSeparable F K] [IsAlgClosed E]
/-- A finite separable extension has one conjugate for each degree. -/
@[simp]
theorem embeddingConjugates_card (x : K) :
    (embeddingConjugates F K E x).card = Module.finrank F K := by
  simp [embeddingConjugates, AlgHom.card F K E]

/-- The trace is the sum of all conjugates in an algebraically closed overfield. -/
theorem embeddingConjugates_sum (x : K) :
    (embeddingConjugates F K E x).sum = algebraMap F E (trace F K x) := by
  rw [embeddingConjugates, ← Finset.sum_eq_multiset_sum]
  exact (trace_eq_sum_embeddings E (x := x)).symm
/-- The norm is the product of all conjugates in an algebraically closed overfield. -/
theorem embeddingConjugates_prod (x : K) :
    (embeddingConjugates F K E x).prod = algebraMap F E (norm F K x) := by
  rw [embeddingConjugates, ← Finset.prod_eq_multiset_prod]
  exact (Algebra.norm_eq_prod_embeddings F E x).symm

end Conjugates
section GaloisConjugates

/-- The conjugate of `x` selected by an element of the Galois group. -/
def galoisConjugate {F K : Type*} [Field F] [Field K] [Algebra F K]
    (σ : Gal(K/F)) (x : K) : K := σ x
/-- The multiset of Galois conjugates, counted by automorphisms. -/
noncomputable def galoisConjugates (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (x : K) : Multiset K :=
  (Finset.univ : Finset Gal(K/F)).val.map fun σ => galoisConjugate σ x

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]
/-- The cardinality of the Galois group is the extension degree. -/
@[simp]
theorem galoisConjugates_card (x : K) :
    (galoisConjugates F K x).card = Module.finrank F K := by
  rw [galoisConjugates, Multiset.card_map, ← Finset.card_def, Finset.card_univ,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank F K]

/-- In a finite Galois extension, the trace is the sum of the Galois conjugates. -/
theorem galoisConjugates_sum (x : K) :
    (galoisConjugates F K x).sum = algebraMap F K (trace F K x) := by
  rw [galoisConjugates, ← Finset.sum_eq_multiset_sum]
  exact (trace_eq_sum_automorphisms x).symm
/-- In a finite Galois extension, the norm is the product of the Galois conjugates. -/
theorem galoisConjugates_prod (x : K) :
    (galoisConjugates F K x).prod = algebraMap F K (norm F K x) := by
  rw [galoisConjugates, ← Finset.prod_eq_multiset_prod]
  exact (Algebra.norm_eq_prod_automorphisms F x).symm

/-- Over an infinite base field, the characteristic polynomial of multiplication by `x` splits
as the product of the linear factors indexed by the Galois conjugates of `x`. -/
theorem map_lmul_charpoly_eq_prod_galois [Infinite F] (x : K) :
    (Algebra.lmul F K x).charpoly.map (algebraMap F K) =
      ∏ σ : Gal(K/F), (X - C (σ x)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (algebraMap F K).injective).mono ?_
  rintro z ⟨a, rfl⟩
  change eval (algebraMap F K a)
      ((Algebra.lmul F K x).charpoly.map (algebraMap F K)) =
    eval (algebraMap F K a) (∏ σ : Gal(K/F), (X - C (σ x)))
  rw [Polynomial.eval_map_apply, LinearMap.eval_charpoly]
  have hlin : (algebraMap F (Module.End F K) a - Algebra.lmul F K x) =
      Algebra.lmul F K (algebraMap F K a - x) := by
    ext y
    simp [Algebra.coe_lmul_eq_mul, Algebra.smul_def]
  rw [hlin, ← Algebra.norm_apply, Algebra.norm_eq_prod_automorphisms F]
  change (∏ σ ∈ (Finset.univ : Finset Gal(K/F)),
      σ (algebraMap F K a - x)) =
    eval (algebraMap F K a)
      (∏ σ ∈ (Finset.univ : Finset Gal(K/F)), (X - C (σ x)))
  rw [Polynomial.eval_prod]
  simp
omit [FiniteDimensional F K] [IsGalois F K] in
/-- Trace is invariant under Galois conjugation. -/
@[simp]
theorem trace_galoisConjugate (σ : Gal(K/F)) (x : K) :
    trace F K (σ x) = trace F K x :=
  Algebra.trace_eq_of_algEquiv σ x

omit [FiniteDimensional F K] [IsGalois F K] in
/-- Norm is invariant under Galois conjugation. -/
@[simp]
theorem norm_galoisConjugate (σ : Gal(K/F)) (x : K) :
    norm F K (σ x) = norm F K x :=
  Algebra.norm_eq_of_algEquiv σ x
end GaloisConjugates

section ElementarySymmetric
variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module.Free F K] [Module.Finite F K]

/-- The `j`th elementary symmetric coefficient of an element of a finite extension.
It is the signed characteristic-polynomial coefficient in the base field, and is zero beyond
the extension degree. -/
noncomputable def elementarySymmetric (j : ℕ) (x : K) : F :=
  if j ≤ Module.finrank F K then
    (-1 : F) ^ j * ((Algebra.lmul F K x).charpoly.coeff (Module.finrank F K - j))
  else 0
@[simp]
theorem elementarySymmetric_of_finrank_lt {j : ℕ} (hj : Module.finrank F K < j) (x : K) :
    elementarySymmetric F K j x = 0 := by
  simp [elementarySymmetric, Nat.not_le.mpr hj]

@[simp]
theorem elementarySymmetric_zero (x : K) : elementarySymmetric F K 0 x = 1 := by
  rw [elementarySymmetric, if_pos (Nat.zero_le _), pow_zero, one_mul,
    Nat.sub_zero, ← LinearMap.charpoly_natDegree]
  exact (LinearMap.charpoly_monic (Algebra.lmul F K x)).coeff_natDegree
@[simp]
theorem elementarySymmetric_finrank (x : K) :
    elementarySymmetric F K (Module.finrank F K) x = norm F K x := by
  simp only [elementarySymmetric, le_refl, ↓reduceIte, Nat.sub_self]
  rw [norm_apply, Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]

private theorem trace_eq_neg_charpoly_coeff (x : K) :
    trace F K x =
      -((Algebra.lmul F K x).charpoly.coeff (Module.finrank F K - 1)) := by
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex F K)
  let b := Module.Free.chooseBasis F K
  haveI : Nonempty (Module.Free.ChooseBasisIndex F K) :=
    Fintype.card_pos_iff.mp (by
      rw [← Module.finrank_eq_card_basis b]
      exact Module.finrank_pos)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex F K) = Module.finrank F K :=
    (Module.finrank_eq_card_basis b).symm
  rw [trace_apply, Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F b,
    Matrix.trace_eq_neg_charpoly_coeff, LinearMap.charpoly_toMatrix, hcard]
@[simp]
theorem elementarySymmetric_one (x : K) :
    elementarySymmetric F K 1 x = trace F K x := by
  have hpos : 1 ≤ Module.finrank F K := Module.finrank_pos
  rw [elementarySymmetric, if_pos hpos, trace_eq_neg_charpoly_coeff]
  simp

private theorem elementarySymmetric_eq_sum_minors
    (b : Module.Basis (Module.Free.ChooseBasisIndex F K) F K)
    {j : ℕ} (hj : j ≤ Module.finrank F K) (x : K) :
    elementarySymmetric F K j x =
      ∑ s ∈ (Finset.univ : Finset (Module.Free.ChooseBasisIndex F K)).powersetCard j,
        ((Algebra.leftMulMatrix b x).submatrix
          (Subtype.val : s → Module.Free.ChooseBasisIndex F K)
          (Subtype.val : s → Module.Free.ChooseBasisIndex F K)).det := by
  rw [elementarySymmetric, if_pos hj]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex F K) = Module.finrank F K :=
    (Module.finrank_eq_card_basis b).symm
  have hjcard : j ≤ Fintype.card (Module.Free.ChooseBasisIndex F K) := by
    simpa only [hcard] using hj
  rw [← hcard, ← LinearMap.charpoly_toMatrix (Algebra.lmul F K x) b,
    ← Algebra.leftMulMatrix_apply, Matrix.charpoly_coeff_eq_sum_minors _ j hjcard]
  rw [← mul_assoc, ← pow_add]
  simp [← two_mul]
/-- The exact polynomial norm expansion, including the constant coefficient. -/
theorem norm_one_add_eq_sum_elementarySymmetric (x : K) :
    norm F K (1 + x) =
      ∑ j ∈ Finset.range (Module.finrank F K + 1), elementarySymmetric F K j x := by
  let b := Module.Free.chooseBasis F K
  let M := Algebra.leftMulMatrix b x
  let P : F[X] := Matrix.det (1 + (Polynomial.X : F[X]) • M.map Polynomial.C)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex F K) = Module.finrank F K :=
    (Module.finrank_eq_card_basis b).symm
  have hdeg : P.natDegree < Module.finrank F K + 1 := by
    apply Nat.lt_succ_of_le
    rw [← hcard]
    simpa only [P, Matrix.map_one, Polynomial.C_eq_zero, map_one, add_comm] using
      Polynomial.natDegree_det_X_add_C_le M
        (1 : Matrix (Module.Free.ChooseBasisIndex F K)
          (Module.Free.ChooseBasisIndex F K) F)
  calc
    norm F K (1 + x) = (Algebra.leftMulMatrix b (1 + x)).det := by
      rw [norm_apply]
      exact Algebra.norm_eq_matrix_det b (1 + x)
    _ = (1 + M).det := by simp [M]
    _ = P.eval 1 := by simp [P, eval_det]
    _ = ∑ j ∈ Finset.range (Module.finrank F K + 1), P.coeff j := by
      rw [Polynomial.eval_eq_sum_range' hdeg]
      simp
    _ = ∑ j ∈ Finset.range (Module.finrank F K + 1), elementarySymmetric F K j x := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ Module.finrank F K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [elementarySymmetric_eq_sum_minors F K b hjle]
      exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors M j

/-- The manuscript's norm expansion, with the constant term split off. -/
theorem norm_one_add_eq_one_add_sum_elementarySymmetric (x : K) :
    norm F K (1 + x) =
      1 + ∑ j ∈ Finset.range (Module.finrank F K), elementarySymmetric F K (j + 1) x := by
  rw [norm_one_add_eq_sum_elementarySymmetric, Finset.sum_range_succ',
    elementarySymmetric_zero]
  exact add_comm _ _
/-- Every elementary symmetric coefficient is invariant under an `F`-automorphism of `K`. -/
@[simp]
theorem elementarySymmetric_galoisConjugate
    (σ : Gal(K/F)) (j : ℕ) (x : K) :
    elementarySymmetric F K j (σ x) = elementarySymmetric F K j x := by
  have hconj : σ.toLinearEquiv.conj (Algebra.lmul F K x) =
      Algebra.lmul F K (σ x) := by
    ext y
    simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul]
  rw [elementarySymmetric, elementarySymmetric]
  split_ifs
  · congr 2
    rw [← hconj, LinearEquiv.charpoly_conj]
  · rfl

private theorem algebraMap_elementarySymmetric_eq_esymm_galois_of_le
    [IsGalois F K] [Infinite F] (j : ℕ) (hj : j ≤ Module.finrank F K) (x : K) :
    algebraMap F K (elementarySymmetric F K j x) =
      (galoisConjugates F K x).esymm j := by
  let s := galoisConjugates F K x
  have hcard : s.card = Module.finrank F K := galoisConjugates_card F K x
  have hpoly :
      (Algebra.lmul F K x).charpoly.map (algebraMap F K) =
        (s.map fun t => X - C t).prod := by
    rw [map_lmul_charpoly_eq_prod_galois F K x]
    dsimp only [s]
    rw [galoisConjugates, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp_apply, galoisConjugate]
  have hcoeff := congrArg
    (fun p : K[X] => p.coeff (Module.finrank F K - j)) hpoly
  rw [Polynomial.coeff_map] at hcoeff
  have hk : Module.finrank F K - j ≤ s.card := by
    rw [hcard]
    exact Nat.sub_le _ _
  rw [Multiset.prod_X_sub_C_coeff s (k := Module.finrank F K - j) hk] at hcoeff
  rw [hcard, Nat.sub_sub_self hj] at hcoeff
  change algebraMap F K (elementarySymmetric F K j x) = s.esymm j
  rw [elementarySymmetric, if_pos hj, map_mul, map_pow, map_neg, map_one,
    hcoeff, ← mul_assoc, ← pow_add, (Even.add_self j).neg_one_pow, one_mul]
/-- For a finite Galois extension over an infinite field, the signed characteristic-polynomial
coefficient `elementarySymmetric F K j x`, mapped to `K`, is the `j`th elementary symmetric
function of the multiset of Galois conjugates of `x`. -/
theorem algebraMap_elementarySymmetric_eq_esymm_galois
    [IsGalois F K] [Infinite F] (j : ℕ) (x : K) :
    algebraMap F K (elementarySymmetric F K j x) =
      (galoisConjugates F K x).esymm j := by
  by_cases hj : j ≤ Module.finrank F K
  · exact algebraMap_elementarySymmetric_eq_esymm_galois_of_le F K j hj x
  · rw [elementarySymmetric, if_neg hj, map_zero]
    have hcard : (galoisConjugates F K x).card < j := by
      simpa only [galoisConjugates_card] using Nat.lt_of_not_ge hj
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty j hcard]
    rfl

end ElementarySymmetric
section Topology

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]
  [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace S] [IsModuleTopology R S]
/-- The trace as a continuous additive homomorphism. -/
noncomputable def continuousTrace : ContinuousAddMonoidHom S R :=
  ⟨(trace R S).toAddMonoidHom,
    IsModuleTopology.continuous_of_linearMap (trace R S)⟩

/-- The norm is continuous for the module topology on a finite free algebra. -/
theorem continuous_norm : Continuous (norm R S : S → R) := by
  let b := Module.Free.chooseBasis R S
  rw [show (norm R S : S → R) = fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.leftMulMatrix b).toLinearMap).matrix_det
/-- The norm as a continuous multiplicative homomorphism. -/
noncomputable def continuousNorm : ContinuousMonoidHom S R :=
  ⟨norm R S, continuous_norm R S⟩

/-- The norm on unit groups as a continuous multiplicative homomorphism. -/
noncomputable def continuousNormUnits : ContinuousMonoidHom Sˣ Rˣ :=
  ⟨normUnits R S, (continuous_norm R S).units_map (norm R S)⟩
omit [Module.Free R S] [Module.Finite R S] in
@[simp]
theorem continuousTrace_apply (x : S) : continuousTrace R S x = trace R S x := rfl

@[simp]
theorem continuousNorm_apply (x : S) : continuousNorm R S x = norm R S x := rfl
@[simp]
theorem coe_continuousNormUnits (u : Sˣ) :
    (continuousNormUnits R S u : R) = norm R S (u : S) := rfl

end Topology
section ValuativeExtension

variable (F K : Type*) [CommRing F] [Ring K] [ValuativeRel F] [ValuativeRel K]
  [Algebra F K] [ValuativeExtension F K]
/-- A Mathlib valuative extension makes the canonical valuation on `K` an extension of the
canonical valuation on `F`. -/
instance valuativeExtensionHasExtension :
    (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation K) where
  val_isEquiv_comap := by
    intro x y
    change (ValuativeRel.valuation F) x ≤ (ValuativeRel.valuation F) y ↔
      (ValuativeRel.valuation K) (algebraMap F K x) ≤
        (ValuativeRel.valuation K) (algebraMap F K y)
    rw [← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
      ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    exact (ValuativeExtension.vle_iff_vle (A := F) (B := K) x y).symm

end ValuativeExtension
section ValuationRingFiniteness

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
/-- The algebra map of a valuative extension of nonarchimedean local fields is continuous. -/
theorem continuous_algebraMap : Continuous (algebraMap F K) := by
  apply continuous_of_continuousAt_zero (algebraMap F K)
  rw [ContinuousAt, map_zero]
  rw [(IsValuativeTopology.hasBasis_nhds_zero F).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero K)]
  intro gammaK _
  obtain ⟨pi, hpi⟩ := ValuativeRel.valuation_surjective
    (ValuativeRel.uniformizer F)
  have hpiF : (ValuativeRel.valuation F) pi < 1 := by
    rw [hpi]
    exact ValuativeRel.uniformizer_lt_one
  have hpiK : (ValuativeRel.valuation K) (algebraMap F K pi) < 1 := by
    simpa only [map_one] using
      (Valuation.HasExtension.val_map_lt_iff
        (ValuativeRel.valuation F) (ValuativeRel.valuation K) pi 1).2 hpiF
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hpiK gammaK
  have hpi0 : (ValuativeRel.valuation F) pi ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro hzero
    subst pi
    exact ValuativeRel.uniformizer_ne_zero (R := F) hpi.symm
  refine ⟨Units.mk0 ((ValuativeRel.valuation F) pi ^ n) (pow_ne_zero n hpi0), trivial, ?_⟩
  intro x hx
  have hlt : (ValuativeRel.valuation K) (algebraMap F K x) <
      (ValuativeRel.valuation K) (algebraMap F K (pi ^ n)) :=
    (Valuation.HasExtension.val_map_lt_iff
      (ValuativeRel.valuation F) (ValuativeRel.valuation K) x (pi ^ n)).2 (by
        simpa using hx)
  rw [map_pow, map_pow] at hlt
  exact hlt.trans hn

variable [Module.Finite F K]
/-- A finite valuative extension of local fields carries its canonical finite-dimensional module
topology. -/
noncomputable instance localFieldExtensionIsModuleTopology : IsModuleTopology F K := by
  letI : ContinuousSMul F K :=
    continuousSMul_of_algebraMap F K (continuous_algebraMap F K)
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
    exact isModuleTopologyOfFiniteDimensional

/-- The canonical valuation ring of a finite local-field extension is a finite module over the
base valuation ring. -/
theorem ringOfIntegers_moduleFinite :
    Module.Finite (ringOfIntegers F) (ringOfIntegers K) := by
  let b := Module.Free.chooseBasis F K
  let L : Submodule (ringOfIntegers F) K :=
    Submodule.span (ringOfIntegers F) (Set.range fun i => b i)
  letI : Finite (Module.Free.ChooseBasisIndex F K) := inferInstance
  have hRange : (Set.range fun i => b i).Finite := Set.finite_range _
  letI : Module.Finite (ringOfIntegers F) L :=
    Module.Finite.span_of_finite (ringOfIntegers F) hRange
  have hcoord (i : Module.Free.ChooseBasisIndex F K) : Continuous (b.coord i) := by
    exact IsModuleTopology.continuous_of_linearMap (b.coord i)
  let S : Set K := ⋂ i, (b.coord i) ⁻¹' (ringOfIntegers F : Set F)
  have hSopen : IsOpen S := by
    dsimp only [S]
    apply isOpen_iInter_of_finite
    intro i
    exact (Valuation.isOpen_integer (v := ValuativeRel.valuation F)).preimage (hcoord i)
  have hSL : S ⊆ (L : Set K) := by
    intro x hx
    have hxcoord : ∀ i, b.repr x i ∈ ringOfIntegers F := by
      intro i
      exact Set.mem_iInter.mp hx i
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i hi
    let a : ringOfIntegers F := ⟨b.repr x i, hxcoord i⟩
    have hbi : b i ∈ L := Submodule.subset_span (Set.mem_range_self i)
    have hsmul := L.smul_mem a hbi
    have haeq : algebraMap (ringOfIntegers F) F a = b.repr x i := by
      change (a : F) = b.repr x i
      rfl
    rw [Algebra.smul_def,
      IsScalarTower.algebraMap_apply (ringOfIntegers F) F K, haeq] at hsmul
    simpa only [Algebra.smul_def] using hsmul
  have h0S : (0 : K) ∈ S := by
    simp [S]
  have hLnhds : (L : Set K) ∈ 𝓝 (0 : K) :=
    Filter.mem_of_superset (hSopen.mem_nhds h0S) hSL
  have hLopen : IsOpen (L : Set K) :=
    L.toAddSubgroup.isOpen_of_mem_nhds hLnhds

  let coeLinear : ringOfIntegers K →ₗ[ringOfIntegers F] K :=
    { toFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun a y => rfl }
  let N : Submodule (ringOfIntegers F) (ringOfIntegers K) := L.comap coeLinear
  let f : N →ₗ[ringOfIntegers F] L :=
    LinearMap.codRestrict L (coeLinear.comp N.subtype) (fun y => y.prop)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : L => (z : K)) hxy
  have hNfg : (⊤ : Submodule (ringOfIntegers F) N).FG := by
    apply Submodule.fg_of_fg_map_injective f hf
    exact IsNoetherian.noetherian _
  letI : Module.Finite (ringOfIntegers F) N := ⟨hNfg⟩
  have hNopen : IsOpen (N : Set (ringOfIntegers K)) := by
    change IsOpen (Subtype.val ⁻¹' (L : Set K))
    exact hLopen.preimage continuous_subtype_val
  have hOKcompact : IsCompact ((ringOfIntegers K : Subring K) : Set K) := by
    change IsCompact {y : K | (ValuativeRel.valuation K) y ≤ 1}
    exact IsNonarchimedeanLocalField.isCompact_closedBall K 1
  letI : CompactSpace (ringOfIntegers K) :=
    isCompact_iff_compactSpace.mp hOKcompact
  letI : Finite ((ringOfIntegers K) ⧸ N) :=
    N.toAddSubgroup.quotient_finite_of_isOpen hNopen
  letI : Module.Finite (ringOfIntegers F) ((ringOfIntegers K) ⧸ N) :=
    Module.Finite.of_finite
  exact Module.Finite.of_submodule_quotient N

/-- The upper canonical valuation ring is the integral closure of the lower valuation ring in the
finite extension field. -/
theorem ringOfIntegers_isIntegralClosure :
    IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  infer_instance
end ValuationRingFiniteness

section IntegralOrder
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem ord_coe_unit_eq_zero (u : (ringOfIntegers K)ˣ) :
    ord K (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) = 0 := by
  have huval : (ValuativeRel.valuation K)
      (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) = 1 :=
    Valuation.Integers.one_of_isUnit
      (Valuation.integer.integers (ValuativeRel.valuation K)) u.isUnit
  apply le_antisymm
  · rw [← ord_one K, ord_le_ord_iff]
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    simp [huval]
  · rw [← ord_one K, ord_le_ord_iff]
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    simp [huval]
private theorem ord_coe_irreducible_eq_one
    {ϖ : ringOfIntegers K} (hϖ : Irreducible ϖ) :
    ord K (algebraMap (ringOfIntegers K) K ϖ) = 1 := by
  rw [show algebraMap (ringOfIntegers K) K ϖ = (ϖ : K) by
    exact congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) ϖ]
  apply ord_uniformizer K
  apply Valuation.isUniformizer_of_maximalIdeal_eq_span
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ

private theorem ord_coe_eq_addVal_of_eq_nat
    (a : ringOfIntegers K) (n : ℕ)
    (ha : IsDiscreteValuationRing.addVal (ringOfIntegers K) a = n) :
    ord K (a : K) = (n : WithTop ℤ) := by
  by_cases ha0 : a = 0
  · subst a
    have hbad : (⊤ : ℕ∞) = (n : ℕ∞) := by
      simp at ha
    exact ((WithTop.top_ne_coe : (⊤ : ℕ∞) ≠ (n : ℕ∞)) hbad).elim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)
  obtain ⟨m, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hmn : m = n := by
    rw [IsDiscreteValuationRing.addVal_def' u hϖ m] at ha
    exact_mod_cast ha
  subst m
  change ord K (algebraMap (ringOfIntegers K) K
    ((u : ringOfIntegers K) * ϖ ^ n)) = (n : WithTop ℤ)
  rw [map_mul, map_pow, ord_mul, ord_pow, ord_coe_unit_eq_zero,
    ord_coe_irreducible_eq_one K hϖ, zero_add]
  simp
end IntegralOrder

section GaloisOrder
variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K]

/-- Every `F`-automorphism of `K` preserves the canonical valuation ring. -/
theorem galoisConjugate_mem_ringOfIntegers_iff (σ : Gal(K/F)) (x : K) :
    σ x ∈ ringOfIntegers K ↔ x ∈ ringOfIntegers K := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  have hmap (τ : Gal(K/F)) (y : K) (hy : y ∈ ringOfIntegers K) :
      τ y ∈ ringOfIntegers K := by
    have hyint : IsIntegral (ringOfIntegers F) y :=
      (IsIntegralClosure.isIntegral_iff (A := ringOfIntegers K)).2
        ⟨⟨y, hy⟩, rfl⟩
    have htint : IsIntegral (ringOfIntegers F) (τ y) :=
      (isIntegral_algEquiv (τ.restrictScalars (ringOfIntegers F))).2 hyint
    obtain ⟨z, hz⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := ringOfIntegers K)).1 htint
    change (ValuativeRel.valuation K) (τ y) ≤ 1
    rw [← hz]
    exact z.prop
  constructor
  · intro hsx
    have := hmap σ.symm (σ x) hsx
    simpa using this
  · exact hmap σ x
/-- Restriction of an `F`-automorphism to the canonical valuation ring. -/
noncomputable def galoisIntegerEquiv (σ : Gal(K/F)) :
    ringOfIntegers K ≃+* ringOfIntegers K where
  toFun y := ⟨σ (y : K), (galoisConjugate_mem_ringOfIntegers_iff F K σ y).2 y.prop⟩
  invFun y := ⟨σ.symm (y : K),
    (galoisConjugate_mem_ringOfIntegers_iff F K σ.symm y).2 y.prop⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem coe_galoisIntegerEquiv (σ : Gal(K/F)) (y : ringOfIntegers K) :
    ((galoisIntegerEquiv F K σ y : ringOfIntegers K) : K) = σ (y : K) := rfl
/-- Every `F`-automorphism of a finite local-field extension preserves normalized order. -/
@[simp]
theorem ord_galoisConjugate (σ : Gal(K/F)) (x : K) :
    ord K (σ x) = ord K x := by
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)
  obtain ⟨n, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hpi hx0
  have hcoePi : algebraMap (ringOfIntegers K) K pi = (pi : K) :=
    congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) pi
  have hx' : x = algebraMap (ringOfIntegers K) K (u : ringOfIntegers K) *
      (pi : K) ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def, hcoePi] using hx
  let e := galoisIntegerEquiv F K σ
  let eu : (ringOfIntegers K)ˣ := Units.map e.toMonoidHom u
  have heu : algebraMap (ringOfIntegers K) K (eu : ringOfIntegers K) =
      σ (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) := by
    rfl
  have hepi : algebraMap (ringOfIntegers K) K (e pi) = σ (pi : K) := by
    rfl
  have hirr : Irreducible (e pi) := hpi.map e
  calc
    ord K (σ x) = ord K
        (σ (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) *
          σ (pi : K) ^ n) := by rw [hx', map_mul, map_zpow₀]
    _ = ord K (algebraMap (ringOfIntegers K) K (eu : ringOfIntegers K)) +
          n • ord K (algebraMap (ringOfIntegers K) K (e pi)) := by
      rw [← heu, ← hepi, ord_mul, ord_zpow]
    _ = n • (1 : WithTop ℤ) := by
      rw [ord_coe_unit_eq_zero K eu, ord_coe_irreducible_eq_one K hirr, zero_add]
    _ = ord K (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) +
          n • ord K (algebraMap (ringOfIntegers K) K pi) := by
      rw [ord_coe_unit_eq_zero K u, ord_coe_irreducible_eq_one K hpi, zero_add]
    _ = ord K x := by
      rw [hx', ord_mul, ord_zpow, hcoePi]

end GaloisOrder
section RamificationInvariants

variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
/-- The residue-field map induced by a valuative extension of local fields. -/
noncomputable abbrev extensionResidueMap : ResidueField F →+* ResidueField K :=
  algebraMap (ResidueField F) (ResidueField K)

/-- A named alias for Mathlib's canonical residue-field algebra structure. -/
noncomputable abbrev residueFieldAlgebraOfValuativeExtension :
    Algebra (ResidueField F) (ResidueField K) :=
  inferInstance
/-- The canonical ideal-theoretic ramification index of `K/F`. -/
noncomputable def ramificationIndex : ℕ :=
  (IsLocalRing.maximalIdeal (ringOfIntegers K)).ramificationIdx (ringOfIntegers F)

/-- The canonical ideal-theoretic residue (inertia) degree of `K/F`. -/
noncomputable def residueDegree : ℕ :=
  (IsLocalRing.maximalIdeal (ringOfIntegers K)).inertiaDeg (ringOfIntegers F)
private theorem ramificationIdx'_eq_factor_exponent
    (ϖF : ringOfIntegers F) (hϖF : Irreducible ϖF)
    (ϖK : ringOfIntegers K) (hϖK : Irreducible ϖK)
    (m : ℕ) (u : (ringOfIntegers K)ˣ)
    (hy : algebraMap (ringOfIntegers F) (ringOfIntegers K) ϖF =
      (u : ringOfIntegers K) * ϖK ^ m) :
    (IsLocalRing.maximalIdeal (ringOfIntegers F)).ramificationIdx'
      (IsLocalRing.maximalIdeal (ringOfIntegers K)) = m := by
  let p := IsLocalRing.maximalIdeal (ringOfIntegers F)
  let q := IsLocalRing.maximalIdeal (ringOfIntegers K)
  have hp : p = Ideal.span {ϖF} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖF).mp hϖF
  have hq : q = Ideal.span {ϖK} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖK).mp hϖK
  have hmap : Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K)) p = q ^ m := by
    rw [hp, Ideal.map_span, hq, Ideal.span_singleton_pow]
    simp only [Set.image_singleton]
    rw [hy, Ideal.span_singleton_mul_left_unit u.isUnit]
  apply Ideal.ramificationIdx'_spec
  · rw [hmap]
  · rw [hmap]
    intro hle
    have hdvd : ϖK ^ (m + 1) ∣ ϖK ^ m := by
      rw [← Ideal.span_singleton_le_span_singleton,
        ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
      simpa only [← hq] using hle
    have hvle :
        IsDiscreteValuationRing.addVal (ringOfIntegers K) (ϖK ^ (m + 1)) ≤
          IsDiscreteValuationRing.addVal (ringOfIntegers K) (ϖK ^ m) :=
      (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdvd
    rw [hϖK.addVal_pow, hϖK.addVal_pow] at hvle
    exact (Nat.not_succ_le_self m) (by exact_mod_cast hvle)

private theorem ramificationIndex_eq_factor_exponent
    (ϖF : ringOfIntegers F) (hϖF : Irreducible ϖF)
    (ϖK : ringOfIntegers K) (hϖK : Irreducible ϖK)
    (m : ℕ) (u : (ringOfIntegers K)ˣ)
    (hy : algebraMap (ringOfIntegers F) (ringOfIntegers K) ϖF =
      (u : ringOfIntegers K) * ϖK ^ m) :
    ramificationIndex F K = m := by
  let p := IsLocalRing.maximalIdeal (ringOfIntegers F)
  let q := IsLocalRing.maximalIdeal (ringOfIntegers K)
  have hp0 : p ≠ ⊥ := (IsDiscreteValuationRing.maximalIdeal (ringOfIntegers F)).ne_bot
  have hOld := ramificationIdx'_eq_factor_exponent F K ϖF hϖF ϖK hϖK m u hy
  have hNew := Ideal.ramificationIdx'_eq_ramificationIdx p q hp0
  exact hNew.symm.trans hOld
private theorem ord_algebraMap_irreducible
    (ϖF : ringOfIntegers F) (hϖF : Irreducible ϖF) :
    ord K (algebraMap F K (ϖF : F)) =
      (ramificationIndex F K : WithTop ℤ) := by
  let y : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) ϖF
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hϖF.ne_zero
    apply Valuation.HasExtension.algebraMap_injective
      (vK := ValuativeRel.valuation F) (vA := ValuativeRel.valuation K)
    simpa only [map_zero] using hy0
  obtain ⟨ϖK, hϖK⟩ := IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)
  obtain ⟨m, u, hy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖK
  have he : ramificationIndex F K = m :=
    ramificationIndex_eq_factor_exponent F K ϖF hϖF ϖK hϖK m u hy
  rw [he]
  have hadd : IsDiscreteValuationRing.addVal (ringOfIntegers K) y = m := by
    rw [hy, IsDiscreteValuationRing.addVal_def' u hϖK m]
  have hord := ord_coe_eq_addVal_of_eq_nat K y m hadd
  rw [show (y : K) = algebraMap F K (ϖF : F) by
    exact Valuation.HasExtension.val_algebraMap ϖF] at hord
  exact hord

/-- The ideal-theoretic residue degree is the degree of the induced residue-field extension. -/
theorem residueDegree_eq_finrank_residueField :
    residueDegree F K = Module.finrank (ResidueField F) (ResidueField K) := by
  exact Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal (ringOfIntegers F))
    (IsLocalRing.maximalIdeal (ringOfIntegers K))
/-- The residue degree of a valuative extension of local fields is positive. -/
theorem residueDegree_pos : 0 < residueDegree F K := by
  rw [residueDegree_eq_finrank_residueField]
  exact Module.finrank_pos

/-- The ramification index of a valuative extension of local fields is positive. -/
theorem ramificationIndex_pos : 0 < ramificationIndex F K := by
  let p := IsLocalRing.maximalIdeal (ringOfIntegers F)
  let q := IsLocalRing.maximalIdeal (ringOfIntegers K)
  have hp0 : p ≠ ⊥ := (IsDiscreteValuationRing.maximalIdeal (ringOfIntegers F)).ne_bot
  have hold : Ideal.ramificationIdx' p q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q hp0
  have heq : Ideal.ramificationIdx' p q = ramificationIndex F K := by
    exact Ideal.ramificationIdx'_eq_ramificationIdx p q hp0
  exact Nat.pos_iff_ne_zero.mpr (heq ▸ hold)
/-- The degree of a finite local-field extension is the product of its ramification index and
residue degree. -/
theorem finrank_eq_ramificationIndex_mul_residueDegree
    [Module.Finite F K] :
    Module.finrank F K = ramificationIndex F K * residueDegree F K := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  let p := IsLocalRing.maximalIdeal (ringOfIntegers F)
  have hp0 : p ≠ ⊥ :=
    (IsDiscreteValuationRing.maximalIdeal (ringOfIntegers F)).ne_bot
  have h := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (R := ringOfIntegers F) (S := ringOfIntegers K) F K hp0
  let q := IsLocalRing.maximalIdeal (ringOfIntegers K)
  have hmap : Ideal.map (algebraMap (ringOfIntegers F) (ringOfIntegers K)) p ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0
  rw [Ideal.ramificationIdx'_eq_ramificationIdx' p q hmap,
    Ideal.inertiaDeg'_eq_inertiaDeg p q] at h
  exact h.symm

/-- Qualitative compatibility already supplied by `ValuativeExtension`: the algebra map preserves
comparisons of normalized orders. -/
theorem ord_algebraMap_le_iff (x y : F) :
    ord K (algebraMap F K x) ≤ ord K (algebraMap F K y) ↔ ord F x ≤ ord F y := by
  rw [ord_le_ord_iff, ValuativeExtension.vle_iff_vle, ← ord_le_ord_iff]
/-- Strict comparisons of normalized orders are also preserved by the algebra map. -/
theorem ord_algebraMap_lt_iff (x y : F) :
    ord K (algebraMap F K x) < ord K (algebraMap F K y) ↔ ord F x < ord F y := by
  rw [ord_lt_ord_iff, ValuativeExtension.vlt_iff_vlt, ← ord_lt_ord_iff]

private theorem ord_algebraMap_eq_zero_of_ord_eq_zero
    (a : F) (ha : ord F a = 0) : ord K (algebraMap F K a) = 0 := by
  apply le_antisymm
  · have h : ord F a ≤ ord F 1 := by simp [ha]
    simpa only [map_one, ord_one] using (ord_algebraMap_le_iff F K a 1).2 h
  · have h : ord F 1 ≤ ord F a := by simp [ha]
    simpa only [map_one, ord_one] using (ord_algebraMap_le_iff F K 1 a).2 h
private theorem zsmul_natCast_comm (n : ℤ) (e : ℕ) :
    n • (e : WithTop ℤ) = e • (n : WithTop ℤ) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      calc
        n • (e : WithTop ℤ) = ((n • (e : ℤ) : ℤ) : WithTop ℤ) :=
          (WithTop.coe_nsmul (e : ℤ) n).symm
        _ = ((e • (n : ℤ) : ℤ) : WithTop ℤ) := by
          congr 1
          simp [mul_comm]
        _ = e • ((n : ℤ) : WithTop ℤ) := WithTop.coe_nsmul (n : ℤ) e
  | negSucc n =>
      rw [negSucc_zsmul]
      calc
        -((n + 1) • (e : WithTop ℤ)) =
            -(((n + 1) • (e : ℤ) : ℤ) : WithTop ℤ) := by
              exact congrArg Neg.neg (WithTop.coe_nsmul (e : ℤ) (n + 1)).symm
        _ = ((-((n + 1) • (e : ℤ)) : ℤ) : WithTop ℤ) :=
          (WithTop.LinearOrderedAddCommGroup.coe_neg _).symm
        _ = ((e • Int.negSucc n : ℤ) : WithTop ℤ) := by
          congr 1
          rw [Int.negSucc_eq]
          ring
        _ = e • ((Int.negSucc n : ℤ) : WithTop ℤ) :=
          WithTop.coe_nsmul (Int.negSucc n) e

/-- Base-field order scales by the ideal-theoretic ramification index. -/
@[simp]
theorem ord_algebraMap (x : F) :
    ord K (algebraMap F K x) = ramificationIndex F K • ord F x := by
  by_cases hx0 : x = 0
  · subst x
    rw [map_zero, ord_zero, ord_zero]
    symm
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (ramificationIndex_pos F K))
    rw [he]
    simp [succ_nsmul]
  obtain ⟨ϖF, hϖF⟩ := IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  obtain ⟨n, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖF hx0
  have hcoeϖ : algebraMap (ringOfIntegers F) F ϖF = (ϖF : F) :=
    congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers F)) ϖF
  have hx' : x = algebraMap (ringOfIntegers F) F (u : ringOfIntegers F) *
      (ϖF : F) ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def, hcoeϖ] using hx
  have huF : ord F (algebraMap (ringOfIntegers F) F
      (u : ringOfIntegers F)) = 0 := ord_coe_unit_eq_zero F u
  have hϖFOrd : ord F (ϖF : F) = 1 := by
    rw [← hcoeϖ]
    exact ord_coe_irreducible_eq_one F hϖF
  have hxOrd : ord F x = (n : WithTop ℤ) := by
    rw [hx', ord_mul, ord_zpow, huF, hϖFOrd, zero_add]
    simpa using zsmul_natCast_comm n 1
  rw [hxOrd]
  rw [hx', map_mul, map_zpow₀, ord_mul, ord_zpow]
  rw [ord_algebraMap_eq_zero_of_ord_eq_zero F K _ huF,
    ord_algebraMap_irreducible F K ϖF hϖF, zero_add]
  exact zsmul_natCast_comm n (ramificationIndex F K)
end RamificationInvariants

section NormOrder
variable (F K : Type*) [Field F] [Field K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra F K] [ValuativeExtension F K]
  [Module.Finite F K]

private theorem ord_norm_coe_unit (u : (ringOfIntegers K)ˣ) :
    ord F (Algebra.norm F
      (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K))) = 0 := by
  letI : Module.Finite (ringOfIntegers F) (ringOfIntegers K) :=
    ringOfIntegers_moduleFinite F K
  letI : IsIntegralClosure (ringOfIntegers K) (ringOfIntegers F) K :=
    ringOfIntegers_isIntegralClosure F K
  let v : (ringOfIntegers F)ˣ :=
    Units.map (Algebra.intNorm (ringOfIntegers F) (ringOfIntegers K)) u
  have hv : algebraMap (ringOfIntegers F) F (v : ringOfIntegers F) =
      Algebra.norm F
        (algebraMap (ringOfIntegers K) K (u : ringOfIntegers K)) := by
    change algebraMap (ringOfIntegers F) F
        (Algebra.intNorm (ringOfIntegers F) (ringOfIntegers K)
          (u : ringOfIntegers K)) = _
    exact Algebra.algebraMap_intNorm
      (A := ringOfIntegers F) (K := F) (L := K)
      (B := ringOfIntegers K) (u : ringOfIntegers K)
  rw [← hv]
  exact ord_coe_unit_eq_zero F v
private theorem ord_norm_irreducible (piK : ringOfIntegers K)
    (hpiK : Irreducible piK) :
    ord F (Algebra.norm F (piK : K)) =
      (residueDegree F K : WithTop ℤ) := by
  obtain ⟨piF, hpiF⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers F)
  let y : ringOfIntegers K :=
    algebraMap (ringOfIntegers F) (ringOfIntegers K) piF
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hpiF.ne_zero
    apply Valuation.HasExtension.algebraMap_injective
      (vK := ValuativeRel.valuation F) (vA := ValuativeRel.valuation K)
    simpa only [map_zero] using hy0
  obtain ⟨m, u, hy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hpiK
  have hyK : algebraMap F K (piF : F) =
      algebraMap (ringOfIntegers K) K (u : ringOfIntegers K) *
        (piK : K) ^ m := by
    rw [← Valuation.HasExtension.val_algebraMap
      (vR := ValuativeRel.valuation F) (vA := ValuativeRel.valuation K) piF]
    change (y : K) = _
    rw [hy]
    rfl
  have hm : m = ramificationIndex F K :=
    (ramificationIndex_eq_factor_exponent F K piF hpiF piK hpiK m u hy).symm
  have hnorm := congrArg (Algebra.norm F) hyK
  rw [Algebra.norm_algebraMap, map_mul, map_pow] at hnorm
  have hord := congrArg (ord F) hnorm
  rw [ord_pow, ord_mul, ord_pow] at hord
  rw [show ord F (piF : F) = 1 by
    exact ord_coe_irreducible_eq_one F hpiF] at hord
  rw [ord_norm_coe_unit F K u, zero_add] at hord
  have hnormpi0 : Algebra.norm F (piK : K) ≠ 0 := by
    exact (Algebra.norm_eq_zero_iff.not.mpr (by exact_mod_cast hpiK.ne_zero))
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp
    ((ord_ne_top_iff F).2 hnormpi0)
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree F K
  have hepos : 0 < ramificationIndex F K := ramificationIndex_pos F K
  rw [hm] at hord
  rw [← hz] at hord
  have hordZ : (Module.finrank F K : ℤ) = ramificationIndex F K * z := by
    rw [nsmul_one] at hord
    rw [← WithTop.coe_nsmul z (ramificationIndex F K)] at hord
    exact_mod_cast hord
  have hdegreeZ : (Module.finrank F K : ℤ) =
      ramificationIndex F K * residueDegree F K := by
    exact_mod_cast hdegree
  have hzF : z = (residueDegree F K : ℤ) := by
    apply mul_left_cancel₀
      (show (ramificationIndex F K : ℤ) ≠ 0 by exact_mod_cast hepos.ne')
    exact hordZ.symm.trans hdegreeZ
  rw [← hz]
  exact_mod_cast hzF

/-- In a finite extension of local fields, normalized order of the field norm is residue degree
times normalized order upstairs. -/
@[simp]
theorem ord_norm (x : K) :
    ord F (norm F K x) = residueDegree F K • ord K x := by
  by_cases hx0 : x = 0
  · subst x
    obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (residueDegree_pos F K))
    rw [hf, succ_nsmul]
    simp
  obtain ⟨piK, hpiK⟩ :=
    IsDiscreteValuationRing.exists_irreducible (ringOfIntegers K)
  obtain ⟨n, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hpiK hx0
  have hcoePi : algebraMap (ringOfIntegers K) K piK = (piK : K) :=
    congrFun (Algebra.coe_algebraMap_ofSubsemiring (ringOfIntegers K)) piK
  have hx' : x = algebraMap (ringOfIntegers K) K
      (u : ringOfIntegers K) * (piK : K) ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def, hcoePi] using hx
  have hxOrd : ord K x = (n : WithTop ℤ) := by
    rw [hx', ord_mul, ord_zpow, ord_coe_unit_eq_zero K u]
    rw [← hcoePi, ord_coe_irreducible_eq_one K hpiK, zero_add]
    simpa using zsmul_natCast_comm n 1
  rw [hxOrd]
  rw [hx', map_mul, Algebra.norm_zpow, ord_mul, ord_zpow,
    ord_norm_coe_unit F K u, ord_norm_irreducible F K piK hpiK, zero_add]
  exact zsmul_natCast_comm n (residueDegree F K)
end NormOrder

end LanglandsFirstMainLemma
