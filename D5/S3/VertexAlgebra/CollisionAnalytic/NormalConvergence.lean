/- GID: D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact normal convergence of the original labelled collision Hahn coefficients. -/

import D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith

/-!
A local annular box is controlled coefficient by coefficient by its finitely
many positive-real vertices. Compactness then gives a single summable majorant.
All integer exponents and original labels are retained. The infinite-sum,
compactness and continuous-map machinery is from mathlib (Apache 2.0).
-/

noncomputable section
open scoped Topology BigOperators
open Set

namespace D5.S3.VertexAlgebra.CollisionNormalConvergence
open CollisionAbsoluteEvaluation.Labelled
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.FiniteConvolution

private def radiusDomain {n : ℕ} (sigma : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {r | (∀ i, 0 < r i) ∧ ∀ i j, i < j → r (sigma j) < r (sigma i)}

private lemma radiusDomain_open {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    IsOpen (radiusDomain sigma) := by
  apply IsOpen.inter
  · exact isOpen_setOf_forall fun i => isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_setOf_forall fun i => isOpen_setOf_forall fun j =>
      isOpen_setOf_forall fun (_ : i < j) =>
        isOpen_lt (continuous_apply (sigma j)) (continuous_apply (sigma i))

private def vertex {n : ℕ} (a b : Fin n → ℝ) (s : Fin n → Bool) : Fin n → ℂ :=
  fun i => ((if s i then b i else a i : ℝ) : ℂ)

private lemma annular_vertices {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (z : Fin n → ℂ) (hz : RadialChamber sigma z) :
    ∃ a b : Fin n → ℝ,
      (∀ i, 0 < a i ∧ a i < ‖z i‖ ∧ ‖z i‖ < b i) ∧
      ∀ s, RadialChamber sigma (vertex a b s) := by
  let r : Fin n → ℝ := fun i => ‖z i‖
  have hr : r ∈ radiusDomain sigma := ⟨fun i => norm_pos_iff.mpr (hz.1 i), hz.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((radiusDomain_open sigma).mem_nhds hr)
  let a : Fin n → ℝ := fun i => r i - ε / 2
  let b : Fin n → ℝ := fun i => r i + ε / 2
  have hv (s : Fin n → Bool) :
      (fun i => if s i then b i else a i) ∈ radiusDomain sigma := by
    apply hball
    apply lt_of_le_of_lt ((dist_pi_le_iff (by linarith : 0 ≤ ε / 2)).mpr ?_)
      (by linarith : ε / 2 < ε)
    intro i
    dsimp [a, b]
    cases s i <;> simp [Real.dist_eq, abs_of_nonneg hε.le, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    have ha := (hv (fun _ => false)).1 i
    refine ⟨by simpa using ha, ?_, ?_⟩ <;> dsimp [a, b, r] <;> linarith
  · intro s
    have hs := hv s
    have hn (i) : ‖vertex a b s i‖ = (if s i then b i else a i) := by
      rw [vertex, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs.1 i)]
    exact ⟨fun i => norm_pos_iff.mp (by rw [hn]; exact hs.1 i), by simpa only [hn] using hs.2⟩

private lemma annular_term_bound {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (w : Fin n → ℂ)
    (hw : ∀ i, a i ≤ ‖w i‖ ∧ ‖w i‖ ≤ b i)
    (c : ℂ) (e : Fin n → ℤ) :
    ‖c * monomial w e‖ ≤ ∑ s : Fin n → Bool, ‖c * monomial (vertex a b s) e‖ := by
  classical
  let s : Fin n → Bool := fun i => decide (0 ≤ e i)
  have hv (i) : 0 < (if s i then b i else a i) := by
    split_ifs
    · exact (ha i).trans_le ((hw i).1.trans (hw i).2)
    · exact ha i
  have hp (i) : ‖w i‖ ^ e i ≤ (if s i then b i else a i) ^ e i := by
    by_cases he : 0 ≤ e i
    · simpa [s, he] using zpow_le_zpow_left₀ he (norm_nonneg (w i)) (hw i).2
    · have h := zpow_le_zpow_left₀ (by omega : 0 ≤ -e i) (ha i).le (hw i).1
      have hpos : 0 < a i ^ (-e i) := zpow_pos (ha i) _
      have hi := inv_anti₀ hpos h
      simpa [s, he, ← zpow_neg] using hi
  have hvertex : ‖c * monomial w e‖ ≤ ‖c * monomial (vertex a b s) e‖ := by
    simp only [norm_mul, monomial, norm_prod, norm_zpow]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    apply Finset.prod_le_prod (fun i _ => zpow_nonneg (norm_nonneg _) _)
    intro i _
    simpa only [vertex, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv i)] using hp i
  exact hvertex.trans (Finset.single_le_sum (fun t _ => norm_nonneg _) (Finset.mem_univ s))

private lemma chamber_local_majorant {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (c : (Fin n → ℤ) → ℂ)
    (habs : ∀ z : Fin n → ℂ, RadialChamber sigma z →
      Summable (fun e : Fin n → ℤ => ‖c e * monomial z e‖))
    (z : Fin n → ℂ) (hz : RadialChamber sigma z) :
    ∃ (U : Set (Fin n → ℂ)) (u : (Fin n → ℤ) → ℝ),
      IsOpen U ∧ z ∈ U ∧ (∀ e, 0 ≤ u e) ∧ Summable u ∧
      ∀ e w, w ∈ U → ‖c e * monomial w e‖ ≤ u e := by
  classical
  obtain ⟨a, b, hab, hv⟩ := annular_vertices sigma z hz
  let U : Set (Fin n → ℂ) := {w | ∀ i, a i < ‖w i‖ ∧ ‖w i‖ < b i}
  let u := fun e => ∑ s : Fin n → Bool, ‖c e * monomial (vertex a b s) e‖
  refine ⟨U, u, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_setOf_forall fun i =>
      (isOpen_lt continuous_const (continuous_apply i).norm).inter
        (isOpen_lt (continuous_apply i).norm continuous_const)
  · exact fun i => ⟨(hab i).2.1, (hab i).2.2⟩
  · intro e; exact Finset.sum_nonneg fun s _ => norm_nonneg _
  · exact summable_sum fun s _ => habs _ (hv s)
  · intro e w hw
    exact annular_term_bound a b (fun i => (hab i).1) w
      (fun i => ⟨(hw i).1.le, (hw i).2.le⟩) (c e) e

/-- A single nonnegative ℓ¹ majorant on any compact subset of a strict radial
chamber, for the original signed, labelled monomial family. -/
theorem chamber_compact_summable_majorant {n : ℕ}
    (sigma : Equiv.Perm (Fin n)) (c : (Fin n → ℤ) → ℂ)
    (habs : ∀ z : Fin n → ℂ, RadialChamber sigma z →
      Summable (fun e : Fin n → ℤ => ‖c e * monomial z e‖))
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hKU : K ⊆ {z | RadialChamber sigma z}) :
    ∃ u : (Fin n → ℤ) → ℝ,
      (∀ e, 0 ≤ u e) ∧ Summable u ∧
      ∀ (e : Fin n → ℤ) (z : Fin n → ℂ), z ∈ K →
        ‖c e * monomial z e‖ ≤ u e := by
  classical
  choose U u hU hz hu hs hb using fun z : K =>
    chamber_local_majorant sigma c habs z (hKU z.property)
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hzK
    exact mem_iUnion.mpr ⟨⟨z, hzK⟩, hz ⟨z, hzK⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨fun e => ∑ z ∈ t, u z e, ?_, summable_sum (fun z _ => hs z), ?_⟩
  · intro e; exact Finset.sum_nonneg fun z _ => hu z e
  · intro e w hw
    obtain ⟨z, hzt, hwU⟩ := mem_iUnion₂.mp (ht hw)
    exact (hb z e w hwU).trans (Finset.single_le_sum (fun z _ => hu z e) hzt)

/-- Normal convergence in C(K,ℂ), with the exact rational value and uniform
convergence of the net of all finite subsets of labelled integer exponents. -/
theorem collision_normal_evaluation {n : ℕ}
    (sigma : Equiv.Perm (Fin n)) (L : LabelledPolynomial ℂ n)
    (m : (Fin n × Fin n) → ℕ)
    (K : TopologicalSpace.Compacts (Fin n → ℂ))
    (hKU : (K : Set (Fin n → ℂ)) ⊆ {z | RadialChamber sigma z}) :
    let Q : LabelledPolynomial ℂ n :=
      ∏ p ∈ labelledPairs n, pairPolynomial p.1 p.2 ^ m p
    let c := fun e : Fin n → ℤ =>
      (orderedRationalFor ℂ n sigma
        (algebraMap _ (CommonRational ℂ n) L /
          algebraMap _ (CommonRational ℂ n) Q)).coeff (orderExponents n sigma e)
    let value := fun z : Fin n → ℂ =>
      laurentValue L z / ∏ p ∈ labelledPairs n, (z p.1 - z p.2) ^ m p
    ∃ (T : (Fin n → ℤ) → C(K, ℂ)) (F : C(K, ℂ)),
      (∀ e (z : K), T e z = c e * monomial (z : Fin n → ℂ) e) ∧
      (∀ z : K, F z = value (z : Fin n → ℂ)) ∧
      Summable (fun e : Fin n → ℤ => ‖T e‖) ∧ HasSum T F ∧
      HasSumUniformlyOn (fun e z => c e * monomial z e) value
        (K : Set (Fin n → ℂ)) := by
  classical
  dsimp only
  let Q : LabelledPolynomial ℂ n := ∏ p ∈ labelledPairs n, pairPolynomial p.1 p.2 ^ m p
  let c := fun e : Fin n → ℤ => (orderedRationalFor ℂ n sigma
    (algebraMap _ (CommonRational ℂ n) L / algebraMap _ (CommonRational ℂ n) Q)).coeff
      (orderExponents n sigma e)
  let value := fun z : Fin n → ℂ =>
    laurentValue L z / ∏ p ∈ labelledPairs n, (z p.1 - z p.2) ^ m p
  have heval z (hz : RadialChamber sigma z) := collision_absolute_evaluation sigma L m z hz
  obtain ⟨u, hu0, hu, hub⟩ := chamber_compact_summable_majorant sigma c
    (fun z hz => (heval z hz).2.1) K K.isCompact hKU
  let T : (Fin n → ℤ) → C(K, ℂ) := fun e =>
    ⟨fun z => c e * monomial (z : Fin n → ℂ) e, continuous_const.mul
      (continuous_finset_prod _ fun i _ =>
        ((continuous_apply i).comp continuous_subtype_val).zpow₀ (e i)
          (fun z => Or.inl ((hKU z.property).1 i)))⟩
  have hnorm : Summable (fun e => ‖T e‖) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun e =>
      ((T e).norm_le (hu0 e)).mpr (fun z => hub e z z.property))
  have hsum : HasSum T (∑' e, T e) := hnorm.of_norm.hasSum
  have hvalue (z : K) : (∑' e, T e) z = value z :=
    (hasSum_apply hsum z).unique ((heval z (hKU z.property)).2.2.1)
  refine ⟨T, ∑' e, T e, fun _ _ => rfl, hvalue, hnorm, hsum, ?_⟩
  exact (HasSumUniformlyOn.of_norm_le_summable hu hub).congr_right
    (fun z hz => ((heval z (hKU hz)).2.2.1).tsum_eq)

end D5.S3.VertexAlgebra.CollisionNormalConvergence
