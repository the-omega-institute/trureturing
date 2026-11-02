/- GID: D5/S3/Combinatorics/Graph/Laman/PlanarRows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/PlanarRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas, mathlib/module/Mathlib.LinearAlgebra.Matrix.Polynomial]
   utility: none
   digest: Row bases, moment curve perturbations, and induced sparsity for real planar rigidity. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver imports and API adaptations; unconsumed declarations omitted.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.TrivialMotions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde

/-!
# PlanarRows

Independent rigidity rows restrict to induced subgraphs. A moment curve perturbation preserves any open placement property while making each sufficiently large vertex subset affinely spanning. Independent translations and rotations then give the planar sparsity bound.
-/

@[expose] public section

namespace LinearMap

variable {ι R M N : Type*} [CommSemiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Finite ι] [DecidableEq ι]

/-- **The row space is spanned by the rows.** The range of the dual map
`f.dualMap` is the `R`-linear span of the family
`fun i ↦ f.dualMap (b.dualBasis i)` for any basis `b` on the codomain. -/
theorem range_dualMap_eq_span_image_dualBasis (b : Module.Basis ι R N)
    (f : M →ₗ[R] N) :
    LinearMap.range f.dualMap =
      Submodule.span R (Set.range (f.dualMap ∘ b.dualBasis)) := by
  rw [Set.range_comp, Submodule.span_image, b.dualBasis.span_eq, Submodule.map_top]

end LinearMap

namespace Polynomial

open Matrix

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

/-- Evaluating the matrix-polynomial determinant `det (X • A.map C + B.map C)`
at a scalar `t` yields the scalar determinant `det (t • A + B)`. Companion to
`Polynomial.coeff_det_X_add_C_zero` / `Polynomial.coeff_det_X_add_C_card`. -/
theorem eval_det_X_add_C (A B : Matrix n n α) (t : α) :
    eval t (det ((X : α[X]) • A.map C + B.map C)) = (t • A + B).det := by
  rw [show eval t (det ((X : α[X]) • A.map C + B.map C)) =
        evalRingHom t (det ((X : α[X]) • A.map C + B.map C)) from rfl,
      (evalRingHom t).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, coe_evalRingHom, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, eval_add, eval_mul,
    eval_X, eval_C]

end Polynomial

namespace Matrix

open Polynomial Finset

/-- The `n × n` matrix `M i j = v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)` has
determinant equal to the `(n + 1) × (n + 1)` Vandermonde determinant
`∏_{0 ≤ i < j ≤ n} (v j - v i)`.

Geometrically, row `i` of `M` is the difference `p i.succ - p 0` of points on the
moment curve, `p i = (v i, v i ^ 2, …, v i ^ n) ∈ Rⁿ`. -/
theorem det_powerDifferences {n : ℕ} {R : Type*} [CommRing R] (v : Fin (n + 1) → R) :
    (Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1))).det =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  -- Trivial ring: both sides are `0`.
  nontriviality R
  -- Strategy: realize `M` as the `(Fin.succ, Fin.succ)`-minor of the
  -- `(n+1) × (n+1)` evaluation matrix `A i j = (p j).eval (v i)` where
  -- `p 0 = 1` and `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))`. Then
  -- `det A = det (vandermonde v)` by
  -- `det_eval_matrixOfPolynomials_eq_det_vandermonde`, and `det A = det M`
  -- by cofactor-expansion along row 0 (only the `(0, 0)`-entry is nonzero).
  set p : Fin (n + 1) → R[X] :=
    Fin.cases 1 (fun k : Fin n => X ^ (k.val + 1) - C (v 0 ^ (k.val + 1))) with hp
  have h_p_zero : p 0 = 1 := by simp [p]
  have h_p_succ : ∀ k : Fin n, p k.succ = X ^ (k.val + 1) - C (v 0 ^ (k.val + 1)) := by
    intro k; simp [p]
  have h_deg : ∀ i, (p i).natDegree = (i : ℕ) := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero, Fin.val_zero, natDegree_one]
    · intro k
      rw [h_p_succ, natDegree_X_pow_sub_C, Fin.val_succ]
  have h_monic : ∀ i, (p i).Monic := by
    refine Fin.cases ?_ ?_
    · rw [h_p_zero]; exact monic_one
    · intro k
      rw [h_p_succ]
      exact monic_X_pow_sub_C _ (Nat.succ_ne_zero _)
  -- The (n+1) × (n+1) evaluation matrix and its identification with `vandermonde v`.
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of (fun i j : Fin (n + 1) => (p j).eval (v i)) with hA
  have h_vand : (Matrix.vandermonde v).det = A.det :=
    det_eval_matrixOfPolynomials_eq_det_vandermonde v p h_deg h_monic
  rw [det_vandermonde] at h_vand
  -- Row 0 of `A`: only the `(0, 0)`-entry is nonzero (= 1).
  have h_A_row_zero : ∀ j : Fin (n + 1), j ≠ 0 → A 0 j = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp [A, h_p_succ]
  have h_A_zero_zero : A 0 0 = 1 := by simp [A, h_p_zero]
  -- Cofactor-expand along row 0.
  have h_det_A : A.det = (A.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_row_zero A]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [h_A_zero_zero, Fin.succAbove_zero]
    · intros j _ hj
      rw [h_A_row_zero j hj]; ring
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- The submatrix `A.submatrix Fin.succ Fin.succ` is our target.
  have h_submatrix :
      A.submatrix Fin.succ Fin.succ =
        Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1)) := by
    ext i j
    simp [A, h_p_succ, eval_sub, eval_pow, eval_X, eval_C]
  rw [← h_submatrix, ← h_det_A, ← h_vand]

end Matrix

open Module
open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

def EdgeSetRowIndependent (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) : Prop :=
  LinearIndepOn ℝ
    (fun e : G.edgeSet => fun motion : Framework V d => G.RigidityMap p motion e) I


@[expose] noncomputable def rigidityRow (G : SimpleGraph V) (p : Framework V d) :
    G.edgeSet → Module.Dual ℝ (Framework V d) :=
  fun e => (LinearMap.proj e).comp (G.RigidityMap p)

theorem edgeSetRowIndependent_iff_linearIndepOn_rigidityRow
    (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) :
    G.EdgeSetRowIndependent p I ↔ LinearIndepOn ℝ (G.rigidityRow p) I := by
  change LinearIndepOn ℝ
      (fun e : G.edgeSet => LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ (G.rigidityRow p e)) I ↔ _
  exact (LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ).linearIndepOn_iff_of_injOn
    DFunLike.coe_injective.injOn


theorem rigidityRow_lift_eq_funLeft_dualMap
    {V W : Type*} {d : ℕ} (φ : V → W)
    {G' : SimpleGraph V} {H : SimpleGraph W}
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    (e' : G'.edgeSet) (hlift : Sym2.map φ e'.val ∈ H.edgeSet) :
    H.rigidityRow p_ext ⟨Sym2.map φ e'.val, hlift⟩ =
      (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap
        (G'.rigidityRow p' e') := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨e, he⟩ := e'
  induction e with
  | h u v => simp [rigidityRow, rigidityMap_apply, hcompat]


theorem linearIndependent_rigidityRow_of_lift
    {V W : Type*} {d : ℕ}
    {G' : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    {ι : Type*} {s : ι → G'.edgeSet}
    (hlift : ∀ i : ι, Sym2.map φ (s i).val ∈ H.edgeSet)
    (h : LinearIndependent ℝ
      (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet))) :
    LinearIndependent ℝ (fun i : ι => G'.rigidityRow p' (s i)) := by
  refine LinearIndependent.of_comp
    (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap ?_
  convert h using 1
  funext i
  exact (rigidityRow_lift_eq_funLeft_dualMap φ hcompat (s i) (hlift i)).symm


theorem span_range_rigidityRow (G : SimpleGraph V) [Finite G.edgeSet] (p : Framework V d) :
    Submodule.span ℝ (Set.range (G.rigidityRow p)) =
      LinearMap.range (G.RigidityMap p).dualMap := by
  classical
  have h_row : G.rigidityRow p =
      (G.RigidityMap p).dualMap ∘ (Pi.basisFun ℝ G.edgeSet).dualBasis := by
    funext e; ext _; simp [rigidityRow]
  rw [h_row]
  exact (LinearMap.range_dualMap_eq_span_image_dualBasis (Pi.basisFun ℝ G.edgeSet) _).symm


theorem rigidityMap_finrank_range_le_of_affinelySpanning [Fintype V] {d : ℕ}
    (G : SimpleGraph V) {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + d * (d + 1) / 2 ≤
      d * Fintype.card V := by
  have h_ker : d * (d + 1) / 2 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
    G.rigidityMap_ker_finrank_ge_of_affinelySpanning hp
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega


theorem exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two [Fintype V]
    {G : SimpleGraph V} {p : Framework V 2}
    (hp : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3) :
    ∃ I : Set G.edgeSet,
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  -- Extend ∅ to a row-LI subset `b ⊆ univ` whose image spans the whole row family.
  obtain ⟨b, _hb_sub, _, h_range_sub, hb_li⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ (G.rigidityRow p))
      (Set.empty_subset (Set.univ : Set G.edgeSet))
  have : Fintype ↥b := Fintype.ofFinite _
  -- The span of `rigidityRow '' b` equals `range R.dualMap`: forward inclusion is monotonicity
  -- of `span` (from `rigidityRow '' b ⊆ Set.range rigidityRow`) plus `span_range_rigidityRow`;
  -- reverse uses the `rigidityRow '' univ ⊆ span ...` output of `exists_linearIndepOn_extension`.
  have h_span_b : Submodule.span ℝ (G.rigidityRow p '' b) =
      LinearMap.range (G.RigidityMap p).dualMap := by
    rw [← G.span_range_rigidityRow p]
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_
    rw [Submodule.span_le, ← Set.image_univ]
    exact h_range_sub
  -- `b` is an LI family spanning that submodule, so its cardinality is the finrank.
  have h_card_b : Fintype.card ↥b =
      finrank ℝ (Submodule.span ℝ (G.rigidityRow p '' b)) := by
    have h :=
      (linearIndependent_iff_card_eq_finrank_span
        (b := fun e : ↥b => G.rigidityRow p e.val)).mp hb_li
    rwa [Set.finrank, ← Set.image_eq_range] at h
  -- Chain `Fintype.card ↥b = finrank (range R.dualMap) = finrank (range R) ≥ 2 * #V - 3`.
  have h_le_card : 2 * Fintype.card V - 3 ≤ b.ncard := by
    have h1 := h_card_b
    rw [h_span_b, LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    omega
  -- Truncate `b` to a subset `I ⊆ b` with `|I| = 2 * #V - 3`.
  obtain ⟨I, hI_sub, hI_card⟩ := Set.exists_subset_card_eq h_le_card
  exact ⟨I, hI_card,
    (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mpr (hb_li.mono hI_sub)⟩


private lemma affineIndependent_of_difference_det_ne_zero {d : ℕ}
    (q : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (h : (Matrix.of fun i j : Fin d => q i.succ j - q 0 j).det ≠ 0) :
    AffineIndependent ℝ q := by
  have h_LI_rows : LinearIndependent ℝ
      (fun i : Fin d => Matrix.of (fun i' j : Fin d => q i'.succ j - q 0 j) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero h
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0,
    ← linearIndependent_equiv (finSuccAboveEquiv 0),
    ← (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)]
  exact h_LI_rows


theorem exists_affinelySpanning_of_eventually [Finite V] {d : ℕ}
    {P : Framework V d → Prop} {p₀ : Framework V d}
    (hP : ∀ᶠ p in 𝓝 p₀, P p) :
    ∃ p : Framework V d, P p ∧
      ∀ S : Set V, d + 1 ≤ S.ncard →
        affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  -- Step 1: pick `φ : V → ℝ` injective.
  let ψ : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let φ : V → ℝ := fun v => ((ψ v).val : ℝ)
  have hφ_inj : Function.Injective φ := by
    intro a b h
    apply ψ.injective
    apply Fin.ext
    have h' : ((ψ a).val : ℝ) = ((ψ b).val : ℝ) := h
    exact_mod_cast h'
  -- Step 2: moment-curve direction `w v = (φ(v)^1, …, φ(v)^d)`.
  let w : V → EuclideanSpace ℝ (Fin d) :=
    fun v => WithLp.toLp 2 (fun j : Fin d => (φ v) ^ (j.val + 1))
  have hw : ∀ (v : V) (j : Fin d), (w v) j = (φ v) ^ (j.val + 1) := fun _ _ => rfl
  -- Step 3: perturbed placement `pt t = p₀ + t • w`.
  let pt : ℝ → Framework V d := fun t v => p₀ v + t • w v
  have h_pt_zero : pt 0 = p₀ := by ext v i; simp [pt]
  have h_pt_cont : Continuous pt := by
    refine continuous_pi fun v => ?_
    exact continuous_const.add (continuous_id'.smul continuous_const)
  -- Step 4: pull the openness premise back to `t`.
  have h_event_P : ∀ᶠ t in 𝓝 (0 : ℝ), P (pt t) := by
    have h_tendsto : Filter.Tendsto pt (𝓝 0) (𝓝 p₀) :=
      h_pt_zero ▸ h_pt_cont.tendsto 0
    exact h_tendsto.eventually hP
  rw [Metric.eventually_nhds_iff] at h_event_P
  obtain ⟨ε, hε_pos, hε_P⟩ := h_event_P
  -- Coordinate identity: `(pt t v) j = (p₀ v) j + t * φ(v)^(j+1)`.
  have h_pt_coord : ∀ (t : ℝ) (v : V) (j : Fin d),
      (pt t v) j = (p₀ v) j + t * (φ v) ^ (j.val + 1) := by
    intros t v j
    simp [pt, hw, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- Step 5: for each injective `q : Fin (d + 1) → V`, the per-tuple bad-`t` set is finite.
  have h_per_tuple : ∀ q : Fin (d + 1) → V, Function.Injective q →
      {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}.Finite := by
    intros q hq_inj
    -- Difference matrices: `M₀` from `p₀`, `M₁` from the moment curve.
    set M₀ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => p₀ (q i.succ) j - p₀ (q 0) j) with hM₀_def
    set M₁ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => (φ (q i.succ)) ^ (j.val + 1) - (φ (q 0)) ^ (j.val + 1))
      with hM₁_def
    -- `det M₁ = ∏_{i<j} (φ(qⱼ) - φ(qᵢ)) ≠ 0` by injectivity of `φ ∘ q`.
    have h_det_M₁_ne : M₁.det ≠ 0 := by
      rw [hM₁_def, Matrix.det_powerDifferences (fun k : Fin (d + 1) => φ (q k))]
      refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr ?_)
      intros j hij
      rw [Finset.mem_Ioi] at hij
      refine sub_ne_zero.mpr ?_
      intro h
      exact (Fin.ne_of_lt hij).symm (hq_inj (hφ_inj h))
    -- The polynomial `P(X) = det (X • M₁.map C + M₀.map C) ∈ ℝ[X]`.
    set P : Polynomial ℝ :=
      ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C + M₀.map Polynomial.C).det
      with hP_def
    -- `coeff P d = det M₁ ≠ 0`, so `P ≠ 0`.
    have hP_ne : P ≠ 0 := by
      intro h
      apply h_det_M₁_ne
      have := Polynomial.coeff_det_X_add_C_card M₁ M₀
      rw [show Fintype.card (Fin d) = d from Fintype.card_fin d, ← hP_def, h] at this
      simpa using this.symm
    -- `P.eval t = (t • M₁ + M₀).det` via `Polynomial.eval_det_X_add_C`.
    have hP_eval : ∀ t : ℝ, P.eval t = (t • M₁ + M₀).det := fun t => by
      rw [hP_def, Polynomial.eval_det_X_add_C]
    -- The rows of `t • M₁ + M₀` are `(pt t (q i.succ) - pt t (q 0))` coordinatewise.
    have h_rows : ∀ t : ℝ,
        (t • M₁ + M₀ : Matrix (Fin d) (Fin d) ℝ) =
        Matrix.of (fun i j : Fin d => (pt t (q i.succ)) j - (pt t (q 0)) j) := by
      intro t
      ext i j
      simp [Matrix.add_apply, smul_eq_mul, hM₀_def, hM₁_def, h_pt_coord]
      ring
    -- The bad-`t` set is contained in the zero set of `P`.
    have h_bad_sub : {t : ℝ | ¬ AffineIndependent ℝ (fun i => pt t (q i))} ⊆
        {t : ℝ | P.IsRoot t} := by
      intros t ht
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hP_eval] at *
      by_contra h_det_ne
      exact ht (affineIndependent_of_difference_det_ne_zero (fun i => pt t (q i))
        (by rw [← h_rows t]; exact h_det_ne))
    exact (Polynomial.finite_setOfPred_isRoot hP_ne).subset h_bad_sub
  -- Step 6: assemble the global bad set as a finite union over injective `(d+1)`-tuples.
  let tuples : Finset (Fin (d + 1) → V) :=
    (Finset.univ : Finset (Fin (d + 1) → V)).filter Function.Injective
  let bad : Set ℝ :=
    ⋃ q ∈ tuples, {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}
  have h_bad_finite : bad.Finite := by
    apply (Finset.finite_toSet tuples).biUnion
    intros q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    exact h_per_tuple q hq.2
  -- Step 7: pick `t ∈ (0, ε) \ bad`.
  have h_nonempty : ((Set.Ioo (0 : ℝ) ε) \ bad).Nonempty :=
    ((Set.Ioo_infinite hε_pos).sdiff h_bad_finite).nonempty
  obtain ⟨t, ⟨ht_pos, ht_lt⟩, ht_good⟩ := h_nonempty
  -- Step 8: assemble the witness.
  refine ⟨pt t, ?_, ?_⟩
  · -- `P (pt t)` since `t` is in the openness neighborhood.
    apply hε_P
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact ht_lt
  · -- Affinely spans on every size-`≥ d + 1` subset.
    intros S hS
    -- Pick `d + 1` distinct elements in `S` as an injective `q : Fin (d + 1) → V`.
    obtain ⟨q, hq_S, hq_inj⟩ := (Set.le_encard_iff_exists_fin_injective S (d + 1)).mp
      (by rw [← S.toFinite.cast_ncard_eq]; exact_mod_cast hS)
    -- The `(d+1)`-tuple at `pt t` is affinely independent.
    have h_AI : AffineIndependent ℝ (fun i => pt t (q i)) := by
      by_contra h
      apply ht_good
      simp only [bad, Set.mem_iUnion]
      refine ⟨q, ?_, h⟩
      simp [tuples, hq_inj]
    -- The affine span of these `d + 1` points is `⊤` in `EuclideanSpace ℝ (Fin d)`.
    have h_span_tuple : affineSpan ℝ (Set.range (fun i => pt t (q i))) = ⊤ := by
      rw [h_AI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp [finrank_euclideanSpace]
    -- The tuple is included in the image of `p|_S`.
    have h_incl : Set.range (fun i => pt t (q i)) ⊆
        Set.range (fun v : S => pt t v.val) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨q i, hq_S i⟩, rfl⟩
    -- Hence the larger affine span is `⊤`.
    apply top_le_iff.mp
    calc ⊤ = affineSpan ℝ (Set.range (fun i => pt t (q i))) := h_span_tuple.symm
      _ ≤ affineSpan ℝ (Set.range (fun v : S => pt t v.val)) :=
          affineSpan_mono ℝ h_incl


theorem isSparse_of_edgeSetRowIndependent_dim_two {V : Type*} {G : SimpleGraph V}
    {p : Framework V 2}
    (hp : ∀ S : Set V, 3 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤)
    {I : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) :
    (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsSparse 2 3 := by
  classical
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  -- `H.edgeSet = Subtype.val '' I`: the `fromEdgeSet \ diagSet` reduces because every
  -- edge in the image is already a non-loop (it came from `G.edgeSet`).
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  -- `H ≤ G` (the spanning subgraph is contained in `G`).
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  intro s hs
  -- Bridge `(H.edgesIn ↑s).ncard` to `(H.induce ↑s).edgeSet.ncard` via the
  -- `Sym2.map Subtype.val` bijection.
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet]
  set S : Set V := (↑s : Set V) with hS_def
  have hS_ncard : S.ncard = s.card := by rw [hS_def]; exact Set.ncard_coe_finset s
  have hS_card : Fintype.card ↥S = s.card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hS_ncard
    exact hS_ncard
  -- Case split: `hs : 3 ≤ 2 * s.card` forces `s.card = 2 ∨ 3 ≤ s.card`.
  obtain hs_two | hs_ge : s.card = 2 ∨ 3 ≤ s.card := by omega
  · -- `s.card = 2`: simple-graph combinatorics gives ≤ 1 edge in the induced subgraph.
    have h_card_le : (H.induce S).edgeFinset.card ≤ (Fintype.card ↥S).choose 2 :=
      card_edgeFinset_le_card_choose_two
    rw [hS_card, hs_two, Nat.choose_self] at h_card_le
    have h_ncard_eq : (H.induce S).edgeSet.ncard = (H.induce S).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← SimpleGraph.edgeFinset_card]
    omega
  · -- `s.card ≥ 3`: row factoring + rank upper bound at affinely-spanning placement.
    set p_s : Framework ↥S 2 := fun v => p v.val with hp_s_def
    -- The hypothesis supplies affine spanning for the restricted placement.
    have h_affineSpan : affineSpan ℝ (Set.range p_s) = ⊤ :=
      hp S (by rw [hS_ncard]; exact hs_ge)
    -- Rank upper bound at the induced subgraph.
    have h_rank_le : Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) + 3 ≤
        2 * s.card := by
      have h := rigidityMap_finrank_range_le_of_affinelySpanning (H.induce S) h_affineSpan
      rwa [hS_card] at h
    -- V-side lift of an induced-subgraph edge, landing in `H.edgeSet ⊆ G.edgeSet`.
    have hlift_mem_H : ∀ e' : (H.induce S).edgeSet,
        Sym2.map (Subtype.val : ↥S → V) e'.val ∈ H.edgeSet := by
      intro e'
      obtain ⟨e, he⟩ := e'
      induction e with | h u v =>
        rw [mem_edgeSet, induce_adj] at he
        rw [Sym2.map_mk, mem_edgeSet]
        exact he
    let liftEdge : (H.induce S).edgeSet → G.edgeSet :=
      fun e' => ⟨Sym2.map (Subtype.val : ↥S → V) e'.val,
        edgeSet_mono hHG (hlift_mem_H e')⟩
    -- The lift lands in `I`: `(liftEdge e').val ∈ H.edgeSet = Subtype.val '' I`.
    have hlift_in_I : ∀ e' : (H.induce S).edgeSet, liftEdge e' ∈ I := by
      intro e'
      have h_in_H : (liftEdge e').val ∈ H.edgeSet := hlift_mem_H e'
      rw [hH_edgeSet] at h_in_H
      obtain ⟨e₀, he₀_in_I, he₀_eq⟩ := h_in_H
      have : liftEdge e' = e₀ := Subtype.ext he₀_eq.symm
      rw [this]; exact he₀_in_I
    -- `liftEdge` is injective.
    have hlift_inj : Function.Injective liftEdge := fun _ _ h =>
      Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h))
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via the reverse-direction helper (factoring + `of_comp`).
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') :=
      linearIndependent_rigidityRow_of_lift (Subtype.val : ↥S → V) (fun _ => rfl)
        (fun i => edgeSet_mono hHG (hlift_mem_H i)) h_li_V
    -- Convert LI to a finrank identity, then chain through the dualMap rank equality.
    have h_card_eq : Fintype.card (H.induce S).edgeSet =
        Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) := by
      have h := (linearIndependent_iff_card_eq_finrank_span
        (b := fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e')).mp h_li_s
      rw [Set.finrank] at h
      rw [h, (H.induce S).span_range_rigidityRow p_s]
      exact LinearMap.finrank_range_dualMap_eq_finrank_range _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    omega


end SimpleGraph
