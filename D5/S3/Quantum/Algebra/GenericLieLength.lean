/- GID: D5/S3/Quantum/Algebra/GenericLieLength
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericLieLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jia-Capel generic Lie length conjecture formalization. -/
/- admission_basis: open-problem-resolution (#15954; Proved)
   Direct frozen dependencies: none; every D5 proof dependency is in this delivery.
   escape_witness: GenericLieLengthConstruction.anchored_units_mem, GenericLieLengthFiltration.card_words_le.
   The claim retains the prescribed suSet, layer and Lebesgue-coordinate definitions.
   Heap depth uses Nat.size; coordinate and matrix operations use their Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
   ae_mvPolynomial_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: ae_finitePolynomial_ne_zero.
   bracket_coordinate: proof_shape: bind-only; escape_witness: none; consumers: eval_wordPolynomial.
   wordPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_boundedPolynomial,eval_spanningPolynomial,eval_wordPolynomial,spanningPolynomial.
   eval_wordPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_boundedPolynomial.
   ae_finitePolynomial_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: ae_nestedPolynomial_ne_zero.
   uncurry_volume_preserving: proof_shape: bind-only; escape_witness: none; consumers: ae_nestedPolynomial_ne_zero.
   ae_nestedPolynomial_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   rightSpan_eq_range: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   combination_mem: proof_shape: bind-only; escape_witness: none; consumers: determinant_ne_zero_implies_span_top.
   eval_boundedPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_spanningPolynomial.
   spanningPolynomial: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness,eval_spanningPolynomial.
   eval_spanningPolynomial: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   determinant_ne_zero_implies_span_top: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   ae_span_top_of_witness: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq.
   extendedPair: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,extendedPair_span_top.
   extendedPair_span_top: proof_shape: content; escape_witness: GenericLieLengthConstruction.anchored_units_mem; consumers: ae_rightSpan_eq.
   coordinateLinearMap: proof_shape: bind-only; escape_witness: none; consumers: suCoordinateMap_measurableEmbedding.
   suCoordinateMap_measurableEmbedding: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq.
   ae_rightSpan_eq: proof_shape: content; escape_witness: GenericLieLengthConstruction.anchored_units_mem; consumers: result.
   claim: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: content; escape_witness: GenericLieLengthConstruction.anchored_units_mem, GenericLieLengthFiltration.card_words_le; consumers: terminal.
-/


import D5.S3.Quantum.Algebra.GenericLieLengthConstruction
import D5.S3.Analytic.NullSets.AnalyticZeroSetNull
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext



namespace D5.S3.Quantum.Algebra.GenericLieLength

noncomputable section


open MeasureTheory

theorem ae_mvPolynomial_ne_zero (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  have hex : ∃ a : Fin n → ℝ, MvPolynomial.eval a p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    exact MvPolynomial.funext fun x => by simpa using h x
  obtain ⟨a, ha⟩ := hex
  exact D5.S3.Analytic.NullSets.AnalyticZeroSetNull.ae_ne_zero_of_analytic
    (AnalyticOnNhd.eval_mvPolynomial p) ha


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration MvPolynomial Matrix Module

variable {M : Type*} [LieRing M] [LieAlgebra ℝ M] {g d : ℕ}

private theorem bracket_coordinate (b : Basis (Fin d) ℝ M) (X Y : M) (k : Fin d) :
    b.equivFun ⁅X, Y⁆ k =
      ∑ i, ∑ j, b.equivFun ⁅b i, b j⁆ k * b.equivFun X i * b.equivFun Y j := by
  conv_lhs => rw [← b.sum_equivFun X, ← b.sum_equivFun Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def wordPolynomial (b : Basis (Fin d) ℝ M) : RightWord (Fin g) → Fin d →
      MvPolynomial (Fin g × Fin d) ℝ
    | .single i, k => X (i, k)
    | .cons i w, k => ∑ a, ∑ z,
        C (b.equivFun ⁅b a, b z⁆ k) * X (i, a) * wordPolynomial b w z

private theorem eval_wordPolynomial (b : Basis (Fin d) ℝ M) (w : RightWord (Fin g))
    (x : Fin g × Fin d → ℝ) (k : Fin d) :
    MvPolynomial.eval x (wordPolynomial b w k) =
      b.equivFun (w.rightWordEval ((fun i => b.equivFun.symm (fun k => x (i, k))))) k := by
  induction w generalizing k with
  | single i =>
    simp only [wordPolynomial, eval_X, rightWordEval, LinearEquiv.apply_symm_apply]
  | cons i w ih =>
    simp only [wordPolynomial, map_sum, map_mul, eval_C, eval_X, ih, rightWordEval]
    rw [bracket_coordinate]
    simp only [LinearEquiv.apply_symm_apply]


open MeasureTheory MvPolynomial

private theorem ae_finitePolynomial_ne_zero {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ)
    (hp : p ≠ 0) : ∀ᵐ x : σ → ℝ, MvPolynomial.eval x p ≠ 0 := by
  let e := Fintype.equivFin σ
  let q := MvPolynomial.rename e p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    have hh := congrArg (MvPolynomial.rename e.symm) h
    simpa only [q, MvPolynomial.rename_rename, e.symm_comp_self,
      MvPolynomial.rename_id, AlgHom.id_apply, map_zero] using hh
  have hh := D5.S3.Quantum.Algebra.GenericLieLength.ae_mvPolynomial_ne_zero _ q hq
  have he := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have h := he.quasiMeasurePreserving.ae hh
  filter_upwards [h] with x hx
  simpa [q, MvPolynomial.eval_rename, MeasurableEquiv.piCongrLeft, Function.comp_def] using hx

private theorem uncurry_volume_preserving (g d : ℕ) :
    MeasurePreserving (Function.uncurry : (Fin g → Fin d → ℝ) → (Fin g × Fin d → ℝ)) := by
  refine ⟨measurable_uncurry, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.univ_pi hs)]
  have hpre : Function.uncurry ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i : Fin g => Set.pi Set.univ (fun j : Fin d => s (i, j))) := by
    ext x
    simp [Set.mem_pi, Function.uncurry]
  rw [hpre, volume_pi_pi]
  simp only [volume_pi_pi]
  rw [Fintype.prod_prod_type]

private theorem ae_nestedPolynomial_ne_zero {g d : ℕ} (p : MvPolynomial (Fin g × Fin d) ℝ)
    (hp : p ≠ 0) : ∀ᵐ x : Fin g → Fin d → ℝ, MvPolynomial.eval (Function.uncurry x) p ≠ 0 := by
  exact (uncurry_volume_preserving g d).quasiMeasurePreserving.ae (ae_finitePolynomial_ne_zero p hp)


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLength MvPolynomial Matrix Module MeasureTheory

variable {M : Type*} [LieRing M] [LieAlgebra ℝ M] {g d L : ℕ}


private theorem rightSpan_eq_range (S : Fin g → M) (L : ℕ) :
    rightSpan (K := ℝ) S L = Submodule.span ℝ
      (Set.range (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval S)) := by
  unfold rightSpan
  apply congrArg (Submodule.span ℝ)
  ext X
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, w.property, rfl⟩

private theorem combination_mem (S : Fin g → M) (c : {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ) :
    (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval S) c) ∈ rightSpan (K := ℝ) S L := by
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (word_mem S w.val L w.property)

private theorem eval_boundedPolynomial (b : Basis (Fin d) ℝ M) (c : {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ)
    (x : Fin g × Fin d → ℝ) (k : Fin d) :
    MvPolynomial.eval x ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => wordPolynomial b w.val k) c)) =
      b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval (fun i => b.equivFun.symm (fun k => x (i, k)))) c)) k := by
  simp [Finsupp.linearCombination_apply, Algebra.smul_def, Finsupp.linearCombination_apply, Finsupp.sum, eval_wordPolynomial, map_sum, map_smul]

private def spanningPolynomial (b : Basis (Fin d) ℝ M) (c : Fin d → {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ) :
    MvPolynomial (Fin g × Fin d) ℝ :=
    Matrix.det (fun i j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => wordPolynomial b w.val i) (c j)))

private theorem eval_spanningPolynomial (b : Basis (Fin d) ℝ M)
    (c : Fin d → {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ) (x : Fin g × Fin d → ℝ) :
    MvPolynomial.eval x (spanningPolynomial b c) =
      Matrix.det (fun i j => b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval (fun i => b.equivFun.symm (fun k => x (i, k)))) (c j))) i) := by
  let P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin g × Fin d) ℝ) :=
    fun i j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => wordPolynomial b w.val i) (c j))
  change MvPolynomial.eval x P.det = _
  rw [(MvPolynomial.eval x).map_det P]
  congr 1
  ext i j
  exact eval_boundedPolynomial b (c j) x i

private theorem determinant_ne_zero_implies_span_top [FiniteDimensional ℝ M]
    (b : Basis (Fin d) ℝ M) (c : Fin d → {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ) (S : Fin g → M)
    (hdet : Matrix.det (fun i j => b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval S) (c j))) i) ≠ 0) :
    rightSpan (K := ℝ) S L = ⊤ := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hli' : LinearIndependent ℝ (fun j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval S) (c j))) :=
    LinearIndependent.of_comp b.equivFun.toLinearMap hli
  have hspan := hli'.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b).symm
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro X ⟨j, rfl⟩
  exact combination_mem S (c j)

theorem ae_span_top_of_witness [FiniteDimensional ℝ M]
    (b : Basis (Fin d) ℝ M) (S0 : Fin g → M)
    (hS0 : rightSpan (K := ℝ) S0 L = ⊤) :
    ∀ᵐ x : Fin g → Fin d → ℝ,
      rightSpan (K := ℝ) ((fun i => b.equivFun.symm (x i))) L = ⊤ := by
  classical
  have hex : ∀ j : Fin d, ∃ c : {w : RightWord (Fin g) // w.rightWordLength ≤ L} →₀ ℝ, (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.rightWordLength ≤ L} => w.val.rightWordEval S0) c) = b j := by
    intro j
    apply Finsupp.mem_span_range_iff_exists_finsupp.mp
    rw [← rightSpan_eq_range, hS0]
    exact Submodule.mem_top
  choose c hc using hex
  let x0 : Fin g × Fin d → ℝ := fun ik => b.equivFun (S0 ik.1) ik.2
  have hg : (fun i => b.equivFun.symm (fun k => x0 (i, k))) = S0 := by
    funext i
    exact b.equivFun.symm_apply_apply (S0 i)
  have hp0 : MvPolynomial.eval x0 (spanningPolynomial b c) = 1 := by
    rw [eval_spanningPolynomial, hg]
    simp_rw [hc]
    have hm : (fun i j => b.equivFun (b j) i) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      simp [Basis.equivFun_self, Matrix.one_apply, eq_comm]
    rw [hm, Matrix.det_one]
  have hp : spanningPolynomial b c ≠ 0 := by
    intro h
    simp [h] at hp0
  filter_upwards [ae_nestedPolynomial_ne_zero _ hp] with x hx
  apply determinant_ne_zero_implies_span_top b c
  rwa [eval_spanningPolynomial] at hx


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction
  MeasureTheory
attribute [local instance] LieRing.ofAssociativeRing


private def extendedPair (g n : ℕ) (i : Fin g) : suSet (n + 2) :=
    if h : i.val < 2 then compactPair n ⟨i.val, h⟩ else 0

private theorem extendedPair_span_top (g n : ℕ) (hg : 2 ≤ g) :
    rightSpan (K := ℝ) (extendedPair g n) (16 * (1 + Nat.log 2 (n + 1))) = ⊤ := by
  apply top_unique
  rw [← compactPair_span_top n]
  apply rightSpan_reindex_le (Fin.castLE hg)
  intro i
  simp [extendedPair, i.isLt]

private def coordinateLinearMap (g n : ℕ) :
    (Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) →ₗ[ℝ]
      (Fin g → Fin n → Fin n → ℂ) :=
  LinearMap.pi fun i => (suSet n).subtype.comp
    ((Module.finBasis ℝ (suSet n)).equivFun.symm.toLinearMap.comp (LinearMap.proj i))


private theorem suCoordinateMap_measurableEmbedding (g n : ℕ) :
    MeasurableEmbedding (show (Fin g → Fin (Module.finrank ℝ (suSet n)) → ℝ) →
      (Fin g → Fin n → Fin n → ℂ) from suCoordinateMap g n) := by
  have hinj : Function.Injective (coordinateLinearMap g n) := by
    intro x y h
    funext i
    have hi := congrArg (fun S : Fin g → (Matrix (Fin n) (Fin n) ℂ) => S i) h
    apply ((Module.finBasis ℝ (suSet n))).equivFun.symm.injective
    exact Subtype.ext hi
  exact ((coordinateLinearMap g n).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)).measurableEmbedding


private theorem ae_rightSpan_eq (g n : ℕ) (hg : 2 ≤ g) :
    ∀ᵐ (S : Fin g → Fin (n + 2) → Fin (n + 2) → ℂ) ∂(suPairMeasure g (n + 2)),
      rightSpan (K := ℝ)
        (show Fin g → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ from S)
        (16 * (1 + Nat.log 2 (n + 1))) = suSet (n + 2) := by
  have hh := ae_span_top_of_witness ((Module.finBasis ℝ (suSet (n + 2)))) (extendedPair g n)
    (extendedPair_span_top g n hg)
  rw [suPairMeasure, (suCoordinateMap_measurableEmbedding g (n + 2)).ae_map_iff]
  filter_upwards [hh] with x hx
  have hm := congrArg (Submodule.map (suSet (n + 2)).subtype) hx
  rw [Submodule.map_subtype_top] at hm
  change Submodule.map (show suSet (n + 2) →ₗ⁅ℝ⁆ Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ
    from (suLie (n + 2)).incl).toLinearMap _ = _ at hm
  rw [rightSpan_map] at hm
  exact hm

open D5.S3.Quantum.Algebra.GenericLieLengthConstruction D5.S3.Quantum.Algebra.GenericLieLengthFiltration MeasureTheory

def claim : Prop := ∀ g ≥ 2, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ), n ≥ 2 →
  ∀ᵐ (S : Fin g → Fin n → Fin n → ℂ) ∂(suPairMeasure g n),
    c * Real.log n ≤ (lieLength n (Finset.univ.image S) : ℝ) ∧
    (lieLength n (Finset.univ.image S) : ℝ) ≤ C * Real.log n

set_option maxHeartbeats 800000 in
theorem result : claim := by
  intro g hg
  have hgl : 0 < Real.log ((g : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < g + 1 by omega))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log (g + 1), 32 / Real.log 2, div_pos zero_lt_one hgl,
    div_pos (by norm_num) h2, ?_⟩
  intro n hn
  let m := n - 2
  have he : n = m + 2 := by dsimp [m]; omega
  rw [he]
  filter_upwards [ae_rightSpan_eq g m hg] with S hS
  constructor
  · exact lower_lieLength_of_saturation (m + 2) g (16 * (1 + Nat.log 2 (m + 1))) (by omega) hg S
      (by  omega) hS
  · have hu := D5.S3.Quantum.Algebra.GenericLieLengthFiltration.lieLength_le_of_span S (by  omega : 1 ≤ 16 * (1 + Nat.log 2 (m + 1))) hS
    have hur : (lieLength (m + 2) (Finset.univ.image S) : ℝ) ≤
        16 * (1 + (Nat.log 2 (m + 1) : ℝ)) := by
      exact_mod_cast hu
    exact hur.trans (by simpa only [Nat.cast_add, Nat.cast_ofNat] using upper_log m)


end
end D5.S3.Quantum.Algebra.GenericLieLength
