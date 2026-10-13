/- GID: D5/S3/Quantum/Algebra/GenericLieLengthGenericity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericLieLengthGenericity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jia-Capel generic Lie length conjecture formalization. -/
/- admission_basis: escape-witness
   Direct frozen dependencies: none; every D5 proof dependency is in this delivery.
   Module witnesses: ae_mvPolynomial_ne_zero, ae_span_top_of_witness.
   Heap depth uses Nat.size; coordinate and matrix operations use their Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
   ae_univariate_ne_zero: proof_shape: bind-only; escape_witness: none; consumers: ae_mvPolynomial_ne_zero.
   ae_mvPolynomial_ne_zero: proof_shape: content; escape_witness: ae_mvPolynomial_ne_zero; consumers: ae_finitePolynomial_ne_zero.
   bracket_coordinate: proof_shape: bind-only; escape_witness: none; consumers: eval_wordPolynomial.
   wordPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_boundedPolynomial,eval_spanningPolynomial,eval_wordPolynomial,spanningPolynomial.
   eval_wordPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_boundedPolynomial.
   ae_finitePolynomial_ne_zero: proof_shape: content; escape_witness: ae_mvPolynomial_ne_zero; consumers: ae_nestedPolynomial_ne_zero.
   uncurry_volume_preserving: proof_shape: bind-only; escape_witness: none; consumers: ae_nestedPolynomial_ne_zero.
   ae_nestedPolynomial_ne_zero: proof_shape: content; escape_witness: ae_mvPolynomial_ne_zero; consumers: ae_span_top_of_witness.
   rightSpan_eq_range: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   combination_mem: proof_shape: bind-only; escape_witness: none; consumers: determinant_ne_zero_implies_span_top.
   eval_boundedPolynomial: proof_shape: bind-only; escape_witness: none; consumers: eval_spanningPolynomial.
   spanningPolynomial: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness,eval_spanningPolynomial.
   eval_spanningPolynomial: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   determinant_ne_zero_implies_span_top: proof_shape: bind-only; escape_witness: none; consumers: ae_span_top_of_witness.
   ae_span_top_of_witness: proof_shape: content; escape_witness: ae_span_top_of_witness; consumers: ae_rightSpan_eq.
-/


import D5.S3.Quantum.Algebra.GenericLieLengthFiltration
import Mathlib.Topology.Algebra.MvPolynomial



namespace D5.S3.Quantum.Algebra.GenericLieLengthGenericity

noncomputable section



open MeasureTheory

private theorem ae_univariate_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : ℝ, p.eval x ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hp).measure_zero volume

theorem ae_mvPolynomial_ne_zero (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  induction n with
  | zero =>
    have hC := MvPolynomial.eq_C_of_isEmpty p
    have hc : p.coeff 0 ≠ 0 := by
      intro h
      apply hp
      simpa [h] using hC
    exact Filter.Eventually.of_forall (fun x => by rw [hC, MvPolynomial.eval_C]; exact hc)
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv ℝ n p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by simpa [q] using h)
    have hex : ∃ k, q.coeff k ≠ 0 := by
      by_contra h
      push_neg at h
      apply hq
      apply Polynomial.ext
      intro k
      simpa only [Polynomial.coeff_zero] using h k
    obtain ⟨k, hk⟩ := hex
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hm : Measurable (fun z : ℝ × (Fin n → ℝ) => MvPolynomial.eval (e.symm z) p) :=
      p.continuous_eval.measurable.comp e.symm.measurable
    have hs : MeasurableSet {z : ℝ × (Fin n → ℝ) | MvPolynomial.eval (e.symm z) p ≠ 0} :=
      (measurableSet_singleton (0 : ℝ)).preimage hm |>.compl
    have hy : ∀ᵐ y : Fin n → ℝ, ∀ᵐ x : ℝ,
        MvPolynomial.eval (e.symm (x, y)) p ≠ 0 := by
      filter_upwards [ih (q.coeff k) hk] with y hy
      have hmap : q.map (MvPolynomial.eval y) ≠ 0 := by
        intro h
        have hc := congrArg (fun f : Polynomial ℝ => f.coeff k) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy hc
      have hz := ae_univariate_ne_zero (q.map (MvPolynomial.eval y)) hmap
      filter_upwards [hz] with x hx
      have heval : e.symm (x, y) = Fin.cons x y := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
        rfl

      rw [heval]
      rw [MvPolynomial.eval_eq_eval_mv_eval']
      exact hx
    have hx : ∀ᵐ z : ℝ × (Fin n → ℝ), MvPolynomial.eval (e.symm z) p ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hs).mpr ((Measure.ae_ae_comm hs).mpr hy)
    have he := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have h := he.quasiMeasurePreserving.ae hx
    filter_upwards [h] with x hx
    simpa only [e, MeasurableEquiv.symm_apply_apply] using hx


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
      b.equivFun (w.eval ((fun i => b.equivFun.symm (fun k => x (i, k))))) k := by
  induction w generalizing k with
  | single i =>
    simp only [wordPolynomial, eval_X, RightWord.eval, LinearEquiv.apply_symm_apply]
  | cons i w ih =>
    simp only [wordPolynomial, map_sum, map_mul, eval_C, eval_X, ih, RightWord.eval]
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
  have hh := D5.S3.Quantum.Algebra.GenericLieLengthGenericity.ae_mvPolynomial_ne_zero _ q hq
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


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthGenericity MvPolynomial Matrix Module MeasureTheory

variable {M : Type*} [LieRing M] [LieAlgebra ℝ M] {g d L : ℕ}


private theorem rightSpan_eq_range (S : Fin g → M) (L : ℕ) :
    rightSpan (K := ℝ) S L = Submodule.span ℝ
      (Set.range (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval S)) := by
  unfold rightSpan
  apply congrArg (Submodule.span ℝ)
  ext X
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, w.property, rfl⟩

private theorem combination_mem (S : Fin g → M) (c : {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ) :
    (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval S) c) ∈ rightSpan (K := ℝ) S L := by
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (word_mem S w.val L w.property)

private theorem eval_boundedPolynomial (b : Basis (Fin d) ℝ M) (c : {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ)
    (x : Fin g × Fin d → ℝ) (k : Fin d) :
    MvPolynomial.eval x ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => wordPolynomial b w.val k) c)) =
      b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval (fun i => b.equivFun.symm (fun k => x (i, k)))) c)) k := by
  simp [Finsupp.linearCombination_apply, Algebra.smul_def, Finsupp.linearCombination_apply, Finsupp.sum, eval_wordPolynomial, map_sum, map_smul]

private def spanningPolynomial (b : Basis (Fin d) ℝ M) (c : Fin d → {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ) :
    MvPolynomial (Fin g × Fin d) ℝ :=
    Matrix.det (fun i j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => wordPolynomial b w.val i) (c j)))

private theorem eval_spanningPolynomial (b : Basis (Fin d) ℝ M)
    (c : Fin d → {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ) (x : Fin g × Fin d → ℝ) :
    MvPolynomial.eval x (spanningPolynomial b c) =
      Matrix.det (fun i j => b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval (fun i => b.equivFun.symm (fun k => x (i, k)))) (c j))) i) := by
  let P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin g × Fin d) ℝ) :=
    fun i j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => wordPolynomial b w.val i) (c j))
  change MvPolynomial.eval x P.det = _
  rw [(MvPolynomial.eval x).map_det P]
  congr 1
  ext i j
  exact eval_boundedPolynomial b (c j) x i

private theorem determinant_ne_zero_implies_span_top [FiniteDimensional ℝ M]
    (b : Basis (Fin d) ℝ M) (c : Fin d → {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ) (S : Fin g → M)
    (hdet : Matrix.det (fun i j => b.equivFun ((Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval S) (c j))) i) ≠ 0) :
    rightSpan (K := ℝ) S L = ⊤ := by
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hli' : LinearIndependent ℝ (fun j => (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval S) (c j))) :=
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
  have hex : ∀ j : Fin d, ∃ c : {w : RightWord (Fin g) // w.length ≤ L} →₀ ℝ, (Finsupp.linearCombination ℝ (fun w : {w : RightWord (Fin g) // w.length ≤ L} => w.val.eval S0) c) = b j := by
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


end
end D5.S3.Quantum.Algebra.GenericLieLengthGenericity
