/- GID: D5/S3/Analytic/Hunter/NCHunterKernelRigidity
   generality: G
   mirror-B: D5/B/S3/Analytic/Hunter/NCHunterKernelRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Hunter residual has the common operator kernel. -/
/-
admission_basis: open-problem-resolution (#13735; Proved)
Direct frozen dependencies: none; NCHunterPositivity is first delivered here; its frozen antecedent is OccupancyWordSectors.
Information-escape registration is paused under CLAUDE.md section 3.9.
selfadjoint_square_zero: proof_shape: bind-only; escape_witness: none; consumer: selfadjoint_power_zero | selfadjoint_power_zero: proof_shape: bind-only; escape_witness: none; consumer: even_rows_force_zero
sum_fibers: proof_shape: bind-only; escape_witness: none; consumer: form_grouped | form_grouped: proof_shape: bind-only; escape_witness: none; consumer: word_moment_grouped
word_moment_grouped: proof_shape: bind-only; escape_witness: none; consumer: word_moment_zero_powers | degree_fiber_constant: proof_shape: bind-only; escape_witness: none; consumer: grouped_constant
grouped_constant: proof_shape: bind-only; escape_witness: none; consumer: word_moment_zero_powers | eval_constant: proof_shape: bind-only; escape_witness: none; consumer: word_moment_zero_powers
shifted_moment_complex_posDef: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_zero_coefficients | shifted_moment_zero_coefficients: proof_shape: bind-only; escape_witness: none; consumer: word_moment_zero_powers
word_moment_zero_powers: proof_shape: bind-only; escape_witness: none; consumer: even_rows_force_zero | word_moment_even_identity: proof_shape: bind-only; escape_witness: none; consumer: even_rows_force_zero
mixed_row_vanishes: proof_shape: bind-only; escape_witness: none; consumer: mixed_sharp_row_eq | mixed_sharp_row_eq: proof_shape: bind-only; escape_witness: none; consumer: kernel_to_mixed_rows
kernel_to_mixed_rows: proof_shape: bind-only; escape_witness: none; consumer: mixed_rows_as_moments | eval_cons: proof_shape: bind-only; escape_witness: none; consumer: moment_words_succ_inner
word_kills_common_kernel: proof_shape: bind-only; escape_witness: none; consumer: common_kernel_to_residual | common_kernel_to_residual: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp
cons_mixed: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp | even_rows_force_zero: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp
exists_mixed_word: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp | gram_row_as_moment: proof_shape: bind-only; escape_witness: none; consumer: mixed_rows_as_moments
mixed_rows_as_moments: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp | moment_coefficient_cons: proof_shape: bind-only; escape_witness: none; consumer: moment_words_succ_inner
moment_words_succ_inner: proof_shape: bind-only; escape_witness: none; consumer: odd_rows_force_zero | odd_rows_force_zero: proof_shape: bind-only; escape_witness: none; consumer: kernel_rigidity_from_sharp
kernel_rigidity_from_sharp: proof_shape: bind-only; escape_witness: none; consumer: kernel_equality_from_sharp | kernel_equality_from_sharp: proof_shape: bind-only; escape_witness: none; consumer: result
result: proof_shape: content; escape_witness: urn_closed_form
-/
import D5.S3.Analytic.Hunter.NCHunterPositivity
open scoped BigOperators Matrix MatrixOrder ComplexOrder InnerProductSpace Matrix.Module
set_option backward.isDefEq.respectTransparency false
namespace GVHunter
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (occupation)
attribute [local instance] Classical.propDecidable Classical.decEq
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I K : Type*} [Fintype I] [Fintype K]
variable {A : Type*} [Ring A] [Algebra ℂ A]
private theorem selfadjoint_square_zero (T : H →L[ℂ] H) (hs : IsSelfAdjoint T) (h : H) (hh : (T ^ 2) h = 0) : T h = 0 := by
  have he : (star T).comp T = T ^ 2 := by
    rw [hs.star_eq]
    rfl
  have hker := T.ker_adjoint_comp_self
  change LinearMap.ker ((star T).comp T).toLinearMap = _ at hker
  rw [he] at hker
  have hm : h ∈ LinearMap.ker (T ^ 2).toLinearMap := hh
  rw [hker] at hm
  exact hm
private theorem selfadjoint_power_zero (T : H →L[ℂ] H) (hs : IsSelfAdjoint T) {k : ℕ} (hk : 0 < k) (h : H) (hh : (T ^ k) h = 0) : T h = 0 := by
  have he : LinearMap.ker (T.toLinearMap ^ 1) = LinearMap.ker (T.toLinearMap ^ 2) := by
    ext x
    simp only [LinearMap.mem_ker, pow_one]
    constructor
    · intro hx
      change T x = 0 at hx
      change T (T x) = 0
      rw [hx, map_zero]
    · intro hx
      apply selfadjoint_square_zero T hs x
      simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe] using hx
  have hker := Module.End.ker_pow_constant he (k-1)
  rw [show 1 + (k-1) = k by omega, pow_one] at hker
  have hm : h ∈ LinearMap.ker (T.toLinearMap ^ k) := by
    simpa only [LinearMap.mem_ker, ← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe] using hh
  rw [← hker] at hm
  exact hm
private noncomputable def momentCoefficient {n k : ℕ} (g : Fin n → ℕ) (w : (Fin k → Fin n)) : ℂ :=
  ∏ i : Fin n, (Nat.factorial ((occupation w).count i + g i) : ℂ)
private noncomputable def momentWords {n k : ℕ} (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (h : H) : H :=
  ∑ w : (Fin k → Fin n), momentCoefficient g w • wordEval X w h
private noncomputable def wordMomentMatrix {n m : ℕ} (g : Fin n → ℕ) : Matrix ((Fin m → Fin n)) ((Fin m → Fin n)) ℂ :=
  fun u v => ∏ i : Fin n, (Nat.factorial ((occupation u).count i + (occupation v).count i + g i) : ℂ)
private lemma sum_fibers {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq J] [AddCommMonoid A] (f : I → J) (T : J → I → A) : (∑ a : J, ∑ w : I with f w = a, T a w) = ∑ w : I, T (f w) w := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
omit [CompleteSpace H] in
private lemma form_grouped {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] (f : I → J) (D : Matrix J J ℂ) (v : I → H) : matrixForm D (fun a => ∑ w : I with f w = a, v w) = matrixForm (fun u w => D (f u) (f w)) v := by
  classical
  simp only [matrixForm, Matrix.Module.smul_apply, inner_sum, sum_inner, inner_smul_right,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [sum_fibers]
  apply Finset.sum_congr rfl
  intro u hu
  rw [sum_fibers]
private noncomputable def groupedWords {n m : ℕ} (v : (Fin m → Fin n) → H) (a : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m}) : H :=
  ∑ w : (Fin m → Fin n) with wordDegree w = a, v w
private noncomputable def shiftedMomentMatrix {n m : ℕ} (g : Fin n → ℕ) : Matrix ({a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m}) ({a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m}) ℂ :=
  fun a b => (factorialMoment g a.val b.val : ℂ)
omit [CompleteSpace H] in
private lemma word_moment_grouped {n m : ℕ} (g : Fin n → ℕ) (v : (Fin m → Fin n) → H) : matrixForm (shiftedMomentMatrix g) (groupedWords v) = matrixForm (wordMomentMatrix g) v := by
  change matrixForm (shiftedMomentMatrix g) (fun a => ∑ w : (Fin m → Fin n) with wordDegree w = a, v w) = _
  rw [form_grouped]
  congr 1
  ext u w
  simp only [shiftedMomentMatrix, factorialMoment, wordDegree, wordMomentMatrix]
  push_cast
  rfl
private lemma degree_fiber_constant {n m : ℕ} (i : Fin n) (w : (Fin m → Fin n)) (hw : wordDegree w = wordDegree (fun _ : Fin m => i)) : w = fun _ => i := by
  have hc : (occupation w).count i = m := by
    have he := congrArg (fun a : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m} => (a.val i : ℕ)) hw
    simpa only [wordDegree, count_constant] using he
  have hcard : (occupation w).count i = (occupation w).card := by
    simpa only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation_card] using hc
  have hm := Multiset.count_eq_card.mp hcard
  funext j
  exact (hm (w j) (by simp [occupation, List.mem_ofFn])).symm
omit [InnerProductSpace ℂ H] [CompleteSpace H] in
private lemma grouped_constant {n m : ℕ} (v : (Fin m → Fin n) → H) (i : Fin n) : groupedWords v (wordDegree (fun _ : Fin m => i)) = v (fun _ => i) := by
  classical
  unfold groupedWords
  apply Finset.sum_eq_single (fun _ : Fin m => i)
  · intro w hw hne
    exact (hne (degree_fiber_constant i w (Finset.mem_filter.mp hw).2)).elim
  · intro hn
    exact (hn (by simp)).elim
omit [CompleteSpace H] in
private lemma eval_constant {n m : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) : wordEval X (fun _ : Fin m => i) = X i ^ m := by
  simp [wordEval, List.ofFn_const]
private theorem shifted_moment_complex_posDef {n m : ℕ} (g : Fin n → ℕ) : (shiftedMomentMatrix (m:=m) g).PosDef := by
  classical
  let F : Matrix (Fin n → Fin (m+1)) ({a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m}) ℂ :=
    fun k a => (factorialFeature g a.val k : ℂ)
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    funext a
    have hh := congrFun hxy a.val
    have ha : (factorialFeature g a.val a.val : ℂ) ≠ 0 := by
      exact_mod_cast (factorial_feature_self_pos g a.val).ne'
    have hrow (z : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m} → ℂ) :
        F.mulVec z a.val = (factorialFeature g a.val a.val : ℂ) * z a := by
      change (∑ b : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m}, (factorialFeature g b.val a.val : ℂ) * z b) = _
      apply Finset.sum_eq_single a
      · intro b hb hba
        rw [degree_feature_diagonal g a b (Ne.symm hba)]
        simp
      · intro hn
        exact (hn (Finset.mem_univ a)).elim
    rw [hrow x, hrow y] at hh
    exact mul_left_cancel₀ ha hh
  have hdiag : (Matrix.diagonal (fun k : Fin n → Fin (m+1) => (factorialWeight g k : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun k => by exact_mod_cast factorial_weight_pos g k)
  have hp := hdiag.conjTranspose_mul_mul_same hinj
  have hm : shiftedMomentMatrix (m:=m) g =
      Fᴴ * (Matrix.diagonal (fun k : Fin n → Fin (m+1) => (factorialWeight g k : ℂ))) * F := by
    ext a b
    simp only [shiftedMomentMatrix, factorial_moment_gram, Complex.ofReal_sum,
      Complex.ofReal_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    dsimp only [F]
    simp only [Complex.star_def, Complex.conj_ofReal, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hm]
  exact hp
omit [CompleteSpace H] in
private theorem shifted_moment_zero_coefficients {n m : ℕ} (g : Fin n → ℕ) (v : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m} → H) (hz : matrixForm (shiftedMomentMatrix g) v = 0) : ∀ a, v a = 0 :=
  positive_definite_form_zero_vectors _ (shifted_moment_complex_posDef g) v hz
omit [CompleteSpace H] in
private lemma word_moment_zero_powers {n m : ℕ} (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (h : H) (hz : matrixForm (wordMomentMatrix g) (fun w : (Fin m → Fin n) => wordEval X w h) = 0) : ∀ i, (X i ^ m) h = 0 := by
  have he : matrixForm (shiftedMomentMatrix g)
      (groupedWords (fun w : (Fin m → Fin n) => wordEval X w h)) = 0 := by
    rw [word_moment_grouped]
    exact hz
  have hv := shifted_moment_zero_coefficients g _ he
  intro i
  have hi := hv (wordDegree (fun _ : Fin m => i))
  simpa only [grouped_constant, eval_constant] using hi
private lemma word_moment_even_identity {n m : ℕ} (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) : inner ℂ h (momentWords (k:=m+m) g X h) =
      matrixForm (wordMomentMatrix g) (fun w : (Fin m → Fin n) => wordEval X w h) := by
  classical
  unfold momentWords
  rw [← (gramWordEquiv n m).sum_comp
    (fun w => momentCoefficient g w • wordEval X w h), Fintype.sum_prod_type]
  simp only [matrixForm, Matrix.Module.smul_apply, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change momentCoefficient g (Fin.append ((Equiv.piCongrLeft' (fun _ : Fin m => Fin n) Fin.revPerm) u) v) *
    inner ℂ h (wordEval X (Fin.append ((Equiv.piCongrLeft' (fun _ : Fin m => Fin n) Fin.revPerm) u) v) h) = _
  rw [word_eval_append, word_eval_reverse X hs, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  simp only [momentCoefficient, count_append, count_reverse, wordMomentMatrix]
def claim : Prop :=
  ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X : Fin n → H →L[ℂ] H), (∀ i, IsSelfAdjoint (X i)) →
    LinearMap.ker (residual n d X).toLinearMap =
      ⨅ i : Fin n, LinearMap.ker (X i).toLinearMap
private theorem mixed_row_vanishes {n d : ℕ} (w : (Fin d → Fin n)) (hw : ¬ pure w) : ∀ v : (Fin d → Fin n), pureProjection n d w v = 0 := by
  classical
  intro v
  simp [pureProjection, Matrix.diagonal, hw]
private theorem mixed_sharp_row_eq {n d : ℕ} (w : (Fin d → Fin n)) (hw : ¬ pure w) : ∀ v : (Fin d → Fin n), sharpGram n d w v = gram n d w v := by
  intro v
  simp [sharpGram, mixed_row_vanishes w hw v]
private lemma kernel_to_mixed_rows {n d : ℕ} (hd : 0 < d) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (hD : (sharpGram n d).PosSemidef) (h : H) (hh : residual n d X h = 0) : ∀ w : (Fin d → Fin n), ¬ pure w → ((gram n d) • (fun v : (Fin d → Fin n) => wordEval X v h)) w = 0 := by
  have hf : matrixForm (sharpGram n d) (fun w : (Fin d → Fin n) => wordEval X w h) = 0 := by
    rw [← residual_inner_gram hd X hs h, hh, inner_zero_right]
  have hr := positive_form_zero_rows _ hD _ hf
  intro w hw
  simpa only [Matrix.Module.smul_apply, mixed_sharp_row_eq w hw] using hr w
omit [CompleteSpace H] in
private lemma eval_cons {n k : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : (Fin k → Fin n)) : wordEval X (Fin.cons i w) = X i * wordEval X w := by
  simp [wordEval, List.ofFn_succ]
omit [CompleteSpace H] in
private lemma word_kills_common_kernel {n k : ℕ} (hk : 0 < k) (X : Fin n → H →L[ℂ] H) (h : H) (hX : ∀ i, X i h = 0) (w : (Fin k → Fin n)) : wordEval X w h = 0 := by
  unfold wordEval
  apply List.prod_induction_nonempty (fun T : H →L[ℂ] H => T h = 0)
  · intro T S _ hS
    simp only [mul_apply_eq_comp, hS, map_zero]
  · intro he
    have ht := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at ht
    omega
  · intro T hT
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
    exact hX (w j)
omit [CompleteSpace H] in
private lemma common_kernel_to_residual {n d : ℕ} (hd : 0 < d) (X : Fin n → H →L[ℂ] H) (h : H) (hX : ∀ i, X i h = 0) : residual n d X h = 0 := by
  have hw : ∀ w : (Fin (2*d) → Fin n), wordEval X w h = 0 :=
    word_kills_common_kernel (by omega) X h hX
  have hp : ∀ i, (X i ^ (2*d)) h = 0 := by
    intro i
    simpa only [eval_constant] using hw (fun _ => i)
  simp [residual, nchs, sum_apply, smul_apply, hw, hp]
private lemma cons_mixed {n k : ℕ} (i : Fin n) (w : (Fin k → Fin n)) (hw : ¬ pure w) : ¬ pure (Fin.cons i w) := by
  rintro ⟨j,hj⟩
  apply hw
  refine ⟨j,fun t => ?_⟩
  simpa using hj t.succ
private lemma even_rows_force_zero {n m : ℕ} (hm : 0 < m) (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) (hz : momentWords (k:=m+m) g X h = 0) : ∀ i, X i h = 0 := by
  have hf : matrixForm (wordMomentMatrix g) (fun w : (Fin m → Fin n) => wordEval X w h) = 0 := by
    rw [← word_moment_even_identity g X hs h, hz, inner_zero_right]
  have hp := word_moment_zero_powers g X h hf
  intro i
  exact selfadjoint_power_zero (X i) (hs i) hm h (hp i)
private lemma exists_mixed_word {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) : ∃ w : (Fin k → Fin n), ¬ pure w := by
  classical
  let w : (Fin k → Fin n) := fun j => if j.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  refine ⟨w, ?_⟩
  rintro ⟨i,hi⟩
  have h0 := hi ⟨0,by omega⟩
  have h1 := hi ⟨1,by omega⟩
  have he : (1:ℕ)=0 := by
    have ht := h0.trans h1.symm
    simpa [w] using congrArg Fin.val ht
  omega
omit [CompleteSpace H] in
private lemma gram_row_as_moment {n d : ℕ} (X : Fin n → H →L[ℂ] H) (h : H) (w : (Fin d → Fin n)) : ((gram n d) • (fun v : (Fin d → Fin n) => wordEval X v h)) w = (1/(Nat.factorial (2*d) : ℂ)) • momentWords (k:=d) ((occupation w).count) X h := by
  simp only [Matrix.Module.smul_apply, gram, momentWords, momentCoefficient, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  simp only [Nat.add_comm]
  ring
private lemma mixed_rows_as_moments {n d : ℕ} (hd : 0 < d) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (hD : (sharpGram n d).PosSemidef) (h : H) (hh : residual n d X h = 0) : ∀ w : (Fin d → Fin n), ¬ pure w → momentWords (k:=d) ((occupation w).count) X h = 0 := by
  have hr := kernel_to_mixed_rows hd X hs hD h hh
  intro w hw
  have he := hr w hw
  rw [gram_row_as_moment] at he
  have hc : (1/(Nat.factorial (2*d) : ℂ)) ≠ 0 := by
    apply one_div_ne_zero
    exact_mod_cast Nat.factorial_ne_zero (2*d)
  exact (smul_eq_zero.mp he).resolve_left hc
private lemma moment_coefficient_cons {n k : ℕ} (g : Fin n → ℕ) (i : Fin n) (w : (Fin k → Fin n)) : momentCoefficient g (Fin.cons i w) = momentCoefficient (Function.update g i (g i + 1)) w := by
  classical
  unfold momentCoefficient
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [count_cons, ite_true, Function.update_self,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp only [count_cons, if_neg hji, Function.update_of_ne hji, zero_add]
private lemma moment_words_succ_inner {n k : ℕ} (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) : inner ℂ h (momentWords (k:=k+1) g X h) =
      ∑ i : Fin n, inner ℂ (X i h) (momentWords (k:=k) (Function.update g i (g i + 1)) X h) := by
  unfold momentWords
  rw [sum_word_succ]
  simp only [inner_sum, inner_smul_right, moment_coefficient_cons, eval_cons,
    mul_apply_eq_comp]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hs i) h (wordEval X w h)).symm
private lemma odd_rows_force_zero {n m k : ℕ} (hm : 0 < m) (hk : k+1=m+m) (g : Fin n → ℕ) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) (hz : ∀ i, momentWords (k:=k) (Function.update g i (g i + 1)) X h = 0) : ∀ i, X i h = 0 := by
  have he : inner ℂ h (momentWords (k:=m+m) g X h) = 0 := by
    rw [← hk, moment_words_succ_inner g X hs h]
    simp only [hz, inner_zero_right, Finset.sum_const_zero]
  have hf : matrixForm (wordMomentMatrix g) (fun w : (Fin m → Fin n) => wordEval X w h) = 0 := by
    rw [← word_moment_even_identity g X hs h]
    exact he
  have hp := word_moment_zero_powers g X h hf
  intro i
  exact selfadjoint_power_zero (X i) (hs i) hm h (hp i)
private theorem kernel_rigidity_from_sharp {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (hD : (sharpGram n d).PosSemidef) (h : H) : residual n d X h = 0 ↔ ∀ i, X i h = 0 := by
  constructor
  · intro hh
    have hr := mixed_rows_as_moments (by omega) X hs hD h hh
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨m,hm⟩ := he
      obtain ⟨w,hw⟩ := exists_mixed_word hn hd
      have hz := hr w hw
      have hlen : d=m+m := hm
      have hz' : momentWords (k:=m+m) ((occupation w).count) X h = 0 := by
        simpa only [← hlen] using hz
      exact even_rows_force_zero (by omega) ((occupation w).count) X hs h hz'
    · obtain ⟨m,hm⟩ := ho
      have hbase : 2 ≤ m+m := by omega
      obtain ⟨w,hw⟩ := exists_mixed_word hn hbase
      have hlen : d=m+m+1 := by omega
      have hz : ∀ i, momentWords (k:=m+m+1) (Function.update ((occupation w).count) i ((occupation w).count i + 1)) X h = 0 := by
        intro i
        have hh' : residual n (m+m+1) X h = 0 := by rw [← hlen]; exact hh
        have hD' : (sharpGram n (m+m+1)).PosSemidef := by rw [← hlen]; exact hD
        have he := mixed_rows_as_moments (by omega) X hs hD' h hh'
          (Fin.cons i w) (cons_mixed i w hw)
        have hg : (occupation (Fin.cons i w)).count = Function.update ((occupation w).count) i ((occupation w).count i + 1) := by
          funext j
          by_cases hji : j = i
          · subst j
            simp only [count_cons, ite_true, Function.update_self, Nat.add_comm]
          · simp only [count_cons, if_neg hji, Function.update_of_ne hji, zero_add]
        simpa only [hg] using he
      exact odd_rows_force_zero (m:=m+1) (by omega) (by omega) ((occupation w).count) X hs h hz
  · exact common_kernel_to_residual (by omega) X h
private lemma kernel_equality_from_sharp {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (hD : (sharpGram n d).PosSemidef) : LinearMap.ker (residual n d X).toLinearMap = ⨅ i : Fin n, LinearMap.ker (X i).toLinearMap := by
  ext h
  simp only [LinearMap.mem_ker, Submodule.mem_iInf, ContinuousLinearMap.coe_coe]
  exact kernel_rigidity_from_sharp hn hd X hs hD h
theorem result : claim := by
  intro n d hn hd H _ _ _ X hs
  exact kernel_equality_from_sharp hn hd X hs (sharp_gram_posSemidef hn (by omega))
end GVHunter
