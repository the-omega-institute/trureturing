/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex-Zariski density of actual periodic two-site phase ambiguity. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-! Unitary covariance and polynomial continuation extend the parity collisions
to a complex-Zariski-dense set of actual targets. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity

open PeriodicMPSParentIntersection PeriodicMPSTwoSiteAmbiguity
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped BigOperators Matrix

noncomputable section

private def changePhysical (U : Bond) (A : Fin 2 → Bond) : Fin 2 → Bond :=
  fun i => ∑ j, U i j • A j

private def wordBasis (U : Bond) (n : ℕ) : Matrix (Word n) (Word n) ℂ :=
  fun w v => ∏ i, U (w i) (v i)

private def pairBasis (U : Bond) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p s => U p.1 s.1 * U p.2 s.2

private lemma wordMatrix_changePhysical (U : Bond) (A : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    wordMatrix (changePhysical U A) w = ∑ v, wordBasis U n w v • wordMatrix A v := by
  classical
  induction n with
  | zero =>
    simp [wordMatrix, wordBasis, List.ofFn_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    simp only [changePhysical, Fin.cons_zero, Finset.sum_mul, Finset.mul_sum,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, Fin.consEquiv, Equiv.coe_fn_mk,
      wordMatrix_cons, wordBasis, Fin.prod_univ_succ, Fin.cons_succ]
    rw [Finset.sum_comm]
    simp only [mul_comm (U _ _)]

private lemma state_changePhysical (U : Bond) (A : Fin 2 → Bond) (n : ℕ) :
    gamma (changePhysical U A) n 1 = (wordBasis U n) *ᵥ (gamma A n 1) := by
  funext w
  simp [gamma, wordMatrix_changePhysical, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mulVec, dotProduct, smul_eq_mul]

private lemma wordBasis_mul (U V : Bond) (n : ℕ) :
    wordBasis (U * V) n = wordBasis U n * wordBasis V n := by
  ext a b
  simp only [wordBasis, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp_rw [Finset.prod_mul_distrib]

private lemma wordBasis_one (n : ℕ) : wordBasis (1 : Bond) n = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [wordBasis]
  · have he : ∃ i, a i ≠ b i := by simpa [funext_iff] using h
    obtain ⟨i, hi⟩ := he
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

private lemma wordBasis_star (U : Bond) (n : ℕ) :
    wordBasis U.conjTranspose n = (wordBasis U n).conjTranspose := by
  ext a b
  simp [wordBasis, star_prod, Matrix.conjTranspose_apply]

private lemma wordBasis_transpose (U : Bond) (n : ℕ) :
    wordBasis U.transpose n = (wordBasis U n).transpose := rfl

private lemma mix_associates (U V : Bond) (A : Fin 2 → Bond) :
    changePhysical U (changePhysical V A) = changePhysical (U * V) A := by
  funext i
  simp only [changePhysical, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

private lemma changePhysical_one (A : Fin 2 → Bond) : changePhysical 1 A = A := by
  classical
  funext i
  simp [changePhysical, Matrix.one_apply]

private lemma flattening_changePhysical (U : Bond) (A : Fin 2 → Bond) (r : ℕ) :
    twoFlattening (changePhysical U A) r =
      pairBasis U * twoFlattening A r * (wordBasis U (r + 2)).transpose := by
  classical
  ext ⟨i, j⟩ w
  rw [flattening_entry, wordMatrix_changePhysical]
  simp only [changePhysical, Matrix.mul_apply, Matrix.transpose_apply, pairBasis]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [flattening_entry]
  ring

private lemma changePhysical_unitary_raw (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A : Fin 2 → Bond) (r : ℕ) :
    rawTwo (changePhysical U.val A) r =
      pairBasis U.val * rawTwo A r * (pairBasis U.val).conjTranspose := by
  have hu : (U.val.transpose) * (U.val.transpose).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.transpose_mem_unitaryGroup_iff.mpr U.property)
  have h : (wordBasis U.val (r + 2)).transpose *
      ((wordBasis U.val (r + 2)).transpose).conjTranspose = 1 := by
    rw [← wordBasis_transpose, ← wordBasis_star, ← wordBasis_mul, hu, wordBasis_one]
  rw [rawTwo, flattening_changePhysical, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.transpose _) (Matrix.conjTranspose _) _, h]
  simp only [Matrix.one_mul, rawTwo, Matrix.mul_assoc]

private lemma changePhysical_spanning (U : Matrix.unitaryGroup (Fin 2) ℂ) (A : Fin 2 → Bond)
    (h : TwoSiteSpanning A) : TwoSiteSpanning (changePhysical U.val A) := by
  let T := changePhysical U.val A
  let S := Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => T p.1 * T p.2)
  have hu : U.val.conjTranspose * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have he : changePhysical U.val.conjTranspose T = A := by
    rw [show T = changePhysical U.val A from rfl, mix_associates, hu, changePhysical_one]
  change S = ⊤
  apply top_unique
  rw [← h]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simp only [← he, changePhysical, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  exact S.sum_mem (fun k _ => S.sum_mem (fun l _ =>
    S.smul_mem _ (Submodule.subset_span ⟨(l, k), rfl⟩)))

private lemma changePhysical_preserves_collision (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (A B : Fin 2 → Bond) (r : ℕ)
    (he : rawTwo B r = rawTwo A r)
    (hne : ∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma A (r + 4) 1) :
    rawTwo (changePhysical U.val B) r = rawTwo (changePhysical U.val A) r ∧
      ∀ c : ℂ, gamma (changePhysical U.val B) (r + 4) 1 ≠
        c • gamma (changePhysical U.val A) (r + 4) 1 := by
  constructor
  · simp only [changePhysical_unitary_raw, he]
  intro c hc
  have hu : U.val.conjTranspose * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [state_changePhysical, state_changePhysical] at hc
  apply hne c
  have e := congrArg (fun x => wordBasis U.val.conjTranspose (r + 4) *ᵥ x) hc
  simpa only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← wordBasis_mul, hu, wordBasis_one,
    Matrix.one_mulVec] using e

private def polynomialPullback {R : Type*} [CommSemiring R] (C : ℂ →+* R)
    {n : ℕ} (P : MvPolynomial (Word n) ℂ) (A : Fin 2 → Matrix (Fin 2) (Fin 2) R) : R :=
  P.eval₂ C fun w => ((List.ofFn fun i => A (w i)).prod).trace

private lemma polynomialPullback_map {R : Type*} [CommSemiring R] (C : ℂ →+* R)
    (e : R →+* ℂ) (he : e.comp C = RingHom.id ℂ) {n : ℕ} (P : MvPolynomial (Word n) ℂ)
    (A : Fin 2 → Matrix (Fin 2) (Fin 2) R) :
    e (polynomialPullback C P A) = P.eval (traceWord 2 2 n (fun i => (A i).map e)) := by
  rw [polynomialPullback, MvPolynomial.eval₂_comp_left, he]
  congr 1
  funext w
  dsimp [Function.comp_def, traceWord]
  rw [AddMonoidHom.map_trace]
  have hp := map_list_prod (e.mapMatrix (m := Fin 2)) (List.ofFn fun i => A (w i))
  simpa only [RingHom.mapMatrix_apply, List.map_ofFn, Function.comp_def] using
    congrArg Matrix.trace hp

private lemma polynomial_eval_of_open {ι : Type*} [Finite ι] (P : MvPolynomial ι ℂ)
    {S : Set (ι → ℂ)} (hS : IsOpen S) (hSne : S.Nonempty) (h : ∀ x ∈ S, P.eval x = 0) :
    ∀ x, P.eval x = 0 := by
  let := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := hSne
  exact fun y => (AnalyticOnNhd.eval_mvPolynomial P).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ x) (Filter.mem_of_superset (hS.mem_nhds hx) h)
    (Set.mem_univ y)

private lemma polynomial_on_parity (r : ℕ) (P : MvPolynomial (Word (r + 4)) ℂ)
    (h : ∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 → rawTwo B r = rawTwo A r →
      (∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma A (r + 4) 1) →
      P.eval (traceWord 2 2 (r + 4) A) = 0)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (a b q : ℂ) :
    P.eval (traceWord 2 2 (r + 4) (changePhysical U.val (parityPair a b q))) = 0 := by
  classical
  let X := MvPolynomial.X (R := ℂ) (σ := Fin 3)
  let M : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 3) ℂ) :=
    ![!![X 0, 0; 0, X 1], !![0, X 2; X 2, 0]]
  let F := polynomialPullback (R := MvPolynomial (Fin 3) ℂ) MvPolynomial.C P
    (fun i => ∑ j, MvPolynomial.C (σ := Fin 3) (U.val i j) • M j)
  have hF (x : Fin 3 → ℂ) : F.eval x =
      P.eval (traceWord 2 2 (r + 4) (changePhysical U.val (parityPair (x 0) (x 1) (x 2)))) := by
    have he : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ :=
      RingHom.ext fun z => MvPolynomial.eval_C z
    dsimp only [F]
    rw [polynomialPullback_map _ (MvPolynomial.eval x) he]
    apply congrArg (fun M : Fin 2 → Bond => P.eval (traceWord 2 2 (r + 4) M))
    funext i
    apply Matrix.ext
    intro j k
    simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, MvPolynomial.eval_C, changePhysical]
    congr 1
    funext l
    fin_cases l <;> fin_cases j <;> fin_cases k <;> simp [M, X, parityPair]
  have hv := polynomial_eval_of_open F (parityCondition_open r) (parityCondition_nonempty r)
    (fun x hx => by
      rw [hF]
      obtain ⟨hspan, B, hB, hne⟩ := parity_actual_collision x r hx
      obtain ⟨he, hc⟩ := changePhysical_preserves_collision U _ B r hB hne
      exact h _ _ (rank_of_spanning _
        (changePhysical_spanning U _ hspan) r) he hc)
  simpa [hF] using hv ![a, b, q]

private lemma polynomial_unit_circle (P : Polynomial ℂ) (h : ∀ z : ℂ, ‖z‖ = 1 → P.eval z = 0) :
    P = 0 := by
  apply P.eq_zero_of_infinite_isRoot
  have hz : (Set.Ioo (0 : ℝ) Real.pi).Infinite := Set.Ioo_infinite Real.pi_pos
  refine (hz.image (f := circleMap 0 1) ?_).mono ?_
  · intro x hx y hy hxy
    apply eq_of_circleMap_eq one_ne_zero _ hxy
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Real.pi_pos]
  · rintro _ ⟨x, _, rfl⟩
    exact h _ (by simp [norm_circleMap_zero])

private lemma diagonal_unitary (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    Matrix.diagonal ![z, w] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hz' : z * star z = 1 := by simpa [hz] using Complex.mul_conj' z
  have hw' : w * star w = 1 := by simpa [hw] using Complex.mul_conj' w
  exact congrArg Matrix.diagonal (by funext i; fin_cases i <;> first | exact hz' | exact hw')

private def diagonalPullback {n : ℕ} (P : MvPolynomial (Word n) ℂ)
    (U W : Bond) (A : Fin 2 → Bond) (z w : Polynomial ℂ) : Polynomial ℂ :=
  polynomialPullback Polynomial.C P (fun i =>
    ∑ j, (((U.map Polynomial.C) * Matrix.diagonal ![z, w]) *
      (W.map Polynomial.C)) i j • (A j).map Polynomial.C)

private lemma diagonalPullback_eval {n : ℕ} (P : MvPolynomial (Word n) ℂ)
    (U W : Bond) (A : Fin 2 → Bond) (z w : Polynomial ℂ) (t : ℂ) :
    (diagonalPullback P U W A z w).eval t =
      P.eval (traceWord 2 2 n
        (changePhysical (U * Matrix.diagonal ![z.eval t, w.eval t] * W) A)) := by
  classical
  let e := Polynomial.evalRingHom t
  have he : e.comp Polynomial.C = RingHom.id ℂ :=
    RingHom.ext fun c => Polynomial.eval_C
  change e (diagonalPullback P U W A z w) = _
  rw [diagonalPullback, polynomialPullback_map _ e he]
  apply congrArg (fun M : Fin 2 → Bond => P.eval (traceWord 2 2 n M))
  funext i
  apply Matrix.ext
  intro j k
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul,
    changePhysical, Matrix.mul_apply, Matrix.diagonal_apply]
  have hC (c : ℂ) : e (Polynomial.C c) = c := Polynomial.eval_C
  simp only [hC]
  congr 1
  funext l
  congr 1
  congr 1
  funext m
  congr 1
  congr 1
  funext p
  congr 1
  split_ifs with h
  · fin_cases p <;> rfl
  · exact map_zero e

private lemma polynomial_on_diagonals {n : ℕ} (P : MvPolynomial (Word n) ℂ)
    (U W : Matrix.unitaryGroup (Fin 2) ℂ) (A : Fin 2 → Bond)
    (h : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ,
      P.eval (traceWord 2 2 n (changePhysical V.val A)) = 0) (z w : ℂ) :
    P.eval (traceWord 2 2 n
      (changePhysical (U.val * Matrix.diagonal ![z, w] * W.val) A)) = 0 := by
  let f (a b : ℂ) :=
    P.eval (traceWord 2 2 n (changePhysical (U.val * Matrix.diagonal ![a, b] * W.val) A))
  have hunit (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : f a b = 0 := by
    let D : Matrix.unitaryGroup (Fin 2) ℂ := ⟨Matrix.diagonal ![a, b], diagonal_unitary a b ha hb⟩
    exact h (U * D * W)
  let g := diagonalPullback P U.val W.val A
  have he (a b : Polynomial ℂ) (t : ℂ) : (g a b).eval t = f (a.eval t) (b.eval t) :=
    diagonalPullback_eval P U.val W.val A a b t
  have hfirst (a b : ℂ) (hb : ‖b‖ = 1) : f a b = 0 := by
    have hp : g Polynomial.X (Polynomial.C b) = 0 :=
      polynomial_unit_circle _ (fun t ht => by
        rw [he, Polynomial.eval_X, Polynomial.eval_C]
        exact hunit t b ht hb)
    simpa only [he, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero] using
      congrArg (Polynomial.eval a) hp
  have hp : g (Polynomial.C z) Polynomial.X = 0 := polynomial_unit_circle _ (fun t ht => by
    rw [he, Polynomial.eval_C, Polynomial.eval_X]
    exact hfirst z t ht)
  simpa only [he, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero] using
    congrArg (Polynomial.eval w) hp

private lemma polynomial_on_physical (r : ℕ) (P : MvPolynomial (Word (r + 4)) ℂ)
    (A : Fin 2 → Bond)
    (h : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      P.eval (traceWord 2 2 (r + 4) (changePhysical U.val A)) = 0) (L : Bond) :
    P.eval (traceWord 2 2 (r + 4) (changePhysical L A)) = 0 := by
  obtain ⟨U, V, hL⟩ :=
    D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues L
  let W : Matrix.unitaryGroup (Fin 2) ℂ := V⁻¹
  obtain ⟨d, hd⟩ : ∃ d : Fin 2 → ℂ, L = U.val * Matrix.diagonal d * W.val :=
    ⟨_, hL⟩
  rw [hd, ← FinVec.etaExpand_eq d]
  exact polynomial_on_diagonals P U W A h (d 0) (d 1)

private lemma square_traceless (T : Bond) (h : T.trace = 0) :
    T * T = (-(T.det)) • (1 : Bond) := by
  rw [Matrix.trace_fin_two] at h
  have ht : T 1 1 = -(T 0 0) := eq_neg_of_add_eq_zero_right h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, ht] <;> ring

private lemma anticommute_traceless (T Y : Bond) (hT : T.trace = 0) (hY : Y.trace = 0)
    (h : (T * Y).trace = 0) : T * Y = -(Y * T) := by
  rw [Matrix.trace_fin_two] at hT hY
  have ht : T 1 1 = -(T 0 0) := eq_neg_of_add_eq_zero_right hT
  have hy : Y 1 1 = -(Y 0 0) := eq_neg_of_add_eq_zero_right hY
  have hh : T 0 0 * Y 0 0 + T 0 1 * Y 1 0 + (T 1 0 * Y 0 1 + T 0 0 * Y 0 0) = 0 := by
    simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, ht, hy] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hy] <;>
    first | linear_combination hh | ring

private def traceComponent (X : Bond) : ℂ := X.trace / 2

private def tracelessPart (X : Bond) : Bond := X - traceComponent X • (1 : Bond)

private lemma tracelessPart_trace (X : Bond) : (tracelessPart X).trace = 0 := by
  simp [tracelessPart, traceComponent, Matrix.trace_smul, Matrix.trace_one]

private lemma parity_virtual_form (X Y : Bond) (hy : Y.trace = 0)
    (hxy : (X * Y).trace = 0) (hyDet : Y.det ≠ 0) (hxDet : (tracelessPart X).det ≠ 0) :
    ∃ a b q : ℂ, ∃ S : Bond, IsUnit S.det ∧
      ∀ i, (![X, Y] : Fin 2 → Bond) i = S * parityPair a b q i * S⁻¹ := by
  let T := tracelessPart X
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-T.det) (n := 2) (by decide)
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (-Y.det) (n := 2) (by decide)
  have hs0 : s ≠ 0 := by intro h; simp [h, T, hxDet] at hs
  have hq0 : q ≠ 0 := by intro h; simp [h, hyDet] at hq
  have htY : (T * Y).trace = 0 := by
    simp [T, tracelessPart, sub_mul, Matrix.trace_smul, hxy, hy]
  have ht := tracelessPart_trace X
  have hanti := anticommute_traceless T Y ht hy htY
  have hsq : Y * Y = q ^ 2 • (1 : Bond) := by rw [hq, square_traceless Y hy]
  have hsDet : (T - s • (1 : Bond)).det = 0 := by
    have hd : T 1 1 = -(T 0 0) :=
      eq_neg_of_add_eq_zero_right (by simpa only [Matrix.trace_fin_two] using ht)
    simp only [Matrix.det_fin_two] at hs ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    norm_num [hd] at hs ⊢
    linear_combination hs
  obtain ⟨u, hu, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hsDet
  have huT : T *ᵥ u = s • u := by
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
  let v := q⁻¹ • (Y *ᵥ u)
  have hYu : Y *ᵥ u = q • v := by simp [v, hq0]
  have hYv : Y *ᵥ v = q • u := by
    rw [show v = q⁻¹ • (Y *ᵥ u) from rfl, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hsq, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
    congr 1
    field_simp
  have hv : v ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hYv
    exact hu ((smul_eq_zero.mp hYv.symm).resolve_left hq0)
  have hvT : T *ᵥ v = (-s) • v := by
    calc
      T *ᵥ v = q⁻¹ • ((T * Y) *ᵥ u) := by rw [show v = q⁻¹ • (Y *ᵥ u) from rfl,
        Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      _ = (-s) • v := by
        rw [hanti, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, huT, Matrix.mulVec_smul]
        rw [neg_smul, ← smul_neg, smul_smul, show q⁻¹ * s = s * q⁻¹ by ring]
        simp only [v, smul_smul, smul_neg]
  let S : Bond := !![u 0, v 0; u 1, v 1]
  have hS (c : Fin 2 → ℂ) : S *ᵥ c = c 0 • u + c 1 • v := by
    funext i
    fin_cases i <;> simp [S, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdetS : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    obtain ⟨c, hc, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    rw [hS] at hzero
    have hz := congrArg (fun x => T *ᵥ x) hzero
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, huT, hvT, Matrix.mulVec_zero,
      smul_smul] at hz
    have h0 : (2 * s * c 0) • u = 0 := calc
      _ = s • (c 0 • u + c 1 • v) + ((c 0 * s) • u + (c 1 * -s) • v) := by module
      _ = 0 := by rw [hzero, hz, smul_zero, add_zero]
    have hc0 : c 0 = 0 :=
      (mul_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hu)).resolve_left
        (mul_ne_zero two_ne_zero hs0)
    have hc1 : c 1 = 0 := by
      simpa [hc0, hv] using hzero
    exact hc (funext (Fin.forall_fin_two.mpr ⟨hc0, hc1⟩))
  have hXu : X *ᵥ u = (traceComponent X + s) • u := by
    have hXT : X = T + traceComponent X • (1 : Bond) := by simp [T, tracelessPart]
    conv_lhs => rw [hXT]
    rw [Matrix.add_mulVec, huT, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul, add_comm]
  have hXv : X *ᵥ v = (traceComponent X - s) • v := by
    have hXT : X = T + traceComponent X • (1 : Bond) := by simp [T, tracelessPart]
    conv_lhs => rw [hXT]
    rw [Matrix.add_mulVec, hvT, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_add_neg,
      add_smul, add_comm]
  refine ⟨traceComponent X + s, traceComponent X - s, q, S, hdetS, fun i => ?_⟩
  have entry (M : Bond) (x y : Fin 2 → ℂ) (c : ℂ) (he : M *ᵥ x = c • y) (j : Fin 2) :
      M j 0 * x 0 + M j 1 * x 1 = c * y j := by
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] using
      congrFun he j
  have hmul : (![X, Y] : Fin 2 → Bond) i * S =
      S * parityPair (traceComponent X + s) (traceComponent X - s) q i := by
    fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k
    all_goals simp [S, parityPair, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      first
      | linear_combination entry _ _ _ _ hXu 0
      | linear_combination entry _ _ _ _ hXu 1
      | linear_combination entry _ _ _ _ hXv 0
      | linear_combination entry _ _ _ _ hXv 1
      | linear_combination entry _ _ _ _ hYu 0
      | linear_combination entry _ _ _ _ hYu 1
      | linear_combination entry _ _ _ _ hYv 0
      | linear_combination entry _ _ _ _ hYv 1
  exact (Matrix.mul_nonsing_inv_cancel_right _ _ hdetS).symm.trans (congrArg (· * S⁻¹) hmul)

private lemma wordMatrix_virtual (A : Fin 2 → Bond) (S : Bond) (h : IsUnit S.det)
    {n : ℕ} (w : Word n) :
    wordMatrix (fun i => S * A i * S⁻¹) w = S * wordMatrix A w * S⁻¹ := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero, Matrix.mul_nonsing_inv S h]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ih]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left S _ h]

private lemma traceWord_virtual (A : Fin 2 → Bond) (S : Bond) (h : IsUnit S.det) (n : ℕ) :
    traceWord 2 2 n (fun i => S * A i * S⁻¹) = traceWord 2 2 n A := by
  funext w
  change (wordMatrix (fun i => S * A i * S⁻¹) w).trace = (wordMatrix A w).trace
  rw [wordMatrix_virtual _ _ h, Matrix.mul_assoc, Matrix.trace_mul_comm S,
    Matrix.mul_assoc (wordMatrix A w) S⁻¹ S, Matrix.nonsing_inv_mul S h, mul_one]

private def parityY (A : Fin 2 → Bond) : Bond := A 1 - ((A 1).trace / (A 0).trace) • A 0

private def parityX (A : Fin 2 → Bond) : Bond :=
  A 0 - (((A 0) * parityY A).trace / (parityY A * parityY A).trace) • parityY A

private def generalCondition (A : Fin 2 → Bond) : Prop :=
  (A 0).trace ≠ 0 ∧ (parityY A * parityY A).trace ≠ 0 ∧
    (tracelessPart (parityX A)).det ≠ 0

private lemma generalCondition_parity (A : Fin 2 → Bond) (h : generalCondition A) (n : ℕ) :
    ∃ L : Bond, ∃ a b q : ℂ,
      traceWord 2 2 n A = traceWord 2 2 n (changePhysical L (parityPair a b q)) := by
  let d := (A 1).trace / (A 0).trace
  let e := ((A 0) * parityY A).trace / (parityY A * parityY A).trace
  have hy : (parityY A).trace = 0 := by
    simp [parityY, Matrix.trace_smul]
    field_simp [h.1]
    ring
  have hxy : (parityX A * parityY A).trace = 0 := by
    simp [parityX, sub_mul, Matrix.trace_smul]
    field_simp [h.2.1]
    ring
  have hyDet : (parityY A).det ≠ 0 := by
    intro hd
    have hzero := square_traceless (parityY A) hy
    rw [hd, neg_zero, zero_smul] at hzero
    exact h.2.1 (by simp [hzero])
  obtain ⟨a, b, q, S, hS, he⟩ :=
    parity_virtual_form (parityX A) (parityY A) hy hxy hyDet h.2.2
  let L : Bond := !![1, e; d, 1 + d * e]
  have hA : changePhysical L ![parityX A, parityY A] = A := by
    funext i
    fin_cases i <;> simp [changePhysical, L, e, d, parityX, parityY, Fin.sum_univ_two]
    module
  have hc : A = fun i => S * changePhysical L (parityPair a b q) i * S⁻¹ := by
    rw [← hA]
    funext i
    simp only [changePhysical, he, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  exact ⟨L, a, b, q, hc ▸ traceWord_virtual _ _ hS n⟩

private lemma generalCondition_open : IsOpen {A | generalCondition A} := by
  have htr : Continuous (fun A : Fin 2 → Bond => (A 0).trace) := by
    simp only [Matrix.trace_fin_two]
    fun_prop
  have hy : ContinuousOn parityY {A | (A 0).trace ≠ 0} := by
    apply (continuous_apply 1).continuousOn.sub
    have h1 : Continuous (fun A : Fin 2 → Bond => (A 1).trace) := by
      simp only [Matrix.trace_fin_two]
      fun_prop
    exact (h1.continuousOn.div htr.continuousOn (fun _ hA => hA)).smul
      (continuous_apply 0).continuousOn
  let U : Set (Fin 2 → Bond) := {A | (A 0).trace ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun htr continuous_const
  have hy2 : ContinuousOn (fun A => (parityY A * parityY A).trace) U := by
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  let V : Set (Fin 2 → Bond) := U ∩ {A | (parityY A * parityY A).trace ≠ 0}
  have hV : IsOpen V := hy2.isOpen_inter_preimage hU (isOpen_ne_fun continuous_id continuous_const)
  have hx : ContinuousOn parityX V := by
    have hy' := hy.mono (Set.inter_subset_left : V ⊆ U)
    apply (continuous_apply 0).continuousOn.sub
    have hn : ContinuousOn (fun A : Fin 2 → Bond => (A 0 * parityY A).trace) V := by
      simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      fun_prop
    exact (hn.div (hy2.mono Set.inter_subset_left) (fun _ hA => hA.2)).smul hy'
  have ht : Continuous (fun X : Bond => (tracelessPart X).det) := by
    simp only [tracelessPart, traceComponent, Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have ho := (ht.comp_continuousOn hx).isOpen_inter_preimage hV
    (isOpen_ne (x := (0 : ℂ)))
  have hset : {A | generalCondition A} =
      V ∩ (fun X => (tracelessPart (parityX X)).det) ⁻¹' {y | y ≠ 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, generalCondition, V, U, Set.mem_inter_iff, Set.mem_preimage,
      and_assoc]
  rw [hset]
  exact ho

private lemma generalCondition_nonempty : {A | generalCondition A}.Nonempty := by
  refine ⟨parityPair 1 2 1, ?_⟩
  norm_num [generalCondition, parityY, parityX, tracelessPart, traceComponent, parityPair,
    Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.one_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]

/-- The ambiguous rank-four targets are complex-Zariski dense in the actual
periodic trace-word image, in the polynomial-vanishing formulation. -/
theorem actual_collision_polynomial_vanishing (r : ℕ) (P : MvPolynomial (Word (r + 4)) ℂ)
    (h : ∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 → rawTwo B r = rawTwo A r →
      (∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma A (r + 4) 1) →
      P.eval (traceWord 2 2 (r + 4) A) = 0) :
    ∀ A : Fin 2 → Bond, P.eval (traceWord 2 2 (r + 4) A) = 0 := by
  classical
  let ι := Fin 2 × Fin 2 × Fin 2
  let ofEntries (x : ι → ℂ) : Fin 2 → Bond := fun i j k => x (i, j, k)
  let F := polynomialPullback (R := MvPolynomial ι ℂ) MvPolynomial.C P
    (fun i => Matrix.of fun j k => MvPolynomial.X (i, j, k))
  have hF (x : ι → ℂ) : F.eval x = P.eval (traceWord 2 2 (r + 4) (ofEntries x)) := by
    have he : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ :=
      RingHom.ext fun z => MvPolynomial.eval_C z
    dsimp only [F]
    rw [polynomialPullback_map _ (MvPolynomial.eval x) he]
    apply congrArg (fun M : Fin 2 → Bond => P.eval (traceWord 2 2 (r + 4) M))
    funext i
    apply Matrix.ext
    intro j k
    simp [ofEntries, Matrix.map_apply]
  have hcont : Continuous ofEntries :=
    continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => continuous_apply (i, j, k)
  have hS : IsOpen (ofEntries ⁻¹' {A | generalCondition A}) := generalCondition_open.preimage hcont
  obtain ⟨T, hT⟩ := generalCondition_nonempty
  have hne : (ofEntries ⁻¹' {A | generalCondition A}).Nonempty :=
    ⟨fun p => T p.1 p.2.1 p.2.2, hT⟩
  have hz := polynomial_eval_of_open F hS hne (fun x hx => by
    rw [hF]
    obtain ⟨L, a, b, q, he⟩ := generalCondition_parity (ofEntries x) hx (r + 4)
    rw [he]
    exact polynomial_on_physical r P (parityPair a b q) (fun U =>
      polynomial_on_parity r P h U a b q) L)
  intro A
  simpa only [hF] using hz (fun p => A p.1 p.2.1 p.2.2)

/-- Every nonempty principal complex-Zariski open in the actual image contains
a rank-four two-site ambiguity. Three sites recover phase on the rank-four locus. -/
theorem two_vs_three_phase_recovery (r : ℕ) :
    (∀ (P : MvPolynomial (Word (r + 4)) ℂ) (A : Fin 2 → Bond),
      P.eval (traceWord 2 2 (r + 4) A) ≠ 0 →
      ∃ B C : Fin 2 → Bond, P.eval (traceWord 2 2 (r + 4) B) ≠ 0 ∧
        (twoFlattening B r).rank = 4 ∧ rawTwo C r = rawTwo B r ∧
        (∀ c : ℂ, gamma C (r + 4) 1 ≠ c • gamma B (r + 4) 1)) ∧
    (∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 →
      (rawThree B r = rawThree A r ↔
        ∃ c : ℂ, ‖c‖ = 1 ∧ gamma B (r + 4) 1 = c • gamma A (r + 4) 1)) := by
  refine ⟨?_, (rank_locus_inhabited_and_phase_recovery r).2⟩
  intro P A hA
  classical
  by_cases hex : ∃ B C : Fin 2 → Bond, P.eval (traceWord 2 2 (r + 4) B) ≠ 0 ∧
      (twoFlattening B r).rank = 4 ∧ rawTwo C r = rawTwo B r ∧
      (∀ c : ℂ, gamma C (r + 4) 1 ≠ c • gamma B (r + 4) 1)
  · exact hex
  exfalso
  apply hA
  apply actual_collision_polynomial_vanishing r P _ A
  intro B C hB hC hp
  by_contra hP
  exact hex ⟨B, C, hP, hB, hC, hp⟩

private lemma traceWord_cast {m n : ℕ} (h : m = n) (A : Fin 2 → Bond) (w : Word m) :
    traceWord 2 2 n A (cast (congrArg Word h) w) = traceWord 2 2 m A w := by
  subst n
  rfl

/-- Three sites recover phase on a nonempty principal complex-Zariski open of the
actual image. The polynomial is constructed so that each target on this open has rank four. -/
theorem three_site_recovery_principal_open (r : ℕ) :
    ∃ P : MvPolynomial (Word (r + 4)) ℂ,
      (∃ A : Fin 2 → Bond, P.eval (traceWord 2 2 (r + 4) A) ≠ 0) ∧
      ∀ A B : Fin 2 → Bond, P.eval (traceWord 2 2 (r + 4) A) ≠ 0 →
        (rawThree B r = rawThree A r ↔
          ∃ c : ℂ, ‖c‖ = 1 ∧ gamma B (r + 4) 1 = c • gamma A (r + 4) 1) := by
  classical
  obtain ⟨A₀, hA₀⟩ := (rank_locus_inhabited_and_phase_recovery r).1
  have hsurj : Function.Surjective (twoFlattening A₀ r).mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hA₀)
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  have hn : 2 + (r + 2) = r + 4 := by omega
  let F : Matrix (Fin 2 × Fin 2) (Word (r + 2)) (MvPolynomial (Word (r + 4)) ℂ) :=
    Matrix.of fun p w =>
      MvPolynomial.X (cast (congrArg Word hn) (Fin.append ![p.1, p.2] w))
  let R' : Matrix (Word (r + 2)) (Fin 2 × Fin 2) (MvPolynomial (Word (r + 4)) ℂ) :=
    R.map MvPolynomial.C
  let M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (MvPolynomial (Word (r + 4)) ℂ) :=
    F * R'
  let P := M.det
  have he (A : Fin 2 → Bond) :
      P.eval (traceWord 2 2 (r + 4) A) = (twoFlattening A r * R).det := by
    let e := MvPolynomial.eval (traceWord 2 2 (r + 4) A)
    change e M.det = _
    rw [e.map_det]
    have hmul : M.map e = F.map e * R'.map e := Matrix.map_mul (f := e)
    have hF : F.map e = twoFlattening A r := by
      apply Matrix.ext
      intro p w
      change e (MvPolynomial.X _) = _
      rw [show e (MvPolynomial.X (cast (congrArg Word hn) (Fin.append ![p.1, p.2] w))) =
        traceWord 2 2 (r + 4) A (cast (congrArg Word hn) (Fin.append ![p.1, p.2] w)) from
          MvPolynomial.eval_X _, traceWord_cast hn]
      rfl
    have hR' : R'.map e = R := by
      apply Matrix.ext
      intro p w
      exact MvPolynomial.eval_C _
    change (M.map e).det = _
    rw [hmul, hF, hR']
  refine ⟨P, ⟨A₀, by rw [he, hR, Matrix.det_one]; exact one_ne_zero⟩, ?_⟩
  intro A B hA
  have hdet : IsUnit (twoFlattening A r * R).det := isUnit_iff_ne_zero.mpr (he A ▸ hA)
  have hright := Matrix.mul_nonsing_inv _ hdet
  have hsurj' : Function.Surjective (twoFlattening A r * R).mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_, hright⟩
  have hlow := Matrix.rank_mul_le_left (twoFlattening A r) R
  rw [Matrix.mulVec_surjective_iff_rank_eq_card.mp hsurj'] at hlow
  have hr : (twoFlattening A r).rank = 4 := by
    apply le_antisymm
    · simpa using (twoFlattening A r).rank_le_card_height
    · simpa using hlow
  exact (rank_locus_inhabited_and_phase_recovery r).2 A B hr

private lemma wordMatrix_scaled (z : ℂ) (A : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    wordMatrix (z • A) w = z ^ n • wordMatrix A w := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ih]
    simp [Pi.smul_apply, smul_smul, pow_succ, mul_comm]

private lemma gamma_scaled (z : ℂ) (A : Fin 2 → Bond) (n : ℕ) :
    gamma (z • A) n 1 = z ^ n • gamma A n 1 := by
  funext w
  simp only [gamma, one_mul, wordMatrix_scaled, Matrix.trace_smul, Pi.smul_apply]

private lemma rawTwo_scaled (z : ℂ) (A : Fin 2 → Bond) (r : ℕ) :
    rawTwo (z • A) r = (z ^ (r + 4) * star (z ^ (r + 4))) • rawTwo A r := by
  have h : twoFlattening (z • A) r = z ^ (r + 4) • twoFlattening A r := by
    ext p w
    change (wordMatrix (z • A) (Fin.append ![p.1, p.2] w)).trace = _
    have hp : z ^ (2 + (r + 2)) = z ^ (r + 4) :=
      congrArg (fun k : ℕ => z ^ k) (by omega)
    rw [wordMatrix_scaled, Matrix.trace_smul, hp]
    rfl
  simp only [rawTwo, h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm]

private lemma rawTwo_trace_eq_mass (A : Fin 2 → Bond) (r : ℕ) :
    (rawTwo A r).trace =
      (↑(∑ p : Fin 2 × Fin 2, ∑ w, Complex.normSq (twoFlattening A r p w)) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.star_def, Complex.mul_conj]

/-- An actual two-site collision at positive rank can be transported to the
unit-mass slice by scaling both shared cores by the same scalar. -/
theorem normalize_two_site_collision (A B : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4)
    (he : rawTwo B r = rawTwo A r)
    (hne : ∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma A (r + 4) 1) :
    ∃ z : ℂ, (rawTwo (z • A) r).trace = 1 ∧
      rawTwo (z • B) r = rawTwo (z • A) r ∧
      ∀ c : ℂ, gamma (z • B) (r + 4) 1 ≠ c • gamma (z • A) (r + 4) 1 := by
  classical
  let m : ℝ := ∑ p : Fin 2 × Fin 2, ∑ w, Complex.normSq (twoFlattening A r p w)
  have hmass : (rawTwo A r).trace = (m : ℂ) := rawTwo_trace_eq_mass A r
  have hm : 0 < m := by
    by_contra! hn
    have hz : m = 0 := le_antisymm hn
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    have hf : twoFlattening A r = 0 := by
      ext p w
      have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp hz p (Finset.mem_univ p)
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp hp w
          (Finset.mem_univ w))
    rw [hf, Matrix.rank_zero] at hr
    norm_num at hr
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((Real.sqrt m)⁻¹ : ℝ) : ℂ)
    (n := r + 4) (by omega)
  have hz0 : z ^ (r + 4) ≠ 0 := by
    rw [hz]
    exact_mod_cast inv_ne_zero (Real.sqrt_pos.2 hm).ne'
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [rawTwo_scaled, Matrix.trace_smul, hmass, hz]
    change (((Real.sqrt m)⁻¹ : ℝ) : ℂ) *
      star (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * (m : ℂ) = 1
    have hc : star (((Real.sqrt m)⁻¹ : ℝ) : ℂ) = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    rw [hc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [← sq, inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  · simp only [rawTwo_scaled, he]
  · intro c h
    rw [gamma_scaled, gamma_scaled, smul_comm c] at h
    exact hne c (smul_right_injective _ hz0 h)

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity
