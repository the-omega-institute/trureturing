/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BV weighted arithmetic moments of every positive fixed order transfer to their quadratic formal values. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CentredCorrelationSummation
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionErrorBounds
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform arithmetic transfer for weighted interval moments of every fixed positive order. -/

open scoped BigOperators Topology Pointwise
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private def redA (r : ℕ) : Polynomial ℝ := (reduction_polynomial r).choose
private def redB (r : ℕ) : Polynomial ℝ := (reduction_polynomial r).choose_spec.choose

private lemma red_eval (r : ℕ) (s : ℝ) :
    (red r s).1 = (redA r).eval s ∧ (red r s).2 = (redB r).eval s :=
  (reduction_polynomial r).choose_spec.choose_spec.2.2 s

private def coefficientPool (q : ℕ) : Finset (Polynomial ℝ) :=
  insert 1 (((Finset.range (q + 1)).image redA) ∪ ((Finset.range (q + 1)).image redB))

private def coefficientFamily (q : ℕ) : Finset (Polynomial ℝ) := coefficientPool q ^ q

private def tuplePolynomial {k : ℕ} (d : Fin k → ℕ) (J : Finset ℕ) : Polynomial ℝ :=
  ∏ e ∈ Finset.univ.image d, if e ∈ J then redA (mult d e) else redB (mult d e)

private lemma tuplePolynomial_eval {k : ℕ} (d : Fin k → ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.univ.image d) (s : ℝ) :
    (tuplePolynomial d J).eval s =
      (∏ e ∈ J, (red (mult d e) s).1) *
        ∏ e ∈ Finset.univ.image d \ J, (red (mult d e) s).2 := by
  simp only [tuplePolynomial, Polynomial.eval_prod]
  simp_rw [apply_ite (fun p : Polynomial ℝ => p.eval s), ← (red_eval _ s).1,
    ← (red_eval _ s).2]
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext e; simp only [Finset.mem_filter]; exact ⟨And.right, fun he => ⟨hJ he, he⟩⟩
  · congr 1; ext e; simp

private lemma tuplePolynomial_mem {q k : ℕ} (hk : k ≤ q) (d : Fin k → ℕ)
    (J : Finset ℕ) : tuplePolynomial d J ∈ coefficientFamily q := by
  classical
  let D := Finset.univ.image d
  have hm (e : ℕ) : mult d e < q + 1 := by
    have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin k))) (fun i => d i = e)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    dsimp [mult]; omega
  have hf (e : ℕ) (_he : e ∈ D) :
      (if e ∈ J then redA (mult d e) else redB (mult d e)) ∈ coefficientPool q := by
    split_ifs <;> simp only [coefficientPool, Finset.mem_insert, Finset.mem_union]
    · exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (hm e), rfl⟩))
    · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (hm e), rfl⟩))
  have hp : tuplePolynomial d J ∈ coefficientPool q ^ D.card := by
    have hh := Set.finsetProd_mem_finsetProd D
      (fun _ => (coefficientPool q : Set (Polynomial ℝ)))
      (fun e => if e ∈ J then redA (mult d e) else redB (mult d e)) hf
    simpa only [Finset.prod_const, ← Finset.coe_pow, Finset.mem_coe, tuplePolynomial, D] using hh
  exact Finset.pow_subset_pow_right (by simp [coefficientPool])
    ((Finset.card_image_le).trans (by simpa using hk)) hp

private lemma finite_polynomial_correlation {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε)
    (P : Finset (Polynomial ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ p ∈ P, ∀ k : ℕ, k ≤ q → ∀ K : ℕ,
        1 ≤ K → (K : ℝ) ≤ M * N ^ β →
        ∀ T : Finset (Fin k → ℕ),
        T ⊆ Fintype.piFinset (fun _ => Finset.Ioc 0 K) →
        ∀ q : (Fin k → ℕ) → Finset ℕ → Polynomial ℝ,
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (w ((n : ℝ) / N) * p.eval (Real.log n)) *
                ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
                  if q d J = p then
                    ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1) else 0) -
            (∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
              if q d J = p then center SS J else 0) *
                (∫ x in N..2 * N, w (x / N) * p.eval (Real.log x))| ≤
              C * B * N ^ (1 / 2 + ε) * (K : ℝ) ^ k * (1 + Real.log N) ^ m := by
  choose C hC hbound using centred_polynomial_log_correlation SS β hSS hMS M ε hM hε
  refine ⟨∑ p ∈ P, C p, Finset.sum_nonneg (fun p _ => hC p),
    P.sup Polynomial.natDegree, ?_⟩
  filter_upwards [(Filter.eventually_all_finset P).mpr (fun p _ => hbound p),
    eventually_ge_atTop (2 : ℝ)] with N hN hN2
  refine ⟨hN2, ?_⟩
  intro p hp k hk K hK hKN T hT q B w hw
  have hB : 0 ≤ B := hw.2.2.1
  have hN0 : 0 ≤ N := by linarith
  have hCs : 0 ≤ ∑ p ∈ P, C p := Finset.sum_nonneg (fun p _ => hC p)
  have hlog : 1 ≤ 1 + Real.log N := by
    linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
  exact ((hN p hp).2 k hk K hK hKN T hT q B w hw).trans (by
    gcongr
    · exact Finset.single_le_sum (fun q _ => hC q) hp
    · exact Finset.le_sup hp)

lemma polynomial_weight_integrable (N : ℝ) (hN : 2 ≤ N)
    (B : ℝ) (w : ℝ → ℝ) (hw : BVBound w B) (p : Polynomial ℝ) :
    IntervalIntegrable (fun x => w (x / N) * p.eval (Real.log x)) volume N (2 * N) := by
  obtain ⟨C, _, hp⟩ := polynomial_log_bv_bound p
  obtain ⟨U, hU, hu, _⟩ := hw.2.2.2
  have h := (hp N U (eVariationOn w univ).toReal w hN hU ENNReal.toReal_nonneg
    hw.1 hu (by rw [ENNReal.ofReal_toReal hw.1])).1
  exact h.intervalIntegrable (by rw [uIcc_of_le (by linarith : N ≤ 2 * N)])

theorem formal_weight_integrable (SS : Finset ℕ → ℝ) (N H B : ℝ)
    (w : ℝ → ℝ) (k : ℕ) (a b : Fin k → ℝ) (hN : 2 ≤ N) (hw : BVBound w B) :
    IntervalIntegrable (fun x => w (x / N) * Phi SS H (Real.log x) a b)
      volume N (2 * N) := by
  classical
  have hphi (x : ℝ) : w (x / N) * Phi SS H (Real.log x) a b =
      ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
        ∑ J ∈ (Finset.univ.image d).powerset,
          center SS J * (w (x / N) * (tuplePolynomial d J).eval (Real.log x)) := by
    simp only [Phi, reducedTuple, reducedFinite, center, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro J hJ
    rw [tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
    ring
  simp_rw [hphi]
  simpa only [Finset.sum_fn] using
    (IntervalIntegrable.sum (Fintype.piFinset (fun i => points H (a i) (b i))) (fun d _ =>
    IntervalIntegrable.sum (Finset.univ.image d).powerset (fun J _ =>
      (polynomial_weight_integrable N hN B w hw (tuplePolynomial d J)).const_mul
        (center SS J))))

private lemma reduced_correlation_transfer {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
        ∀ k : ℕ, k ≤ q → ∀ a b : Fin k → ℝ, admissible M a b →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
              ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
                reducedAt (Real.log n) n d) -
            (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
              C * B * N ^ (1 / 2 + ε) * H ^ k * (1 + Real.log N) ^ m := by
  classical
  obtain ⟨C, hC, m, hbound⟩ :=
    finite_polynomial_correlation SS β hSS hMS M ε hM hε (coefficientFamily q)
  refine ⟨((coefficientFamily q).card : ℝ) * C * M ^ q, by positivity, m, ?_⟩
  filter_upwards [hbound] with N hN
  have hN0 : 0 ≤ N := by linarith [hN.1]
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN.1])
  refine ⟨hN.1, ?_⟩
  intro H hH hHN B w hw k hk a b hab
  have hB : 0 ≤ B := hw.2.2.1
  let T := Fintype.piFinset (fun i => points H (a i) (b i))
  let K := ⌊M * H⌋₊
  have hK : 1 ≤ K := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ M * H)).mpr
    simpa only [Nat.cast_one] using one_le_mul_of_one_le_of_one_le hM hH
  have hKN : (K : ℝ) ≤ M * N ^ β :=
    (Nat.floor_le (by positivity)).trans (mul_le_mul_of_nonneg_left hHN (by linarith))
  have hT : T ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Ioc 0 K) := by
    intro d hd
    apply Fintype.mem_piFinset.mpr
    intro i
    have hh := Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hd i)
    exact Finset.mem_Ioc.mpr ⟨by omega,
      hh.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_right (hab i).2.2 (by linarith)))⟩
  let f : Polynomial ℝ → ℕ → ℝ := fun p n =>
    ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
      if tuplePolynomial d J = p then
        ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1) else 0
  let c : Polynomial ℝ → ℝ := fun p =>
    ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
      if tuplePolynomial d J = p then center SS J else 0
  have hred (n : ℕ) : w ((n : ℝ) / N) * ∑ d ∈ T, reducedAt (Real.log n) n d =
      ∑ p ∈ coefficientFamily q, (w ((n : ℝ) / N) * p.eval (Real.log n)) * f p n := by
    dsimp [f]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    simp only [reducedAt, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [← tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
    rw [Finset.sum_eq_single (tuplePolynomial d J)]
    · simp; ring
    · intro p _ hp
      simp [Ne.symm hp]
    · intro hnot
      exact (hnot (tuplePolynomial_mem hk d J)).elim
  have hphi (x : ℝ) : w (x / N) * Phi SS H (Real.log x) a b =
      ∑ p ∈ coefficientFamily q, c p * (w (x / N) * p.eval (Real.log x)) := by
    dsimp [c]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Phi, reducedTuple, reducedFinite, center, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.sum_eq_single (tuplePolynomial d J)]
    · simp only [ite_true]
      rw [tuplePolynomial_eval d J (Finset.mem_powerset.mp hJ)]
      ring
    · intro p _ hp
      simp [Ne.symm hp]
    · intro hnot
      exact (hnot (tuplePolynomial_mem hk d J)).elim
  change |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
      ∑ d ∈ T, reducedAt (Real.log n) n d) -
    (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤ _
  simp_rw [hred, hphi]
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum
    (fun p _ => (polynomial_weight_integrable N hN.1 B w hw p).const_mul (c p)),
    ← Finset.sum_sub_distrib]
  simp only [intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∑ _p ∈ coefficientFamily q,
        C * B * N ^ (1 / 2 + ε) * (K : ℝ) ^ k * (1 + Real.log N) ^ m :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp =>
        hN.2 p hp k hk K hK hKN T hT tuplePolynomial B w hw))
    _ = ((coefficientFamily q).card : ℝ) *
        (C * B * N ^ (1 / 2 + ε) * (K : ℝ) ^ k * (1 + Real.log N) ^ m) := by simp
    _ ≤ ((coefficientFamily q).card : ℝ) *
        (C * B * N ^ (1 / 2 + ε) * (M ^ q * H ^ k) * (1 + Real.log N) ^ m) := by
      gcongr
      calc
        (K : ℝ) ^ k ≤ (M * H) ^ k :=
          pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
        _ ≤ _ := by rw [mul_pow]; gcongr
    _ = _ := by ring

private lemma reduced_transfer_power_error {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ H : ℝ, 1 ≤ H → H ≤ N ^ β →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
        ∀ k : ℕ, k ≤ q → ∀ a b : Fin k → ℝ, admissible M a b →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
              ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
                reducedAt (Real.log n) n d) -
            (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
              C * B * N ^ (1 / 2 + ε) * H ^ k := by
  obtain ⟨C, hC, m, hbound⟩ :=
    reduced_correlation_transfer SS β hSS hMS M (ε / 2) hM (by linarith)
  have hlog := (isLittleO_log_rpow_rpow_atTop (m : ℝ)
    (show 0 < ε / 2 by linarith)).bound (by norm_num : (0 : ℝ) < 1)
  refine ⟨C * 2 ^ m, by positivity, ?_⟩
  filter_upwards [hbound, hlog, Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hN hlog hL
  have hN0 : 0 < N := by linarith [hN.1]
  have hp : (Real.log N) ^ m ≤ N ^ (ε / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul, Real.rpow_natCast,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) m)] using hlog
  have hweight : (1 + Real.log N) ^ m ≤ 2 ^ m * N ^ (ε / 2) := by
    calc
      _ ≤ (2 * Real.log N) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 2 ^ m * (Real.log N) ^ m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  refine ⟨hN.1, ?_⟩
  intro H hH hHN B w hw k hk a b hab
  have hB : 0 ≤ B := hw.2.2.1
  calc
    _ ≤ C * B * N ^ (1 / 2 + ε / 2) * H ^ k * (1 + Real.log N) ^ m :=
      hN.2 H hH hHN B w hw k hk a b hab
    _ ≤ C * B * N ^ (1 / 2 + ε / 2) * H ^ k * (2 ^ m * N ^ (ε / 2)) := by
      gcongr
    _ = _ := by
      calc
        _ = C * 2 ^ m * B *
            (N ^ (1 / 2 + ε / 2) * N ^ (ε / 2)) * H ^ k := by ring
        _ = _ := by
          rw [← Real.rpow_add hN0,
            show (1 / 2 + ε / 2) + ε / 2 = (1 / 2 + ε : ℝ) by ring]

/-- Under the mean-square correlation hypothesis through order q, every positive-order
BV weighted arithmetic moment of order at most q differs from its quadratic formal integral
by the uniform square-root error in the prescribed power band. -/
theorem arithmetic_transfer {q : ℕ} (SS : Finset ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (_hαβ : α < β) (hβ : β < 1)
    (hSS : SS ∅ = 1) (_hSS1 : ∀ d, SS {d} = 1) (hMS : MeanSquareHL q SS β)
    (M : ℝ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
      ∀ k : ℕ, 1 ≤ k ∧ k ≤ q →
      ∀ a b : Fin k → ℝ, admissible M a b →
        |discreteRaw N H a b w -
          (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| ≤
          C * B * N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
  obtain ⟨A, hA, hred⟩ := reduced_transfer_power_error SS β hSS hMS M ε hM hε
  obtain ⟨D, hD, hcollision⟩ := collision_error_bound q M hM
  have hlog := (isLittleO_log_rpow_rpow_atTop ((q + 1 : ℕ) : ℝ) hε).bound (by norm_num : (0 : ℝ) < 1)
  have hscale := (tendsto_rpow_atTop (show 0 < 1 - β by linarith)).eventually_ge_atTop M
  refine ⟨A + 2 * D, by positivity, ?_⟩
  filter_upwards [hred, hlog, hscale, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hred hlog hscale hL
  have hN0 : 0 < N := by linarith [hred.1]
  have hN1 : 1 ≤ N := by linarith [hred.1]
  have hlogq : (Real.log N) ^ (q + 1) ≤ N ^ ε := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul, Real.rpow_natCast, Real.rpow_ofNat,
      abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log N) (q + 1))] using hlog
  have hsqrt : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN1
  have hpow : Real.sqrt N * N ^ ε = N ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
  intro H hlo hhi B w hw k hk a b hab
  have hH1 : (1 : ℝ) ≤ H := (Real.one_le_rpow hN1 hα.le).trans hlo
  have hH : 1 ≤ H := by exact_mod_cast hH1
  have hMH : M * (H : ℝ) ≤ N := by
    calc
      _ ≤ M * N ^ β := mul_le_mul_of_nonneg_left hhi (by linarith)
      _ ≤ N ^ (1 - β) * N ^ β := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; simp
  have hB : 0 ≤ B := hw.2.2.1
  have hfirst : Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) ≤
      N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
    calc
      _ ≤ Real.sqrt N * (H : ℝ) ^ k * N ^ ε := by
        gcongr
        · exact Nat.sub_le k 1
        · exact (pow_le_pow_right₀ hL (by omega : k + 1 ≤ q + 1)).trans hlogq
      _ = _ := by rw [← hpow]; ring
  have hsecond : (H : ℝ) ^ k * (Real.log N) ^ (k - 1) ≤
      N ^ (1 / 2 + ε) * (H : ℝ) ^ k := by
    calc
      _ ≤ (H : ℝ) ^ k * N ^ ε := by
        gcongr
        exact (pow_le_pow_right₀ hL (by omega : k - 1 ≤ q + 1)).trans hlogq
      _ ≤ Real.sqrt N * ((H : ℝ) ^ k * N ^ ε) := le_mul_of_one_le_left (by positivity) hsqrt
      _ = _ := by rw [← hpow]; ring
  have hc := hcollision N hred.1 H hH hMH B w hw k hk.1 hk.2 a b hab
  have hr := hred.2 H hH1 hhi B w hw k hk.2 a b hab
  calc
    _ ≤ |discreteRaw N H a b w -
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
          ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
            reducedAt (Real.log n) n d)| +
      |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
          ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
            reducedAt (Real.log n) n d) -
        (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b)| :=
      abs_sub_le _ _ _
    _ ≤ D * B * (Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) +
          (H : ℝ) ^ k * (Real.log N) ^ (k - 1)) +
        A * B * N ^ (1 / 2 + ε) * (H : ℝ) ^ k := add_le_add hc hr
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (show 0 ≤ D * B by positivity)
      nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
