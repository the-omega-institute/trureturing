/- GID: D5/S3/Analytic/Dilation/FiniteBoxDeterminantTrace
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/FiniteBoxDeterminantTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rational representation determinants give stable common-divisor traces. -/

import Mathlib
import D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.FiniteBoxDeterminantTrace

open scoped BigOperators Polynomial
open PowerSeries Matrix
open D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery

noncomputable section

-- The exponent vector of p^a q^b.
def exponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

-- The actual monomial p^m q^n.
def gradeMonomial (m n : ℕ) : BivariateSeries :=
  MvPowerSeries.X 0 ^ m * MvPowerSeries.X 1 ^ n

variable {G : Type*} [Group G]
variable {W : ℕ → ℕ → Type*}
  [∀ m n, AddCommGroup (W m n)] [∀ m n, Module ℚ (W m n)]
  [∀ m n, FiniteDimensional ℚ (W m n)]

-- A finite basis of each given rational representation space, with no positive-rank assumption.
def actionMatrix (ρ : ∀ m n, Representation ℚ G (W m n)) (g : G) (m n : ℕ) :
    Matrix (Fin (Module.finrank ℚ (W m n))) (Fin (Module.finrank ℚ (W m n))) ℚ :=
  LinearMap.toMatrix (Module.finBasis ℚ (W m n)) (Module.finBasis ℚ (W m n)) (ρ m n g)

-- The literal determinant of identity minus p^m q^n times the given action matrix.
def actionFactor (ρ : ∀ m n, Representation ℚ G (W m n)) (g : G) (m n : ℕ) :
    BivariateSeries :=
  Matrix.det (1 - gradeMonomial m n • (actionMatrix ρ g m n).map MvPowerSeries.C)

-- The finite positive box, including its literal determinant product.
def finiteBoxDet (ρ : ∀ m n, Representation ℚ G (W m n)) (g : G) (N : ℕ) :
    BivariateSeries :=
  ∏ mn ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N), actionFactor ρ g mn.1 mn.2

-- This same determinant product, supplied with its constant-coefficient-one proof.
def finiteBoxDenominator (ρ : ∀ m n, Representation ℚ G (W m n)) (g : G) (N : ℕ) :
    MonsterDenominator := ⟨finiteBoxDet ρ g N, by
  classical
  rw [finiteBoxDet, map_prod]
  apply Finset.prod_eq_one
  intro mn hmn
  have hm : 0 < mn.1 := by
    have := (Finset.mem_Icc.mp (Finset.mem_product.mp hmn).1).1
    omega
  rw [actionFactor, RingHom.map_det]
  have hmat : (MvPowerSeries.constantCoeff (σ := Fin 2) (R := ℚ)).mapMatrix
      (1 - gradeMonomial mn.1 mn.2 • (actionMatrix ρ g mn.1 mn.2).map MvPowerSeries.C) = 1 := by
    apply Matrix.ext
    intro i j
    simp [RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, gradeMonomial, hm.ne', Matrix.one_apply]
  rw [hmat, Matrix.det_one]⟩

/-- The finite-box common-divisor trace formula for arbitrary rational representations,
with the intrinsic determinant bridge and stability for every sufficiently large box. -/
theorem finite_box_trace_formula (ρ : ∀ m n, Representation ℚ G (W m n))
    (g : G) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∀ N, finiteBoxDet ρ g N =
      ∏ mn ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N),
        LinearMap.det (1 - gradeMonomial mn.1 mn.2 •
          (ρ mn.1 mn.2 g).baseChange BivariateSeries)) ∧
    (∀ N, max a b ≤ N →
      MvPowerSeries.coeff (exponent a b) (negativeFormalLog (finiteBoxDenominator ρ g N)) =
        ∑ k ∈ (Nat.gcd a b).divisors,
          LinearMap.trace ℚ (W (a / k) (b / k)) (ρ (a / k) (b / k) (g ^ k)) / (k : ℚ)) ∧
    (∀ N M, max a b ≤ N → max a b ≤ M →
      MvPowerSeries.coeff (exponent a b) (negativeFormalLog (finiteBoxDenominator ρ g N)) =
      MvPowerSeries.coeff (exponent a b) (negativeFormalLog (finiteBoxDenominator ρ g M))) := by
  classical
  have matrix_log {ι : Type} [Fintype ι] [DecidableEq ι]
      (A : Matrix ι ι ℚ) (k : ℕ) (hk : 0 < k) :
      coeff k (-logOf (A.charpolyRev : PowerSeries ℚ)) =
        Matrix.trace (A ^ k) / (k : ℚ) := by
    let S := PowerSeries ℚ
    let B : Matrix ι ι S := 1 - (X : S) • A.map C
    let E : Matrix ι ι S := .of fun i j => mk fun n => (A ^ n) i j
    -- Selected resolvent proof from Ralf Stephan, rwst/lean-code,
    -- 7cc2da3f9219e084ee656c096c2055922f4b267c, unsorted/gf-cyc.lean.
    -- Copyright (c) 2026 Ralf Stephan; Apache 2.0 source notice.
    -- Full source and root license notices: Library/Analytic/stephan2026resolvent.md.
    have coeff_E (i j : ι) (n : ℕ) : coeff n (E i j) = (A ^ n) i j := by
      simp [E, coeff_mk]
    have coeff_CAE (i j : ι) (n : ℕ) :
        coeff n ((A.map C * E) i j) = (A ^ (n + 1)) i j := by
      rw [mul_apply, map_sum]
      simp_rw [map_apply, coeff_C_mul, coeff_E]
      rw [← mul_apply, ← pow_succ']
    have coeff_one (i j : ι) (n : ℕ) :
        coeff n ((1 : Matrix ι ι S) i j) =
          if n = 0 then (1 : Matrix ι ι ℚ) i j else 0 := by
      have h1 : (1 : Matrix ι ι S) = (1 : Matrix ι ι ℚ).map C :=
        (Matrix.map_one C (map_zero _) (map_one _)).symm
      rw [h1, map_apply, coeff_C]
    have hBE : B * E = 1 := by
      dsimp [B]
      rw [sub_mul, one_mul, Matrix.smul_mul]
      ext i j n
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_E, coeff_one]
      obtain _ | n := n
      · simp [coeff_zero_eq_constantCoeff_apply]
      · rw [coeff_succ_X_mul, coeff_CAE, sub_self]
        simp
    -- End of selected attributed geometric inverse proof.
    have hdet : (A.charpolyRev : S) = det B := by
      rw [charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
      congr 1
      apply Matrix.ext
      intro i j
      simp [B, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Polynomial.coeToPowerSeries.ringHom_apply, Matrix.one_apply]
      split_ifs <;> simp [mul_comm]
    have hc : constantCoeff (A.charpolyRev : S) = 1 := by
      rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
    let P := A.charpolyRev.map (C : ℚ →+* S)
    let T : Matrix ι ι S[X] := B.map Polynomial.C
    let U : Matrix ι ι S := -(E * A.map C)
    have hT : T * (1 + (Polynomial.X : S[X]) • U.map Polynomial.C) =
        T - (Polynomial.X : S[X]) • (A.map C).map Polynomial.C := by
      rw [Matrix.mul_add, mul_one, Matrix.mul_smul, ← Matrix.map_mul]
      have hBU : B * U = -A.map C := by
        dsimp [U]
        rw [mul_neg, ← mul_assoc, hBE, one_mul]
      rw [hBU, Matrix.map_neg _ (map_neg Polynomial.C), smul_neg, ← sub_eq_add_neg]
    have hTaylor : Polynomial.taylor (X : S) P =
        det (T - (Polynomial.X : S[X]) • (A.map C).map Polynomial.C) := by
      change Polynomial.taylor (X : S)
        ((Polynomial.mapRingHom C) (det (1 - Polynomial.X • A.map Polynomial.C))) = _
      rw [RingHom.map_det]
      change (Polynomial.taylorAlgHom (X : S)) _ = _
      rw [AlgHom.map_det]
      congr 1
      apply Matrix.ext
      intro i j
      simp [T, B, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
      split_ifs <;> simp <;> ring
    have hJacobi : derivative ℚ (A.charpolyRev : S) = det B * trace U := by
      have ht := congrArg (fun p : S[X] => p.coeff 1) hTaylor
      rw [← hT, det_mul, show det T = Polynomial.C (det B) from
        (RingHom.map_det Polynomial.C B).symm, Polynomial.coeff_C_mul,
        Matrix.coeff_det_one_add_X_smul_one, Polynomial.taylor_coeff_one] at ht
      have he : P.derivative.eval (X : S) = derivative ℚ (A.charpolyRev : S) := by
        dsimp [P]
        rw [Polynomial.derivative_map, Polynomial.eval_map,
          Polynomial.eval₂_C_X_eq_coe, derivative_coe]
      rwa [he] at ht
    have hLogD : derivative ℚ (log ℚ) * (1 + X) = 1 := by
      rw [deriv_log]
      ext n
      rw [mul_add, mul_one, map_add]
      cases n with
      | zero => simp [coeff_zero_eq_constantCoeff_apply]
      | succ n =>
        rw [coeff_mk, mul_comm _ X, coeff_succ_X_mul, coeff_mk]
        simp [pow_succ]
    have hLog : derivative ℚ (logOf (A.charpolyRev : S)) * det B =
        derivative ℚ (A.charpolyRev : S) := by
      have hs : HasSubst ((A.charpolyRev : S) - 1) :=
        .of_constantCoeff_zero (by
          change constantCoeff ((A.charpolyRev : S) - 1) = 0
          simp [hc])
      have h := congrArg (subst ((A.charpolyRev : S) - 1)) hLogD
      have hm : (derivative ℚ (log ℚ)).subst ((A.charpolyRev : S) - 1) *
          (A.charpolyRev : S) = 1 := by
        simpa [subst_mul hs, subst_add hs, subst_X hs,
          ← coe_substAlgHom hs] using h
      rw [logOf_eq, derivative_subst hs]
      simp only [map_sub, derivative_one, sub_zero]
      rw [← hdet]
      calc
        _ = ((derivative ℚ (log ℚ)).subst ((A.charpolyRev : S) - 1) *
            (A.charpolyRev : S)) * derivative ℚ (A.charpolyRev : S) := by ring
        _ = _ := by rw [hm, one_mul]
    have hu : IsUnit (det B) := by
      rw [← hdet, isUnit_iff_constantCoeff, hc]
      exact isUnit_one
    have hd : derivative ℚ (-logOf (A.charpolyRev : S)) = trace (A.map C * E) := by
      apply hu.mul_right_cancel
      rw [map_neg, neg_mul, hLog, hJacobi]
      dsimp [U]
      rw [trace_neg, mul_neg, neg_neg, trace_mul_comm]
      ring
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hh := congrArg (coeff n) hd
    rw [coeff_derivative] at hh
    have ht : coeff n (trace (A.map C * E)) = trace (A ^ (n + 1)) := by
      simp only [Matrix.trace, diag_apply, map_sum, coeff_CAE]
    rw [ht] at hh
    apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n)).2
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hh
  have hactual (m n : ℕ) : actionFactor ρ g m n =
      LinearMap.det (1 - gradeMonomial m n • (ρ m n g).baseChange BivariateSeries) := by
    rw [← LinearMap.det_toMatrix
      (Algebra.TensorProduct.basis BivariateSeries (Module.finBasis ℚ (W m n)))]
    simp [actionFactor, actionMatrix, map_sub, map_smul,
      LinearMap.toMatrix_baseChange, ← MvPowerSeries.c_eq_algebraMap]
  refine ⟨fun N => Finset.prod_congr rfl (fun mn _ => hactual mn.1 mn.2), ?_⟩
  let R := MvPowerSeries (Fin 1) ℚ
  let ε := MvPowerSeries.finSuccEquiv ℚ 1
  let : IsAddTorsionFree R := .of_module_rat R
  have htransport (z : BivariateSeries) (hz : HasSubst z)
      (hε : constantCoeff (ε z) = 0) (f : PowerSeries ℚ) :
      ε (PowerSeries.subst z f) = (f.map (MvPowerSeries.C : ℚ →+* R)).subst (ε z) := by
    have hs : HasSubst (ε z) := .of_constantCoeff_zero hε
    apply PowerSeries.ext
    intro c
    apply MvPowerSeries.ext
    intro x
    rw [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_subst hz,
      PowerSeries.coeff_subst' hs]
    have hm := AddMonoidHom.map_finsum (MvPowerSeries.coeff x).toAddMonoidHom
      (PowerSeries.coeff_subst_finite' hs (f.map (MvPowerSeries.C : ℚ →+* R)) c)
    change (MvPowerSeries.coeff x) _ = _ at hm
    rw [hm]
    apply finsum_congr
    intro k
    change coeff k f • MvPowerSeries.coeff (Finsupp.cons c x) (z ^ k) =
      MvPowerSeries.coeff x (coeff k (f.map (MvPowerSeries.C : ℚ →+* R)) •
        coeff c (ε z ^ k))
    simp only [coeff_map, smul_eq_mul, MvPowerSeries.coeff_C_mul]
    rw [← MvPowerSeries.coeff_coeff_finSuccEquiv, map_pow]
  have hlogD : derivative R (log R) * (1 + X) = 1 := by
    rw [deriv_log]
    ext n
    rw [mul_add, mul_one, map_add]
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply]
    | succ n =>
      rw [coeff_mk, mul_comm _ X, coeff_succ_X_mul, coeff_mk]
      simp [pow_succ, map_pow, map_neg, map_one]
  have hlog_deriv (f : PowerSeries R) (hf : constantCoeff f = 1) :
      derivative R (logOf f) * f = derivative R f := by
    have hs : HasSubst (f - 1) := .of_constantCoeff_zero (by
      change constantCoeff (f - 1) = 0
      simp [hf])
    have h := congrArg (subst (f - 1)) hlogD
    have hm : (derivative R (log R)).subst (f - 1) * f = 1 := by
      simpa [subst_mul hs, subst_add hs, subst_X hs,
        ← coe_substAlgHom hs] using h
    rw [logOf_eq, derivative_subst hs]
    simp only [map_sub, derivative_one, sub_zero]
    calc
      _ = ((derivative R (log R)).subst (f - 1) * f) * derivative R f := by ring
      _ = _ := by rw [hm, one_mul]
  have hlog_mul (f h : PowerSeries R) (hf : constantCoeff f = 1)
      (hh : constantCoeff h = 1) : logOf (f * h) = logOf f + logOf h := by
    have hfh : constantCoeff (f * h) = 1 := by simp [hf, hh]
    apply derivative.ext
    · have hu : IsUnit (f * h) := by
        rw [isUnit_iff_constantCoeff, hfh]
        exact isUnit_one
      apply hu.mul_right_cancel
      rw [map_add, hlog_deriv _ hfh]
      have h1 := hlog_deriv f hf
      have h2 := hlog_deriv h hh
      calc
        derivative R (f * h) = derivative R f * h + f * derivative R h := by
          rw [Derivation.leibniz]; ring
        _ = (derivative R (logOf f) + derivative R (logOf h)) * (f * h) := by
          rw [← h1, ← h2]; ring
    · simp [constantCoeff_logOf, hf, hh, hfh]
  have hmonoε (m n : ℕ) : ε (gradeMonomial m n) =
      (X : PowerSeries R) ^ m * C (MvPowerSeries.X 0 ^ n) := by
    dsimp only [gradeMonomial]
    rw [map_mul, map_pow, map_pow, MvPowerSeries.finSuccEquiv_X_zero]
    have h1 : ε (MvPowerSeries.X (1 : Fin 2)) = C (MvPowerSeries.X (0 : Fin 1)) :=
      MvPowerSeries.finSuccEquiv_X_succ (0 : Fin 1)
    rw [h1, ← map_pow]
  have hccε (m n : ℕ) (hm : 0 < m) : constantCoeff (ε (actionFactor ρ g m n)) = 1 := by
    rw [actionFactor, AlgEquiv.map_det, RingHom.map_det]
    have hmat : (constantCoeff (R := R)).mapMatrix
        (ε.mapMatrix
          (1 - gradeMonomial m n • (actionMatrix ρ g m n).map MvPowerSeries.C)) = 1 := by
      apply Matrix.ext
      intro i j
      simp [RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, hmonoε, hm.ne', Matrix.one_apply]
    rw [hmat, Matrix.det_one]
  have hfactor_subst (m n : ℕ) (hm : 0 < m) :
      actionFactor ρ g m n =
        PowerSeries.subst (gradeMonomial m n)
          ((actionMatrix ρ g m n).charpolyRev : PowerSeries ℚ) := by
    have hz : HasSubst (gradeMonomial m n) := .of_constantCoeff_zero (by
      simp [gradeMonomial, hm.ne'])
    rw [PowerSeries.subst_coe hz, Matrix.charpolyRev, AlgHom.map_det, actionFactor]
    congr 1
    apply Matrix.ext
    intro i j
    simp [AlgHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, ← MvPowerSeries.c_eq_algebraMap]
    ring
  have hfactor_log (m n : ℕ) (hm : 0 < m) :
      ε.symm (-logOf (ε (actionFactor ρ g m n))) =
        PowerSeries.subst (gradeMonomial m n)
          (-logOf ((actionMatrix ρ g m n).charpolyRev : PowerSeries ℚ)) := by
    let f : PowerSeries ℚ := (actionMatrix ρ g m n).charpolyRev
    have hf : constantCoeff f = 1 := by
      simp [f, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
    have hs : HasSubst (f - 1) := .of_constantCoeff_zero (by
      change constantCoeff (f - 1) = 0
      simp [hf])
    have hz : HasSubst (gradeMonomial m n) := .of_constantCoeff_zero (by
      simp [gradeMonomial, hm.ne'])
    have hd : PowerSeries.subst (gradeMonomial m n) f = actionFactor ρ g m n :=
      (hfactor_subst m n hm).symm
    have hdε : constantCoeff (ε (actionFactor ρ g m n - 1)) = 0 := by
      simp [hccε m n hm]
    have hdiff : PowerSeries.subst (gradeMonomial m n) (f - 1) =
        actionFactor ρ g m n - 1 := by
      rw [subst_sub hz, hd, ← coe_substAlgHom hz, map_one]
    have hs2 : HasSubst (actionFactor ρ g m n - 1) :=
      .of_constantCoeff_zero (by
        rw [← hdiff]
        exact PowerSeries.constantCoeff_subst_eq_zero
          (by simp [gradeMonomial, hm.ne']) _ (by simp [hf]))
    have htr := htransport (actionFactor ρ g m n - 1) hs2 hdε (log ℚ)
    have hsub : PowerSeries.subst (gradeMonomial m n) (-logOf f) =
        -PowerSeries.subst (actionFactor ρ g m n - 1) (log ℚ) := by
      rw [← coe_substAlgHom hz, map_neg, coe_substAlgHom]
      change -PowerSeries.subst (gradeMonomial m n) (PowerSeries.subst (f - 1) (log ℚ)) = _
      rw [subst_comp_subst_apply hs hz, hdiff]
    change ε.symm (-logOf (ε (actionFactor ρ g m n))) =
      PowerSeries.subst (gradeMonomial m n) (-logOf f)
    rw [hsub]
    apply ε.injective
    rw [ε.apply_symm_apply, map_neg, htr, map_log]
    simp only [logOf_eq, map_sub, map_one]
  have hab : Nat.gcd a b ≠ 0 := by
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b ha)
  have hcoef_factor (m n : ℕ) (hm : 0 < m) :
      MvPowerSeries.coeff (exponent a b) (ε.symm (-logOf (ε (actionFactor ρ g m n)))) =
        ∑ k ∈ (Nat.gcd a b).divisors,
          if (a / k, b / k) = (m, n) then
            LinearMap.trace ℚ (W m n) (ρ m n (g ^ k)) / (k : ℚ) else 0 := by
    rw [hfactor_log m n hm]
    have hz : HasSubst (gradeMonomial m n) := .of_constantCoeff_zero (by
      simp [gradeMonomial, hm.ne'])
    have hpow (k : ℕ) : gradeMonomial m n ^ k =
        MvPowerSeries.monomial (exponent (k * m) (k * n)) (1 : ℚ) := by
      dsimp only [gradeMonomial]
      rw [mul_pow, ← pow_mul, ← pow_mul, MvPowerSeries.X_pow_eq,
        MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial]
      simp only [one_mul, exponent, Nat.mul_comm]
    rw [PowerSeries.coeff_subst hz]
    have hexp (k : ℕ) : exponent a b = exponent (k * m) (k * n) ↔
        a = k * m ∧ b = k * n := by
      constructor
      · intro h
        constructor
        · simpa [exponent] using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
        · simpa [exponent] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
      · rintro ⟨rfl, rfl⟩; rfl
    have hsupport : Function.support (fun k =>
        coeff k (-logOf ((actionMatrix ρ g m n).charpolyRev : PowerSeries ℚ)) •
          MvPowerSeries.coeff (exponent a b) (gradeMonomial m n ^ k)) ⊆
        ↑(Nat.gcd a b).divisors := by
      intro k hk
      have he : exponent a b = exponent (k * m) (k * n) := by
        by_contra he
        apply hk
        simp [hpow, MvPowerSeries.coeff_monomial, he]
      obtain ⟨he1, he2⟩ := (hexp k).mp he
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd ⟨m, he1⟩ ⟨n, he2⟩, hab⟩
    rw [finsum_eq_sum_of_support_subset _ hsupport]
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hk) (Nat.pos_of_ne_zero hab)
    have hka : k ∣ a := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hk)).1
    have hkb : k ∣ b := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hk)).2
    have he : exponent a b = exponent (k * m) (k * n) ↔ (a / k, b / k) = (m, n) := by
      rw [hexp, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        simp [hkpos.ne']
      · rintro ⟨he1, he2⟩
        rw [← he1, ← he2, Nat.mul_div_cancel' hka, Nat.mul_div_cancel' hkb]
        exact ⟨rfl, rfl⟩
    rw [hpow, MvPowerSeries.coeff_monomial]
    by_cases hpair : (a / k, b / k) = (m, n)
    · rw [if_pos (he.mpr hpair), if_pos hpair, smul_eq_mul, mul_one,
        matrix_log _ _ hkpos,
        actionMatrix, LinearMap.toMatrix_pow]
      rw [← map_pow (ρ m n), ← LinearMap.trace_eq_matrix_trace ℚ (Module.finBasis ℚ (W m n))]
    · rw [if_neg (he.not.mpr hpair), if_neg hpair, smul_zero]
  have hformula (N : ℕ) (hN : max a b ≤ N) :
      MvPowerSeries.coeff (exponent a b) (negativeFormalLog (finiteBoxDenominator ρ g N)) =
        ∑ k ∈ (Nat.gcd a b).divisors,
          LinearMap.trace ℚ (W (a / k) (b / k)) (ρ (a / k) (b / k) (g ^ k)) / (k : ℚ) := by
    let box := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
    have hbox (mn : ℕ × ℕ) (h : mn ∈ box) : 0 < mn.1 ∧ 0 < mn.2 := by
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp h
      exact ⟨by have := (Finset.mem_Icc.mp h1).1; omega,
        by have := (Finset.mem_Icc.mp h2).1; omega⟩
    have hccprod (s : Finset (ℕ × ℕ)) (hs : s ⊆ box) :
        constantCoeff (∏ mn ∈ s, ε (actionFactor ρ g mn.1 mn.2)) = 1 := by
      rw [map_prod]
      apply Finset.prod_eq_one
      intro mn hmn
      exact hccε mn.1 mn.2 (hbox mn (hs hmn)).1
    have hlogprod (s : Finset (ℕ × ℕ)) (hs : s ⊆ box) :
        -logOf (∏ mn ∈ s, ε (actionFactor ρ g mn.1 mn.2)) =
          ∑ mn ∈ s, -logOf (ε (actionFactor ρ g mn.1 mn.2)) := by
      induction s using Finset.induction_on with
      | empty => simp [logOf_eq, subst_zero_of_constantCoeff_zero]
      | @insert mn s hnot ih =>
        have hs' : s ⊆ box := fun x hx => hs (Finset.mem_insert_of_mem hx)
        have hmn : mn ∈ box := hs (Finset.mem_insert_self _ _)
        rw [Finset.prod_insert hnot, Finset.sum_insert hnot,
          hlog_mul _ _ (hccε _ _ (hbox _ hmn).1) (hccprod s hs'), neg_add, ih hs']
    have hccN : constantCoeff (ε (finiteBoxDet ρ g N)) = 1 := by
      simpa [finiteBoxDet, box, map_prod] using hccprod box (fun _ h => h)
    have hnegative : negativeFormalLog (finiteBoxDenominator ρ g N) =
        ∑ mn ∈ box, ε.symm (-logOf (ε (actionFactor ρ g mn.1 mn.2))) := by
      apply ε.injective
      rw [negativeFormalLog, MvPowerSeries.substAlgHom_apply, map_neg]
      change -ε (PowerSeries.subst (finiteBoxDet ρ g N - 1) (log ℚ)) = _
      have hccB : MvPowerSeries.constantCoeff (finiteBoxDet ρ g N) = 1 :=
        (finiteBoxDenominator ρ g N).2
      rw [htransport _ (.of_constantCoeff_zero (by simp [hccB]))
        (by simp [hccN]), map_log]
      simp only [map_sub, map_one, ← logOf_eq]
      rw [finiteBoxDet, map_prod, hlogprod box (fun _ h => h), map_sum]
      apply Finset.sum_congr rfl
      intro mn _
      rw [ε.apply_symm_apply]
    rw [hnegative, map_sum]
    have hsum :
        (∑ mn ∈ box, MvPowerSeries.coeff (exponent a b)
          (ε.symm (-logOf (ε (actionFactor ρ g mn.1 mn.2))))) =
        ∑ mn ∈ box, ∑ k ∈ (Nat.gcd a b).divisors,
          if (a / k, b / k) = (mn.1, mn.2) then
            LinearMap.trace ℚ (W mn.1 mn.2) (ρ mn.1 mn.2 (g ^ k)) / (k : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro mn hmn
      exact hcoef_factor mn.1 mn.2 (hbox mn hmn).1
    rw [hsum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k :=
      Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hk) (Nat.pos_of_ne_zero hab)
    have hka : k ∣ a := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hk)).1
    have hkb : k ∣ b := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hk)).2
    have hquot : (a / k, b / k) ∈ box := by
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        exact ⟨Nat.div_pos (Nat.le_of_dvd ha hka) hkpos,
          (Nat.div_le_self a k).trans ((le_max_left a b).trans hN)⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨Nat.div_pos (Nat.le_of_dvd hb hkb) hkpos,
          (Nat.div_le_self b k).trans ((le_max_right a b).trans hN)⟩
    rw [Finset.sum_eq_single (a / k, b / k)]
    · simp
    · intro mn _ hne
      simp [Ne.symm hne]
    · exact fun h => (h hquot).elim
  exact ⟨hformula, fun N M hN hM => (hformula N hN).trans (hformula M hM).symm⟩

#print axioms finite_box_trace_formula

end
end D5.S3.Analytic.Dilation.FiniteBoxDeterminantTrace
