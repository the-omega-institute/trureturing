/- GID: D5/S3/Quantum/Measurement/ExactFailureRadius
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ExactFailureRadius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual qubit survival and the extremal recorded-instrument distance. -/

import D5.S3.Quantum.Measurement.ArbitraryDarkReferenceLowerBound
import D5.S3.Quantum.Measurement.TwoRecordResetCalibration
import D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.ExactFailureRadius

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open D5.S3.Quantum.Measurement.TwoRecordResetCalibration
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
open D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
open D5.S3.Quantum.Measurement.ArbitraryDarkReferenceLowerBound
open Matrix Filter Topology
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

private abbrev Q := Fin 2
private abbrev O := Bool × Q
private abbrev KIndex := O × Q

/-- Positive limiting probability of never clicking for an actual initial state. -/
def Fails (I : TwoRecordInstrument Q Q) : Prop :=
  ∃ rho : DensityState Q, ∃ s : ℝ, 0 < s ∧
    Tendsto (fun n => (Matrix.trace (I.noClick^[n] rho.1)).re) atTop (𝓝 s)

/-- The proposed extremal half-diamond distance. -/
def radius : ℝ := Real.sqrt ((11 + 5 * Real.sqrt 5) / 32)

private theorem actual_kraus (I : TwoRecordInstrument Q Q) :
    ∃ (N C : KIndex → Matrix Q Q ℂ),
      (∑ k, (N k)ᴴ * N k) + (∑ k, (C k)ᴴ * C k) = 1 ∧
      (∀ X : Matrix Q Q ℂ, CStarMatrix.ofMatrix.symm
        (I.noClick (CStarMatrix.ofMatrix X)) = ∑ k, N k * X * (N k)ᴴ) ∧
      (∀ X : Matrix Q Q ℂ, CStarMatrix.ofMatrix.symm
        (I.click (CStarMatrix.ofMatrix X)) = ∑ k, C k * X * (C k)ᴴ) := by
  obtain ⟨K, hcomp, hK⟩ := channel_kraus_stinespring.1 I.channel
  let N : KIndex → Matrix Q Q ℂ := fun k i j => K k (false, i) j
  let C : KIndex → Matrix Q Q ℂ := fun k i j => K k (true, i) j
  have hrecord := (two_record_reset_calibration.{0, 0} I).1
  refine ⟨N, C, ?_, ?_, ?_⟩
  · ext i j
    have h := congrArg (fun M : Matrix Q Q ℂ => M i j) hcomp
    change (∑ k, ∑ l : Q, star (N k l i)*N k l j) +
      (∑ k, ∑ l : Q, star (C k l i)*C k l j) = (1 : Matrix Q Q ℂ) i j
    change (∑ k, ∑ p : O, star (K k p i)*K k p j) =
      (1 : Matrix Q Q ℂ) i j at h
    simp only [N, C, Fintype.sum_prod_type, Fintype.sum_bool,
      Finset.sum_add_distrib] at h ⊢
    convert h using 1 <;> abel
  · intro X
    ext i j
    have h := congrArg (fun M : Matrix O O ℂ => M (false, i) (false, j)) (hK X)
    rw [hrecord] at h
    change I.noClick (CStarMatrix.ofMatrix X) i j =
      (∑ k, K k * X * (K k)ᴴ) (false, i) (false, j) at h
    exact h
  · intro X
    ext i j
    have h := congrArg (fun M : Matrix O O ℂ => M (true, i) (true, j)) (hK X)
    rw [hrecord] at h
    change I.click (CStarMatrix.ofMatrix X) i j =
      (∑ k, K k * X * (K k)ᴴ) (true, i) (true, j) at h
    exact h

private def primal (N : KIndex → Matrix Q Q ℂ) (X : Matrix Q Q ℂ) :
    Matrix Q Q ℂ := ∑ k, N k * X * (N k)ᴴ

private theorem primal_dual_trace (N : KIndex → Matrix Q Q ℂ)
    (X Y : Matrix Q Q ℂ) :
    Matrix.trace (primal N X * Y) = Matrix.trace (X * noClickDual N Y) := by
  simp only [primal, noClickDual, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = Matrix.trace ((N k) * (X * ((N k)ᴴ * Y))) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((X * ((N k)ᴴ * Y)) * N k) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem survival_trace (I : TwoRecordInstrument Q Q)
    (N : KIndex → Matrix Q Q ℂ)
    (hN : ∀ X : Matrix Q Q ℂ, CStarMatrix.ofMatrix.symm
      (I.noClick (CStarMatrix.ofMatrix X)) = primal N X)
    (rho : CStarMatrix Q Q ℂ) (n : ℕ) :
    Matrix.trace (I.noClick^[n] rho) =
      Matrix.trace (CStarMatrix.ofMatrix.symm rho * survival N n) := by
  have hiter (X : CStarMatrix Q Q ℂ) (n : ℕ) (Y : Matrix Q Q ℂ) :
      Matrix.trace (CStarMatrix.ofMatrix.symm (I.noClick^[n] X) * Y) =
        Matrix.trace (CStarMatrix.ofMatrix.symm X * (noClickDual N)^[n] Y) := by
    induction n generalizing X Y with
    | zero => rfl
    | succ n ih =>
      have hNX (Z : CStarMatrix Q Q ℂ) :
          CStarMatrix.ofMatrix.symm (I.noClick Z) =
            primal N (CStarMatrix.ofMatrix.symm Z) := by
        simpa only [Equiv.apply_symm_apply] using hN (CStarMatrix.ofMatrix.symm Z)
      rw [Function.iterate_succ_apply', hNX, primal_dual_trace, ih,
        Function.iterate_succ_apply]
  have hs : ∀ n, survival N n = (noClickDual N)^[n] 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [survival, ih, Function.iterate_succ_apply']
  change Matrix.trace (CStarMatrix.ofMatrix.symm (I.noClick^[n] rho)) = _
  simpa only [hs, Matrix.mul_one] using hiter rho n 1

private theorem failing_dark (I : TwoRecordInstrument Q Q)
    (N C : KIndex → Matrix Q Q ℂ)
    (hcomp : (∑ k, (N k)ᴴ * N k) + (∑ k, (C k)ᴴ * C k) = 1)
    (hN : ∀ X : Matrix Q Q ℂ, CStarMatrix.ofMatrix.symm
      (I.noClick (CStarMatrix.ofMatrix X)) = primal N X)
    (hf : Fails I) : darkLayer N C 2 ≠ ⊥ := by
  obtain ⟨rho, s, hs, hlim⟩ := hf
  obtain ⟨F, hF, -, -, -, -, -, htrace⟩ :=
    survival_tendsto_maximal_fixed_effect N C hcomp
  have hlim' := Complex.continuous_re.continuousAt.tendsto.comp
    (htrace (CStarMatrix.ofMatrix.symm rho.1))
  have hsF : (Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * F)).re = s := by
    change Tendsto (fun n => (Matrix.trace
      (CStarMatrix.ofMatrix.symm rho.1 * survival N n)).re) atTop
        (𝓝 (Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * F)).re) at hlim'
    apply tendsto_nhds_unique hlim' _
    simpa only [← survival_trace I N hN rho.1] using hlim
  intro hbot
  have hall : ∀ X : Matrix Q Q ℂ, X.PosSemidef → X.trace = 1 → (X*F).trace = 0 :=
    ((no_dark_direction_tfae N C hcomp F hF).out 0 3 (by rfl) (by rfl)).mp hbot
  have hz := hall (CStarMatrix.ofMatrix.symm rho.1)
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)) rho.2.2
  have : s = 0 := by simpa only [hz, Complex.zero_re] using hsF.symm
  linarith

private theorem unit_in_subspace (D : Submodule ℂ (Q → ℂ)) (hD : D ≠ ⊥) :
    ∃ psi : Q → ℂ, psi ∈ D ∧
      Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1 := by
  obtain ⟨v, hv, hv0⟩ := D.ne_bot_iff.mp hD
  let t := Real.sqrt (Complex.normSq (v 0) + Complex.normSq (v 1))
  have hp : 0 < Complex.normSq (v 0) + Complex.normSq (v 1) := by
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    by_contra h
    have hz : Complex.normSq (v 0) + Complex.normSq (v 1) = 0 := by linarith
    apply hv0
    ext i
    fin_cases i
    · change v 0 = 0
      exact Complex.normSq_eq_zero.mp (by linarith)
    · change v 1 = 0
      exact Complex.normSq_eq_zero.mp (by linarith)
  have ht : 0 < t := Real.sqrt_pos.mpr hp
  have hts : t ^ 2 = Complex.normSq (v 0) + Complex.normSq (v 1) :=
    Real.sq_sqrt hp.le
  refine ⟨fun i => v i / (t : ℂ), ?_, ?_⟩
  · convert D.smul_mem ((t : ℂ)⁻¹) hv using 1
    ext i
    simp [div_eq_mul_inv, mul_comm]
  · simp only [Complex.normSq_div, Complex.normSq_ofReal, ← add_div,
      ← sq, hts]
    exact div_self hp.ne'

private theorem dark_qubit_split (N C : KIndex → Matrix Q Q ℂ)
    (hcomp : (∑ k, (N k)ᴴ * N k) + (∑ k, (C k)ᴴ * C k) = 1)
    (hD : darkLayer N C 2 ≠ ⊥) :
    (∀ k, C k = 0) ∨
      ∃ psi : Q → ℂ,
        Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1 ∧
        primal N (Matrix.vecMulVec psi (star psi)) =
          Matrix.vecMulVec psi (star psi) := by
  let D := darkLayer N C 2
  obtain ⟨-, -, hkill, hstable, -⟩ := darkLayer_closure N C hcomp
  by_cases htop : D = ⊤
  · left
    intro k
    ext i j
    have h := hkill k (Pi.single j 1) (by change Pi.single j 1 ∈ D; rw [htop]; trivial)
    simpa [Matrix.mulVec_single] using congrFun h i
  · right
    obtain ⟨psi, hpsi, hu⟩ := unit_in_subspace D hD
    have hpsi0 : psi ≠ 0 := by intro h; simp [h] at hu
    have hspan : Submodule.span ℂ {psi} = D := by
      have hle : Submodule.span ℂ {psi} ≤ D :=
        (Submodule.span_singleton_le_iff_mem psi D).mpr hpsi
      have hdim : Module.finrank ℂ D < 2 := by
        simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
          Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
          Submodule.finrank_lt htop
      have hdimS : Module.finrank ℂ (Submodule.span ℂ {psi}) = 1 :=
        finrank_span_singleton hpsi0
      apply Submodule.eq_of_le_of_finrank_eq hle
      have hdimle := Submodule.finrank_mono hle
      rw [hdimS] at hdimle ⊢
      exact Nat.le_antisymm (Nat.le_of_lt_succ hdim) hdimle |>.symm
    have hex (k : KIndex) : ∃ c : ℂ, c • psi = N k *ᵥ psi := by
      apply Submodule.mem_span_singleton.mp
      rw [hspan]
      exact hstable k psi hpsi
    choose c hc using hex
    have hz (k : KIndex) : C k *ᵥ psi = 0 := hkill k psi hpsi
    have hunit : star psi ⬝ᵥ psi = 1 := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hu,
        Complex.ofReal_one]
    have hmass : (∑ k, star (c k) * c k) = 1 := by
      have h := congrArg (fun M : Matrix Q Q ℂ => star psi ⬝ᵥ (M *ᵥ psi)) hcomp
      have hnorm (A : Matrix Q Q ℂ) :
          star psi ⬝ᵥ ((Aᴴ * A) *ᵥ psi) = star (A *ᵥ psi) ⬝ᵥ (A *ᵥ psi) := by
        rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_vecMul]
      simp only [Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add,
        dotProduct_sum, Matrix.one_mulVec, hunit] at h
      simp only [hnorm, hz, star_zero, dotProduct_zero, Finset.sum_const_zero,
        add_zero, ← hc] at h
      have hcunit (z : ℂ) : star (z • psi) ⬝ᵥ (z • psi) = star z*z := by
        calc
          _ = star z*z*(star psi ⬝ᵥ psi) := by
            simp only [dotProduct, Pi.smul_apply, Pi.star_apply, star_mul, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [hunit, mul_one]
      simpa only [hcunit] using h
    refine ⟨psi, hu, ?_⟩
    ext i j
    simp only [primal, Matrix.sum_apply, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, ← Matrix.star_mulVec, ← hc,
      Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul]
    calc
      (∑ k, c k * psi i * (star (psi j) * star (c k))) =
          (∑ k, star (c k) * c k) * (psi i * star (psi j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hmass, one_mul]

/-- Every failing actual qubit instrument either never clicks on any input or
has a normalized pure no-click fixed state. No original Kraus representation is assumed. -/
theorem failing_qubit_dark_split (I : TwoRecordInstrument (Fin 2) (Fin 2))
    (hf : Fails I) :
    (∀ X : CStarMatrix (Fin 2) (Fin 2) ℂ, I.click X = 0) ∨
      ∃ psi : Fin 2 → ℂ,
        Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1 ∧
        I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) =
          CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)) := by
  obtain ⟨N, C, hcomp, hN, hC⟩ := actual_kraus I
  rcases dark_qubit_split N C hcomp (failing_dark I N C hcomp hN hf) with hz | hp
  · left
    intro X
    ext i j
    have h := congrArg (fun M : Matrix Q Q ℂ => M i j) (hC (CStarMatrix.ofMatrix.symm X))
    simpa [hz] using h
  · right
    obtain ⟨psi, hu, hp⟩ := hp
    refine ⟨psi, hu, ?_⟩
    apply CStarMatrix.ofMatrix.symm.injective
    exact (hN _).trans hp

private theorem unitary_test_le_diamond (F G : QuantumChannel Q O)
    (psi : Q → ℂ) (hu : star psi ⬝ᵥ psi = 1)
    (U : Matrix O O ℂ) (hU : U ∈ Matrix.unitaryGroup O ℂ) :
    (Matrix.trace (U * (CStarMatrix.ofMatrix.symm (F.mapState (pureState psi hu)).1 -
      CStarMatrix.ofMatrix.symm (G.mapState (pureState psi hu)).1))).re ≤
      diamondDistance F G := by
  let v : Fin 1 × Q → ℂ := fun p => psi p.2
  have hv : star v ⬝ᵥ v = 1 := by
    simpa [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_one, v] using hu
  let rho := pureState v hv
  let V : Matrix (Fin 1 × O) (Fin 1 × O) ℂ := fun p q => U p.2 q.2
  have hV : V ∈ Matrix.unitaryGroup (Fin 1 × O) ℂ := by
    change star V * V = 1 ∧ V * star V = 1
    have h := hU
    change star U * U = 1 ∧ U * star U = 1 at h
    constructor
    · ext p q
      have he := congrArg (fun M : Matrix O O ℂ => M p.2 q.2) h.1
      change (∑ x, star (V x p)*V x q) = if p = q then 1 else 0
      change (∑ x, star (U x p.2)*U x q.2) = if p.2 = q.2 then 1 else 0 at he
      have heq : p = q ↔ p.2 = q.2 := by
        constructor
        · exact fun h => congrArg Prod.snd h
        · intro h; exact Prod.ext (Subsingleton.elim _ _) h
      simpa only [V, Fintype.sum_prod_type, Fin.sum_univ_one, heq] using he
    · ext p q
      have he := congrArg (fun M : Matrix O O ℂ => M p.2 q.2) h.2
      change (∑ x, V p x*star (V q x)) = if p = q then 1 else 0
      change (∑ x, U p.2 x*star (U q.2 x)) = if p.2 = q.2 then 1 else 0 at he
      have heq : p = q ↔ p.2 = q.2 := by
        constructor
        · exact fun h => congrArg Prod.snd h
        · intro h; exact Prod.ext (Subsingleton.elim _ _) h
      simpa only [V, Fintype.sum_prod_type, Fin.sum_univ_one, heq] using he
  have htest := (traceNorm_eq_max_re_tr_U
    (CStarMatrix.ofMatrix.symm (referenceState F rho).1 -
      CStarMatrix.ofMatrix.symm (referenceState G rho).1)).2 ⟨⟨V, hV⟩, rfl⟩
  have hentry (H : QuantumChannel Q O) (p q : Fin 1 × O) :
      (referenceState H rho).1 p q =
        H.toCompletelyPositiveMap (pureState psi hu).1 p.2 q.2 := rfl
  have hval : (Matrix.trace (V *
      (CStarMatrix.ofMatrix.symm (referenceState F rho).1 -
        CStarMatrix.ofMatrix.symm (referenceState G rho).1))).re =
      (Matrix.trace (U * (CStarMatrix.ofMatrix.symm (F.mapState (pureState psi hu)).1 -
        CStarMatrix.ofMatrix.symm (G.mapState (pureState psi hu)).1))).re := by
    change (∑ p : Fin 1 × O, ∑ q : Fin 1 × O, V p q *
      ((referenceState F rho).1 q p - (referenceState G rho).1 q p)).re =
      (∑ p : O, ∑ q : O, U p q *
        (F.toCompletelyPositiveMap (pureState psi hu).1 q p -
          G.toCompletelyPositiveMap (pureState psi hu).1 q p)).re
    simp only [hentry, V, Fintype.sum_prod_type, Fin.sum_univ_one]
  rw [hval] at htest
  have hbdd : BddAbove ({0} ∪ {t : ℝ | ∃ n : ℕ, ∃ sigma : DensityState (Fin n × Q),
      t = referenceError F G sigma}) := by
    refine ⟨2, ?_⟩
    rintro t (ht | ⟨n, sigma, rfl⟩)
    · simpa only [Set.mem_singleton_iff] using ht.le.trans (by norm_num)
    · have h := traceDistance_le_one (referenceState F sigma) (referenceState G sigma)
      change referenceError F G sigma/2 ≤ 1 at h
      linarith
  exact htest.trans (le_csSup hbdd (Or.inr ⟨1, rho, rfl⟩))

set_option maxHeartbeats 2400000 in
private theorem dark_input_test (I : TwoRecordInstrument Q Q) (psi : Q → ℂ)
    (hu : Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1)
    (hf : I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) =
      CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) :
    (Complex.normSq (psi 0) + Real.sqrt
      ((Complex.normSq (psi 0))^2 + 4*(1-Complex.normSq (psi 0))^2))/2 ≤
        diamondDistance I.channel nominalInstrument/2 := by
  let a := Complex.normSq (psi 0)
  let b := Complex.normSq (psi 1)
  let t := Real.sqrt (a^2+4*b^2)
  have ha : 0 ≤ a := Complex.normSq_nonneg _
  have hb : 0 ≤ b := Complex.normSq_nonneg _
  have hab : a+b = 1 := hu
  have hpos : 0 < a^2+4*b^2 := by nlinarith [sq_nonneg (a-b)]
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hts : t^2 = a^2+4*b^2 := Real.sq_sqrt hpos.le
  have hgram : (3*a-2)^2+4*a*b = t^2 := by nlinarith
  have hgramC : (3*(a : ℂ)-2)^2+4*(a : ℂ)*(b : ℂ) = (t : ℂ)^2 := by
    exact_mod_cast hgram
  have hpa : psi 0*star (psi 0) = (a : ℂ) := by
    simpa only [a, Complex.star_def] using Complex.mul_conj (psi 0)
  have hpb : psi 1*star (psi 1) = (b : ℂ) := by
    simpa only [b, Complex.star_def] using Complex.mul_conj (psi 1)
  simp only [Complex.star_def] at hpa hpb
  let W : Matrix Q Q ℂ :=
    !![(3*(a : ℂ)-2)/(t : ℂ), 2*psi 0*star (psi 1)/(t : ℂ);
      2*psi 1*star (psi 0)/(t : ℂ), (2-3*(a : ℂ))/(t : ℂ)]
  have hWstar : Wᴴ = W := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [W, Matrix.conjTranspose_apply, star_div, star_mul, star_sub] <;> ring
  have hWW : W*W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [W, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      field_simp [htne]
    · linear_combination hgramC + 4*(psi 1*(starRingEnd ℂ) (psi 1))*hpa + 4*(a : ℂ)*hpb
    · ring
    · ring
    · linear_combination hgramC + 4*(psi 1*(starRingEnd ℂ) (psi 1))*hpa + 4*(a : ℂ)*hpb
  let U : Matrix O O ℂ := fun p q =>
    if p.1 = q.1 then if p.1 then -(1 : Matrix Q Q ℂ) p.2 q.2
      else W p.2 q.2 else 0
  have hUstar : Uᴴ = U := by
    ext ⟨s, i⟩ ⟨r, j⟩
    change star (U (r, j) (s, i)) = U (s, i) (r, j)
    cases s <;> cases r <;>
      simp only [U, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
        star_zero, star_neg, Matrix.one_apply, apply_ite, star_one]
    · exact congrArg (fun M : Matrix Q Q ℂ => M i j) hWstar
    · by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]
  have hUU : U*U = 1 := by
    ext ⟨s, i⟩ ⟨r, j⟩
    change (∑ p : O, U (s, i) p * U p (r, j)) =
      if (s, i) = (r, j) then 1 else 0
    cases s <;> cases r <;>
      simp [U, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using
      congrArg (fun M : Matrix Q Q ℂ => M i j) hWW
  have hU : U ∈ Matrix.unitaryGroup O ℂ := by
    change star U*U = 1 ∧ U*star U = 1
    simpa only [Matrix.star_eq_conjTranspose, hUstar] using And.intro hUU hUU
  have hunit : star psi ⬝ᵥ psi = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hu, Complex.ofReal_one]
  have hclick : Matrix.trace (I.click (pureState psi hunit).1) = 0 := by
    have h := I.trace_sum (pureState psi hunit).1
    rw [(pureState psi hunit).2.2] at h
    change Matrix.trace (I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)))) +
      Matrix.trace (I.click (pureState psi hunit).1) = 1 at h
    rw [hf] at h
    have hp : Matrix.trace (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) = 1 :=
      (pureState psi hunit).2.2
    rw [hp] at h
    linear_combination h
  have hval : Matrix.trace (U *
      (CStarMatrix.ofMatrix.symm (I.channel.mapState (pureState psi hunit)).1 -
        CStarMatrix.ofMatrix.symm (nominalInstrument.mapState (pureState psi hunit)).1)) =
      ((a+t : ℝ) : ℂ) := by
    have hrecord := (two_record_reset_calibration.{0, 0} I).1 (pureState psi hunit).1
    have hnom := nominal_instrument_apply (Matrix.vecMulVec psi (star psi))
    change Matrix.trace (U * (CStarMatrix.ofMatrix.symm
      (I.channel.toCompletelyPositiveMap (pureState psi hunit).1) -
      CStarMatrix.ofMatrix.symm (nominalInstrument.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)))))) = _
    rw [hrecord, hnom]
    change Matrix.trace (U * (CStarMatrix.ofMatrix.symm (recordBlocks
      (I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))))
      (I.click (pureState psi hunit).1)) - _)) = _
    rw [hf]
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at hclick
    change I.click (pureState psi hunit).1 0 0 + I.click (pureState psi hunit).1 1 1 = 0
      at hclick
    change (∑ p : O, ∑ q : O, U p q *
      ((CStarMatrix.ofMatrix.symm (recordBlocks
        (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)))
        (I.click (pureState psi hunit).1))) q p -
        (if q = (false, 0) ∧ p = (false, 0) then psi 1*star (psi 1)
          else if q = (true, 0) ∧ p = (true, 0) then psi 0*star (psi 0) else 0))) = _
    have hentry (p q : O) : (CStarMatrix.ofMatrix.symm (recordBlocks
        (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)))
        (I.click (pureState psi hunit).1))) p q =
        if p.1 = q.1 then if p.1 then I.click (pureState psi hunit).1 p.2 q.2
          else psi p.2*star (psi q.2) else 0 := rfl
    simp only [hentry]
    simp [Fintype.sum_prod_type, Fintype.sum_bool,
      Fin.sum_univ_two, U, W, recordBlocks, Matrix.one_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.ofReal_add]
    field_simp [htne]
    have htC : (t : ℂ)^2 = (a : ℂ)^2+4*(b : ℂ)^2 := by exact_mod_cast hts
    have habC : (a : ℂ)+(b : ℂ) = 1 := by exact_mod_cast hab
    try simp only [Complex.star_def] at ⊢
    linear_combination -htC + (3*(a : ℂ)-2+(t : ℂ))*hpa +
      (4-6*(a : ℂ))*hpb + 4*(psi 1*(starRingEnd ℂ) (psi 1))*hpa +
      4*(a : ℂ)*hpb - (t : ℂ)*hclick -
      (-2*(a : ℂ)+4*(b : ℂ))*habC
  have h := unitary_test_le_diamond I.channel nominalInstrument psi hunit U hU
  rw [hval, Complex.ofReal_re] at h
  change (a+Real.sqrt (a^2+4*(1-a)^2))/2 ≤ _
  have he : b = 1-a := by linarith
  rw [← he]
  change (a+t)/2 ≤ _
  linarith

private theorem radius_bounds : 0 < radius ∧ radius < 5/6 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hl : Real.sqrt (5 : ℝ) < 101/45 := by nlinarith
  have hp : 0 < (11 + 5 * Real.sqrt (5 : ℝ))/32 := by positivity
  have hr := Real.sq_sqrt hp.le
  have hr0 := Real.sqrt_nonneg ((11 + 5 * Real.sqrt (5 : ℝ))/32)
  exact ⟨Real.sqrt_pos.mpr hp, by unfold radius; nlinarith⟩

set_option maxHeartbeats 2400000 in
private theorem middle_comparison (a : ℝ) (ha : 1/4 ≤ a) (ha1 : a ≤ 2/3) :
    radius ≤ referenceLowerBound a (Real.goldenRatio/2) := by
  let p := Real.goldenRatio
  let b := 1-a
  let A := 1 + (p-3)*b + (2-p)*b^2
  let B := 1 + (p-3)*b + 3*b^2
  let D := (3+5*p)/4
  have hp : 1 < p := Real.one_lt_goldenRatio
  have hp2 : p < 2 := Real.goldenRatio_lt_two
  have hps : p^2 = p+1 := Real.goldenRatio_sq
  have hb : 1/3 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 3/4 := by dsimp [b]; linarith
  have hA : A = a^2 + (p-1)*a*b := by dsimp [A, b]; ring
  have hB : B = A + (p+1)*b^2 := by dsimp [A, B]; ring
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hD : D = 4*radius^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ (11+5*Real.sqrt (5 : ℝ))/32 by positivity)
    dsimp [D, p, radius]
    rw [hs]
    ring
  have hfactor : (D-A-B)^2 - 4*A*B =
      (b-1/2)^2 * ((2+3*p)*(b^2+b) - (14+25*p)/4) := by
    dsimp [D, A, B]
    ring_nf
    simp only [hps]
    ring
  have hbb : b^2+b ≤ 21/16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (show 0 ≤ b+7/4 by linarith)]
  have hbracket : (2+3*p)*(b^2+b) - (14+25*p)/4 ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hbb (show 0 ≤ 2+3*p by linarith)
    nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (b-1/2)) hbracket
  rw [← hfactor] at hprod
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  have hnA := Real.sqrt_nonneg A
  have hnB := Real.sqrt_nonneg B
  have hsum : D ≤ (Real.sqrt A + Real.sqrt B)^2 := by
    by_contra h
    have he : 0 ≤ Real.sqrt A*Real.sqrt B := mul_nonneg hnA hnB
    have hmul := sq_nonneg (D-A-B-2*Real.sqrt A*Real.sqrt B)
    have hx : 2*Real.sqrt A*Real.sqrt B < D-A-B := by nlinarith
    have hy := mul_pos (show 0 < D-A-B-2*Real.sqrt A*Real.sqrt B by linarith)
      (show 0 < D-A-B+2*Real.sqrt A*Real.sqrt B by linarith)
    nlinarith [sq_nonneg (Real.sqrt A*Real.sqrt B)]
  have hform : referenceLowerBound a (p/2) = (Real.sqrt B + Real.sqrt A)/2 := by
    unfold referenceLowerBound
    congr 2
    · congr 1
      dsimp [A, B, b]
      ring_nf
      simp only [hps]
      ring
    · congr 1
      dsimp [A, b]
      ring_nf
      simp only [hps]
      ring
  rw [hform]
  rw [hD] at hsum
  nlinarith [(radius_bounds).1, sq_nonneg (Real.sqrt A+Real.sqrt B+2*radius)]

private theorem high_comparison (a : ℝ) (ha : 2/3 ≤ a) :
    radius ≤ referenceLowerBound a (1/2) := by
  have hab : a*(1-a) ≤ 2/9 := by
    nlinarith [mul_nonneg (show 0 ≤ a-2/3 by linarith)
      (show 0 ≤ a-1/3 by linarith)]
  have hform : referenceLowerBound a (1/2) =
      (Real.sqrt (1-a*(1-a)) + Real.sqrt a)/2 := by
    unfold referenceLowerBound
    congr 2 <;> congr 1 <;> ring
  have h0 : 0 ≤ 1-a*(1-a) := by nlinarith
  have hn := Real.sqrt_nonneg (1-a*(1-a))
  have hns := Real.sq_sqrt h0
  have hn' : 5/6 ≤ Real.sqrt (1-a*(1-a)) := by nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hm := Real.sqrt_nonneg a
  have hms := Real.sq_sqrt ha0
  have hm' : 4/5 ≤ Real.sqrt a := by nlinarith
  rw [hform]
  nlinarith [(radius_bounds).2]

private theorem pure_fixed_lower (I : TwoRecordInstrument Q Q) (psi : Q → ℂ)
    (hu : Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1)
    (hf : I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) =
      CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) :
    radius ≤ diamondDistance I.channel nominalInstrument/2 := by
  let a := Complex.normSq (psi 0)
  have ha : 0 ≤ a := Complex.normSq_nonneg _
  have ha1 : a ≤ 1 := by have hb := Complex.normSq_nonneg (psi 1); dsimp [a]; linarith
  have hend := dark_input_test I psi hu hf
  have hfixed (i j : Q) : I.channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) (false, i) (false, j) =
        psi i*star (psi j) := by
    rw [(two_record_reset_calibration.{0, 0} I).1]
    change I.noClick (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi))) i j = _
    rw [hf]
    rfl
  by_cases hlo : a ≤ 1/4
  · have hnon : 0 ≤ a^2+4*(1-a)^2 := by positivity
    have hs := Real.sq_sqrt hnon
    have hn := Real.sqrt_nonneg (a^2+4*(1-a)^2)
    have hbound : 2*(1-a) ≤ Real.sqrt (a^2+4*(1-a)^2) := by nlinarith
    change (a+Real.sqrt (a^2+4*(1-a)^2))/2 ≤ _ at hend
    linarith [(radius_bounds).2]
  have ha0 : 0 < a := by linarith
  by_cases hlast : a = 1
  · change (a+Real.sqrt (a^2+4*(1-a)^2))/2 ≤ _ at hend
    norm_num [hlast] at hend
    linarith [(radius_bounds).2]
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hlast
  by_cases hmid : a ≤ 2/3
  · have hp1 := Real.one_lt_goldenRatio
    have hp2 := Real.goldenRatio_lt_two
    have hcond : 0 ≤ a+2*(1-2*a)*(Real.goldenRatio/2) := by
      nlinarith [mul_nonneg (show 0 ≤ 2/3-a by linarith)
        (show 0 ≤ 2*Real.goldenRatio-1 by linarith)]
    exact (middle_comparison a (by linarith) hmid).trans
      (reference_lower_bound I.channel psi (Real.goldenRatio/2) hu ha0 ha1'
        (by linarith) (by linarith) hcond hfixed)
  · exact (high_comparison a (by linarith)).trans
      (reference_lower_bound I.channel psi (1/2) hu ha0 ha1'
        (by norm_num) (by norm_num) (by nlinarith) hfixed)

private theorem zero_click_lower (I : TwoRecordInstrument Q Q)
    (hz : ∀ X : CStarMatrix Q Q ℂ, I.click X = 0) :
    1 ≤ diamondDistance I.channel nominalInstrument/2 := by
  let psi : Q → ℂ := ![1, 0]
  have hu : star psi ⬝ᵥ psi = 1 := by norm_num [psi, dotProduct, Fin.sum_univ_two]
  let U : Matrix O O ℂ := Matrix.diagonal (fun p => if p.1 then -1 else 1)
  have hU : U ∈ Matrix.unitaryGroup O ℂ := by
    change star U*U = 1 ∧ U*star U = 1
    constructor <;> ext ⟨s, i⟩ ⟨r, j⟩ <;> cases s <;> cases r <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [U, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.one_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two]
  have htr := I.trace_sum (pureState psi hu).1
  rw [hz] at htr
  have hrho := (pureState psi hu).2.2
  rw [hrho] at htr
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at htr
  change I.noClick (pureState psi hu).1 0 0 + I.noClick (pureState psi hu).1 1 1 +
    ((0 : ℂ)+0) = 1 at htr
  norm_num at htr
  have hval : Matrix.trace (U *
      (CStarMatrix.ofMatrix.symm (I.channel.mapState (pureState psi hu)).1 -
        CStarMatrix.ofMatrix.symm (nominalInstrument.mapState (pureState psi hu)).1)) = 2 := by
    have hnom := nominal_instrument_apply (Matrix.vecMulVec psi (star psi))
    change Matrix.trace (U * (CStarMatrix.ofMatrix.symm
      (I.channel.toCompletelyPositiveMap (pureState psi hu).1) -
      CStarMatrix.ofMatrix.symm (nominalInstrument.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.vecMulVec psi (star psi)))))) = _
    rw [(two_record_reset_calibration.{0, 0} I).1, hnom, hz]
    change (∑ p : O, ∑ q : O, U p q *
      ((CStarMatrix.ofMatrix.symm (recordBlocks (I.noClick (pureState psi hu).1) 0)) q p -
        (if q = (false, 0) ∧ p = (false, 0) then psi 1*star (psi 1)
          else if q = (true, 0) ∧ p = (true, 0) then psi 0*star (psi 0) else 0))) = _
    have hentry (p q : O) : (CStarMatrix.ofMatrix.symm
      (recordBlocks (I.noClick (pureState psi hu).1) 0)) p q =
      if p.1 = false ∧ q.1 = false then I.noClick (pureState psi hu).1 p.2 q.2 else 0 := by
        rcases p with ⟨s, i⟩
        rcases q with ⟨r, j⟩
        change (if s = r then if s then (0 : CStarMatrix Q Q ℂ) i j
          else I.noClick (pureState psi hu).1 i j else 0) = _
        cases s <;> cases r <;> rfl
    simp only [hentry]
    simp [U, Matrix.diagonal,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two,
      Matrix.vecMulVec_apply, psi]
    linear_combination htr
  have h := unitary_test_le_diamond I.channel nominalInstrument psi hu U hU
  rw [hval] at h
  norm_num at h
  linarith

/-- Every legal failing qubit instrument with arbitrary CP branches and retained
quantum successors has half-diamond distance at least the explicit radius. -/
theorem global_failure_distance_lower_bound
    (I : TwoRecordInstrument (Fin 2) (Fin 2)) (hf : Fails I) :
    radius ≤ diamondDistance I.channel nominalInstrument/2 := by
  rcases failing_qubit_dark_split I hf with hz | ⟨psi, hu, hp⟩
  · exact (show radius ≤ 1 by linarith [(radius_bounds).2]).trans (zero_click_lower I hz)
  · exact pure_fixed_lower I psi hu hp

end D5.S3.Quantum.Measurement.ExactFailureRadius
