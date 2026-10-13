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
    simp only [N, C, Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib] at h ⊢
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
      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hu, Complex.ofReal_one]
    have hmass : (∑ k, star (c k) * c k) = 1 := by
      have h := congrArg (fun M : Matrix Q Q ℂ => star psi ⬝ᵥ (M *ᵥ psi)) hcomp
      have hnorm (A : Matrix Q Q ℂ) :
          star psi ⬝ᵥ ((Aᴴ * A) *ᵥ psi) = star (A *ᵥ psi) ⬝ᵥ (A *ᵥ psi) := by
        rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_vecMul]
      simp only [Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add, dotProduct_sum, Matrix.one_mulVec, hunit] at h
      simp only [hnorm, hz, star_zero, dotProduct_zero, Finset.sum_const_zero, add_zero, ← hc] at h
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
    simp only [primal, Matrix.sum_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, ← hc, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul]
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
      simp only [U, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, star_zero, star_neg, Matrix.one_apply, apply_ite, star_one]
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
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add, hu, Complex.ofReal_one]
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
    simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, U, W, recordBlocks, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply, Complex.ofReal_add]
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
    simp [U, Matrix.diagonal, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, Matrix.vecMulVec_apply, psi]
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
private def outer {n : Type*} (x : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec x (star x)
set_option maxHeartbeats 2400000 in
private theorem outer_difference_norm {n : Type*} [Fintype n] [DecidableEq n]
    (x y : n → ℂ) :
    0 ≤ (((∑ i, Complex.normSq (x i)) + (∑ i, Complex.normSq (y i)))^2 -
        4 * Complex.normSq (star x ⬝ᵥ y)) ∧
    traceNorm (outer x - outer y) = Real.sqrt
      (((∑ i, Complex.normSq (x i)) + (∑ i, Complex.normSq (y i)))^2 -
        4 * Complex.normSq (star x ⬝ᵥ y)) := by
  let p : ℝ := ∑ i, Complex.normSq (x i)
  let q : ℝ := ∑ i, Complex.normSq (y i)
  let r := star x ⬝ᵥ y
  let X := outer x
  let Y := outer y
  let Z := Matrix.vecMulVec x (star y)
  let T := Matrix.vecMulVec y (star x)
  let A := X-Y
  let C := ((p+q : ℝ) : ℂ) • (X+Y) - 2 • (r • Z + star r • T)
  have hx : star x ⬝ᵥ x = (p : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, p]
  have hy : star y ⬝ᵥ y = (q : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, q]
  have hr : star y ⬝ᵥ x = star r := by
    simp only [r, dotProduct, star_sum, star_mul, Pi.star_apply, star_star]
  have hxy : star x ⬝ᵥ y = r := rfl
  have hrr : r * star r = (Complex.normSq r : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj r
  have hmul (a b c d : n → ℂ) :
      Matrix.vecMulVec a (star b) * Matrix.vecMulVec c (star d) =
        (star b ⬝ᵥ c) • Matrix.vecMulVec a (star d) := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hW : C = A*A + ∑ i, outer ((y i) • x - (x i) • y) := by
    have he (i : n) : outer ((y i) • x - (x i) • y) =
        (y i*star (y i)) • X + (x i*star (x i)) • Y -
          (y i*star (x i)) • Z - (x i*star (y i)) • T := by
      ext j k
      simp only [outer, X, Y, Z, T, Matrix.vecMulVec_apply, Pi.star_apply, Pi.sub_apply, Pi.smul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, star_sub, star_mul]
      ring
    simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hx' : ∑ i, x i*star (x i) = (p : ℂ) := by
      simpa only [dotProduct, Pi.star_apply, mul_comm] using hx
    have hy' : ∑ i, y i*star (y i) = (q : ℂ) := by
      simpa only [dotProduct, Pi.star_apply, mul_comm] using hy
    have hr' : ∑ i, y i*star (x i) = r := by
      simp only [r, dotProduct, Pi.star_apply, mul_comm]
    have hr'' : ∑ i, x i*star (y i) = star r := by
      simpa only [dotProduct, Pi.star_apply, mul_comm] using hr
    rw [hx', hy', hr', hr'']
    dsimp only [C, A, X, Y, Z, T, outer]
    simp only [sub_mul, mul_sub, hmul, hx, hy, hr]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Complex.ofReal_add]
    ring
  have hA : Aᴴ = A := by
    dsimp [A, X, Y, outer]
    simp [Matrix.conjTranspose_vecMulVec]
  have hCP : C.PosSemidef := by
    rw [hW]
    nth_rw 1 [← hA]
    exact (Matrix.posSemidef_conjTranspose_mul_self A).add
      (Matrix.posSemidef_sum Finset.univ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _))
  let d2 := (p+q)^2 - 4*Complex.normSq r
  have htrace : Matrix.trace C = (d2 : ℂ) := by
    dsimp only [C, d2, X, Y, Z, T, outer]
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_vecMulVec]
    rw [dotProduct_comm x (star x), dotProduct_comm y (star y), hx, hy,
      dotProduct_comm x (star y), dotProduct_comm y (star x), hr, hxy]
    push_cast
    rw [← hrr]
    ring
  have hd2 : 0 ≤ d2 := by
    have h := hCP.trace_nonneg
    rw [htrace] at h
    exact_mod_cast h
  have hsquare : C*C = (d2 : ℂ) • (A*A) := by
    dsimp only [C, A, X, Y, Z, T, outer]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, hmul, hx, hy, hr, hxy, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Complex.ofReal_add]
    dsimp only [d2]
    push_cast
    rw [← hrr]
    ring
  refine ⟨hd2, ?_⟩
  let d := Real.sqrt d2
  have hds : d^2 = d2 := Real.sq_sqrt hd2
  by_cases hd : d = 0
  · have hz2 : d2 = 0 := by nlinarith
    have hz : C = 0 := hCP.trace_eq_zero_iff.mp (by rw [htrace, hz2]; norm_num)
    have hzA : A = 0 := by
      have hAA : A*A = 0 := by
        have hp := (Matrix.posSemidef_sum Finset.univ
          (fun i _ => Matrix.posSemidef_vecMulVec_self_star
            ((y i) • x - (x i) • y))).nonneg
        have hle : Aᴴ*A ≤ 0 := by
          rw [← hz, hW, hA]
          exact le_add_of_nonneg_right hp
        simpa only [hA] using le_antisymm hle (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
      exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hA, hAA]; simp)
    change traceNorm A = d
    rw [hzA, hd]
    simp [traceNorm]
  · have hdpos : 0 < d := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hd)
    let B := ((d : ℂ)⁻¹) • C
    have hBP : B.PosSemidef := hCP.smul (by exact_mod_cast inv_nonneg.mpr hdpos.le)
    have hBsq : B*B = Aᴴ*A := by
      rw [hA]
      dsimp only [B]
      rw [Matrix.smul_mul, Matrix.mul_smul, hsquare, smul_smul, smul_smul]
      have hdC : (d : ℂ)^2 = (d2 : ℂ) := by exact_mod_cast hds
      have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd
      rw [show (d : ℂ)⁻¹*(d : ℂ)⁻¹*(d2 : ℂ) = 1 by
        rw [← hdC]; field_simp, one_smul]
    change (CFC.sqrt (Aᴴ*A)).trace.re = d
    rw [CFC.sqrt_unique hBsq hBP.nonneg]
    dsimp only [B]
    rw [Matrix.trace_smul, htrace]
    change (((d : ℂ)⁻¹)*(d2 : ℂ)).re = d
    have he : ((d : ℂ)⁻¹)*(d2 : ℂ) = (d : ℂ) := by
      have hs : (d2 : ℂ) = (d : ℂ)^2 := by exact_mod_cast hds.symm
      rw [hs]
      field_simp
    rw [he, Complex.ofReal_re]
private def branchCP (K : CStarMatrix Q Q ℂ) : CStarMatrix Q Q ℂ →CP CStarMatrix Q Q ℂ where
  toLinearMap :=
    { toFun := fun X => K*X*star K
      map_add' := fun X Y => by simp only [mul_add, add_mul]
      map_smul' := fun c X => by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
  map_cstarMatrix_nonneg' k X hX := by
    let D : CStarMatrix (Fin k) (Fin k) (CStarMatrix Q Q ℂ) := Matrix.diagonal fun _ => K
    have h := star_right_conjugate_nonneg hX D
    convert h using 1
    apply CStarMatrix.ext
    intro i j
    change K*X i j*star K = (D*X*star D) i j
    change K*X i j*star K = ∑ b : Fin k,
      (∑ a : Fin k, (if i=a then K else 0)*X a b)*star (if j=b then K else 0)
    simp [eq_comm,apply_ite]
private def plusK : CStarMatrix Q Q ℂ := CStarMatrix.ofMatrix !![1/2,1/2;1/2,1/2]
private def plusL : CStarMatrix Q Q ℂ :=
  CStarMatrix.ofMatrix !![(1/Real.sqrt 2 : ℝ),(-1/Real.sqrt 2 : ℝ);0,0]
private theorem plus_complete : star plusK*plusK + star plusL*plusL = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusK, plusL, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp <;> field_simp [hn] <;> nlinarith
/-- The original balanced phase-zero instrument, including its clicked successor. -/
def plusInstrument : TwoRecordInstrument Q Q where
  noClick := branchCP plusK
  click := branchCP plusL
  trace_sum X := by
    change Matrix.trace (plusK*X*star plusK) + Matrix.trace (plusL*X*star plusL) = _
    have hcomp : (CStarMatrix.ofMatrix.symm plusK)ᴴ * CStarMatrix.ofMatrix.symm plusK +
        (CStarMatrix.ofMatrix.symm plusL)ᴴ * CStarMatrix.ofMatrix.symm plusL = 1 := plus_complete
    change Matrix.trace (CStarMatrix.ofMatrix.symm plusK * CStarMatrix.ofMatrix.symm X *
      (CStarMatrix.ofMatrix.symm plusK)ᴴ) + Matrix.trace
      (CStarMatrix.ofMatrix.symm plusL * CStarMatrix.ofMatrix.symm X *
        (CStarMatrix.ofMatrix.symm plusL)ᴴ) = Matrix.trace (CStarMatrix.ofMatrix.symm X)
    rw [Matrix.trace_mul_cycle (CStarMatrix.ofMatrix.symm plusK),
      Matrix.trace_mul_cycle (CStarMatrix.ofMatrix.symm plusL), ← Matrix.trace_add,
      ← Matrix.add_mul, hcomp, Matrix.one_mul]
private theorem candidate_scalar_upper (x : ℝ) (hA : 0 ≤ 5/4-x)
    (hB : 0 ≤ 1/4+x-x^2) :
    (Real.sqrt (5/4-x) + Real.sqrt (1/4+x-x^2))/2 ≤ radius := by
  let s := Real.sqrt (5 : ℝ)
  let A := 5/4-x
  let B := 1/4+x-x^2
  let D := (11+5*s)/8
  have hs : s^2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hD : D = 4*radius^2 := by
    dsimp [D, radius, s]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hfactor : (D-A-B)^2-4*A*B =
      (x-(3-s)/4)^2 * ((x-(5+s)/4)^2+(7+3*s)/2) := by
    have hs3 : s^3 = 5*s := by
      calc
        _ = s*s^2 := by ring
        _ = _ := by rw [hs]; ring
    have hs4 : s^4 = 25 := by
      calc
        _ = (s^2)^2 := by ring
        _ = _ := by rw [hs]; norm_num
    dsimp [D, A, B]
    ring_nf
    rw [hs,hs3,hs4]
    ring
  have hprod : 0 ≤ (D-A-B)^2-4*A*B := by
    rw [hfactor]
    positivity
  have hdiff : 0 < D-A-B := by dsimp [D,A,B]; nlinarith [sq_nonneg x]
  have ha := Real.sqrt_nonneg A
  have hb := Real.sqrt_nonneg B
  have has := Real.sq_sqrt hA
  have hbs := Real.sq_sqrt hB
  change (Real.sqrt A)^2 = A at has
  change (Real.sqrt B)^2 = B at hbs
  have hmul : 2*Real.sqrt A*Real.sqrt B ≤ D-A-B := by
    by_contra h
    have hp := mul_pos (show 0 < 2*Real.sqrt A*Real.sqrt B-(D-A-B) by linarith)
      (show 0 < 2*Real.sqrt A*Real.sqrt B+(D-A-B) by positivity)
    nlinarith [sq_nonneg (Real.sqrt A*Real.sqrt B)]
  rw [hD] at hmul
  change (Real.sqrt A+Real.sqrt B)/2 ≤ radius
  nlinarith [(radius_bounds).1]
set_option maxHeartbeats 2400000 in
private theorem plus_pure_upper (w : (Fin 2 × Q) → ℂ) (hw : star w ⬝ᵥ w = 1) :
    referenceError plusInstrument.channel nominalInstrument (pureState w hw) ≤ 2*radius := by
  let a := Complex.normSq (w (0,0)) + Complex.normSq (w (1,0))
  let c := w (0,0)*star (w (0,1)) + w (1,0)*star (w (1,1))
  let u := c.re
  let v := c.im
  let x := a-u
  let t := Real.sqrt (2 : ℝ)
  have ht : t^2 = 2 := Real.sq_sqrt (by norm_num)
  have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have htotal : Complex.normSq (w (0,0)) + Complex.normSq (w (0,1)) +
      Complex.normSq (w (1,0)) + Complex.normSq (w (1,1)) = 1 := by
    have h := congrArg Complex.re hw
    simpa [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Pi.star_apply, Complex.star_def, Complex.normSq_apply,
      Complex.mul_re,add_assoc] using h
  let xn : (Fin 2 × O) → ℂ := fun p => if p.2.1 then 0 else
    (w (p.1,0)+w (p.1,1))/2
  let yn : (Fin 2 × O) → ℂ := fun p =>
    if p.2 = (false,0) then w (p.1,1) else 0
  let xc : (Fin 2 × O) → ℂ := fun p =>
    if p.2 = (true,0) then (w (p.1,0)-w (p.1,1))/(t : ℂ) else 0
  let yc : (Fin 2 × O) → ℂ := fun p =>
    if p.2 = (true,0) then w (p.1,0) else 0
  have hpN : ∑ p, Complex.normSq (xn p) = 1/2+u := by
    simp [xn, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, u,c,Complex.normSq_apply,Complex.star_def,Complex.mul_re,Complex.mul_im]
    simp [Complex.normSq_apply] at htotal
    linear_combination htotal/2
  have hqN : ∑ p, Complex.normSq (yn p) = 1-a := by
    simp [yn,a,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_two]
    linarith
  have hrN : star xn ⬝ᵥ yn = ((1-a : ℝ) : ℂ)/2 + star c/2 := by
    simp [xn,yn,dotProduct,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_two]
    apply Complex.ext <;> simp [a,c,Complex.normSq_apply,Complex.star_def,
      Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
    · simp [Complex.normSq_apply] at htotal
      linear_combination htotal/2
    · ring
  have hpC : ∑ p, Complex.normSq (xc p) = 1/2-u := by
    simp [xc,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_two, Complex.normSq_div,Complex.normSq_ofReal,← sq,ht]
    simp [u,c,Complex.normSq_apply,Complex.star_def,Complex.mul_re,Complex.mul_im]
    simp [Complex.normSq_apply] at htotal
    linear_combination htotal/2
  have hqC : ∑ p, Complex.normSq (yc p) = a := by
    simp [yc,a,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_two]
  have hrC : star xc ⬝ᵥ yc = ((a : ℂ)-c)/(t : ℂ) := by
    simp [xc,yc,dotProduct,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_two]
    apply Complex.ext <;> simp [a,c,Complex.normSq_apply,Complex.star_def,
      Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]
    all_goals field_simp [ht0] <;> ring
  have hn := outer_difference_norm xn yn
  have hc := outer_difference_norm xc yc
  rw [hpN,hqN,hrN] at hn
  rw [hpC,hqC,hrC] at hc
  have hdN : (1/2+u+(1-a))^2 - 4*Complex.normSq
      (((1-a : ℝ) : ℂ)/2+star c/2) = 5/4-x-v^2 := by
    simp [Complex.normSq_apply,u,v,x,Complex.star_def]
    ring
  have hdC : (1/2-u+a)^2 - 4*Complex.normSq (((a : ℂ)-c)/(t : ℂ)) =
      1/4+x-x^2-2*v^2 := by
    rw [Complex.normSq_div,Complex.normSq_ofReal,← sq,ht]
    simp [Complex.normSq_apply,u,v,x]
    ring
  rw [hdN] at hn
  rw [hdC] at hc
  have hentry : CStarMatrix.ofMatrix.symm
      (referenceState plusInstrument.channel (pureState w hw)).1 -
      CStarMatrix.ofMatrix.symm (referenceState nominalInstrument (pureState w hw)).1 =
        (outer xn-outer yn)+(outer xc-outer yc) := by
    ext ⟨r,⟨s,i⟩⟩ ⟨l,⟨b,j⟩⟩
    change plusInstrument.channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (fun e f => w (r,e)*star (w (l,f)))) (s,i) (b,j) -
      nominalInstrument.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (fun e f => w (r,e)*star (w (l,f)))) (s,i) (b,j) = _
    have hnom := congrArg (fun M : Matrix O O ℂ => M (s,i) (b,j))
      (nominal_instrument_apply (fun e f => w (r,e)*star (w (l,f))))
    change nominalInstrument.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (fun e f => w (r,e)*star (w (l,f)))) (s,i) (b,j) = _ at hnom
    rw [(two_record_reset_calibration.{0,0} plusInstrument).1, hnom]
    change (if s=b then (if s then
      ∑ k : Q, (∑ e : Q, plusL i e*(w (r,e)*star (w (l,k))))*star (plusL j k)
      else ∑ k : Q, (∑ e : Q, plusK i e*(w (r,e)*star (w (l,k))))*star (plusK j k)) else 0) -
      (if (s,i)=(false,0) ∧ (b,j)=(false,0) then w (r,1)*star (w (l,1))
        else if (s,i)=(true,0) ∧ (b,j)=(true,0) then w (r,0)*star (w (l,0)) else 0) =
      (xn (r,(s,i))*star (xn (l,(b,j)))-yn (r,(s,i))*star (yn (l,(b,j)))) +
        (xc (r,(s,i))*star (xc (l,(b,j)))-yc (r,(s,i))*star (yc (l,(b,j))))
    cases s <;> cases b <;> fin_cases i <;> fin_cases j <;>
      simp [plusK,plusL,xn,yn,xc,yc,Fin.sum_univ_two,map_ofNat,t] <;>
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)] <;>
      ring
  unfold referenceError
  rw [hentry]
  have h := traceNorm_add_le (outer xn-outer yn) (outer xc-outer yc)
  rw [hn.2,hc.2] at h
  have ha : 0 ≤ 5/4-x := by nlinarith [hn.1,sq_nonneg v]
  have hb : 0 ≤ 1/4+x-x^2 := by nlinarith [hc.1,sq_nonneg v]
  have hN := Real.sqrt_le_sqrt (show 5/4-x-v^2 ≤ 5/4-x by nlinarith [sq_nonneg v])
  have hC := Real.sqrt_le_sqrt (show 1/4+x-x^2-2*v^2 ≤ 1/4+x-x^2 by nlinarith [sq_nonneg v])
  linarith [candidate_scalar_upper x ha hb]
private theorem plus_upper : diamondDistance plusInstrument.channel nominalInstrument ≤ 2*radius := by
  rw [(D5.S3.Quantum.Foundation.FiniteDiamondDistance.result.{0,0}
    plusInstrument.channel nominalInstrument).2.2]
  refine csSup_le ?_ ?_
  · exact ⟨(0 : ℝ),Or.inl rfl⟩
  · rintro d (hd | ⟨rho,hpure,rfl⟩)
    · have hd0 : d = 0 := hd
      rw [hd0]
      linarith [(radius_bounds).1]
    · obtain ⟨w,hw⟩ := hpure
      have hu : star w ⬝ᵥ w = 1 := by
        have htr := rho.2.2
        rw [hw] at htr
        change Matrix.trace (Matrix.vecMulVec w (star w)) = 1 at htr
        simpa only [Matrix.trace_vecMulVec,dotProduct_comm] using htr
      have he : rho = pureState w hu := Subtype.ext hw
      rw [he]
      exact plus_pure_upper w hu
private theorem plus_failure : Fails plusInstrument := by
  let t := Real.sqrt (2 : ℝ)
  have hs : t^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsC : (t : ℂ)^2 = 2 := by exact_mod_cast hs
  let psi : Q → ℂ := fun _ => (t : ℂ)/2
  have hu : star psi ⬝ᵥ psi = 1 := by
    simp [psi,dotProduct,Fin.sum_univ_two,Complex.star_def]
    linear_combination hsC/2
  let rho := pureState psi hu
  have hrho : rho.1 = plusK := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rho,pureState,psi,plusK,CStarMatrix.ofMatrix_apply, Matrix.vecMulVec_apply,Complex.star_def] <;>
      linear_combination hsC/4
  have hfix : plusInstrument.noClick rho.1 = rho.1 := by
    rw [hrho]
    change plusK*plusK*star plusK = plusK
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [plusK,CStarMatrix.mul_apply,CStarMatrix.star_apply,
        CStarMatrix.ofMatrix_apply,Fin.sum_univ_two,Complex.star_def,map_ofNat]
  refine ⟨rho,1,by norm_num,?_⟩
  have he (n : ℕ) : (Matrix.trace (plusInstrument.noClick^[n] rho.1)).re = 1 := by
    rw [Function.iterate_fixed hfix n,rho.2.2]
    rfl
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
/-- The complete actual-instrument failure radius is attained by the original
balanced projector instrument, with every finite quantum reference retained. -/
theorem exact_failure_radius :
    Fails plusInstrument ∧ diamondDistance plusInstrument.channel nominalInstrument/2 = radius ∧
    sInf {d : ℝ | ∃ I : TwoRecordInstrument (Fin 2) (Fin 2), Fails I ∧
      d = diamondDistance I.channel nominalInstrument/2} = radius := by
  have hf := plus_failure
  have he : diamondDistance plusInstrument.channel nominalInstrument/2 = radius := by
    apply le_antisymm
    · linarith [plus_upper]
    · exact global_failure_distance_lower_bound plusInstrument hf
  have hm : radius ∈ {d : ℝ | ∃ I : TwoRecordInstrument Q Q, Fails I ∧
      d = diamondDistance I.channel nominalInstrument/2} := ⟨plusInstrument,hf,he.symm⟩
  have hlow : ∀ d ∈ {d : ℝ | ∃ I : TwoRecordInstrument Q Q, Fails I ∧
      d = diamondDistance I.channel nominalInstrument/2}, radius ≤ d := by
    rintro d ⟨I,hI,rfl⟩
    exact global_failure_distance_lower_bound I hI
  exact ⟨hf,he,le_antisymm (csInf_le ⟨radius,hlow⟩ hm) (le_csInf ⟨radius,hm⟩ hlow)⟩
end D5.S3.Quantum.Measurement.ExactFailureRadius
