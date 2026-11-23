/- GID: D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryReplacementExact
   mirror-E: none(waiver:exact-finite-channel-optimization)
   anchors: []
   utility: none
   digest: Exact stabilized diamond error for binary matched-diagonal replacement from a fixed pure Schmidt resource. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum

/-! The fixed-resource binary replacement optimum on native channels. -/

namespace D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact

open Matrix
open D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
noncomputable section

private theorem diagonal_l1_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) : ∑ i, |(X i i).re| ≤ traceNorm X := by
  let P := posPart X
  let N := negPart X
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have hN : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  have he : X = P - N := (CFC.posPart_sub_negPart X hX).symm
  rw [trace_norm_jordan_mass X hX]
  change (∑ i, |(X i i).re|) ≤ P.trace.re + N.trace.re
  have hi (i : n) : |(X i i).re| ≤ (P i i).re + (N i i).re := by
    rw [he]
    change |(P i i).re - (N i i).re| ≤ _
    exact abs_sub_le_iff.mpr ⟨by linarith [(Complex.nonneg_iff.mp (hN.diag_nonneg (i := i))).1],
      by linarith [(Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).1]⟩
  simpa [trace, Matrix.diag, Finset.sum_add_distrib] using Finset.sum_le_sum fun i _ => hi i

private theorem referenceError_le_diamond {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t] {n : ℕ}
    (A Bit : QuantumChannel s t) (rho : DensityState (Fin n × s)) :
    referenceError A Bit rho ≤ diamondDistance A Bit := by
  unfold diamondDistance
  apply le_csSup
  · refine ⟨2, ?_⟩
    rintro x (hx | hx)
    · simp [Set.mem_singleton_iff.mp hx]
    · obtain ⟨m, tau, rfl⟩ := hx
      have h := traceDistance_le_one (referenceState A tau) (referenceState Bit tau)
      change referenceError A Bit tau / 2 ≤ 1 at h
      linarith
  · exact Or.inr ⟨n, rho, rfl⟩

private def diagBorn {s t : Type*} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
    (C : QuantumChannel s t) (rho : DensityState (Fin 1 × s)) (i : t) : ℝ :=
  (CStarMatrix.ofMatrix.symm (referenceState C rho).val (0,i) (0,i)).re

def rawEntry {A Bit : Type*} [Fintype A] [DecidableEq A] [Fintype Bit] [DecidableEq Bit]
    (C : QuantumChannel A Bit) (X : Matrix A A ℂ) : Matrix Bit Bit ℂ :=
  CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

private theorem single_basis_psd {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    (Matrix.single a a (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : i = a <;> simp [hi]

private def basisBorn {A Bit : Type*} [Fintype A] [DecidableEq A] [Fintype Bit] [DecidableEq Bit]
    (C : QuantumChannel A Bit) (a : A) (i : Bit) : ℝ :=
  (rawEntry C (Matrix.single a a 1) i i).re

private def basisDensity {A : Type*} [Fintype A] [DecidableEq A] (a : A) : DensityState A :=
  ⟨CStarMatrix.ofMatrix (Matrix.single a a 1),
   map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (single_basis_psd a).nonneg,
   by change (Matrix.single a a (1 : ℂ)).trace = 1; simp⟩

private theorem diagBorn_basis {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (C : QuantumChannel S T) (s : S) (i : T) :
    diagBorn C (basisDensity ((0 : Fin 1),s)) i = basisBorn C s i := by
  change (rawEntry C
      (fun u v => Matrix.single ((0 : Fin 1),s) ((0 : Fin 1),s) (1 : ℂ) (0,u) (0,v)) i i).re = _
  have h : (fun u v => Matrix.single ((0 : Fin 1),s) ((0 : Fin 1),s) (1 : ℂ)
      (0,u) (0,v)) = Matrix.single s s 1 := by
    ext u v
    simp [Matrix.single_apply, Prod.mk.injEq]
  rw [h]
  rfl

private theorem sum_vary_single {A Bit D : Type*} [Fintype D] [DecidableEq A] [DecidableEq Bit]
    (a : A) (b : Bit) (v : D → ℂ) :
    (∑ i, Matrix.single a b (v i)) = Matrix.single a b (∑ i, v i) := by
  ext i j
  by_cases hi : a = i <;> by_cases hj : b = j <;> simp [Matrix.sum_apply, hi, hj]

private theorem diagonal_replacement_exists {A T : Type*} [Fintype A] [DecidableEq A]
    [Fintype T] [DecidableEq T] (d : T → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hs : ∑ t, d t = 1) :
    ∃ C : QuantumChannel A T, ∀ X,
      rawEntry C X = X.trace • Matrix.diagonal (fun t => (d t : ℂ)) := by
  let e (t : T) : ℂ := (Real.sqrt (d t) : ℂ)
  have he₁ (t : T) : star (e t) = e t := by simp [e]
  have he₂ (t : T) : e t * e t = (d t : ℂ) := by
    dsimp [e]
    exact_mod_cast Real.mul_self_sqrt (hd t)
  let K (i : A × T) : Matrix T A ℂ := Matrix.single i.2 i.1 (e i.2)
  have hkc (i : A × T) : (K i)ᴴ = Matrix.single i.1 i.2 (e i.2) := by
    simp [K, Matrix.conjTranspose_single, he₁]
  have hs' : (∑ t, (d t : ℂ)) = 1 := by exact_mod_cast hs
  have hK : (∑ i, (K i)ᴴ * K i) = 1 := by
    simp_rw [hkc, K, Matrix.single_mul_single_same, he₂]
    rw [Fintype.sum_prod_type]
    simp_rw [sum_vary_single, hs']
    exact Matrix.sum_single_one
  obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
  refine ⟨C, fun X => ?_⟩
  change CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
  rw [hC]
  simp_rw [hkc, K, Matrix.single_mul_mul_single]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_vary_single]
  have hq (t : T) : (∑ a, e t * X a a * e t) = X.trace * (d t : ℂ) := by
    simp_rw [show ∀ z : ℂ, e t * z * e t = (e t * e t) * z from fun _ => by ring,
      he₂, ← Finset.mul_sum]
    rw [Matrix.trace, mul_comm]
    rfl
  simp_rw [hq, Matrix.sum_single_eq_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [hij, smul_eq_mul]

private theorem replacer_reference_error {A T U : Type} [Fintype A] [DecidableEq A]
    [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    (C Q : QuantumChannel A T) (M N : Matrix T T ℂ)
    (hC : ∀ X, rawEntry C X = X.trace • M)
    (hQ : ∀ X, rawEntry Q X = X.trace • N)
    (rho : DensityState (U × A)) :
    referenceError C Q rho = traceNorm (M-N) := by
  let X := CStarMatrix.ofMatrix.symm rho.val
  let R : Matrix U U ℂ := ∑ a : A, X.submatrix (fun u => (u,a)) (fun u => (u,a))
  have hX : X.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.prop.1).posSemidef
  have hR : R.PosSemidef := Matrix.posSemidef_sum (s := Finset.univ)
    (fun a _ => hX.submatrix (fun u => (u,a)))
  have ht : R.trace = 1 := by
    rw [← rho.prop.2]
    · simp only [R, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.submatrix_apply]
      change (∑ u : U, ∑ a : A, X (u,a) (u,a)) = ∑ p : U × A, X p p
      rw [Fintype.sum_prod_type]
  have hNorm : traceNorm R = 1 := by
    have h := congrArg Complex.re (traceNorm_of_posSemidef hR)
    simpa [ht] using h
  have he :
      CStarMatrix.ofMatrix.symm (referenceState C rho).val -
      CStarMatrix.ofMatrix.symm (referenceState Q rho).val =
        R ⊗ₖ (M-N) := by
    ext p q
    rcases p with ⟨u,a⟩
    rcases q with ⟨v,b⟩
    change rawEntry C (Matrix.of (fun x y => X (u,x) (v,y))) a b -
      rawEntry Q (Matrix.of (fun x y => X (u,x) (v,y))) a b = _
    rw [hC,hQ]
    simp [R, Matrix.trace, Matrix.diag, Matrix.sum_apply,
      Matrix.submatrix_apply, smul_eq_mul, mul_sub]
  unfold referenceError
  rw [he, traceNorm_kronecker, hNorm, one_mul]

theorem replacer_diamond_exact {A T : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype T] [DecidableEq T]
    (C Q : QuantumChannel A T) (M N : Matrix T T ℂ)
    (hC : ∀ X, rawEntry C X = X.trace • M)
    (hQ : ∀ X, rawEntry Q X = X.trace • N) :
    diamondDistance C Q = traceNorm (M-N) := by
  apply le_antisymm
  · unfold diamondDistance
    apply csSup_le (by exact ⟨0, Or.inl (by simp)⟩)
    rintro y (hy | ⟨n,rho,rfl⟩)
    · rw [Set.mem_singleton_iff.mp hy]
      exact traceNorm_nonneg _
    · exact (replacer_reference_error C Q M N hC hQ rho).le
  · let rho := basisDensity ((0 : Fin 1), Classical.choice (inferInstance : Nonempty A))
    rw [← replacer_reference_error C Q M N hC hQ rho]
    exact referenceError_le_diamond C Q rho

private theorem traceNorm_diagonal_real {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    traceNorm (diagonal (fun i => (d i : ℂ))) = ∑ i, |d i| := by
  have hp : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast abs_nonneg (d i)
  have hs : diagonal (fun i => ((|d i| : ℝ) : ℂ)) * diagonal (fun i => ((|d i| : ℝ) : ℂ)) =
      (diagonal (fun i => (d i : ℂ)))ᴴ * diagonal (fun i => (d i : ℂ)) := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show |d i| * |d i| = d i * d i from by nlinarith [sq_abs (d i)])
  unfold traceNorm
  rw [CFC.sqrt_unique hs hp.nonneg]
  simp only [trace_diagonal, map_sum]
  change (∑ i, Complex.re ((|d i| : ℝ) : ℂ)) = _
  simp

private theorem raw_trace_preserving {A T : Type*} [Fintype A] [DecidableEq A]
    [Fintype T] [DecidableEq T] (S : QuantumChannel A T) (X : Matrix A A ℂ) :
    (rawEntry S X).trace = X.trace :=
  S.trace_preserving (CStarMatrix.ofMatrix X)

private lemma tr_add (X Y : M₂) : tr (X+Y) = tr X + tr Y := by simp [tr,Matrix.trace_add]

private lemma tr_sub (X Y : M₂) : tr (X-Y) = tr X - tr Y := by simp [tr,Matrix.trace_sub]

private lemma tr_comm (X Y : M₂) : tr (X*Y) = tr (Y*X) := by rw [tr,tr,Matrix.trace_mul_comm]

private lemma tr_nonneg {X : M₂} (hX : X.PosSemidef) : 0 ≤ tr X := by
  exact (Complex.nonneg_iff.mp hX.trace_nonneg).1

private def midpoint (X Y : M₂) : M₂ := (1/2 : ℂ) • (X+Y)

private lemma midpoint_psd {X Y : M₂} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (midpoint X Y).PosSemidef := (hX.add hY).smul (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 1/2)

private lemma tr_half (X : M₂) : tr ((1/2 : ℂ) • X) = tr X/2 := by
  simp [tr,Matrix.trace_smul,Complex.mul_re]; ring

private lemma pair_hits_le {X Y : M₂} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    tr (X*Y) ≤ quad (midpoint X Y) := by
  have hh := (hX.sub hY).eq
  have hps := Matrix.posSemidef_conjTranspose_mul_self (X-Y)
  rw [hh] at hps
  have h := tr_nonneg hps
  rw [sub_mul,mul_sub,mul_sub,tr_sub,tr_sub,tr_sub,tr_comm Y X] at h
  unfold quad midpoint
  rw [smul_mul_smul,show (1/2:ℂ)*(1/2)= (1/2)*(1/2) by rfl, mul_smul, tr_half,tr_half]
  rw [add_mul,mul_add,mul_add,tr_add,tr_add,tr_add,tr_comm Y X]
  linarith

private def choiProbe : Matrix (Bit × Bit) (Bit × Bit) ℂ :=
    Matrix.vecMulVec (fun p => if p.1=p.2 then 1 else 0)
      (star (fun p => if p.1=p.2 then (1:ℂ) else 0))

private def probe (C : QuantumChannel Bit Bit) (a : Bit) : M₂ :=
  fun i j => rawEntry C (Matrix.single i j 1) a a

private lemma probe_psd (C : QuantumChannel Bit Bit) (a : Bit) : (probe C a).PosSemidef := by
  have hp : choiProbe.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hq := referenceAction_nonneg C (CStarMatrix.ofMatrix choiProbe)
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp.nonneg)
  have hs := ((map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hq).posSemidef).submatrix
    (fun i : Bit => (i,a))
  convert hs using 1
  ext i j
  change rawEntry C (Matrix.single i j 1) a a =
    rawEntry C (fun u v => choiProbe (i,u) (j,v)) a a
  congr 1
  ext u v
  simp [choiProbe,Matrix.vecMulVec_apply,Matrix.single_apply]
  by_cases hi : i=u <;> by_cases hj : j=v <;> simp [hi,hj]

private lemma probe_total (C : QuantumChannel Bit Bit) : probe C 0 + probe C 1 = 1 := by
  ext i j
  have h := raw_trace_preserving C (Matrix.single i j (1:ℂ))
  rw [Matrix.trace, Fin.sum_univ_two] at h
  change rawEntry C (Matrix.single i j 1) 0 0 + rawEntry C (Matrix.single i j 1) 1 1 = _ at h
  rw [Matrix.add_apply,probe,probe,h]
  by_cases h : i=j
  · subst j; simp [Matrix.trace_single_eq_same]
  · rw [Matrix.one_apply, ite_eq_right h, Matrix.trace_single_eq_of_ne _ _ _ h]

private def amp (i : Bit) : ℝ := if i=0 then Real.sqrt 3/2 else 1/2

private def V : M₂ := Matrix.diagonal (fun i => (Real.sqrt (amp i) : ℝ))

private theorem binary_effect_channels (E : Bit → M₂) (hE : ∀ i, (E i).PosSemidef)
    (hsum : ∑ i, E i = 1) :
    ∃ C : QuantumChannel Bit Bit, ∀ (X : M₂) (i j : Bit),
      rawEntry C X i j = if i=j then (E i*X).trace else 0 := by
  let S (i : Bit) := CFC.sqrt (E i)
  have hS (i : Bit) : (S i)ᴴ = S i :=
    (CFC.sqrt_nonneg (E i)).posSemidef.isHermitian.eq
  have hSq (i : Bit) : S i*S i = E i := CFC.sqrt_mul_sqrt_self _ (hE i).nonneg
  let K (z : Bit × Bit) := Matrix.single z.1 z.2 (1 : ℂ)* S z.1
  have hk (z : Bit × Bit) :
      (K z)ᴴ = S z.1*Matrix.single z.2 z.1 1 := by
    simp [K,Matrix.conjTranspose_mul,Matrix.conjTranspose_single,hS]
  have hk' : ∑ z, (K z)ᴴ * K z = 1 := by
    have hz (z : Bit × Bit) : (K z)ᴴ*K z = S z.1 * Matrix.single z.2 z.2 (1:ℂ) * S z.1 := by
      rw [hk]
      change (S z.1 * Matrix.single z.2 z.1 (1:ℂ)) * (Matrix.single z.1 z.2 (1:ℂ) * S z.1) = _
      rw [← Matrix.mul_assoc,Matrix.mul_assoc (S z.1),Matrix.single_mul_single_same,mul_one]
    simp_rw [hz]
    rw [Fintype.sum_prod_type]
    have hf (a : Bit) :
        (∑ k : Bit, S a*Matrix.single k k (1:ℂ)*S a) = E a := by
      rw [← Matrix.sum_mul,← Matrix.mul_sum,Matrix.sum_single_one,mul_one,hSq]
    simpa only [hf] using hsum
  obtain ⟨C,hC⟩ := finite_kraus_quantum_channel K hk'
  refine ⟨C,fun X i j => ?_⟩
  unfold rawEntry
  rw [hC]
  have hterm (z : Bit × Bit) :
      K z * X * (K z)ᴴ = Matrix.single z.1 z.1 ((S z.1*X*S z.1) z.2 z.2) := by
    rw [hk]
    dsimp only [K]
    calc
      _ = Matrix.single z.1 z.2 1 * (S z.1*X*S z.1) * Matrix.single z.2 z.1 1 := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.single_mul_mul_single, one_mul,mul_one]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_vary_single]
  have hsumTr (a : Bit) :
      (∑ k : Bit, (S a*X*S a) k k) = (E a*X).trace := by
    change (S a*X*S a).trace = _
    rw [Matrix.trace_mul_cycle,hSq]
  simp_rw [hsumTr,Matrix.sum_apply,Matrix.single_apply]
  by_cases h : i=j
  · subst j
    simp
  · fin_cases i <;> fin_cases j <;> simp_all

private lemma probe_trace_pairing (F : M₂) (i j : Bit) :
    (F * Matrix.single i j 1).trace = F j i := by
  rw [Matrix.trace_mul_comm,Matrix.trace_single_mul]
  simp

private def wa (a b : ℝ) (i : Bit) : ℝ := if i=0 then a else b

private def WV (a b : ℝ) : M₂ := Matrix.diagonal (fun i => (Real.sqrt (wa a b i) : ℝ))

private def wc (a b : ℝ) (X : M₂) : M₂ := WV a b * X * WV a b

private def wket (a b : ℝ) (p : Bit × Bit) : ℂ := if p.1=p.2 then (wa a b p.1 : ℂ) else 0

def wresource (a b : ℝ) : Matrix (Bit × Bit) (Bit × Bit) ℂ :=
  Matrix.vecMulVec (wket a b) (star (wket a b))

private lemma diag_wa (a b : ℝ) : DD a b = Matrix.diagonal (fun i => (wa a b i : ℂ)) := by
  unfold DD
  congr 1
  funext i
  fin_cases i <;> simp [wa]

private lemma wa_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Bit) : 0 ≤ wa a b i := by
  unfold wa; split <;> assumption

private lemma WV_self (a b : ℝ) : (WV a b)ᴴ = WV a b := by simp [WV,Matrix.diagonal_conjTranspose]

private lemma WV_square {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : WV a b * WV a b = DD a b := by
  simp_rw [WV,Matrix.diagonal_mul_diagonal,← Complex.ofReal_mul,Real.mul_self_sqrt (wa_nonneg ha hb _)]
  rw [← diag_wa]

private lemma wc_psd (a b : ℝ) (X : M₂) (hX : X.PosSemidef) : (wc a b X).PosSemidef := by
  simpa only [WV_self,wc] using hX.conjTranspose_mul_mul_same (WV a b)

private lemma wc_compl {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (X : M₂) :
    DD a b-wc a b X = wc a b (1-X) := by
  simp [wc,mul_sub,sub_mul,WV_square ha hb]

private lemma wc_sample_complex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (X Y : M₂) :
    (wc a b X * wc a b Y).trace =
    (∑ i : Bit, ∑ j : Bit, ((wa a b i : ℂ)*(wa a b j : ℂ)) * X i j * Y j i) := by
  unfold wc
  calc
    _ = (WV a b*X*(WV a b*WV a b)*Y*WV a b).trace := by
      congr 1; simp only [Matrix.mul_assoc]
    _ = ((WV a b*WV a b)*X*(WV a b*WV a b)*Y).trace := by
      rw [Matrix.trace_mul_comm _ (WV a b)]; congr 1; simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [WV_square ha hb,diag_wa]
      simp only [trace, diag]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma weighted_born_hits_complex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (L R : QuantumChannel Bit Bit) (u v : Bit) :
    tensorRawAction L R (wresource a b) (u,v) (u,v) =
      (wc a b (probe L u) * wc a b ((probe R v)ᵀ)).trace := by
  rw [wc_sample_complex ha hb]
  change (∑ i : Bit, ∑ j : Bit, ∑ k : Bit, ∑ l : Bit,
    wresource a b (i,k) (j,l) * rawEntry L (Matrix.single i j 1) u u *
      rawEntry R (Matrix.single k l 1) v v) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold wresource
  simp only [Matrix.vecMulVec_apply,wket, Pi.star_apply,probe,Matrix.transpose_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private lemma weighted_born_hits {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (L R : QuantumChannel Bit Bit) (u v : Bit) :
    (tensorRawAction L R (wresource a b) (u,v) (u,v)).re =
      tr (wc a b (probe L u) * wc a b ((probe R v)ᵀ)) :=
  congrArg Complex.re (weighted_born_hits_complex ha hb L R u v)

private lemma diag_channel_tensor (L R : QuantumChannel Bit Bit) (X : Matrix (Bit × Bit) (Bit × Bit) ℂ)
    (hL : ∀ A i j, i ≠ j → rawEntry L A i j = 0)
    (hR : ∀ A i j, i ≠ j → rawEntry R A i j = 0) :
    ∀ i j, i ≠ j → tensorRawAction L R X i j = 0 := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  change (∑ a : Bit, ∑ b : Bit, ∑ u : Bit, ∑ v : Bit,
    X (a,u) (b,v) * rawEntry L (Matrix.single a b 1) i k *
      rawEntry R (Matrix.single u v 1) j l) = _
  by_cases hi : i=k
  · have hj : j ≠ l := by intro he; exact h (Prod.ext hi he)
    simp [hR _ _ _ hj]
  · simp [hL _ _ _ hi]

private def WU (a b : ℝ) : M₂ := Matrix.diagonal (fun i => ((Real.sqrt (wa a b i))⁻¹ : ℝ))

private lemma WU_self (a b : ℝ) : (WU a b)ᴴ = WU a b := by simp [WU,Matrix.diagonal_conjTranspose]

private lemma WV_WU {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : WV a b * WU a b = 1 := by
  rw [WV,WU,Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext i
  have h : 0 < wa a b i := by unfold wa; split <;> assumption
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h).ne',Complex.ofReal_one]

private lemma WU_WV {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : WU a b * WV a b = 1 := by
  rw [WU,WV,Matrix.diagonal_mul_diagonal]
  have h := WV_WU ha hb
  rw [WU,WV,Matrix.diagonal_mul_diagonal] at h
  simpa only [mul_comm] using h

private theorem weighted_effect_attains {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (H : M₂)
    (hH : H.PosSemidef) (hC : (DD a b-H).PosSemidef) :
    ∃ L R : QuantumChannel Bit Bit,
      (∀ A i j, i ≠ j → rawEntry L A i j = 0) ∧
      (∀ A i j, i ≠ j → rawEntry R A i j = 0) ∧
      (tensorRawAction L R (wresource a b) (0,0) (0,0)).re = quad H ∧
      (tensorRawAction L R (wresource a b) (1,1) (1,1)).re = quad (DD a b-H) := by
  let U := WU a b
  let E := U*H*U
  let T (i : Bit) : M₂ := if i=0 then E else 1-E
  have heu : E.PosSemidef := by
    change (WU a b*H*WU a b).PosSemidef
    simpa only [WU_self] using hH.conjTranspose_mul_mul_same (WU a b)
  have hDel : U * (DD a b) * U = 1 := by
    rw [← WV_square ha.le hb.le]
    change WU a b * (WV a b * WV a b) * WU a b = 1
    rw [← Matrix.mul_assoc, WU_WV ha hb,one_mul,WV_WU ha hb]
  have hcomp : (1-E).PosSemidef := by
    have h := hC.conjTranspose_mul_mul_same U
    change (Uᴴ * (DD a b - H) * U).PosSemidef at h
    rw [show Uᴴ=U from WU_self _ _,mul_sub,sub_mul,hDel] at h
    exact h
  have ht (i : Bit) : (T i).PosSemidef := by fin_cases i <;> simp [T,heu,hcomp]
  have hsum : ∑ i, T i = 1 := by simp [Fin.sum_univ_two,T]
  obtain ⟨L,hL⟩ := binary_effect_channels (fun i => (T i)ᵀ) (fun i => (ht i).transpose)
    (by rw [← Matrix.transpose_sum, hsum, Matrix.transpose_one])
  obtain ⟨R,hR⟩ := binary_effect_channels T ht hsum
  have hLC (i : Bit) : probe L i = T i := by
    ext x y
    simp [probe,hL,probe_trace_pairing]
  have hRC (i : Bit) : (probe R i)ᵀ = T i := by
    ext x y
    simp [probe,hR,probe_trace_pairing]
  have hW : wc a b E = H := by
    unfold wc E U
    calc
      _ = (WV a b*WU a b) * H * (WU a b*WV a b) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [WU_WV ha hb,WV_WU ha hb,one_mul,mul_one]
  have hCW : wc a b (1-E) = DD a b - H := by rw [← wc_compl ha.le hb.le,hW]
  refine ⟨L,R,fun A i j h => by rw [hL,ite_eq_right h],
    fun A i j h => by rw [hR,ite_eq_right h],?_,?_⟩
  · rw [weighted_born_hits ha.le hb.le,hLC,hRC,show T 0=E by simp [T],hW]
    rfl
  · rw [weighted_born_hits ha.le hb.le,hLC,hRC,show T 1=1-E by simp [T],hCW]
    rfl

private lemma quad_DD (a b : ℝ) : quad (DD a b) = a^2+b^2 := by
  simp [quad,tr,DD,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
    ← Complex.ofReal_mul,pow_two]

private lemma min_l1 (x y : ℝ) : |x-y| = x+y-2*min x y := by
  rcases le_or_gt x y with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h.le), min_eq_right h.le]; ring

def binaryTarget (w : ℝ) (p : Bit × Bit) : ℝ :=
  if p.1=p.2 then (if p.1=0 then w else 1-w) else 0

private def wtOutcome (a b : ℝ) (L R : QuantumChannel Bit Bit) (p : Bit × Bit) : ℝ :=
  (tensorRawAction L R (wresource a b) p p).re

private lemma complex_trace_psd_pair {X Y : M₂} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X*Y).trace := by
  let S := CFC.sqrt X
  have hs : Sᴴ = S := (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
  have hs2 : S*S = X := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have h := (hY.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hs,Matrix.trace_mul_cycle,hs2] at h
  exact h

private lemma actual_weighted_prob {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (L R : QuantumChannel Bit Bit) (i j : Bit) :
    0≤tensorRawAction L R (wresource a b) (i,j) (i,j) := by
  rw [weighted_born_hits_complex ha hb]
  exact complex_trace_psd_pair (wc_psd _ _ _ (probe_psd L i)) (wc_psd _ _ _ (probe_psd R j).transpose)

private lemma wtOutcome_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (L R : QuantumChannel Bit Bit) (p : Bit × Bit) :
    0≤wtOutcome a b L R p := (Complex.nonneg_iff.mp (actual_weighted_prob ha hb L R p.1 p.2)).1

private lemma tr_mul_add (X Y Z : M₂) : tr (X*(Y+Z))=tr (X*Y)+tr (X*Z) := by rw [mul_add,tr_add]

private lemma tr_add_mul (X Y Z : M₂) : tr ((X+Y)*Z)=tr (X*Z)+tr (Y*Z) := by rw [add_mul,tr_add]

private lemma wtOutcome_total {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hn : a^2+b^2=1) (L R : QuantumChannel Bit Bit) :
    ∑ p, wtOutcome a b L R p = 1 := by
  have hw (X Y : M₂) : wc a b X + wc a b Y = wc a b (X+Y) := by simp only [wc,mul_add,add_mul]
  have hp : (probe R 0)ᵀ+(probe R 1)ᵀ=1 := by
    rw [← Matrix.transpose_add,probe_total,Matrix.transpose_one]
  rw [Fintype.sum_prod_type]
  simp only [wtOutcome,weighted_born_hits ha hb,Fin.sum_univ_two]
  rw [← tr_mul_add, ← tr_mul_add, ← tr_add_mul,hw,hw,probe_total,hp]
  have h : wc a b 1 = DD a b := by simp [wc,WV_square ha hb]
  rw [h,show tr (DD a b*DD a b)=1 from (quad_DD a b).trans hn]

private lemma wtOutcome_diagonal {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (L R : QuantumChannel Bit Bit)
    (hL : ∀ A i j, i ≠ j → rawEntry L A i j = 0)
    (hR : ∀ A i j, i ≠ j → rawEntry R A i j = 0) :
    tensorRawAction L R (wresource a b) = Matrix.diagonal (fun p => (wtOutcome a b L R p : ℂ)) := by
  ext i j
  by_cases hh : i=j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    have h := (Complex.nonneg_iff.mp (actual_weighted_prob ha hb L R i.1 i.2)).2
    apply Complex.ext
    · simp [wtOutcome]
    · simpa only [Complex.ofReal_im] using h.symm
  · rw [Matrix.diagonal_apply_ne _ hh]
    exact diag_channel_tensor L R _ hL hR _ _ hh

private lemma weighted_density {a b : ℝ} (hn : a^2+b^2=1) :
    ∃ ρ : DensityState (Bit × Bit), CStarMatrix.ofMatrix.symm ρ.val = wresource a b := by
  have hp : (wresource a b).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  refine ⟨⟨CStarMatrix.ofMatrix _, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp.nonneg, ?_⟩,rfl⟩
  change (wresource a b).trace = 1
  have h : (wresource a b).trace = ((a^2+b^2 : ℝ):ℂ) := by
    norm_num [wresource,wket,Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Fin.sum_univ_two,
      Matrix.vecMulVec_apply,Pi.star_apply,wa, pow_two, Complex.ofReal_add]
  rw [h,hn,Complex.ofReal_one]

private lemma arbitrary_weighted_error_lower {a b w : ℝ} (hb : 0<b) (hba : b≤a)
    (hn : a^2+b^2=1) (hw₀ : 0≤w) (hw₁ : w≤1/2) (L R : QuantumChannel Bit Bit) :
    errorFormula a b w ≤ 2*(1-capped w (wtOutcome a b L R (0,0)) (wtOutcome a b L R (1,1))) := by
  have ha : 0<a := hb.trans_le hba
  let D := DD a b
  let X := wc a b (probe L 0)
  let Y := wc a b ((probe R 0)ᵀ)
  have hX := wc_psd a b _ (probe_psd L 0)
  have hY := wc_psd a b _ (probe_psd R 0).transpose
  have aux (C : QuantumChannel Bit Bit) : 1-probe C 0 = probe C 1 := by
    rw [sub_eq_iff_eq_add,add_comm,probe_total]
  have hXc : D-X = wc a b (probe L 1) := by
    dsimp [D,X]
    rw [wc_compl ha.le hb.le,aux]
  have hYc : D-Y = wc a b ((probe R 1)ᵀ) := by
    dsimp [D,Y]
    rw [wc_compl ha.le hb.le,← Matrix.transpose_one (n:=Bit) (α:=ℂ),← Matrix.transpose_sub,aux]
  have hXcP : (D-X).PosSemidef := hXc ▸ wc_psd a b _ (probe_psd L 1)
  have hYcP : (D-Y).PosSemidef := hYc ▸ wc_psd a b _ (probe_psd R 1).transpose
  let H := midpoint X Y
  have hH : H.PosSemidef := midpoint_psd hX hY
  have hM : D-H = midpoint (D-X) (D-Y) := by
    ext i j; simp [H,midpoint,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply]; ring
  have hcP : (DD a b-H).PosSemidef := hM ▸ midpoint_psd hXcP hYcP
  have h₀ : wtOutcome a b L R (0,0) ≤ quad H := by
    exact (weighted_born_hits ha.le hb.le L R 0 0).le.trans (pair_hits_le hX.isHermitian hY.isHermitian)
  have h₁ : wtOutcome a b L R (1,1) ≤ quad (D-H) := by
    rw [hM]
    exact (weighted_born_hits ha.le hb.le L R 1 1).le.trans
      ((hXc ▸ hYc ▸ pair_hits_le hXcP.isHermitian hYcP.isHermitian) :
       tr (wc a b (probe L 1)*wc a b ((probe R 1)ᵀ)) ≤ quad (midpoint (D-X) (D-Y)))
  let β : Benchmark := ⟨a,b,w,hb,hba,hn,hw₀,hw₁⟩
  obtain ⟨_,_,_,_,hopt⟩ := WeightedBinaryEffectOptimum.result β
  have hcap := add_le_add (min_le_min_left w h₀) (min_le_min_left (1-w) h₁)
  exact (hopt H hH hcP).trans (by unfold capped at *; linarith)


private lemma binaryTarget_nonneg {w : ℝ} (h₀ : 0≤w) (h₁ : w≤1) (p : Bit × Bit) : 0≤binaryTarget w p := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [binaryTarget,h₀,sub_nonneg.mpr h₁]

private lemma binaryTarget_unit (w : ℝ) : ∑ p, binaryTarget w p = 1 := by
  simp [Fintype.sum_prod_type,Fin.sum_univ_two,binaryTarget]

private lemma weighted_l1 (w : ℝ) (f : Bit × Bit → ℝ) (hf : ∀ p, 0≤f p) (hs : ∑ p, f p = 1) :
    ∑ p, |f p-binaryTarget w p| = 2*(1-capped w (f (0,0)) (f (1,1))) := by
  have hm : (∑ p, min (binaryTarget w p) (f p)) = capped w (f (0,0)) (f (1,1)) := by
    simp [Fintype.sum_prod_type,Fin.sum_univ_two,binaryTarget,capped,
      min_eq_left (hf (0,1)),min_eq_left (hf (1,0))]
  simp_rw [min_l1,min_comm (f _)]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hs,binaryTarget_unit,hm]
  ring

private lemma weighted_native_lower {A : Type} [Fintype A] [DecidableEq A] (t : A)
    {a b w : ℝ} (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1)
    (hw₀ : 0≤w) (hw₁ : w≤1/2)
    (Q T : QuantumChannel A (Bit × Bit)) (L R : QuantumChannel Bit Bit)
    (hq : rawEntry Q (Matrix.single t t 1) = tensorRawAction L R (wresource a b))
    (ht : rawEntry T (Matrix.single t t 1) = Matrix.diagonal (fun p => (binaryTarget w p : ℂ))) :
    errorFormula a b w ≤ diamondDistance Q T := by
  let rho := basisDensity ((0 : Fin 1),t)
  let X := CStarMatrix.ofMatrix.symm (referenceState Q rho).val -
    CStarMatrix.ofMatrix.symm (referenceState T rho).val
  have hp (σ : DensityState (Fin 1 × (Bit × Bit))) :
      (CStarMatrix.ofMatrix.symm σ.val).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.prop.1).posSemidef
  have hx : X.IsHermitian := (hp _).isHermitian.sub (hp _).isHermitian
  have he : (∑ i : Fin 1 × (Bit × Bit), |(X i i).re|) = ∑ p, |wtOutcome a b L R p-binaryTarget w p| := by
    rw [Fintype.sum_prod_type,Fin.sum_univ_one]
    apply Finset.sum_congr rfl
    intro i _
    change |diagBorn Q rho i-diagBorn T rho i| = _
    rw [diagBorn_basis Q t i,diagBorn_basis T t i]
    unfold basisBorn wtOutcome
    rw [hq,ht,Matrix.diagonal_apply_eq,Complex.ofReal_re]
  have ha := hb.le.trans hba
  have hw := weighted_l1 w _ (wtOutcome_nonneg ha hb.le L R) (wtOutcome_total ha hb.le hn L R)
  calc
    _ ≤ ∑ i : Fin 1 × (Bit × Bit), |(X i i).re| := by
      rw [he,hw]; exact arbitrary_weighted_error_lower hb hba hn hw₀ hw₁ L R
    _ ≤ traceNorm X := diagonal_l1_le_traceNorm X hx
    _ ≤ _ := referenceError_le_diamond Q T rho

private theorem weighted_binary_exact {A : Type} [Fintype A] [DecidableEq A] (t : A)
    (a b w : ℝ) (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1) (hw₀ : 0≤w) (hw₁ : w≤1/2) :
    ∃ (ρ : DensityState (Bit × Bit)) (L R : QuantumChannel Bit Bit) (Q T : QuantumChannel A (Bit × Bit)),
      CStarMatrix.ofMatrix.symm ρ.val = wresource a b ∧
      (∀ X, rawEntry Q X = X.trace • tensorRawAction L R (CStarMatrix.ofMatrix.symm ρ.val)) ∧
      (∀ X, rawEntry T X = X.trace • Matrix.diagonal (fun p => (binaryTarget w p : ℂ))) ∧
      diamondDistance Q T = errorFormula a b w ∧
      ∀ (E : QuantumChannel A (Bit × Bit)) (U V : QuantumChannel Bit Bit),
        rawEntry E (Matrix.single t t 1) = tensorRawAction U V (CStarMatrix.ofMatrix.symm ρ.val) →
        errorFormula a b w ≤ diamondDistance E T := by
  let _ : Nonempty A := ⟨t⟩
  have ha := hb.le.trans hba
  obtain ⟨ρ,hρ⟩ := weighted_density hn
  let β : Benchmark := ⟨a,b,w,hb,hba,hn,hw₀,hw₁⟩
  obtain ⟨H,hH,hC,hval,_⟩ := WeightedBinaryEffectOptimum.result β
  obtain ⟨L,R,hL,hR,m₀,m₁⟩ := weighted_effect_attains (hb.trans_le hba) hb H hH hC
  let f := wtOutcome a b L R
  have hf := wtOutcome_nonneg ha hb.le L R
  have hs := wtOutcome_total ha hb.le hn L R
  obtain ⟨Q,hQ⟩ := diagonal_replacement_exists (A := A) f hf hs
  obtain ⟨T,hT⟩ := diagonal_replacement_exists (A := A) (binaryTarget w)
    (binaryTarget_nonneg hw₀ (by linarith)) (binaryTarget_unit w)
  refine ⟨ρ,L,R,Q,T,hρ,fun X => ?_,hT,?_,fun E U V he => ?_⟩
  · rw [hρ,hQ,wtOutcome_diagonal ha hb.le L R hL hR]
  · rw [replacer_diamond_exact _ _ _ _ hQ hT,Matrix.diagonal_sub]
    simp_rw [← Complex.ofReal_sub,traceNorm_diagonal_real]
    rw [weighted_l1 w f hf hs]
    rw [show f (0,0) = quad H from m₀,
      show f (1,1) = quad (DD a b-H) from m₁]
    exact hval
  · rw [hρ] at he
    apply weighted_native_lower t hb hba hn hw₀ hw₁ E T U V he
    rw [hT,Matrix.trace_single_eq_same,one_smul]

theorem result {A : Type} [Fintype A] [DecidableEq A] (t : A) (β : Benchmark) :
    ∃ (ρ : DensityState (Bit × Bit)) (L R : QuantumChannel Bit Bit) (Q T : QuantumChannel A (Bit × Bit)),
      CStarMatrix.ofMatrix.symm ρ.val = wresource β.a β.b ∧
      (∀ X, rawEntry Q X = X.trace • tensorRawAction L R (CStarMatrix.ofMatrix.symm ρ.val)) ∧
      (∀ X, rawEntry T X = X.trace • Matrix.diagonal (fun p => (binaryTarget β.w p : ℂ))) ∧
      diamondDistance Q T = exactError β ∧
      ∀ (E : QuantumChannel A (Bit × Bit)) (U V : QuantumChannel Bit Bit),
        rawEntry E (Matrix.single t t 1) = tensorRawAction U V (CStarMatrix.ofMatrix.symm ρ.val) →
        exactError β ≤ diamondDistance E T :=
  weighted_binary_exact t β.a β.b β.w β.bPos β.ordered β.normalized β.wNonneg β.wHalf

#print axioms result
end
end D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact
