/- GID: D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation
   mirror-E: none(waiver:external-counterexample)
   anchors: [lake/module/D5.S3.Quantum.Matrix.BuresWassersteinTransport]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.claim; result=D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.result; claim=D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation.claim
   digest: The specified positive weighted matrix means fail entrywise spectral comparison. -/

import D5.S3.Quantum.Matrix.BuresWassersteinTransport
import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation

/-!
Ma–Zhang revision2, Theorem (entrywise), issue #29594, CC BY 4.0.
Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, Singapore.
The exact weights are (3/4,1/4). This concerns the actual CFC logarithmic
mean and actual positive definite global argmin, not a surrogate mean.
The dual characterization is attributed to Bhatia–Jain–Lim. Their weak
log-majorization theorem and norm/weak-majorization conjecture are intact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Unitary
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open D5.S3.Quantum.Matrix.BuresWassersteinTransport
open private cfc_conjugate_diagonal
  from D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.HwangKimWeightedSpectralRefutation

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private def g : ℝ := Real.sqrt 3
private def h : ℝ := Real.sqrt 399
private def A : Mat := !![256,0;0,1]
private def B : Mat := !![(13/4:ℂ), ((3*g/4:ℝ):ℂ); ((3*g/4:ℝ):ℂ), (7/4:ℂ)]
private def K : Mat :=
  !![((9/(4*h):ℝ):ℂ), ((2*g/(4*h):ℝ):ℂ);
     ((2*g/(4*h):ℝ):ℂ), ((90/(4*h):ℝ):ℂ)]
private def M : Mat := (1/4:ℝ) • ((3:ℝ) • 1 + K)
private def W : Mat := M*A*M
private def weights : Fin 2 → ℝ := ![3/4,1/4]
private def H : Mat := !![(51/8:ℂ), ((g/8:ℝ):ℂ); ((g/8:ℝ):ℂ), (1/8:ℂ)]
private def R : Mat := !![((g/2:ℝ):ℂ), -1/2; 1/2, ((g/2:ℝ):ℂ)]

private theorem A_pos : A.PosDef :=
  SpectralPower.posDef_two 256 0 1 (by norm_num) (by norm_num)

private theorem B_pos : B.PosDef := by
  have hg : g^2=3 := Real.sq_sqrt (by norm_num)
  simpa [B,Complex.ofReal_div] using
    SpectralPower.posDef_two (13/4) (3*g/4) (7/4) (by norm_num) (by nlinarith [hg])

private theorem K_pos : K.PosDef := by
  have hh : 0<h := Real.sqrt_pos.mpr (by norm_num)
  have hg : g^2=3 := Real.sq_sqrt (by norm_num)
  apply SpectralPower.posDef_two (9/(4*h)) (2*g/(4*h)) (90/(4*h))
  · positivity
  · have hn : (0:ℝ)<9*90-(2*g)^2 := by nlinarith
    convert div_pos hn (sq_pos_of_pos (show 0<4*h by positivity)) using 1 <;>
      field_simp <;> ring

private theorem K_transport : K*A*K=B := by
  have hh : (h:ℂ)^2=399 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤399))
  have hg : (g:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  have hh0 : (h:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<399))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K,A,B,Matrix.mul_apply,Fin.sum_univ_two,Complex.ofReal_div,Complex.ofReal_mul] <;>
    field_simp [hh0] <;> ring_nf <;> simp [hh,hg] <;> ring

private theorem M_pos : M.PosDef :=
  ((Matrix.PosDef.one.smul (by norm_num : (0:ℝ)<3)).add K_pos).smul (by norm_num)

private theorem W_pos : W.PosDef := by
  simpa only [W,star_eq_conjTranspose,M_pos.isHermitian.eq] using
    M_pos.isUnit.posDef_star_right_conjugate_iff.mpr A_pos

private theorem actual_W : wassersteinBarycenter weights ![A,B] = W := by
  let T : Mat := M⁻¹
  let V : Mat := K*T
  have hT : T.PosDef := M_pos.inv
  have hTM : T*M=1 := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp M_pos.isUnit)
  have hMT : M*T=1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp M_pos.isUnit)
  have hK : K=(4:ℝ) • M-(3:ℝ) • 1 := by dsimp [M]; module
  have hKT : Commute K T := by
    change K*T=T*K
    rw [hK]
    simp only [sub_mul,mul_sub,smul_mul_assoc,Matrix.mul_smul,hTM,hMT,one_mul,mul_one]
  have hV : V.PosDef := ((K_pos.isStrictlyPositive.commute_iff hT.isStrictlyPositive).1 hKT).posDef
  have ht : T*W*T=A := by
    change T*(M*A*M)*T=A
    calc
      _ = (T*M)*A*(M*T) := by noncomm_ring
      _ = A := by rw [hTM,hMT]; simp
  have hv : V*W*V=B := by
    change K*T*(M*A*M)*(K*T)=B
    calc
      _ = K*T*(M*A*M)*(T*K) := by rw [hKT.eq]
      _ = K*(T*M)*A*(M*T)*K := by noncomm_ring
      _ = B := by rw [hTM,hMT]; simpa using K_transport
  have hb : (3/4:ℝ) • T+(1/4:ℝ) • V=1 := by
    dsimp [V]
    rw [hK]
    simp only [sub_mul,smul_mul_assoc,hMT,one_mul,smul_sub,smul_smul]
    module
  exact (finite_barycenter_of_dual weights ![A,B] ![T,V]
    (by intro j; fin_cases j <;> norm_num [weights])
    (by norm_num [weights,Fin.sum_univ_two])
    (by intro j; fin_cases j; exact A_pos; exact B_pos) W_pos
    (by intro j; fin_cases j; exact hT; exact hV)
    (by intro j; fin_cases j; exact ht; exact hv)
    (by simpa [weights,Fin.sum_univ_two] using hb)).2.2

private theorem R_unitary : R ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hg : (g:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,map_ofNat,Complex.ofReal_div] <;>
    ring_nf <;> simp [hg] <;> ring

private theorem B_diagonal : B=R*diagonal ![(4:ℂ),1]*Rᴴ := by
  have hg : (g:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B,R,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,
      map_ofNat,Matrix.diagonal_apply,Complex.ofReal_div,Complex.ofReal_mul] <;>
    ring_nf <;> simp [hg] <;> ring

private theorem log_sum :
    ∑ j, weights j • cfc Real.log (![A,B] j) = Real.log 2 • H := by
  have ha : A=diagonal (fun i => ((![256,1]:Fin 2 → ℝ) i:ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A,Matrix.diagonal_apply]
  have hla : cfc Real.log A=diagonal ![((8*Real.log 2:ℝ):ℂ),0] := by
    rw [ha,Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
    have hl256 : Real.log 256=8*Real.log 2 := by
      rw [show (256:ℝ)=2^8 by norm_num,Real.log_pow]; norm_num
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply,hl256]
  have hlb := cfc_conjugate_diagonal Real.log ⟨R,R_unitary⟩ (![4,1]:Fin 2 → ℝ)
  change cfc Real.log (R*diagonal ![(4:ℂ),1]*Rᴴ) =
    R*diagonal (fun i => ((Real.log ((![4,1]:Fin 2 → ℝ) i):ℝ):ℂ))*Rᴴ at hlb
  rw [← B_diagonal] at hlb
  have hl4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [Fin.sum_univ_two]
  change (3/4:ℝ) • cfc Real.log A+(1/4:ℝ) • cfc Real.log B=Real.log 2 • H
  rw [hla,hlb]
  have hg : (g:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weights,H,R,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.diagonal_apply,
      Matrix.conjTranspose_apply,map_ofNat,hl4,Complex.ofReal_div,Complex.ofReal_mul] <;>
      ring_nf <;> simp [hg] <;> ring

private theorem H_pos : H.PosDef := by
  have hg : g^2=3 := Real.sq_sqrt (by norm_num)
  simpa [H,Complex.ofReal_div] using
    SpectralPower.posDef_two (51/8) (g/8) (1/8) (by norm_num) (by nlinarith [hg])

private theorem H_lower : (H-(1/10:ℝ) • 1).PosDef := by
  have hg : g^2=3 := Real.sq_sqrt (by norm_num)
  have hp := SpectralPower.posDef_two (251/40) (g/8) (1/40)
    (by norm_num) (by nlinarith [hg])
  convert hp using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H,Matrix.one_apply,Complex.ofReal_div]

private def L : Mat := cfc Real.exp (Real.log 2 • H)

private theorem actual_L : logEuclidean weights ![A,B]=L := by
  rw [logEuclidean,log_sum]
  rfl

private theorem L_lower : (L-(107/100:ℝ) • 1).PosDef := by
  let Z : Mat := Real.log 2 • H
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hZ : Z.PosDef := H_pos.smul hl
  have hz : algebraMap ℝ Mat (Real.log 2/10) ≤ Z := by
    have hs := smul_le_smul_of_nonneg_left
      (sub_nonneg.mp H_lower.posSemidef.nonneg) hl.le
    simpa only [Algebra.algebraMap_eq_smul_one,smul_smul,div_eq_mul_inv,one_mul] using hs
  have hlog : Real.log (107/100:ℝ)<Real.log 2/10 := by
    have hp : (107/100:ℝ)^10<2 := by norm_num
    have hh := Real.log_lt_log (by norm_num : (0:ℝ)<(107/100)^10) hp
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hc : IsStrictlyPositive (cfc (fun x : ℝ => Real.exp x-107/100) Z) := by
    apply (cfc_isStrictlyPositive_iff _ _ (by fun_prop) hZ.isHermitian.isSelfAdjoint).mpr
    intro x hx
    have hs := (algebraMap_le_iff_le_spectrum hZ.isHermitian.isSelfAdjoint).mp hz x hx
    have he : (107/100:ℝ)<Real.exp x := by
      rw [← Real.exp_log (by norm_num : (0:ℝ)<107/100)]
      exact Real.exp_lt_exp.mpr (lt_of_lt_of_le hlog hs)
    linarith
  have heq : cfc (fun x : ℝ => Real.exp x-107/100) Z = L-(107/100:ℝ) • 1 := by
    rw [cfc_sub Real.exp (fun _ : ℝ => (107/100:ℝ)) Z,
      cfc_const (107/100:ℝ) Z hZ.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
    rfl
  rw [heq] at hc
  exact hc.posDef

private theorem L_pos : L.PosDef := by
  have hp := L_lower.add (Matrix.PosDef.one.smul (by norm_num : (0:ℝ)<107/100))
  simpa using hp

private def d : ℝ := 73/8+297/(4*h)

private theorem W_trace : W.trace.re=1159/8+3591/(16*h) := by
  have haff : W=(1/16:ℝ) • ((9:ℝ) • A+(3:ℝ) • (K*A+A*K)+B) := by
    rw [← K_transport]
    dsimp [W,M]
    simp only [add_mul,mul_add,smul_mul_assoc,Matrix.mul_smul,one_mul,mul_one,
      smul_smul,smul_add]
    module
  rw [haff]
  norm_num [A,B,K,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.vecMul,dotProduct,
    Fin.sum_univ_two,← Complex.ofReal_mul,← Complex.ofReal_div]
  ring

private theorem W_det : W.det=(d^2:ℝ) := by
  have hg : (g:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  have hh : (h:ℂ)^2=399 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤399))
  have hh0 : (h:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<399))
  have hmd : M.det=((d/16:ℝ):ℂ) := by
    simp [M,K,d,Matrix.det_fin_two,Complex.ofReal_div,Complex.ofReal_add,
      Complex.ofReal_mul]
    field_simp [hh0]
    ring_nf
    simp [hg,hh]
    ring
  rw [W,Matrix.det_mul,Matrix.det_mul,hmd]
  norm_num [A,Matrix.det_fin_two,Complex.ofReal_div,Complex.ofReal_pow]
  ring

private theorem W_polynomial : (107/100:ℝ)^2-W.trace.re*(107/100)+W.det.re<0 := by
  have hlow : (1997/100:ℝ)<h := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hhigh : h<(999/50:ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hh : 0<h := lt_trans (by norm_num) hlow
  rw [W_trace,W_det]
  simp only [Complex.ofReal_re]
  change (107/100:ℝ)^2-(1159/8+3591/(16*h))*(107/100)+(73/8+297/(4*h))^2<0
  calc
    _ ≤ (107/100:ℝ)^2-(1159/8+3591/(16*(999/50:ℝ)))*(107/100)+
        (73/8+297/(4*(1997/100:ℝ)))^2 := by gcongr
    _ < 0 := by norm_num

/-- Entrywise comparison uses decreasingly sorted Hermitian eigenvalues. -/
def SpectralOrder {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ hX : X.IsHermitian, ∃ hY : Y.IsHermitian,
    ∀ i : Fin (Fintype.card (Fin m)), hX.eigenvalues₀ i ≤ hY.eigenvalues₀ i

/-- The suggested entrywise strengthening, for the actual two means. -/
def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (n : ℕ), 2 ≤ n → ∀ w : Fin n → ℝ,
    (∀ j, 0 < w j) → (∑ j, w j) = 1 →
    ∀ A : Fin n → Matrix (Fin m) (Fin m) ℂ, (∀ j, (A j).PosDef) →
      SpectralOrder (logEuclidean w A) (wassersteinBarycenter w A)

private theorem sorted_pos {X : Mat} (hp : X.PosDef) (i : Fin 2) :
    0<hp.isHermitian.eigenvalues₀ i := by
  let e : Fin (Fintype.card (Fin 2)) ≃ Fin 2 :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))
  have hh := hp.eigenvalues_pos (e i)
  change 0 < hp.isHermitian.eigenvalues₀ (e.symm (e i)) at hh
  exact (congrArg (fun j => 0 < hp.isHermitian.eigenvalues₀ j) (e.symm_apply_apply i)) ▸ hh

private theorem L_min : (107/100:ℝ)<L_pos.isHermitian.eigenvalues₀ 1 := by
  have hs : (L+((-107/100:ℝ):ℂ) • 1).PosDef := by
    convert L_lower using 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply] <;> ring
  have he := LinGProperty.eigenvalues_zero_add_scalar L L_pos.isHermitian (-107/100)
    hs.isHermitian 1
  have hp := sorted_pos hs 1
  linarith [hp,he]

private theorem W_min : W_pos.isHermitian.eigenvalues₀ 1<(107/100:ℝ) := by
  let v := W_pos.isHermitian.eigenvalues₀
  have htr : W.trace.re=v 0+v 1 := by
    rw [W_pos.isHermitian.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_sum,Complex.ofReal_re]
    calc
      _ = ∑ i, W_pos.isHermitian.eigenvalues₀ i :=
        Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm
          W_pos.isHermitian.eigenvalues₀
      _ = _ := Fin.sum_univ_two _
  have hdet : W.det.re=v 0*v 1 := by
    rw [W_pos.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_prod,Complex.ofReal_re]
    calc
      _ = ∏ i, W_pos.isHermitian.eigenvalues₀ i :=
        Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm
          W_pos.isHermitian.eigenvalues₀
      _ = _ := Fin.prod_univ_two _
  have ho : v 1≤v 0 := W_pos.isHermitian.eigenvalues₀_antitone (by decide)
  have hp := W_polynomial
  rw [htr,hdet] at hp
  by_contra hn
  have hn : (107/100:ℝ)≤v 1 := le_of_not_gt hn
  have he := mul_nonneg (sub_nonneg.mpr (le_trans hn ho)) (sub_nonneg.mpr hn)
  nlinarith

/-- The specified weights and inputs refute the entrywise spectral claim.
Both mean identities and the strict rational separating threshold are proved. -/
theorem result : ¬ claim := by
  intro hc
  have hs := hc 2 (by norm_num) 2 (by norm_num) weights
    (by intro j; fin_cases j <;> norm_num [weights])
    (by norm_num [weights,Fin.sum_univ_two]) ![A,B]
    (by intro j; fin_cases j; exact A_pos; exact B_pos)
  rw [actual_L,actual_W] at hs
  obtain ⟨hl,hw,hs⟩ := hs
  have he := hs 1
  have hlow := L_min
  have hhigh := W_min
  have hle : L_pos.isHermitian.eigenvalues₀ 1≤W_pos.isHermitian.eigenvalues₀ 1 := he
  linarith

end D5.S3.Quantum.Matrix.HwangKimWeightedSpectralRefutation
