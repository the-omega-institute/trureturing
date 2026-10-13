/- GID: D5/S3/Quantum/Recovery/PhaseBoundaryCurrentMomentDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundaryCurrentMomentDefect
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Current common-instrument moments and complete-reference defect bounds. -/
import D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Tactic
noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
abbrev Instrument := FlagInstrument (S := Qubit) (J := Qubit) (A := Qubit) (B := Qubit)
/-- Matrix units in the actual received two-dimensional register. -/
def unit (a b : Qubit) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix (Matrix.single a b 1)
/-- Input-first Choi entries of the plus-flag result branch. -/
def choi (Γ : Instrument) (j : Qubit) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  fun p q => Γ.operation j 0 (unit p.1 q.1) p.2 q.2
/-- Diagonal and cross moments are defined from the map, independently of Kraus choices. -/
def A (Γ : Instrument) (j : Qubit) : ℝ := (choi Γ j (0,0) (0,0)).re
def B (Γ : Instrument) (j : Qubit) : ℝ := (choi Γ j (1,0) (1,0)).re
def C (Γ : Instrument) (j : Qubit) : ℝ := (choi Γ j (0,1) (0,1)).re
def D (Γ : Instrument) (j : Qubit) : ℝ := (choi Γ j (1,1) (1,1)).re
def N (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (0,0) (1,0)
def M (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (0,0) (1,1)
def P (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (0,1) (1,1)
def U (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (1,0) (0,1)
def V (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (0,0) (0,1)
def W (Γ : Instrument) (j : Qubit) : ℂ := choi Γ j (1,0) (1,1)
private theorem choi_kraus (Γ : Instrument) (j : Qubit) : ∃ K : (Qubit × Qubit) → Matrix Qubit Qubit ℂ, ∀ p q, choi Γ j p q = ∑ k, K k p.2 p.1 * star (K k q.2 q.1) := by
  obtain ⟨K,hK⟩ := krausRepresentation (Γ.operation j 0)
  refine ⟨K,fun p q => ?_⟩
  have h := congrArg (fun X : Matrix Qubit Qubit ℂ => X p.2 q.2)
    (hK (Matrix.single p.1 q.1 1))
  rcases p with ⟨i,a⟩
  rcases q with ⟨k,b⟩
  fin_cases i <;> fin_cases k <;>
    simpa [choi,unit,Matrix.sum_apply,Matrix.mul_apply,Matrix.single, Matrix.conjTranspose_apply,Fin.sum_univ_two] using h
private theorem choi_positive (Γ : Instrument) (j : Qubit) : (choi Γ j).PosSemidef := by
  obtain ⟨K,hK⟩ := choi_kraus Γ j
  have heq : choi Γ j = ∑ k, Matrix.vecMulVec (fun p => K k p.2 p.1) (star (fun p => K k p.2 p.1)) := by
    ext p q
    simpa [Matrix.sum_apply,Matrix.vecMulVec_apply] using hK p q
  rw [heq]; exact Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg (fun k _ => (Matrix.posSemidef_vecMulVec_self_star _).nonneg))
private theorem psd_gram (Z : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (hZ : Z.PosSemidef) (p q : Qubit × Qubit) : Complex.normSq (Z p q) ≤ (Z p p).re * (Z q q).re := by
  let f : Qubit → Qubit × Qubit := fun i => if i = 0 then p else q; have h := hZ.submatrix f; have hd := h.det_nonneg; have hherm := hZ.1; have hdiag (k : Qubit × Qubit) : (Z k k).im = 0 := by
    have hh := congrArg Complex.im (hherm.apply k k); simp only [Complex.star_def,Complex.conj_im] at hh
    linarith
  have hqp : Z q p = star (Z p q) := by
    exact (hherm.apply q p).symm
  have hr := (Complex.nonneg_iff.mp hd).1; simp only [Matrix.det_fin_two,Matrix.submatrix_apply] at hr; simp only [f,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false] at hr; rw [hqp] at hr
  simp [Complex.mul_re,Complex.sub_re,hdiag,Complex.normSq_apply] at hr ⊢
  nlinarith
private theorem choi_gram (Γ : Instrument) (j : Qubit) (p q : Qubit × Qubit) : Complex.normSq (choi Γ j p q) ≤ (choi Γ j p p).re * (choi Γ j q q).re :=
  psd_gram _ (choi_positive Γ j) p q
private theorem tp_budget (Γ : Instrument) (i k : Qubit) : (∑ j, (choi Γ j (i,0) (k,0) + choi Γ j (i,1) (k,1))) = if i = k then 1 else 0 := by
  have h := Γ.trace_preserving 0 (unit i k)
  fin_cases i <;> fin_cases k <;>
    simpa [Matrix.trace,Matrix.diag,Fin.sum_univ_two,choi,unit,Matrix.single] using h
theorem diagonal_bounds (Γ : Instrument) (j : Qubit) (p : Qubit × Qubit) : 0 ≤ (choi Γ j p p).re ∧ (choi Γ j p p).re ≤ 1 := by
  have hn (j : Qubit) (a : Qubit) : 0 ≤ (choi Γ j (p.1,a) (p.1,a)).re :=
    (Complex.nonneg_iff.mp (choi_positive Γ j).diag_nonneg).1
  have hb := congrArg Complex.re (tp_budget Γ p.1 p.1); simp only [Fin.sum_univ_two,Complex.add_re,ite_true,Complex.one_re] at hb
  rcases p with ⟨i,a⟩
  fin_cases j <;> fin_cases a <;> constructor
  all_goals first | exact hn _ _ | linarith! [hn 0 0,hn 0 1,hn 1 0,hn 1 1]
private theorem moment_budgets (Γ : Instrument) : A Γ 0 + C Γ 0 + A Γ 1 + C Γ 1 = 1 ∧ B Γ 0 + D Γ 0 + B Γ 1 + D Γ 1 = 1 ∧ N Γ 0 + P Γ 0 + N Γ 1 + P Γ 1 = 0 := by
  have h0 := congrArg Complex.re (tp_budget Γ 0 0); have h1 := congrArg Complex.re (tp_budget Γ 1 1); have h01 := tp_budget Γ 0 1; simp only [Fin.sum_univ_two,Complex.add_re,ite_true,Complex.one_re] at h0 h1
  simp only [Fin.sum_univ_two,show (0 : Qubit) ≠ 1 from by decide,ite_false] at h01; exact ⟨by simpa [A,C,add_assoc] using h0, by simpa [B,D,add_assoc] using h1, by simpa [N,P,add_assoc] using h01⟩
/-- The input weight multiplier is shared by all receiver branches. -/
def rate (R : ℝ) (j : Qubit) : ℝ := if j = 0 then 1 else R
def L (Γ : Instrument) (beta gamma R : ℝ) (j : Qubit) : ℝ :=
  rate R j * (beta * (B Γ j - A Γ j) + 2 * gamma * (N Γ j).im)
def F (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : ℝ :=
  (1 - beta * w) * A Γ j + beta * w * B Γ j + 2 * gamma * w * (N Γ j).im
def G (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : ℝ :=
  (1 - beta * w) * D Γ j + beta * w * C Γ j + 2 * gamma * w * (P Γ j).im
def T (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : ℂ :=
  (1 - (beta * w : ℝ)) * M Γ j - (beta * w : ℝ) * U Γ j +
    Complex.I * (gamma * w : ℝ) * (V Γ j + W Γ j)
def conditionalInput (beta gamma w : ℝ) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix !![(1 - beta * w : ℝ), - Complex.I * (gamma * w : ℝ); Complex.I * (gamma * w : ℝ),(beta * w : ℝ)]
private theorem operation_units (Γ : Instrument) (j s : Qubit) (X : CStarMatrix Qubit Qubit ℂ) (a b : Qubit) : Γ.operation j s X a b = ∑ i, ∑ k, X i k * Γ.operation j s (unit i k) a b := by
  have heq : X = ∑ i, ∑ k, X i k • unit i k := by
    ext i k
    simp [unit,Matrix.single,Fin.sum_univ_two]
    fin_cases i <;> fin_cases k <;> simp
  conv_lhs => rw [heq,map_sum]
  simp only [map_sum,map_smul]; change (∑ i, ∑ k, X i k • Γ.operation j s (unit i k)) a b = _; simp [Fin.sum_univ_two]
private theorem F_probability (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : (Γ.operation j 0 (conditionalInput beta gamma w) 0 0).re = F Γ beta gamma w j := by
  rw [operation_units]; have hs := (choi_positive Γ j).1.apply (1,0) (0,0); simp only [Fin.sum_univ_two]
  change (((1 - beta * w : ℝ) : ℂ) * choi Γ j (0,0) (0,0) + ( - Complex.I * (gamma * w : ℝ)) * choi Γ j (0,0) (1,0) + ((Complex.I * (gamma * w : ℝ)) * choi Γ j (1,0) (0,0) + (beta * w : ℝ) * choi Γ j (1,0) (1,0))).re = _; rw [← hs]
  simp [F,A,B,N,Complex.mul_re,Complex.mul_im]
  ring
private theorem conditional_positive {beta gamma w : ℝ} (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) : 0 ≤ conditionalInput beta gamma w := by
  have hp := (eta_positive (ell := 0) hb hw hm 0).submatrix (fun a : Qubit => (0,a))
  have he : (eta 0 beta gamma w 0).submatrix (fun a : Qubit => (0,a)) (fun a : Qubit => (0,a)) = CStarMatrix.ofMatrix.symm (conditionalInput beta gamma w) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [eta,xi,psi,outer,flagSign,conditionalInput,Matrix.vecMulVec_apply]
    all_goals ring
  rw [he] at hp; exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp.nonneg
private theorem conditional_trace (beta gamma w : ℝ) : Matrix.trace (conditionalInput beta gamma w) = 1 := by
  simp [conditionalInput,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
private theorem output_probability (Γ : Instrument) (X : CStarMatrix Qubit Qubit ℂ) (hx : 0 ≤ X) (ht : Matrix.trace X = 1) (j a : Qubit) : 0 ≤ (Γ.operation j 0 X a a).re ∧ (Γ.operation j 0 X a a).re ≤ 1 := by
  have hp (k : Qubit) : (CStarMatrix.ofMatrix.symm (Γ.operation k 0 X)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (map_nonneg (Γ.operation k 0) hx))
  have hn (k b : Qubit) : 0 ≤ (Γ.operation k 0 X b b).re :=
    (Complex.nonneg_iff.mp (hp k).diag_nonneg).1
  have hb := congrArg Complex.re (Γ.trace_preserving 0 X); rw [ht] at hb; simp only [Fin.sum_univ_two,Matrix.trace,Matrix.diag_apply,Complex.add_re,Complex.one_re] at hb
  fin_cases j <;> fin_cases a <;> exact ⟨hn _ _, by linarith! [hn 0 0,hn 0 1,hn 1 0,hn 1 1]⟩
private theorem F_bounds (Γ : Instrument) {beta gamma w : ℝ} (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) (j : Qubit) : 0 ≤ F Γ beta gamma w j ∧ F Γ beta gamma w j ≤ 1 := by
  rw [← F_probability]; exact output_probability Γ _ (conditional_positive hb hw hm) (conditional_trace _ _ _) j 0
/-- Receiver Z conjugation, without an operation on the inaccessible memory. -/
def phaseInput (X : CStarMatrix Qubit Qubit ℂ) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix fun a b => (flagSign a : ℂ) * X a b * (flagSign b : ℂ)
theorem sym_operation_entry (Γ : Instrument) (j s a b : Qubit) (X : CStarMatrix Qubit Qubit ℂ) : (symInstrument Γ).operation j s X a b = (1 / 2 : ℂ) * (Γ.operation j s X a b + (flagSign a : ℂ) * Γ.operation j (if s = 0 then 1 else 0) (phaseInput X) a b * (flagSign b : ℂ)) := by
  change (PhaseBoundaryReferenceReduction.flagSymmetrizedDecoder (instrumentRealization Γ)).toCompletelyPositiveMap
    (insertBlock s X) (j,a) (j,b) = _
  rw [PhaseBoundaryReferenceReduction.flagSymmetrizedDecoder,PhaseBoundaryReferenceReduction.average_entry]
  congr 1
  rw [realization_entry,if_pos rfl]; have hfirst : (∑ t, Γ.operation j t (CStarMatrix.ofMatrix fun r u => insertBlock s X (t,r) (t,u)) a b) = Γ.operation j s X a b := by
    have hb (t : Qubit) : (CStarMatrix.ofMatrix fun r u => insertBlock s X (t,r) (t,u)) = if t = s then X else 0 := by
      ext r u
      by_cases h : t = s <;> simp [insertBlock,h]
    simp_rw [hb]
    fin_cases s <;> simp [Fin.sum_univ_two]
  rw [hfirst,PhaseBoundaryReferenceReduction.reflectedDecoder,QuantumChannel.comp_apply, PhaseBoundaryReferenceReduction.rout_entry,QuantumChannel.comp_apply,realization_entry,if_pos rfl]
  have hblock (t : Qubit) : (CStarMatrix.ofMatrix fun r u => PhaseBoundaryReferenceReduction.flagConjugation.toCompletelyPositiveMap (insertBlock s X) (t,r) (t,u)) = if t = (if s = 0 then 1 else 0) then phaseInput X else 0 := by
    ext r u
    rw [CStarMatrix.ofMatrix_apply,PhaseBoundaryReferenceReduction.flag_conjugation_entry]
    fin_cases t <;> fin_cases s <;>
      simp [insertBlock,phaseInput,PhaseBoundaryReferenceReduction.flipFlag]
  simp_rw [hblock]
  fin_cases s <;> simp [Fin.sum_univ_two]
private theorem phase_involution (X : CStarMatrix Qubit Qubit ℂ) : phaseInput (phaseInput X) = X := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [phaseInput,flagSign]
private theorem sym_reflection (Γ : Instrument) (j a b : Qubit) (X : CStarMatrix Qubit Qubit ℂ) : (symInstrument Γ).operation j 1 X a b = (flagSign a : ℂ) * (symInstrument Γ).operation j 0 (phaseInput X) a b * (flagSign b : ℂ) := by
  rw [sym_operation_entry,sym_operation_entry,phase_involution]
  fin_cases a <;> fin_cases b <;> simp [flagSign] <;> ring
private theorem choi_norm_bound (Γ : Instrument) (j : Qubit) (p q : Qubit × Qubit) : ‖choi Γ j p q‖ ≤ 1 := by
  obtain ⟨hp0,hp1⟩ := diagonal_bounds Γ j p
  obtain ⟨hq0,hq1⟩ := diagonal_bounds Γ j q
  have hg := choi_gram Γ j p q; rw [Complex.normSq_eq_norm_sq] at hg
  nlinarith [norm_nonneg (choi Γ j p q),mul_nonneg (sub_nonneg.mpr hp1) hq0]
private theorem L_bound (Γ : Instrument) {beta gamma R : ℝ} (hb : 0 < beta) (hR : 1 < R) (j : Qubit) : |L Γ beta gamma R j| ≤ rate R j * (beta + 2 * |gamma|) := by
  have ha := diagonal_bounds Γ j (0,0); have hbb := diagonal_bounds Γ j (1,0); have hab : |B Γ j - A Γ j| ≤ 1 := by
    rw [abs_le]; dsimp [A,B]
    constructor <;> linarith
  have hn : |(N Γ j).im| ≤ 1 :=
    (Complex.abs_im_le_norm _).trans (choi_norm_bound Γ j (0,0) (1,0))
  have hr : 0 ≤ rate R j := by
    fin_cases j <;> simp [rate] <;> linarith
  calc
    |L Γ beta gamma R j| = rate R j *
        |beta * (B Γ j - A Γ j) + 2 * gamma * (N Γ j).im| := by
      rw [L,abs_mul,abs_of_nonneg hr]
    _ ≤ rate R j * (|beta * (B Γ j - A Γ j)| + |2 * gamma * (N Γ j).im|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hr
    _ ≤ rate R j * (beta + 2 * |gamma|) := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_pos hb]; norm_num
      apply mul_le_mul_of_nonneg_left _ hr
      nlinarith [abs_nonneg gamma]
private theorem L_sum_bound (Γ : Instrument) {beta gamma R : ℝ} (hb : 0 < beta) (hR : 1 < R) : |L Γ beta gamma R 0| + |L Γ beta gamma R 1| ≤ (1 + R) * (beta + 2 * |gamma|) := by
  have h0 := L_bound Γ (gamma := gamma) hb hR 0; have h1 := L_bound Γ (gamma := gamma) hb hR 1; simp only [rate,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false] at h0 h1
  nlinarith
private theorem F_expansion (Γ : Instrument) (beta gamma R eps : ℝ) (j : Qubit) : F Γ beta gamma (rate R j * eps) j = A Γ j + eps * L Γ beta gamma R j := by
  dsimp [F,L]
  ring
private theorem F_sum (Γ : Instrument) (beta gamma R eps : ℝ) : F Γ beta gamma eps 0 + F Γ beta gamma (R * eps) 1 = 1 - (C Γ 0 + C Γ 1) + eps * (L Γ beta gamma R 0 + L Γ beta gamma R 1) := by
  have h0 := F_expansion Γ beta gamma R eps 0; have h1 := F_expansion Γ beta gamma R eps 1; simp only [rate,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false,one_mul] at h0 h1; rw [h0,h1]
  linarith [(moment_budgets Γ).1]
def reverseInput (beta gamma w : ℝ) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix !![(beta * w : ℝ), - Complex.I * (gamma * w : ℝ); Complex.I * (gamma * w : ℝ),(1 - beta * w : ℝ)]
def crossInput (beta gamma w : ℝ) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix !![Complex.I * (gamma * w : ℝ),(1 - beta * w : ℝ); - (beta * w : ℝ),Complex.I * (gamma * w : ℝ)]
def sourceSlice (ell beta gamma w : ℝ) (m n s : Qubit) : CStarMatrix Qubit Qubit ℂ :=
  CStarMatrix.ofMatrix fun a b => omega ell beta gamma w (m,(s,a)) (n,(s,b))
private theorem slice_zero {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) (beta gamma w : ℝ) (s : Qubit) : sourceSlice ell beta gamma w 0 0 s = (((1 - ell) / 2 : ℝ) : ℂ) • (if s = 0 then conditionalInput beta gamma w else phaseInput (conditionalInput beta gamma w)) := by
  ext a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [sourceSlice,omega,eta,xi,psi,outer,conditionalInput,phaseInput,flagSign, Matrix.vecMulVec_apply,Complex.ofReal_sub,Complex.ofReal_div]
  all_goals
    have hs : ((Real.sqrt (1 - ell) : ℝ) : ℂ) ^ 2 = ((1 - ell : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hu)
    ring_nf
    simp [hs] <;> ring
private theorem slice_one {ell : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) (beta gamma w : ℝ) (s : Qubit) : sourceSlice ell beta gamma w 1 1 s = ((ell / 2 : ℝ) : ℂ) • (if s = 0 then reverseInput beta gamma w else phaseInput (reverseInput beta gamma w)) := by
  ext a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [sourceSlice,omega,eta,xi,psi,outer,reverseInput,phaseInput,flagSign, Matrix.vecMulVec_apply,Complex.ofReal_div]
  all_goals
    have hs : ((Real.sqrt ell : ℝ) : ℂ) ^ 2 = (ell : ℂ) := by exact_mod_cast Real.sq_sqrt hl
    ring_nf
    simp [hs] <;> ring
private theorem slice_cross (ell beta gamma w : ℝ) (s : Qubit) : sourceSlice ell beta gamma w 0 1 s = ((Real.sqrt (1 - ell) * Real.sqrt ell / 2 : ℝ) : ℂ) • (if s = 0 then crossInput beta gamma w else - (phaseInput (crossInput beta gamma w))) := by
  ext a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [sourceSlice,omega,eta,xi,psi,outer,crossInput,phaseInput,flagSign, Matrix.vecMulVec_apply,Complex.ofReal_mul,Complex.ofReal_div]
  all_goals ring_nf
  all_goals simp [Complex.I_sq] <;> ring
private theorem G_probability (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : (Γ.operation j 0 (reverseInput beta gamma w) 1 1).re = G Γ beta gamma w j := by
  rw [operation_units]; have hs := (choi_positive Γ j).1.apply (1,1) (0,1); simp only [Fin.sum_univ_two]
  change (((beta * w : ℝ) : ℂ) * choi Γ j (0,1) (0,1) + ( - Complex.I * (gamma * w : ℝ)) * choi Γ j (0,1) (1,1) + ((Complex.I * (gamma * w : ℝ)) * choi Γ j (1,1) (0,1) + (1 - beta * w : ℝ) * choi Γ j (1,1) (1,1))).re = _; rw [← hs]
  simp [G,C,D,P,Complex.mul_re,Complex.mul_im]
  ring
private theorem reverse_positive {beta gamma w : ℝ} (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) : 0 ≤ reverseInput beta gamma w := by
  have hp : (CStarMatrix.ofMatrix.symm (conditionalInput beta ( - gamma) w)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (conditional_positive hb hw (by simpa only [neg_sq] using hm)))
  have hs := hp.submatrix (fun a : Qubit => if a = 0 then 1 else 0)
  have he : (CStarMatrix.ofMatrix.symm (conditionalInput beta ( - gamma) w)).submatrix (fun a : Qubit => if a = 0 then 1 else 0) (fun a : Qubit => if a = 0 then 1 else 0) = CStarMatrix.ofMatrix.symm (reverseInput beta gamma w) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [conditionalInput,reverseInput] <;> ring
  rw [he] at hs; exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hs.nonneg
private theorem reverse_trace (beta gamma w : ℝ) : Matrix.trace (reverseInput beta gamma w) = 1 := by
  simp [reverseInput,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
private theorem G_bounds (Γ : Instrument) {beta gamma w : ℝ} (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) (j : Qubit) : 0 ≤ G Γ beta gamma w j ∧ G Γ beta gamma w j ≤ 1 := by
  rw [← G_probability]; exact output_probability Γ _ (reverse_positive hb hw hm) (reverse_trace _ _ _) j 1
private theorem T_probability (Γ : Instrument) (beta gamma w : ℝ) (j : Qubit) : Γ.operation j 0 (crossInput beta gamma w) 0 1 = T Γ beta gamma w j := by
  rw [operation_units]; simp [crossInput,Fin.sum_univ_two,T,M,U,V,W,choi,unit]
  ring
private theorem diagonal_real (Γ : Instrument) (j : Qubit) (X : CStarMatrix Qubit Qubit ℂ) (hx : 0 ≤ X) (a : Qubit) : Γ.operation j 0 X a a = ((Γ.operation j 0 X a a).re : ℂ) := by
  have hp : (CStarMatrix.ofMatrix.symm (Γ.operation j 0 X)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (map_nonneg (Γ.operation j 0) hx))
  have hi := (Complex.nonneg_iff.mp (hp.diag_nonneg (i := a))).2
  apply Complex.ext <;> simp [hi]
private theorem current_zero_block (Γ : Instrument) {ell beta gamma w : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) (j : Qubit) : (∑ s, (symInstrument Γ).operation j s (sourceSlice ell beta gamma w 0 0 s) 0 0) = ((1 - ell) * F (symInstrument Γ) beta gamma w j : ℝ) := by
  simp_rw [slice_zero hl hu]
  simp only [Fin.sum_univ_two,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false,map_smul, CStarMatrix.smul_apply,smul_eq_mul]; rw [sym_reflection,phase_involution]; simp only [flagSign,ite_true,Complex.ofReal_one,one_mul,mul_one]
  rw [diagonal_real _ _ _ (conditional_positive hb hw hm),F_probability]; push_cast
  ring
private theorem current_one_block (Γ : Instrument) {ell beta gamma w : ℝ} (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta) (hw : 0 ≤ w) (hm : w ≤ beta / (beta ^ 2 + gamma ^ 2)) (j : Qubit) : (∑ s, (symInstrument Γ).operation j s (sourceSlice ell beta gamma w 1 1 s) 1 1) = (ell * G (symInstrument Γ) beta gamma w j : ℝ) := by
  simp_rw [slice_one hl hu]
  simp only [Fin.sum_univ_two,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false,map_smul, CStarMatrix.smul_apply,smul_eq_mul]; rw [sym_reflection,phase_involution]; simp [flagSign]
  rw [diagonal_real _ _ _ (reverse_positive hb hw hm),G_probability]; push_cast
  ring
private theorem current_cross_block (Γ : Instrument) (ell beta gamma w : ℝ) (j : Qubit) : (∑ s, (symInstrument Γ).operation j s (sourceSlice ell beta gamma w 0 1 s) 0 1) = (Real.sqrt (1 - ell) * Real.sqrt ell : ℝ) * T (symInstrument Γ) beta gamma w j := by
  simp_rw [slice_cross]
  simp only [Fin.sum_univ_two,ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false,map_smul, map_neg,CStarMatrix.smul_apply,CStarMatrix.neg_apply,smul_eq_mul]; rw [sym_reflection,phase_involution]
  simp only [flagSign,ite_true,ite_false,Complex.ofReal_one,Complex.ofReal_neg,one_mul,mul_neg, mul_one,neg_neg]; rw [T_probability]; push_cast
  ring
private theorem block_trial_identity (Z : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (hZ : Z.IsHermitian) (u : Qubit → ℂ) (a : ℝ) : let b : Qubit → ℂ := fun k => ∑ j, star (Z (j,0) (k,1)) * u j
    let x : Qubit × Qubit → ℂ := fun p => if p.2 = 0 then u p.1 else (a : ℂ) * b p.1
    (star x ⬝ᵥ (Z *ᵥ x)).re =
      (star u ⬝ᵥ (Z.submatrix (fun j => (j,0)) (fun k => (k,0)) *ᵥ u)).re +
      2 * a * (∑ k, Complex.normSq (b k)) +
      a ^ 2 * (star b ⬝ᵥ (Z.submatrix (fun j => (j,1)) (fun k => (k,1)) *ᵥ b)).re := by
  intro b x; have hc (j k : Qubit) : Z (j,1) (k,0) = star (Z (k,0) (j,1)) :=
    (hZ.apply (j,1) (k,0)).symm
  have hn : ((∑ k, Complex.normSq (b k) : ℝ) : ℂ) = star b ⬝ᵥ b := by
    simp [dotProduct,Complex.normSq_eq_conj_mul_self]
  have he : star x ⬝ᵥ (Z *ᵥ x) = star u ⬝ᵥ (Z.submatrix (fun j => (j,0)) (fun k => (k,0)) *ᵥ u) + ((2 * a : ℝ) : ℂ) * (star b ⬝ᵥ b) + (a ^ 2 : ℝ) * (star b ⬝ᵥ (Z.submatrix (fun j => (j,1)) (fun k => (k,1)) *ᵥ b)) := by
    simp [x,b,Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Fintype.sum_prod_type, Fin.sum_univ_two,Pi.star_apply,star_add,star_mul,star_star,hc]; push_cast
    ring
  rw [he,← hn]; simp only [Complex.add_re,Complex.mul_re,← Complex.ofReal_pow,Complex.ofReal_re, Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
section Actual
variable (ell beta gamma : ℝ) (w : Qubit → ℝ)
  (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
  (hw : ∀ j, 0 ≤ w j) (hm : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
  (Γ : Instrument)
/-- Half diamond error of the actual receiver-only lawful flag average. -/
def actualError : ℝ :=
  diamondDistance (targetChannel ell hl hu)
    ((receiverChannel (M := Qubit) (PhaseBoundaryReferenceReduction.flagSymmetrizedDecoder (instrumentRealization Γ))).comp (sourceChannel ell beta gamma w hl hu hb hw hm)) / 2
private theorem even_entry (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) (j k m n : Qubit) : evenBlock ell beta gamma w hl hu hb hw hm Γ c hc (j,m) (k,n) = c j * star (c k) * xi ell (m,m) * star (xi ell (n,n)) - if j = k then (c j * star (c j)) * ∑ s, (symInstrument Γ).operation j s (sourceSlice ell beta gamma (w j) m n s) m n else 0 := by
  let rho := pureState (diagonalInput c) (diagonal_input_norm c hc); change referenceAction (targetChannel ell hl hu) rho.1
    (j,(m,(j,m))) (k,(n,(k,n))) -
    referenceAction (receiverChannel (M := Qubit) (instrumentRealization (symInstrument Γ)))
      (referenceAction (sourceChannel ell beta gamma w hl hu hb hw hm) rho.1)
        (j,(m,(j,m))) (k,(n,(k,n))) = _
  rw [target_reference,PhaseBoundarySourceModel.receiver_reference,realization_entry]; have htarget : rho.1 (j,j) (k,k) = c j * star (c k) := by
    simp [rho,pureState,diagonalInput,Matrix.vecMulVec_apply]
  rw [htarget]
  by_cases hjk : j = k
  · subst k
    simp only [ite_true]
    have hslice (s : Qubit) : (CStarMatrix.ofMatrix fun a b => referenceAction (sourceChannel ell beta gamma w hl hu hb hw hm) rho.1 (j,(m,(s,a))) (j,(n,(s,b)))) = (c j * star (c j)) • sourceSlice ell beta gamma (w j) m n s := by
      ext a b
      rw [CStarMatrix.ofMatrix_apply,source_reference]; simp [rho,pureState,diagonalInput,Matrix.vecMulVec_apply,sourceSlice,Fin.sum_univ_two]
    congr 1
    calc
      _ = ∑ s, (c j * star (c j)) *
          (symInstrument Γ).operation j s (sourceSlice ell beta gamma (w j) m n s) m n := by
        apply Finset.sum_congr rfl
        intro s _; change (symInstrument Γ).operation j s
          (CStarMatrix.ofMatrix fun a b => referenceAction (sourceChannel ell beta gamma w hl hu hb hw hm) rho.1 (j,(m,(s,a))) (j,(n,(s,b)))) m n = _
        rw [hslice,map_smul]
        rfl
      _ = _ := (Finset.mul_sum _ _ _).symm
  · simp only [if_neg hjk]
theorem upper_entry (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) (j k : Qubit) : evenBlock ell beta gamma w hl hu hb hw hm Γ c hc (j,0) (k,0) = (1 - ell : ℝ) * (c j * star (c k) - if j = k then (c j * star (c j)) * (F (symInstrument Γ) beta gamma (w j) j : ℝ) else 0) := by
  rw [even_entry]; have hs : ((Real.sqrt (1 - ell) : ℝ) : ℂ) ^ 2 = ((1 - ell : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hu)
  simp only [xi,ite_true,Complex.star_def,Complex.conj_ofReal]; rw [current_zero_block Γ hl hu hb (hw j) (hm j)]; push_cast at hs
  split_ifs <;> push_cast <;> linear_combination (c j * (starRingEnd ℂ) (c k)) * hs
theorem cross_entry (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) (j k : Qubit) : evenBlock ell beta gamma w hl hu hb hw hm Γ c hc (j,0) (k,1) = (Real.sqrt (1 - ell) * Real.sqrt ell : ℝ) * (c j * star (c k) - if j = k then (c j * star (c j)) * T (symInstrument Γ) beta gamma (w j) j else 0) := by
  rw [even_entry,current_cross_block]; simp only [xi,ite_true,show ((1,1) : Qubit × Qubit) ≠ ((0,0) : Qubit × Qubit) from by decide,ite_false, Complex.star_def,Complex.conj_ofReal]
  split_ifs <;> push_cast <;> ring
theorem lower_entry (c : Qubit → ℂ) (hc : ∑ j, Complex.normSq (c j) = 1) (j k : Qubit) : evenBlock ell beta gamma w hl hu hb hw hm Γ c hc (j,1) (k,1) = (ell : ℂ) * (c j * star (c k) - if j = k then (c j * star (c j)) * (G (symInstrument Γ) beta gamma (w j) j : ℝ) else 0) := by
  rw [even_entry]; have hs : ((Real.sqrt ell : ℝ) : ℂ) ^ 2 = (ell : ℂ) := by exact_mod_cast Real.sq_sqrt hl
  simp only [xi,show ((1,1) : Qubit × Qubit) ≠ ((0,0) : Qubit × Qubit) from by decide,ite_false,ite_true, Complex.star_def,Complex.conj_ofReal]; rw [current_one_block Γ hl hu hb (hw j) (hm j)]; push_cast at hs
  split_ifs <;> push_cast <;> linear_combination (c j * (starRingEnd ℂ) (c k)) * hs
private theorem quadratic_le_error (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∑ j, Complex.normSq (weightInput q j) = 1) (x : Qubit × Qubit → ℂ) : (star x ⬝ᵥ (evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc *ᵥ x)).re ≤ actualError ell beta gamma w hl hu hb hw hm Γ * ∑ i, Complex.normSq (x i) := by
  obtain ⟨_,_,_,_,_,hbound⟩ := diamond_eq_even_spectral_max ell beta gamma w hl hu hb hw hm Γ
  obtain ⟨hT,hB⟩ := hbound q hq0 hq1
  have hle : evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc ≤ algebraMap ℝ (Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) (actualError ell beta gamma w hl hu hb hw hm Γ) := by
    apply (le_algebraMap_iff_spectrum_le hT.isSelfAdjoint).mpr
    rw [hT.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i,rfl⟩
    exact hB i
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hle)).re_dotProduct_nonneg x
  simp only [Matrix.sub_mulVec,Algebra.algebraMap_eq_smul_one,Matrix.smul_mulVec, Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,Complex.sub_re] at hp; have hn : (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
    simp [dotProduct,Complex.normSq_apply,pow_two]
  simpa [hn] using hp
private theorem principal_quadratic (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∑ j, Complex.normSq (weightInput q j) = 1) : (star (fun p : Qubit × Qubit => if p.2 = 0 then weightInput q p.1 else 0) ⬝ᵥ (evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc *ᵥ (fun p : Qubit × Qubit => if p.2 = 0 then weightInput q p.1 else 0))).re = (1 - ell) * (1 - q ^ 2 * F (symInstrument Γ) beta gamma (w 0) 0 - (1 - q) ^ 2 * F (symInstrument Γ) beta gamma (w 1) 1) := by
  let x : Qubit × Qubit → ℂ := fun p => if p.2 = 0 then weightInput q p.1 else 0; have hs0 := Real.sq_sqrt hq0; have hs1 := Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hs04 : (Real.sqrt q) ^ 4 = q ^ 2 := by rw [show (Real.sqrt q) ^ 4 = ((Real.sqrt q) ^ 2) ^ 2 by ring,hs0]
  have hs14 : (Real.sqrt (1 - q)) ^ 4 = (1 - q) ^ 2 := by
    rw [show (Real.sqrt (1 - q)) ^ 4 = ((Real.sqrt (1 - q)) ^ 2) ^ 2 by ring,hs1]
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,x]; simp only [ite_true,show (1 : Qubit) ≠ 0 from by decide,ite_false,Pi.star_apply,star_zero, mul_zero,zero_mul,add_zero]
  simp_rw [upper_entry]
  simp [weightInput,Complex.mul_re,Complex.mul_im]
  ring_nf
  simp only [hs04,hs14,hs0,hs1]
  ring
private theorem principal_lower_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : (1 - ell) * (1 - q ^ 2 * F (symInstrument Γ) beta gamma (w 0) 0 - (1 - q) ^ 2 * F (symInstrument Γ) beta gamma (w 1) 1) ≤ actualError ell beta gamma w hl hu hb hw hm Γ := by
  have hs0 := Real.sq_sqrt hq0; have hs1 := Real.sq_sqrt (sub_nonneg.mpr hq1); have hs04 : (Real.sqrt q) ^ 4 = q ^ 2 := by calc
    _ = ((Real.sqrt q) ^ 2) ^ 2 := by ring
    _ = q ^ 2 := by rw [hs0]
  have hs14 : (Real.sqrt (1 - q)) ^ 4 = (1 - q) ^ 2 := by calc
    _ = ((Real.sqrt (1 - q)) ^ 2) ^ 2 := by ring
    _ = (1 - q) ^ 2 := by rw [hs1]
  have hc : ∑ j, Complex.normSq (weightInput q j) = 1 := by
    simp [weightInput,Fin.sum_univ_two,Complex.normSq_ofReal,← sq,hs0,hs1]
  let x : Qubit × Qubit → ℂ := fun p => if p.2 = 0 then weightInput q p.1 else 0; have hx : ∑ i, Complex.normSq (x i) = 1 := by
    simpa [x,Fintype.sum_prod_type,Fin.sum_univ_two] using hc
  have hq := quadratic_le_error ell beta gamma w hl hu hb hw hm Γ q hq0 hq1 hc x; rw [hx,mul_one] at hq; have he := principal_quadratic ell beta gamma w hl hu hb hw hm Γ q hq0 hq1 hc
  rwa [he] at hq
private theorem balanced_lower_bound (hs : 0 < F (symInstrument Γ) beta gamma (w 0) 0 + F (symInstrument Γ) beta gamma (w 1) 1) : (1 - ell) * (1 - F (symInstrument Γ) beta gamma (w 0) 0 * F (symInstrument Γ) beta gamma (w 1) 1 / (F (symInstrument Γ) beta gamma (w 0) 0 + F (symInstrument Γ) beta gamma (w 1) 1)) ≤ actualError ell beta gamma w hl hu hb hw hm Γ := by
  let f0 := F (symInstrument Γ) beta gamma (w 0) 0; let f1 := F (symInstrument Γ) beta gamma (w 1) 1; have hf0 := F_bounds (symInstrument Γ) hb (hw 0) (hm 0) 0; have hf1 := F_bounds (symInstrument Γ) hb (hw 1) (hm 1) 1
  have hq0 : 0 ≤ f1 / (f0 + f1) := div_nonneg hf1.1 hs.le; have hq1 : f1 / (f0 + f1) ≤ 1 := (div_le_one hs).mpr (by linarith); have h := principal_lower_bound ell beta gamma w hl hu hb hw hm Γ _ hq0 hq1
  have he : 1 - (f1 / (f0 + f1)) ^ 2 * f0 - (1 - f1 / (f0 + f1)) ^ 2 * f1 = 1 - f0 * f1 / (f0 + f1) := by
    have hs0 : f0 + f1 ≠ 0 := ne_of_gt hs; field_simp [hs0]
    ring
  change (1 - ell) * (1 - (f1 / (f0 + f1)) ^ 2 * f0 - (1 - f1 / (f0 + f1)) ^ 2 * f1) ≤ _ at h
  rwa [he] at h
private theorem offdiagonal_norm_identity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∑ j, Complex.normSq (weightInput q j) = 1) : (∑ k, Complex.normSq (∑ j, star (evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc (j,0) (k,1)) * weightInput q j)) = (1 - ell) * ell * (q * Complex.normSq (1 - (q : ℂ) * T (symInstrument Γ) beta gamma (w 0) 0) + (1 - q) * Complex.normSq (1 - ((1 - q : ℝ) : ℂ) * T (symInstrument Γ) beta gamma (w 1) 1)) := by
  have hqC : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq0
  have h1C : ((Real.sqrt (1 - q) : ℝ) : ℂ) ^ 2 = ((1 - q : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hqC3 : ((Real.sqrt q : ℝ) : ℂ) ^ 3 = (q : ℂ) * (Real.sqrt q : ℝ) := by
    rw [show ((Real.sqrt q : ℝ) : ℂ) ^ 3 = ((Real.sqrt q : ℝ) : ℂ) ^ 2 * (Real.sqrt q : ℝ) by ring,hqC]
  have h1C3 : ((Real.sqrt (1 - q) : ℝ) : ℂ) ^ 3 = ((1 - q : ℝ) : ℂ) * (Real.sqrt (1 - q) : ℝ) := by
    rw [show ((Real.sqrt (1 - q) : ℝ) : ℂ) ^ 3 = ((Real.sqrt (1 - q) : ℝ) : ℂ) ^ 2 * (Real.sqrt (1 - q) : ℝ) by ring,h1C]
  have hv (k : Qubit) : (∑ j, star (evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc (j,0) (k,1)) * weightInput q j) = ((Real.sqrt (1 - ell) * Real.sqrt ell : ℝ) : ℂ) * weightInput q k * star (1 - ((if k = 0 then q else 1 - q : ℝ) : ℂ) * T (symInstrument Γ) beta gamma (w k) k) := by
    simp_rw [cross_entry]
    fin_cases k <;>
      simp [Fin.sum_univ_two,weightInput,star_sub,star_mul,Complex.star_def]
    all_goals
      push_cast at h1C
      ring_nf
      simp [hqC,h1C,hqC3,h1C3] <;> ring
  have hstar (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq,norm_star,Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  simp only [Complex.normSq_mul,hstar,Fin.sum_univ_two,ite_true, show (1 : Qubit) ≠ 0 from by decide,ite_false]; have hprod : (Real.sqrt (1 - ell) * Real.sqrt ell) ^ 2 = (1 - ell) * ell := by
    rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hu),Real.sq_sqrt hl]
  simp [weightInput,Complex.normSq_ofReal,← sq,Real.sq_sqrt hq0, Real.sq_sqrt (sub_nonneg.mpr hq1),Real.sq_sqrt (sub_nonneg.mpr hu),Real.sq_sqrt hl,hprod]
  ring
private theorem lower_quadratic_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∑ j, Complex.normSq (weightInput q j) = 1) (b : Qubit → ℂ) : - ell * (∑ j, Complex.normSq (b j)) ≤ (star b ⬝ᵥ ((evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc).submatrix (fun j => (j,1)) (fun k => (k,1)) *ᵥ b)).re := by
  let Z := (evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc).submatrix
    (fun j => (j,1)) (fun k => (k,1))
  let u := weightInput q; let d : Qubit → ℝ := fun j => 1 - Complex.normSq (u j) * G (symInstrument Γ) beta gamma (w j) j; have hd (j : Qubit) : 0 ≤ d j := by
    have hg := G_bounds (symInstrument Γ) hb (hw j) (hm j) j; have hp : 0 ≤ Complex.normSq (u j) ∧ Complex.normSq (u j) ≤ 1 := by
      fin_cases j <;> simp [u,weightInput,Complex.normSq_ofReal,← sq, Real.sq_sqrt hq0,Real.sq_sqrt (sub_nonneg.mpr hq1)] <;> constructor <;> linarith
    dsimp [d]
    nlinarith
  have he : Z + (ell : ℂ) • (1 : Matrix Qubit Qubit ℂ) = (ell : ℂ) • Matrix.vecMulVec u (star u) + (ell : ℂ) • Matrix.diagonal (fun j => (d j : ℂ)) := by
    ext j k
    change evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc (j,1) (k,1) + _ = _; rw [lower_entry]
    simp only [Z,u,d,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply, Pi.star_apply,Matrix.diagonal,Matrix.one_apply,smul_eq_mul]
    by_cases hjk : j = k
    · subst k
      simp [Complex.normSq_eq_conj_mul_self]
      ring
    · simp [hjk,Ne.symm hjk]
  have hell : (0 : ℂ) ≤ (ell : ℂ) := by exact_mod_cast hl
  have hp : (Z + (ell : ℂ) • (1 : Matrix Qubit Qubit ℂ)).PosSemidef := by
    rw [he]; exact ((Matrix.posSemidef_vecMulVec_self_star u).smul hell).add
      ((Matrix.PosSemidef.diagonal (fun j => by change (0 : ℂ) ≤ (d j : ℂ); exact_mod_cast hd j)).smul hell)
  have hbq := hp.re_dotProduct_nonneg b; have hn : (star b ⬝ᵥ b).re = ∑ j, Complex.normSq (b j) := by
    simp [dotProduct,Complex.normSq_apply,pow_two]
  have hsum : (star b ⬝ᵥ ((Z + (ell : ℂ) • (1 : Matrix Qubit Qubit ℂ)) *ᵥ b)).re = (star b ⬝ᵥ (Z *ᵥ b)).re + ell * (∑ j, Complex.normSq (b j)) := by
    rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]; simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, zero_mul,sub_zero,hn]
  change 0 ≤ (star b ⬝ᵥ ((Z + (ell : ℂ) • (1 : Matrix Qubit Qubit ℂ)) *ᵥ b)).re at hbq; rw [hsum] at hbq; change - ell * (∑ j, Complex.normSq (b j)) ≤ (star b ⬝ᵥ (Z *ᵥ b)).re
  linarith
private theorem rayleigh_trial_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : ∑ j, Complex.normSq (weightInput q j) = 1) : let Z := evenBlock ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc
    let b : Qubit → ℂ := fun k => ∑ j, star (Z (j,0) (k,1)) * weightInput q j; let nu := ∑ k, Complex.normSq (b k)
    (1 - ell) * (1 - q ^ 2 * F (symInstrument Γ) beta gamma (w 0) 0 - (1 - q) ^ 2 * F (symInstrument Γ) beta gamma (w 1) 1) +
      4 * nu / 3 - (16 / 9) * (actualError ell beta gamma w hl hu hb hw hm Γ - 3 / 4 + ell) * nu ≤
        actualError ell beta gamma w hl hu hb hw hm Γ := by
  intro Z b nu; let x : Qubit × Qubit → ℂ := fun p =>
    if p.2 = 0 then weightInput q p.1 else ((4 / 3 : ℝ) : ℂ) * b p.1
  have hq := quadratic_le_error ell beta gamma w hl hu hb hw hm Γ q hq0 hq1 hc x
  obtain ⟨hZ,_⟩ := even_error_eq_top_eigenvalue ell beta gamma w hl hu hb hw hm Γ (weightInput q) hc
  have hid := block_trial_identity Z hZ (weightInput q) (4 / 3); dsimp only at hid; change (star x ⬝ᵥ (Z *ᵥ x)).re = _ at hid; have huq := principal_quadratic ell beta gamma w hl hu hb hw hm Γ q hq0 hq1 hc
  have hu0 : (star (weightInput q) ⬝ᵥ (Z.submatrix (fun j => (j,0)) (fun k => (k,0)) *ᵥ weightInput q)).re = (1 - ell) * (1 - q ^ 2 * F (symInstrument Γ) beta gamma (w 0) 0 - (1 - q) ^ 2 * F (symInstrument Γ) beta gamma (w 1) 1) := by
    simpa [Z,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two] using huq
  rw [hu0] at hid; have hlower := lower_quadratic_bound ell beta gamma w hl hu hb hw hm Γ q hq0 hq1 hc b; have hnorm : ∑ i, Complex.normSq (x i) = 1 + (16 / 9) * nu := by
    have hu1 := hc; simp only [Fin.sum_univ_two] at hu1; simp [x,nu,Complex.normSq_mul,Fintype.sum_prod_type,Fin.sum_univ_two]
    nlinarith
  rw [hnorm] at hq
  nlinarith [hid]
end Actual
/-- Fixed physical parameters; no condition on decoder Kraus rank is present. -/
structure Parameters where
  beta : ℝ
  gamma : ℝ
  R : ℝ
  H : ℝ
  beta_pos : 0 < beta
  R_gt_one : 1 < R
  H_pos : 0 < H
/-- A lawful coupled point, retaining the zero-memory-weight boundary. -/
structure CoupledPoint (p : Parameters) where
  eps : ℝ
  h : ℝ
  eps_pos : 0 < eps
  h_nonneg : 0 ≤ h
  h_le : h ≤ p.H
  ell_le : h * eps ≤ 1
  input_le : p.R * eps ≤ p.beta / (p.beta ^ 2 + p.gamma ^ 2)
namespace CoupledPoint
variable {p : Parameters} (x : CoupledPoint p)
def weights (j : Qubit) : ℝ := rate p.R j * x.eps
theorem weights_nonneg (j : Qubit) : 0 ≤ x.weights j := by
  have hR := p.R_gt_one; have heps := x.eps_pos
  fin_cases j <;> simp [weights,rate] <;> positivity
theorem weights_legal (j : Qubit) : x.weights j ≤ p.beta / (p.beta ^ 2 + p.gamma ^ 2) := by
  fin_cases j <;> simp [weights,rate]
  · have h := x.input_le
    nlinarith [p.R_gt_one,x.eps_pos]
  · exact x.input_le
/-- Complete-reference error after the lawful receiver-only flag average. -/
def error (Γ : Instrument) : ℝ :=
  actualError (x.h * x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
      x.weights_nonneg x.weights_legal Γ
def f (Γ : Instrument) (j : Qubit) : ℝ := F (symInstrument Γ) p.beta p.gamma (x.weights j) j
def s (Γ : Instrument) : ℝ := x.f Γ 0 + x.f Γ 1
def d (Γ : Instrument) : ℝ := x.f Γ 0 - x.f Γ 1
def c (_x : CoupledPoint p) (Γ : Instrument) : ℝ := C (symInstrument Γ) 0 + C (symInstrument Γ) 1
def lambda (Γ : Instrument) : ℝ := (1 - x.h * x.eps) * (1 - x.f Γ 0 * x.f Γ 1 / x.s Γ)
end CoupledPoint
/-- Uniform absolute first-order coefficient budget. -/
def Lbar (p : Parameters) : ℝ := (1 + p.R) * (p.beta + 2 * |p.gamma|)
def Kone (p : Parameters) (K : ℝ) : ℝ := K + 3 * p.H / 4 + Lbar p / 4
private theorem coupled_sum (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : x.s Γ = 1 - x.c Γ + x.eps * (L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1) := by
  simpa [CoupledPoint.s,CoupledPoint.f,CoupledPoint.c,CoupledPoint.weights,rate] using
    F_sum (symInstrument Γ) p.beta p.gamma p.R x.eps
private theorem coupled_positive_sum (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (K : ℝ) (hsmall : (p.H + K) * x.eps < 1 / 4) (hne : x.error Γ ≤ 3 / 4 + K * x.eps) : 0 < x.s Γ := by
  have hf0 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 0) (x.weights_legal 0) 0; have hf1 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 1) (x.weights_legal 1) 1; change 0 ≤ x.f Γ 0 ∧ x.f Γ 0 ≤ 1 at hf0
  change 0 ≤ x.f Γ 1 ∧ x.f Γ 1 ≤ 1 at hf1
  by_contra h
  have hz : x.s Γ = 0 := by dsimp [CoupledPoint.s] at * ; linarith
  have hz0 : x.f Γ 0 = 0 := by dsimp [CoupledPoint.s] at hz; linarith
  have hz1 : x.f Γ 1 = 0 := by dsimp [CoupledPoint.s] at hz; linarith
  have hcomp := principal_lower_bound (x.h * x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
      x.weights_nonneg x.weights_legal Γ (1 / 2) (by norm_num) (by norm_num)
  change (1 - x.h * x.eps) * (1 - (1 / 2) ^ 2 * x.f Γ 0 - (1 - 1 / 2) ^ 2 * x.f Γ 1) ≤ x.error Γ at hcomp; rw [hz0,hz1] at hcomp
  nlinarith [mul_le_mul_of_nonneg_right x.h_le x.eps_pos.le]
private theorem lambda_decomposition (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (hs : 0 < x.s Γ) : x.lambda Γ - 3 / 4 = - 3 * x.h * x.eps / 4 - (1 - x.h * x.eps) * x.eps * (L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1) / 4 + (1 - x.h * x.eps) * (x.c Γ / 4 + (x.d Γ) ^ 2 / (4 * x.s Γ)) := by
  have hsum := coupled_sum p x Γ; dsimp only [CoupledPoint.lambda,CoupledPoint.d]; have hrel : (x.f Γ 0 + x.f Γ 1) ^ 2 - (x.f Γ 0 - x.f Γ 1) ^ 2 = 4 * x.f Γ 0 * x.f Γ 1 := by ring
  have hsrel : x.f Γ 0 + x.f Γ 1 = x.s Γ := rfl; rw [hsrel] at hrel; field_simp [ne_of_gt hs]
  linear_combination (1 - x.h * x.eps) * hrel - (1 - x.h * x.eps) * x.s Γ * hsum
/-- The main compression simultaneously forces both current nonnegative defects.
This is the uncorrected compression bound, before the off-diagonal Rayleigh gain. -/
theorem current_compression_defect_bound (p : Parameters) (x : CoupledPoint p) (Γ : Instrument)
    (K : ℝ) (hK : 0 ≤ K) (hrare : x.h * x.eps ≤ 1 / 2)
    (hsmall : (p.H + K) * x.eps < 1 / 4) (hne : x.error Γ ≤ 3 / 4 + K * x.eps) :
    0 < x.s Γ ∧ x.lambda Γ ≤ x.error Γ ∧
      x.c Γ / 8 + (x.d Γ) ^ 2 / 16 ≤ Kone p K * x.eps := by
  have hs := coupled_positive_sum p x Γ K hsmall hne; have hroot := balanced_lower_bound (x.h * x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
      x.weights_nonneg x.weights_legal Γ hs
  change x.lambda Γ ≤ x.error Γ at hroot
  refine ⟨hs,hroot,?_⟩
  have hf0 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 0) (x.weights_legal 0) 0; have hf1 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 1) (x.weights_legal 1) 1
  have hs2 : x.s Γ ≤ 2 := by dsimp [CoupledPoint.s,CoupledPoint.f]; linarith
  have hc : 0 ≤ x.c Γ := by
    have h0 := (diagonal_bounds (symInstrument Γ) 0 (0,1)).1; have h1 := (diagonal_bounds (symInstrument Γ) 1 (0,1)).1; exact add_nonneg h0 h1
  have hr0 : 1 / 2 ≤ 1 - x.h * x.eps := by linarith
  have hr1 : 1 - x.h * x.eps ≤ 1 := by nlinarith [x.h_nonneg,x.eps_pos]
  have hL := L_sum_bound (symInstrument Γ) (gamma := p.gamma) p.beta_pos p.R_gt_one; change |L (symInstrument Γ) p.beta p.gamma p.R 0| +
    |L (symInstrument Γ) p.beta p.gamma p.R 1| ≤ Lbar p at hL
  let ls := L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1; have hLs : ls ≤ Lbar p := by
    have ha := le_abs_self (L (symInstrument Γ) p.beta p.gamma p.R 0); have hb := le_abs_self (L (symInstrument Γ) p.beta p.gamma p.R 1); dsimp [ls]
    linarith
  have hLb : 0 ≤ Lbar p := by
    have hβ := p.beta_pos; have hR := p.R_gt_one; dsimp [Lbar]
    positivity
  have hLe : (1 - x.h * x.eps) * x.eps * ls ≤ x.eps * Lbar p := by
    calc
      _ ≤ (1 - x.h * x.eps) * x.eps * Lbar p := mul_le_mul_of_nonneg_left hLs
        (mul_nonneg (le_trans (by norm_num) hr0) x.eps_pos.le)
      _ ≤ _ := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (mul_nonneg x.eps_pos.le hLb)]
  have hcostC : x.c Γ / 8 ≤ (1 - x.h * x.eps) * (x.c Γ / 4) := by nlinarith
  have hcostD : (x.d Γ) ^ 2 / 16 ≤ (1 - x.h * x.eps) * ((x.d Γ) ^ 2 / (4 * x.s Γ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 4 * x.s Γ)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr0) (sq_nonneg (x.d Γ)), mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg (x.d Γ))]
  have heq := lambda_decomposition p x Γ hs; change x.lambda Γ - 3 / 4 = - 3 * x.h * x.eps / 4 - (1 - x.h * x.eps) * x.eps * ls / 4 +
    (1 - x.h * x.eps) * (x.c Γ / 4 + (x.d Γ) ^ 2 / (4 * x.s Γ)) at heq
  dsimp [Kone]
  nlinarith [mul_le_mul_of_nonneg_right x.h_le x.eps_pos.le]
private theorem sum_N_bound (Γ : Instrument) : ‖N Γ 0 + N Γ 1‖ ≤ Real.sqrt (C Γ 0 + C Γ 1) := by
  have hbud := moment_budgets Γ; have hpos := (choi_positive Γ 0).add (choi_positive Γ 1); have hgram := psd_gram _ hpos (0,1) (1,1); change Complex.normSq (P Γ 0 + P Γ 1) ≤ (C Γ 0 + C Γ 1) * (D Γ 0 + D Γ 1) at hgram
  have he : N Γ 0 + N Γ 1 = - (P Γ 0 + P Γ 1) := by linear_combination hbud.2.2
  rw [he,norm_neg]; have hc0 : 0 ≤ C Γ 0 + C Γ 1 := add_nonneg
    (diagonal_bounds Γ 0 (0,1)).1 (diagonal_bounds Γ 1 (0,1)).1
  have hd1 : D Γ 0 + D Γ 1 ≤ 1 := by
    have hb0 := (diagonal_bounds Γ 0 (1,0)).1; have hb1 := (diagonal_bounds Γ 1 (1,0)).1; dsimp [B] at hbud
    linarith
  have hsq := Real.sq_sqrt hc0; rw [Complex.normSq_eq_norm_sq] at hgram
  nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hd1),Real.sqrt_nonneg (C Γ 0 + C Γ 1),norm_nonneg (P Γ 0 + P Γ 1)]
theorem current_A_bound (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (j : Qubit) : |A (symInstrument Γ) j - 1 / 2| ≤ (x.c Γ + |x.d Γ| + x.eps * Lbar p) / 2 := by
  have hbud := (moment_budgets (symInstrument Γ)).1; have hL := L_sum_bound (symInstrument Γ) (gamma := p.gamma) p.beta_pos p.R_gt_one; change |L (symInstrument Γ) p.beta p.gamma p.R 0| +
    |L (symInstrument Γ) p.beta p.gamma p.R 1| ≤ Lbar p at hL
  let ld := L (symInstrument Γ) p.beta p.gamma p.R 0 - L (symInstrument Γ) p.beta p.gamma p.R 1; have hLd : |ld| ≤ Lbar p := (abs_sub _ _).trans hL; have hd : x.d Γ = A (symInstrument Γ) 0 - A (symInstrument Γ) 1 + x.eps * ld := by
    dsimp [CoupledPoint.d,CoupledPoint.f,CoupledPoint.weights,rate,F,L,ld]
    ring
  have hc : 0 ≤ x.c Γ := add_nonneg
    (diagonal_bounds (symInstrument Γ) 0 (0,1)).1 (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hld0 : - Lbar p ≤ ld := (abs_le.mp hLd).1; have hld1 : ld ≤ Lbar p := (abs_le.mp hLd).2; have he0 := mul_le_mul_of_nonneg_left hld0 x.eps_pos.le; have he1 := mul_le_mul_of_nonneg_left hld1 x.eps_pos.le; have hd0 := neg_abs_le (x.d Γ)
  have hd1 := le_abs_self (x.d Γ); have hbud' : A (symInstrument Γ) 0 + A (symInstrument Γ) 1 + x.c Γ = 1 := by
    dsimp [CoupledPoint.c]
    linarith [hbud]
  fin_cases j <;> rw [abs_le] <;> constructor <;> linarith!
private theorem T_difference_bound (Γ : Instrument) {beta gamma w : ℝ} (hb : 0 < beta) (hw : 0 ≤ w) (j : Qubit) : ‖T Γ beta gamma w j - M Γ j‖ ≤ 2 * (beta + |gamma|) * w := by
  have hM : ‖M Γ j‖ ≤ 1 := choi_norm_bound Γ j (0,0) (1,1); have hU : ‖U Γ j‖ ≤ 1 := choi_norm_bound Γ j (1,0) (0,1); have hV : ‖V Γ j‖ ≤ 1 := choi_norm_bound Γ j (0,0) (0,1); have hW : ‖W Γ j‖ ≤ 1 := choi_norm_bound Γ j (1,0) (1,1)
  have he : T Γ beta gamma w j - M Γ j = - (beta * w : ℝ) * (M Γ j + U Γ j) + Complex.I * (gamma * w : ℝ) * (V Γ j + W Γ j) := by
    dsimp [T]; push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖ - (beta * w : ℝ) * (M Γ j + U Γ j)‖ + ‖Complex.I * (gamma * w : ℝ) * (V Γ j + W Γ j)‖ := norm_add_le _ _
    _ = beta * w * ‖M Γ j + U Γ j‖ + |gamma| * w * ‖V Γ j + W Γ j‖ := by
      simp [norm_mul,Complex.norm_real,abs_mul,abs_of_nonneg hw,abs_of_pos hb]
    _ ≤ beta * w * (‖M Γ j‖ + ‖U Γ j‖) + |gamma| * w * (‖V Γ j‖ + ‖W Γ j‖) := by
      gcongr <;> exact norm_add_le _ _
    _ ≤ _ := by
      have hMU : ‖M Γ j‖ + ‖U Γ j‖ ≤ 2 := by linarith
      have hVW : ‖V Γ j‖ + ‖W Γ j‖ ≤ 2 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hMU) (mul_nonneg hb.le hw), mul_nonneg (sub_nonneg.mpr hVW) (mul_nonneg (abs_nonneg gamma) hw)]
def deviation (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : ℝ :=
  Real.sqrt (x.c Γ) + |x.d Γ| + x.eps
def diskQ (p : Parameters) (h m n : ℝ) : ℝ :=
  7 * h / 12 - p.beta * (p.R - 1) / 8 - 4 * h * m / 3 + (h / 3 + p.beta * p.R) * m ^ 2 +
    (p.R - 1) * (p.beta * n ^ 2 - |p.gamma| * n) / 2
def momentG (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : ℝ :=
  7 * x.h / 12 + p.beta * (p.R + 1) / 8 - p.beta * (B (symInstrument Γ) 0 + p.R * B (symInstrument Γ) 1) / 4 +
    p.gamma * (p.R - 1) * (N (symInstrument Γ) 0).im / 2 -
    2 * x.h * (M (symInstrument Γ) 0 + M (symInstrument Γ) 1).re / 3 +
    x.h * (Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 6
private theorem moment_near_disk (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : let m := Real.sqrt ((Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 2)
    let n := ‖N (symInstrument Γ) 0‖
    m ^ 2 + n ^ 2 ≤ 1 / 4 + (3 + 2 * Lbar p) * deviation p x Γ ∧
      B (symInstrument Γ) 0 + p.R * B (symInstrument Γ) 1 ≤
        p.R - 4 * p.R * m ^ 2 - 2 * (p.R - 1) * n ^ 2 + 6 * p.R * (1 + Lbar p) * deviation p x Γ := by
  intro m n; let t := deviation p x Γ; let a := (1 + Lbar p) * t; have ht : 0 ≤ t := by
    have heps := x.eps_pos; dsimp [t,deviation]
    positivity
  have hLb : 0 ≤ Lbar p := by
    have hβ := p.beta_pos; have hR := p.R_gt_one; dsimp [Lbar]
    positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hbud := moment_budgets (symInstrument Γ); have hc0 : 0 ≤ x.c Γ := add_nonneg
    (diagonal_bounds (symInstrument Γ) 0 (0,1)).1 (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hc1 : x.c Γ ≤ 1 := by
    have hA0 := (diagonal_bounds (symInstrument Γ) 0 (0,0)).1; have hA1 := (diagonal_bounds (symInstrument Γ) 1 (0,0)).1; dsimp [CoupledPoint.c]
    linarith! [hbud.1]
  have hcS := Real.sq_sqrt hc0; have hcRoot : x.c Γ ≤ Real.sqrt (x.c Γ) := by
    nlinarith [Real.sqrt_nonneg (x.c Γ)]
  have hAb (j : Qubit) : |A (symInstrument Γ) j - 1 / 2| ≤ a := by
    have h := current_A_bound p x Γ j; have hroot := Real.sqrt_nonneg (x.c Γ); have habsd := abs_nonneg (x.d Γ); dsimp [a,t,deviation] at *
    nlinarith [x.eps_pos,mul_nonneg hLb hroot,mul_nonneg hLb habsd,mul_nonneg hLb x.eps_pos.le]
  have hD (j : Qubit) : 2 * Complex.normSq (M (symInstrument Γ) j) - 2 * a ≤ D (symInstrument Γ) j := by
    have hg := choi_gram (symInstrument Γ) j (0,0) (1,1); have hd := diagonal_bounds (symInstrument Γ) j (1,1); have hu := (abs_le.mp (hAb j)).2
    change Complex.normSq (M (symInstrument Γ) j) ≤ A (symInstrument Γ) j * D (symInstrument Γ) j at hg; change 0 ≤ D (symInstrument Γ) j ∧ D (symInstrument Γ) j ≤ 1 at hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) ha]
  have hB (j : Qubit) : 2 * Complex.normSq (N (symInstrument Γ) j) - 2 * a ≤ B (symInstrument Γ) j := by
    have hg := choi_gram (symInstrument Γ) j (0,0) (1,0); have hb := diagonal_bounds (symInstrument Γ) j (1,0); have hu := (abs_le.mp (hAb j)).2
    change Complex.normSq (N (symInstrument Γ) j) ≤ A (symInstrument Γ) j * B (symInstrument Γ) j at hg; change 0 ≤ B (symInstrument Γ) j ∧ B (symInstrument Γ) j ≤ 1 at hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) ha]
  have hn0 : n ≤ 1 := choi_norm_bound (symInstrument Γ) 0 (0,0) (1,0); have hn1 := choi_norm_bound (symInstrument Γ) 1 (0,0) (1,0); change ‖N (symInstrument Γ) 1‖ ≤ 1 at hn1
  have hdiff := abs_norm_sub_norm_le (N (symInstrument Γ) 0) ( - N (symInstrument Γ) 1); simp only [norm_neg,sub_neg_eq_add] at hdiff; have hnd : n - ‖N (symInstrument Γ) 1‖ ≤ Real.sqrt (x.c Γ) :=
    (le_abs_self _).trans (hdiff.trans (sum_N_bound (symInstrument Γ)))
  have hns : n + ‖N (symInstrument Γ) 1‖ ≤ 2 := by linarith
  have hnnonneg : 0 ≤ n + ‖N (symInstrument Γ) 1‖ := add_nonneg (norm_nonneg _) (norm_nonneg _); have hnSq : n ^ 2 - 2 * Real.sqrt (x.c Γ) ≤ Complex.normSq (N (symInstrument Γ) 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_left hnd hnnonneg, mul_le_mul_of_nonneg_right hns (Real.sqrt_nonneg (x.c Γ))]
  have hmSq : m ^ 2 = (Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 2 :=
    Real.sq_sqrt (div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num))
  have hB0 := hB 0; have hB1 := hB 1; rw [Complex.normSq_eq_norm_sq] at hB0; change 2 * n ^ 2 - 2 * a ≤ B (symInstrument Γ) 0 at hB0; have hD0 := hD 0; have hD1 := hD 1; have hbTotal := hbud.2.1; have hrootT : Real.sqrt (x.c Γ) ≤ t := by
    dsimp [t,deviation]
    nlinarith [abs_nonneg (x.d Γ),x.eps_pos]
  have hDsum : 4 * m ^ 2 - 4 * a ≤ D (symInstrument Γ) 0 + D (symInstrument Γ) 1 := by nlinarith
  constructor
  · change m ^ 2 + n ^ 2 ≤ 1 / 4 + (3 + 2 * Lbar p) * t
    dsimp [a] at hDsum hB0 hB1
    nlinarith
  · have hR := p.R_gt_one
    have hRD := mul_le_mul_of_nonneg_left hDsum (show 0 ≤ p.R by linarith); have hRB := mul_le_mul_of_nonneg_left hB0 (show 0 ≤ p.R - 1 by linarith); have hbR := congrArg (fun z : ℝ => p.R * z) hbTotal; dsimp [a,t] at ha hRD hRB
    nlinarith
def diskValues (p : Parameters) (h : ℝ) : Set ℝ :=
  {v | ∃ m n : ℝ, 0 ≤ m ∧ 0 ≤ n ∧ m ^ 2 + n ^ 2 ≤ 1 / 4 ∧ v = diskQ p h m n}
def Phi (p : Parameters) (h : ℝ) : ℝ := sInf (diskValues p h)
theorem disk_minimum (p : Parameters) (h : ℝ) : ∃ m n : ℝ, 0 ≤ m ∧ 0 ≤ n ∧ m ^ 2 + n ^ 2 ≤ 1 / 4 ∧ Phi p h = diskQ p h m n ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 ≤ 1 / 4 → diskQ p h m n ≤ diskQ p h a b := by
  let S : Set (ℝ × ℝ) := {v | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 ^ 2 + v.2 ^ 2 ≤ 1 / 4}; have hs : IsClosed S := by
    have hg : Continuous (fun v : ℝ × ℝ => v.1 ^ 2 + v.2 ^ 2) := by fun_prop
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter (isClosed_le hg continuous_const))
  have hcompact : IsCompact S := by
    refine ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).prod (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).of_isClosed_subset hs ?_
    intro v hv; exact ⟨⟨hv.1,by nlinarith [hv.2.2,sq_nonneg v.2]⟩, ⟨hv.2.1,by nlinarith [hv.2.2,sq_nonneg v.1]⟩⟩
  have hne : S.Nonempty := ⟨(0,0),by dsimp [S]; norm_num⟩; have hf : Continuous (fun v : ℝ × ℝ => diskQ p h v.1 v.2) := by unfold diskQ; fun_prop
  have himg : diskValues p h = (fun v : ℝ × ℝ => diskQ p h v.1 v.2) '' S := by
    ext z; constructor
    · rintro ⟨m,n,hm,hn,hd,rfl⟩; exact ⟨(m,n),⟨hm,hn,hd⟩,rfl⟩
    · rintro ⟨v,hv,rfl⟩; exact ⟨v.1,v.2,hv.1,hv.2.1,hv.2.2,rfl⟩
  obtain ⟨v,hv,hval,hmin⟩ := hcompact.exists_sInf_image_eq_and_le hne hf.continuousOn
  refine ⟨v.1,v.2,hv.1,hv.2.1,hv.2.2,?_,?_⟩
  · simpa [Phi,himg] using hval
  · intro a b ha hb hd; exact hmin (a,b) ⟨ha,hb,hd⟩
private theorem disk_inf_le (p : Parameters) (h : ℝ) {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hd : m ^ 2 + n ^ 2 ≤ 1 / 4) : Phi p h ≤ diskQ p h m n := by
  obtain ⟨a,b,_,_,_,hPhi,hmin⟩ := disk_minimum p h
  rw [hPhi]; exact hmin m n hm hn hd
private theorem radial_projection {m n delta : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hdelta : 0 ≤ delta) (hd : m ^ 2 + n ^ 2 ≤ 1 / 4 + delta) : ∃ m' n' : ℝ, 0 ≤ m' ∧ 0 ≤ n' ∧ m' ^ 2 + n' ^ 2 ≤ 1 / 4 ∧ m' ≤ m ∧ n' ≤ n ∧ |m - m'| ≤ delta ∧ |n - n'| ≤ delta := by
  by_cases hin : m ^ 2 + n ^ 2 ≤ 1 / 4
  · exact ⟨m,n,hm,hn,hin,le_rfl,le_rfl,by simpa using hdelta,by simpa using hdelta⟩
  let rho := Real.sqrt (m ^ 2 + n ^ 2); have hr : rho ^ 2 = m ^ 2 + n ^ 2 := Real.sq_sqrt (by positivity); have hr0 : 0 ≤ rho := Real.sqrt_nonneg _; have hrh : 1 / 2 < rho := by nlinarith
  have hp : 0 < 2 * rho := by linarith
  have hmR : m ≤ rho := by nlinarith [sq_nonneg n]
  have hnR : n ≤ rho := by nlinarith [sq_nonneg m]
  have hgap : rho - 1 / 2 ≤ delta := by nlinarith [sq_nonneg (rho - 1 / 2)]
  have hproj (a : ℝ) (ha : 0 ≤ a) (haR : a ≤ rho) : a / (2 * rho) ≤ a ∧ |a - a / (2 * rho)| ≤ delta := by
    have hsmall : a / (2 * rho) ≤ a := (div_le_iff₀ hp).mpr
      (by nlinarith [mul_nonneg ha (show 0 ≤ 2 * rho - 1 by linarith)])
    refine ⟨hsmall,?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hsmall)]; have he : a - a / (2 * rho) = a * (2 * rho - 1) / (2 * rho) := by field_simp <;> ring
    rw [he]
    calc
      _ ≤ rho - 1 / 2 := (div_le_iff₀ hp).mpr
        (by nlinarith [mul_nonneg (sub_nonneg.mpr haR) (show 0 ≤ 2 * rho - 1 by linarith)])
      _ ≤ delta := hgap
  refine ⟨m / (2 * rho),n / (2 * rho),div_nonneg hm hp.le,div_nonneg hn hp.le,?_, (hproj m hm hmR).1,(hproj n hn hnR).1,(hproj m hm hmR).2,(hproj n hn hnR).2⟩
  apply le_of_eq
  field_simp [hp.ne',show rho ≠ 0 by linarith]
  nlinarith [hr]
def Qlip (p : Parameters) : ℝ := 2 * p.H + 2 * p.beta * p.R + (p.R - 1) * (p.beta + |p.gamma| / 2)
private theorem disk_lipschitz (p : Parameters) {h m n m' n' delta : ℝ} (hh : 0 ≤ h) (hH : h ≤ p.H) (hm : 0 ≤ m) (hm1 : m ≤ 1) (hn : 0 ≤ n) (hn1 : n ≤ 1) (hm' : 0 ≤ m') (hm1' : m' ≤ 1) (hn' : 0 ≤ n') (hn1' : n' ≤ 1) (hdelta : 0 ≤ delta) (hmd : |m - m'| ≤ delta) (hnd : |n - n'| ≤ delta) : |diskQ p h m n - diskQ p h m' n'| ≤ Qlip p * delta := by
  have hs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) (h : |a - b| ≤ delta) : |a ^ 2 - b ^ 2| ≤ 2 * delta := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg ha hb)]
    nlinarith [mul_le_mul_of_nonneg_right h (add_nonneg ha hb), mul_nonneg (show 0 ≤ 2 - a - b by linarith) hdelta]
  have hms := hs m m' hm hm' hm1 hm1' hmd; have hns := hs n n' hn hn' hn1 hn1' hnd; have hβ := p.beta_pos; have hR := p.R_gt_one; have hH0 := p.H_pos; have h0 : 0 ≤ h / 3 + p.beta * p.R := by positivity
  have h1 : 0 ≤ (p.R - 1) / 2 := by linarith
  let a := - (4 * h / 3) * (m - m'); let b := (h / 3 + p.beta * p.R) * (m ^ 2 - m' ^ 2); let c := (p.R - 1) / 2 * (p.beta * (n ^ 2 - n' ^ 2) - |p.gamma| * (n - n')); have he : diskQ p h m n - diskQ p h m' n' = a + b + c := by dsimp [diskQ,a,b,c]; ring
  have ha : |a| ≤ (4 * p.H / 3) * delta := by
    dsimp [a]; rw [abs_mul,abs_neg,abs_of_nonneg (show 0 ≤ 4 * h / 3 by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hmd (show 0 ≤ 4 * h / 3 by positivity), mul_le_mul_of_nonneg_right hH hdelta]
  have hb : |b| ≤ 2 * (p.H / 3 + p.beta * p.R) * delta := by
    dsimp [b]; rw [abs_mul,abs_of_nonneg h0]
    nlinarith [mul_le_mul_of_nonneg_left hms h0,mul_le_mul_of_nonneg_right hH hdelta]
  have hc : |c| ≤ (p.R - 1) / 2 * (2 * p.beta + |p.gamma|) * delta := by
    dsimp [c]; rw [abs_mul,abs_of_nonneg h1]; have hs0 := abs_sub (p.beta * (n ^ 2 - n' ^ 2)) (|p.gamma| * (n - n')); simp only [abs_mul,abs_of_pos hβ,abs_abs] at hs0; have hs1 := mul_le_mul_of_nonneg_left hns hβ.le
    have hs2 := mul_le_mul_of_nonneg_left hnd (abs_nonneg p.gamma); have he : |p.beta * (n ^ 2 - n' ^ 2) - |p.gamma| * (n - n')| ≤ (2 * p.beta + |p.gamma|) * delta := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left he h1]
  rw [he]; dsimp [Qlip]
  nlinarith [abs_add_le (a + b) c,abs_add_le a b]
def Cdisk (p : Parameters) : ℝ := 1 + 3 * p.beta * p.R * (1 + Lbar p) / 2 + Qlip p * (3 + 2 * Lbar p)
private theorem moment_G_lower_Phi (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : Phi p x.h - Cdisk p * deviation p x Γ ≤ momentG p x Γ := by
  let m := Real.sqrt ((Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 2); let n := ‖N (symInstrument Γ) 0‖; let t := deviation p x Γ; have hm0 : 0 ≤ m := Real.sqrt_nonneg _; have hn0 : 0 ≤ n := norm_nonneg _
  have hmSq : m ^ 2 = (Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 2 :=
    Real.sq_sqrt (div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num))
  have hn1 : n ≤ 1 := choi_norm_bound (symInstrument Γ) 0 (0,0) (1,0); have hmj (j : Qubit) : ‖M (symInstrument Γ) j‖ ≤ 1 := choi_norm_bound (symInstrument Γ) j (0,0) (1,1); have hm1 : m ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hmSq
    nlinarith [hmj 0,hmj 1,norm_nonneg (M (symInstrument Γ) 0),norm_nonneg (M (symInstrument Γ) 1)]
  have ht : 0 ≤ t := by have heps := x.eps_pos; dsimp [t,deviation]; positivity
  have hLb : 0 ≤ Lbar p := by have hβ := p.beta_pos; have hR := p.R_gt_one; dsimp [Lbar]; positivity
  obtain ⟨hdisk,hB⟩ := moment_near_disk p x Γ
  change m ^ 2 + n ^ 2 ≤ 1 / 4 + (3 + 2 * Lbar p) * t at hdisk
  obtain ⟨m',n',hm'0,hn'0,hd',hm'm,hn'n,hmd,hnd⟩ :=
    radial_projection hm0 hn0 (mul_nonneg (by positivity) ht) hdisk
  have hPhi := disk_inf_le p x.h hm'0 hn'0 hd'; have hQ := disk_lipschitz p x.h_nonneg x.h_le hm0 hm1 hn0 hn1 hm'0
    (hm'm.trans hm1) hn'0 (hn'n.trans hn1) (mul_nonneg (by positivity) ht) hmd hnd
  have hMsum : (M (symInstrument Γ) 0 + M (symInstrument Γ) 1).re ≤ 2 * m := by
    have hr0 := Complex.re_le_norm (M (symInstrument Γ) 0); have hr1 := Complex.re_le_norm (M (symInstrument Γ) 1); rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hmSq; rw [Complex.add_re]
    nlinarith [sq_nonneg (‖M (symInstrument Γ) 0‖ - ‖M (symInstrument Γ) 1‖), norm_nonneg (M (symInstrument Γ) 0),norm_nonneg (M (symInstrument Γ) 1)]
  have hIm : - |p.gamma| * n ≤ p.gamma * (N (symInstrument Γ) 0).im := by
    have hab : |p.gamma * (N (symInstrument Γ) 0).im| ≤ |p.gamma| * n := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg p.gamma)
    nlinarith [neg_abs_le (p.gamma * (N (symInstrument Γ) 0).im)]
  have hbase : diskQ p x.h m n - 3 * p.beta * p.R * (1 + Lbar p) * t / 2 ≤ momentG p x Γ := by
    have hβ := p.beta_pos; have hR := p.R_gt_one; change B (symInstrument Γ) 0 + p.R * B (symInstrument Γ) 1 ≤
      p.R - 4 * p.R * m ^ 2 - 2 * (p.R - 1) * n ^ 2 + 6 * p.R * (1 + Lbar p) * t at hB
    have hh := x.h_nonneg; have hW := mul_le_mul_of_nonneg_left hB (show 0 ≤ p.beta / 4 by positivity); have hMR := mul_le_mul_of_nonneg_left hMsum (show 0 ≤ 2 * x.h / 3 by positivity); simp only [Complex.add_re] at hMR
    have hNI := mul_le_mul_of_nonneg_left hIm (show 0 ≤ (p.R - 1) / 2 by linarith); have hMQ := congrArg (fun z : ℝ => x.h * z / 3) hmSq; dsimp [diskQ,momentG]; change B (symInstrument Γ) 0 + p.R * B (symInstrument Γ) 1 ≤
      p.R - 4 * p.R * m ^ 2 - 2 * (p.R - 1) * n ^ 2 + 6 * p.R * (1 + Lbar p) * t at hB
    nlinarith
  have hQ' := (abs_le.mp hQ).1; dsimp [Cdisk,t] at *
  nlinarith
private theorem normsq_lipschitz {z w : ℂ} {v delta : ℝ} (hz : ‖z‖ ≤ v) (hw : ‖w‖ ≤ v) (hd : ‖z - w‖ ≤ delta) : |Complex.normSq z - Complex.normSq w| ≤ 2 * v * delta := by
  have hδ : 0 ≤ delta := (norm_nonneg _).trans hd; have hv : 0 ≤ v := (norm_nonneg _).trans hz; rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,sq_sub_sq,abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hn := (abs_norm_sub_norm_le z w).trans hd
  nlinarith [mul_le_mul_of_nonneg_right hn (add_nonneg (norm_nonneg z) (norm_nonneg w)), mul_nonneg (show 0 ≤ 2 * v - ‖z‖ - ‖w‖ by linarith) hδ]
def alpha (p : Parameters) : ℝ := 2 * p.R * (p.beta + |p.gamma|)
def size (p : Parameters) : ℝ := 2 + alpha p
private theorem alpha_nonneg (p : Parameters) : 0 ≤ alpha p := by
  have hb := p.beta_pos; have hR := p.R_gt_one; dsimp [alpha]; positivity
private theorem size_ge (p : Parameters) : 2 ≤ size p := by
  dsimp [size]; linarith [alpha_nonneg p]
private theorem coupled_T_bound (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (he : x.eps ≤ 1) (j : Qubit) : ‖T (symInstrument Γ) p.beta p.gamma (x.weights j) j - M (symInstrument Γ) j‖ ≤ alpha p * x.eps ∧ ‖T (symInstrument Γ) p.beta p.gamma (x.weights j) j‖ ≤ size p - 1 := by
  have h := T_difference_bound (symInstrument Γ) (gamma := p.gamma) p.beta_pos (x.weights_nonneg j) j; have hw : x.weights j ≤ p.R * x.eps := by
    have hR := p.R_gt_one; have he0 := x.eps_pos
    fin_cases j <;> simp [CoupledPoint.weights,rate] <;> nlinarith
  have h' : ‖T (symInstrument Γ) p.beta p.gamma (x.weights j) j - M (symInstrument Γ) j‖ ≤ alpha p * x.eps := by
    dsimp [alpha]
    calc
      _ ≤ 2 * (p.beta + |p.gamma|) * (p.R * x.eps) := h.trans (mul_le_mul_of_nonneg_left hw (by have hb := p.beta_pos; positivity))
      _ = _ := by ring
  refine ⟨h',?_⟩
  have ht := norm_add_le (T (symInstrument Γ) p.beta p.gamma (x.weights j) j - M (symInstrument Γ) j)
    (M (symInstrument Γ) j)
  simp only [sub_add_cancel] at ht; have hM : ‖M (symInstrument Γ) j‖ ≤ 1 := choi_norm_bound (symInstrument Γ) j (0,0) (1,1); dsimp [size]
  nlinarith [hM, mul_le_mul_of_nonneg_left he (alpha_nonneg p)]
private theorem weighted_center_bound (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (he : x.eps ≤ 1) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (delta : ℝ) (hδ : |a - 1 / 2| ≤ delta) (j : Qubit) : |a * Complex.normSq (1 - (a : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights j) j) - (1 / 2) * Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) j)| ≤ (size p ^ 2 + 2 * size p) * delta + 2 * size p * alpha p * x.eps := by
  let Z := T (symInstrument Γ) p.beta p.gamma (x.weights j) j; let Y := M (symInstrument Γ) j; let z : ℂ := 1 - (a : ℂ) * Z; let y : ℂ := 1 - (1 / 2 : ℂ) * Y; have hT := coupled_T_bound p x Γ he j
  have hY : ‖Y‖ ≤ 1 := choi_norm_bound (symInstrument Γ) j (0,0) (1,1); have hv := size_ge p; have hv0 : 0 ≤ size p := (by norm_num : (0 : ℝ) ≤ 2).trans hv; have hδ0 : 0 ≤ delta := (abs_nonneg _).trans hδ; have hz : ‖z‖ ≤ size p := by
    have hn := norm_sub_le (1 : ℂ) ((a : ℂ) * Z); simp only [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] at hn; dsimp [z]
    nlinarith [mul_le_mul_of_nonneg_left ha1 (norm_nonneg Z)]
  have hy : ‖y‖ ≤ size p := by
    have hn := norm_sub_le (1 : ℂ) ((1 / 2 : ℂ) * Y); norm_num [norm_mul] at hn; dsimp [y]; linarith
  have hdiff : ‖z - y‖ ≤ delta + alpha p * x.eps := by
    have hid : z - y = - (a : ℂ) * (Z - Y) - ((a - 1 / 2 : ℝ) : ℂ) * Y := by
      dsimp [z,y]; push_cast; ring
    rw [hid]; have hn := norm_sub_le ( - (a : ℂ) * (Z - Y)) (((a - 1 / 2 : ℝ) : ℂ) * Y); simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] at hn
    nlinarith [mul_le_mul_of_nonneg_left ha1 (norm_nonneg (Z - Y)), mul_le_mul_of_nonneg_left hY (abs_nonneg (a - 1 / 2))]
  have hsq := normsq_lipschitz hz hy hdiff; have hzsq : Complex.normSq z ≤ size p ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hid : a * Complex.normSq z - (1 / 2) * Complex.normSq y = (a - 1 / 2) * Complex.normSq z + (1 / 2) * (Complex.normSq z - Complex.normSq y) := by ring
  change |a * Complex.normSq z - (1 / 2) * Complex.normSq y| ≤ _; rw [hid]; have hn := abs_add_le ((a - 1 / 2) * Complex.normSq z) ((1 / 2) * (Complex.normSq z - Complex.normSq y)); simp only [abs_mul,abs_of_nonneg (Complex.normSq_nonneg z)] at hn
  norm_num at hn
  nlinarith [mul_le_mul hδ hzsq (Complex.normSq_nonneg z) hδ0, mul_nonneg hv0 hδ0,mul_nonneg (mul_nonneg hv0 (alpha_nonneg p)) x.eps_pos.le]
def center (Γ : Instrument) : ℝ :=
  (Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 0) + Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 1)) / 2
private theorem center_bounds (Γ : Instrument) : 0 ≤ center Γ ∧ center Γ ≤ 4 := by
  have hs (j : Qubit) : Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) j) ≤ 4 := by
    have hn := norm_sub_le (1 : ℂ) ((1 / 2 : ℂ) * M (symInstrument Γ) j); norm_num [norm_mul] at hn; rw [Complex.normSq_eq_norm_sq]; have hM : ‖M (symInstrument Γ) j‖ ≤ 1 := choi_norm_bound (symInstrument Γ) j (0,0) (1,1)
    nlinarith [hM, norm_nonneg (1 - (1 / 2 : ℂ) * M (symInstrument Γ) j),norm_nonneg (M (symInstrument Γ) j)]
  dsimp [center]
  constructor
  · exact div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num)
  · linarith [hs 0,hs 1]
private theorem center_identity (Γ : Instrument) : center Γ = 1 - (M (symInstrument Γ) 0 + M (symInstrument Γ) 1).re / 2 + (Complex.normSq (M (symInstrument Γ) 0) + Complex.normSq (M (symInstrument Γ) 1)) / 8 := by
  simp [center,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring
def Cgain (p : Parameters) (K : ℝ) : ℝ :=
  1 + 8 * p.H * (size p ^ 2 + 2 * size p) / 3 + 16 * p.H * size p * alpha p / 3 +
    16 * p.H ^ 2 / 3 + 16 * (K + p.H) * p.H * size p ^ 2 / 9
private theorem balanced_rayleigh_gain (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (K : ℝ) (hK : 0 ≤ K) (he : x.eps ≤ 1) (hs : 1 / 2 ≤ x.s Γ) (hne : x.error Γ ≤ 3 / 4 + K * x.eps) : x.lambda Γ + x.eps * (4 * x.h / 3) * center Γ - Cgain p K * x.eps * |x.d Γ| - Cgain p K * x.eps ^ 2 ≤ x.error Γ := by
  let q := x.f Γ 1 / x.s Γ; have hs0 : 0 < x.s Γ := by linarith
  have hf0 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 0) (x.weights_legal 0) 0; have hf1 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 1) (x.weights_legal 1) 1; change 0 ≤ x.f Γ 0 ∧ x.f Γ 0 ≤ 1 at hf0
  change 0 ≤ x.f Γ 1 ∧ x.f Γ 1 ≤ 1 at hf1; have hq0 : 0 ≤ q := div_nonneg hf1.1 hs0.le; have hq1 : q ≤ 1 := (div_le_one hs0).mpr (by dsimp [CoupledPoint.s]; linarith); have hqd : |q - 1 / 2| ≤ |x.d Γ| := by
    have hid : q - 1 / 2 = - x.d Γ / (2 * x.s Γ) := by
      dsimp [q,CoupledPoint.d]; field_simp [hs0.ne']; dsimp [CoupledPoint.s]; ring
    rw [hid,abs_div,abs_neg,abs_of_pos (show 0 < 2 * x.s Γ by positivity)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * x.s Γ)).mpr
    nlinarith [abs_nonneg (x.d Γ)]
  have h1qd : |(1 - q) - 1 / 2| ≤ |x.d Γ| := by
    convert hqd using 1
    rw [show (1 - q) - 1 / 2 = - (q - 1 / 2) by ring,abs_neg]
  have hc : ∑ j, Complex.normSq (weightInput q j) = 1 := by
    simp [weightInput,Fin.sum_univ_two,Complex.normSq_ofReal,← sq, Real.sq_sqrt hq0,Real.sq_sqrt (sub_nonneg.mpr hq1)]
  let ell := x.h * x.eps; let Z := q * Complex.normSq (1 - (q : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 0) 0) +
    (1 - q) * Complex.normSq (1 - ((1 - q : ℝ) : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 1) 1)
  let nu := (1 - ell) * ell * Z; have hell : 0 ≤ ell := mul_nonneg x.h_nonneg x.eps_pos.le; have hell1 : ell ≤ 1 := x.ell_le; have hellH : ell ≤ p.H * x.eps := mul_le_mul_of_nonneg_right x.h_le x.eps_pos.le; have hv := size_ge p
  have hv0 : 0 ≤ size p := (by norm_num : (0 : ℝ) ≤ 2).trans hv; have hα := alpha_nonneg p; have hh := p.H_pos; have he0 := x.eps_pos.le; have hZ0 : 0 ≤ Z := add_nonneg (mul_nonneg hq0 (Complex.normSq_nonneg _))
    (mul_nonneg (sub_nonneg.mpr hq1) (Complex.normSq_nonneg _))
  have hns (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (j : Qubit) : Complex.normSq (1 - (a : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights j) j) ≤ size p ^ 2 := by
    have hT := (coupled_T_bound p x Γ he j).2; have hn := norm_sub_le (1 : ℂ) ((a : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights j) j); simp only [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha] at hn
    rw [Complex.normSq_eq_norm_sq]; have hn0 := norm_nonneg (1 - (a : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights j) j)
    nlinarith [mul_le_mul_of_nonneg_left ha1 (norm_nonneg (T (symInstrument Γ) p.beta p.gamma (x.weights j) j))]
  have hZ1 : Z ≤ size p ^ 2 := by
    have h0 := mul_le_mul_of_nonneg_left (hns q hq0 hq1 0) hq0; have h1 := mul_le_mul_of_nonneg_left (hns (1 - q) (by linarith) (by linarith) 1) (by linarith : 0 ≤ 1 - q); dsimp [Z]; nlinarith
  have hnu0 : 0 ≤ nu := by dsimp [nu]; positivity
  have hnu1 : nu ≤ p.H * size p ^ 2 * x.eps := by
    calc
      nu ≤ ell * Z := by dsimp [nu]; nlinarith [mul_nonneg hell hZ0]
      _ ≤ ell * size p ^ 2 := mul_le_mul_of_nonneg_left hZ1 hell
      _ ≤ p.H * x.eps * size p ^ 2 := mul_le_mul_of_nonneg_right hellH (sq_nonneg _)
      _ = _ := by ring
  have hray := rayleigh_trial_bound ell p.beta p.gamma x.weights hell hell1 p.beta_pos
    x.weights_nonneg x.weights_legal Γ q hq0 hq1 hc
  have hnu := offdiagonal_norm_identity ell p.beta p.gamma x.weights hell hell1 p.beta_pos
    x.weights_nonneg x.weights_legal Γ q hq0 hq1 hc
  dsimp only at hray; rw [hnu] at hray; have hid : (1 - ell) * (1 - q ^ 2 * x.f Γ 0 - (1 - q) ^ 2 * x.f Γ 1) = x.lambda Γ := by
    dsimp [q,CoupledPoint.lambda]; field_simp [hs0.ne']; dsimp [CoupledPoint.s,ell]; ring
  change (1 - ell) * (1 - q ^ 2 * x.f Γ 0 - (1 - q) ^ 2 * x.f Γ 1) + 4 * nu / 3 -
    (16 / 9) * (x.error Γ - 3 / 4 + ell) * nu ≤ x.error Γ at hray
  rw [hid] at hray; have hrem : (16 / 9) * (x.error Γ - 3 / 4 + ell) * nu ≤ (16 / 9) * (K + p.H) * p.H * size p ^ 2 * x.eps ^ 2 := by
    have hc0 : 0 ≤ (K + p.H) * x.eps := by have hh := p.H_pos; positivity
    have h0 := mul_le_mul_of_nonneg_right (show x.error Γ - 3 / 4 + ell ≤ (K + p.H) * x.eps by nlinarith) hnu0; have h1 := mul_le_mul_of_nonneg_left hnu1 hc0
    nlinarith
  have h0 := weighted_center_bound p x Γ he q hq0 hq1 _ hqd 0; have h1 := weighted_center_bound p x Γ he (1 - q) (by linarith) (by linarith) _ h1qd 1; have hdiff : |Z - center Γ| ≤ 2 * (size p ^ 2 + 2 * size p) * |x.d Γ| + 4 * size p * alpha p * x.eps := by
    have ha := abs_add_le
      (q * Complex.normSq (1 - (q : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 0) 0) - (1 / 2) * Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 0))
      ((1 - q) * Complex.normSq (1 - ((1 - q : ℝ) : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 1) 1) - (1 / 2) * Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 1))
    have hid : Z - center Γ = (q * Complex.normSq (1 - (q : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 0) 0) - (1 / 2) * Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 0)) + ((1 - q) * Complex.normSq (1 - ((1 - q : ℝ) : ℂ) * T (symInstrument Γ) p.beta p.gamma (x.weights 1) 1) - (1 / 2) * Complex.normSq (1 - (1 / 2 : ℂ) * M (symInstrument Γ) 1)) := by dsimp [Z,center]; ring
    rw [hid]; linarith
  let err := 2 * (size p ^ 2 + 2 * size p) * |x.d Γ| + 4 * size p * alpha p * x.eps; have herr : 0 ≤ err := by dsimp [err]; positivity
  have hgain : ell * center Γ - ell * err - 4 * ell ^ 2 ≤ nu := by
    have h0 := mul_le_mul_of_nonneg_left (abs_le.mp hdiff).1 (mul_nonneg (sub_nonneg.mpr hell1) hell); have hcen := center_bounds Γ; dsimp [nu,err] at *
    nlinarith [mul_le_mul_of_nonneg_left hcen.2 (sq_nonneg ell), mul_nonneg (sq_nonneg ell) herr]
  have hE : ell * err ≤ 2 * p.H * (size p ^ 2 + 2 * size p) * x.eps * |x.d Γ| + 4 * p.H * size p * alpha p * x.eps ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hellH herr; dsimp [err] at h ⊢; nlinarith
  have hellSq : ell ^ 2 ≤ p.H ^ 2 * x.eps ^ 2 := by
    nlinarith [mul_nonneg hell (sub_nonneg.mpr hellH)]
  have hC0 : 0 ≤ Cgain p K := by have hh := p.H_pos; dsimp [Cgain]; positivity
  have hab : 0 ≤ x.eps * |x.d Γ| := mul_nonneg x.eps_pos.le (abs_nonneg _); have hC1 : 8 * p.H * (size p ^ 2 + 2 * size p) / 3 ≤ Cgain p K := by
    have hh := p.H_pos; dsimp [Cgain]; have h0 : 0 ≤ p.H * size p * alpha p := by positivity
    have h1 : 0 ≤ (K + p.H) * p.H * size p ^ 2 := by positivity
    nlinarith [sq_nonneg p.H]
  have hC2 : 16 * p.H * size p * alpha p / 3 + 16 * p.H ^ 2 / 3 + (16 / 9) * (K + p.H) * p.H * size p ^ 2 ≤ Cgain p K := by
    have hh := p.H_pos; dsimp [Cgain]; have h0 : 0 ≤ p.H * (size p ^ 2 + 2 * size p) := by positivity
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hC1 hab; have h2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg x.eps); dsimp [ell] at hgain hE hellSq
  nlinarith
def coefficient (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : ℝ :=
 - 3 * x.h / 4 - (L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1) / 4 +
    4 * x.h / 3 * center Γ
def Ccoef (p : Parameters) : ℝ := p.beta * (1 + p.R) * (1 + Lbar p) / 4 + |p.gamma| * p.R / 2
private theorem coefficient_lower (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) : momentG p x Γ - Ccoef p * deviation p x Γ ≤ coefficient p x Γ := by
  let t := deviation p x Γ; have he := x.eps_pos; have hR := p.R_gt_one; have hb := p.beta_pos; have hLb : 0 ≤ Lbar p := by dsimp [Lbar]; positivity
  have hc0 : 0 ≤ x.c Γ := add_nonneg (diagonal_bounds (symInstrument Γ) 0 (0,1)).1
    (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hc1 : x.c Γ ≤ 1 := by
    have hbud := (moment_budgets (symInstrument Γ)).1; have hA0 := (diagonal_bounds (symInstrument Γ) 0 (0,0)).1; have hA1 := (diagonal_bounds (symInstrument Γ) 1 (0,0)).1; dsimp [CoupledPoint.c]; linarith!
  have hroot : x.c Γ ≤ Real.sqrt (x.c Γ) := by
    nlinarith [Real.sq_sqrt hc0,Real.sqrt_nonneg (x.c Γ)]
  have ht : 0 ≤ t := by dsimp [t,deviation]; positivity
  have hA (j : Qubit) : - (1 + Lbar p) * t ≤ A (symInstrument Γ) j - 1 / 2 := by
    have h := (abs_le.mp (current_A_bound p x Γ j)).1; dsimp [t,deviation]
    nlinarith [abs_nonneg (x.d Γ),Real.sqrt_nonneg (x.c Γ), mul_nonneg hLb (Real.sqrt_nonneg (x.c Γ)),mul_nonneg hLb (abs_nonneg (x.d Γ))]
  have hN : |p.gamma * (N (symInstrument Γ) 0 + N (symInstrument Γ) 1).im| ≤ |p.gamma| * t := by
    have hs := sum_N_bound (symInstrument Γ); have hi := (Complex.abs_im_le_norm (N (symInstrument Γ) 0 + N (symInstrument Γ) 1)).trans hs; rw [abs_mul]
    calc
      _ ≤ |p.gamma| * Real.sqrt (x.c Γ) := mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      _ ≤ _ := by dsimp [t,deviation]; nlinarith [abs_nonneg (x.d Γ),abs_nonneg p.gamma]
  have hA0 := mul_le_mul_of_nonneg_left (hA 0) (show 0 ≤ p.beta / 4 by positivity); have hA1 := mul_le_mul_of_nonneg_left (hA 1) (show 0 ≤ p.beta * p.R / 4 by positivity)
  have hNI := mul_le_mul_of_nonneg_left (abs_le.mp hN).2 (show 0 ≤ p.R / 2 by positivity)
  have hid : coefficient p x Γ - momentG p x Γ = p.beta / 4 * (A (symInstrument Γ) 0 - 1 / 2) + p.beta * p.R / 4 * (A (symInstrument Γ) 1 - 1 / 2) - p.R / 2 * (p.gamma * (N (symInstrument Γ) 0 + N (symInstrument Γ) 1).im) := by
    rw [coefficient,center_identity]; simp [momentG,L,rate,Complex.add_im]
    ring
  dsimp [Ccoef]
  nlinarith
def defectConstant (p : Parameters) (K : ℝ) : ℝ :=
  1 + Cgain p K + Ccoef p + Cdisk p + p.H * Lbar p / 4
private theorem constants_nonneg (p : Parameters) (K : ℝ) (hK : 0 ≤ K) : 0 ≤ Lbar p ∧ 0 ≤ Cgain p K ∧ 0 ≤ Ccoef p ∧ 0 ≤ Cdisk p := by
  have hb := p.beta_pos; have hR := p.R_gt_one; have hH := p.H_pos; have hα := alpha_nonneg p; have hv := size_ge p; have hv0 : 0 ≤ size p := (by norm_num : (0 : ℝ) ≤ 2).trans hv; have hLb : 0 ≤ Lbar p := by dsimp [Lbar]; positivity
  refine ⟨hLb,?_,?_,?_⟩
  · dsimp [Cgain]; positivity
  · dsimp [Ccoef]; positivity
  · dsimp [Cdisk,Qlip]; positivity
private theorem uniform_defect_bound (p : Parameters) (x : CoupledPoint p) (Γ : Instrument) (K : ℝ) (hK : 0 ≤ K) (he : x.eps ≤ 1) (hrare : x.h * x.eps ≤ 1 / 2) (hs : 1 / 2 ≤ x.s Γ) (hne : x.error Γ ≤ 3 / 4 + K * x.eps) : 3 / 4 + x.eps * Phi p x.h + x.c Γ / 8 + (x.d Γ) ^ 2 / 16 - defectConstant p K * x.eps * (Real.sqrt (x.c Γ) + |x.d Γ|) - defectConstant p K * x.eps ^ 2 ≤ x.error Γ := by
  have hs0 : 0 < x.s Γ := by linarith
  have hray := balanced_rayleigh_gain p x Γ K hK he hs hne; have hco := mul_le_mul_of_nonneg_left (coefficient_lower p x Γ) x.eps_pos.le; have hPhi := mul_le_mul_of_nonneg_left (moment_G_lower_Phi p x Γ) x.eps_pos.le
  have hdec := lambda_decomposition p x Γ hs0; have hf0 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 0) (x.weights_legal 0) 0; have hf1 := F_bounds (symInstrument Γ) p.beta_pos (x.weights_nonneg 1) (x.weights_legal 1) 1
  have hs2 : x.s Γ ≤ 2 := by dsimp [CoupledPoint.s,CoupledPoint.f]; linarith
  have hc : 0 ≤ x.c Γ := add_nonneg (diagonal_bounds (symInstrument Γ) 0 (0,1)).1
    (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hr0 : 1 / 2 ≤ 1 - x.h * x.eps := by linarith
  have hcostC : x.c Γ / 8 ≤ (1 - x.h * x.eps) * (x.c Γ / 4) := by nlinarith
  have hcostD : (x.d Γ) ^ 2 / 16 ≤ (1 - x.h * x.eps) * ((x.d Γ) ^ 2 / (4 * x.s Γ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 4 * x.s Γ)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr0) (sq_nonneg (x.d Γ)), mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg (x.d Γ))]
  have hL := L_sum_bound (symInstrument Γ) (gamma := p.gamma) p.beta_pos p.R_gt_one; let ls := L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1; have hLs : - Lbar p ≤ ls := by
    have ha := neg_abs_le (L (symInstrument Γ) p.beta p.gamma p.R 0); have hb := neg_abs_le (L (symInstrument Γ) p.beta p.gamma p.R 1)
    change |L (symInstrument Γ) p.beta p.gamma p.R 0| + |L (symInstrument Γ) p.beta p.gamma p.R 1| ≤ Lbar p at hL; dsimp [ls]; linarith
  have hrem : - (p.H * Lbar p / 4) * x.eps ^ 2 ≤ x.h * x.eps ^ 2 * ls / 4 := by
    have hLb := (constants_nonneg p K hK).1; have h0 := mul_le_mul_of_nonneg_left hLs (mul_nonneg x.h_nonneg (sq_nonneg x.eps)); have h1 := mul_le_mul_of_nonneg_right x.h_le (mul_nonneg hLb (sq_nonneg x.eps))
    nlinarith
  have hlam : 3 / 4 + x.eps * coefficient p x Γ + x.c Γ / 8 + (x.d Γ) ^ 2 / 16 - (p.H * Lbar p / 4) * x.eps ^ 2 ≤ x.lambda Γ + x.eps * (4 * x.h / 3) * center Γ := by
    change x.lambda Γ - 3 / 4 = - 3 * x.h * x.eps / 4 - (1 - x.h * x.eps) * x.eps * ls / 4 +
      (1 - x.h * x.eps) * (x.c Γ / 4 + (x.d Γ) ^ 2 / (4 * x.s Γ)) at hdec
    dsimp [coefficient]; change _ ≤ _ at hrem; dsimp [ls] at *
    nlinarith
  obtain ⟨hLb,hgain,hcoef,hdisk⟩ := constants_nonneg p K hK
  have hh := p.H_pos; have hroot := Real.sqrt_nonneg (x.c Γ); have hab := abs_nonneg (x.d Γ); have he0 := x.eps_pos.le; have hD1 : Cgain p K + Ccoef p + Cdisk p ≤ defectConstant p K := by
    dsimp [defectConstant]; nlinarith
  have hD2 : Cgain p K + Ccoef p + Cdisk p + p.H * Lbar p / 4 ≤ defectConstant p K := by
    dsimp [defectConstant]; linarith
  have ha1 := mul_le_mul_of_nonneg_right hD1 (mul_nonneg he0 (add_nonneg hroot hab)); have ha2 := mul_le_mul_of_nonneg_right hD2 (sq_nonneg x.eps); have hg0 : 0 ≤ Cgain p K * x.eps * Real.sqrt (x.c Γ) := by positivity
  dsimp [deviation] at hco hPhi
  nlinarith
/-- The actual complete-reference error retains both current defects uniformly.
The constants precede the lawful coupled point and the arbitrary common instrument. -/
theorem current_moment_defect_lower_bound (p : Parameters) (K : ℝ) (hK : 0 ≤ K) :
    ∃ b : ℝ, 0 < b ∧ ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ (x : CoupledPoint p) (Γ : Instrument), x.eps < epsStar →
        x.error Γ ≤ 3 / 4 + K * x.eps →
        3 / 4 + x.eps * Phi p x.h + x.c Γ / 8 + (x.d Γ) ^ 2 / 16 -
          b * x.eps * (Real.sqrt (x.c Γ) + |x.d Γ|) - b * x.eps ^ 2 ≤ x.error Γ ∧
        3 / 4 + x.eps * Phi p x.h - (6 * b ^ 2 + b) * x.eps ^ 2 ≤ x.error Γ := by
  obtain ⟨hLb,hgain,hcoef,hdisk⟩ := constants_nonneg p K hK
  have hh := p.H_pos; have hKone : 0 ≤ Kone p K := by dsimp [Kone]; positivity
  let S := 1 + p.H + K + 8 * Kone p K + Lbar p; have hS : 0 < S := by dsimp [S]; positivity
  have hb : 0 < defectConstant p K := by dsimp [defectConstant]; positivity
  refine ⟨defectConstant p K,hb,1 / (8 * S),by positivity,?_⟩
  intro x Γ he hne; have he0 := x.eps_pos.le; have hse : S * x.eps < 1 / 8 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * S)).mp he
    nlinarith
  have he1 : x.eps ≤ 1 := by
    have h := mul_nonneg (show 0 ≤ S - 1 by dsimp [S]; linarith) he0
    nlinarith
  have hrare : x.h * x.eps ≤ 1 / 2 := by
    have h := mul_nonneg (show 0 ≤ S - p.H by dsimp [S]; linarith) he0
    nlinarith [mul_le_mul_of_nonneg_right x.h_le he0]
  have hsmall : (p.H + K) * x.eps < 1 / 4 := by
    have h := mul_nonneg (show 0 ≤ S - (p.H + K) by dsimp [S]; linarith) he0
    nlinarith
  have hcomp := current_compression_defect_bound p x Γ K hK hrare hsmall hne; have hc0 : 0 ≤ x.c Γ := add_nonneg (diagonal_bounds (symInstrument Γ) 0 (0,1)).1
    (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hc : x.c Γ ≤ 8 * Kone p K * x.eps := by nlinarith [hcomp.2.2,sq_nonneg (x.d Γ)]
  have hL := L_sum_bound (symInstrument Γ) (gamma := p.gamma) p.beta_pos p.R_gt_one; have hls : - Lbar p ≤ L (symInstrument Γ) p.beta p.gamma p.R 0 + L (symInstrument Γ) p.beta p.gamma p.R 1 := by
    have h0 := neg_abs_le (L (symInstrument Γ) p.beta p.gamma p.R 0); have h1 := neg_abs_le (L (symInstrument Γ) p.beta p.gamma p.R 1)
    change |L (symInstrument Γ) p.beta p.gamma p.R 0| + |L (symInstrument Γ) p.beta p.gamma p.R 1| ≤ Lbar p at hL
    linarith
  have hs : 1 / 2 ≤ x.s Γ := by
    have hsum := coupled_sum p x Γ; have hle := mul_le_mul_of_nonneg_left hls he0; have hS' := mul_nonneg (show 0 ≤ S - (8 * Kone p K + Lbar p) by dsimp [S]; linarith) he0
    nlinarith
  have hw := uniform_defect_bound p x Γ K hK he1 hrare hs hne
  refine ⟨hw,?_⟩
  have hsqrt := Real.sq_sqrt hc0; have habs : |x.d Γ| ^ 2 = (x.d Γ) ^ 2 := sq_abs _; have hu := sq_nonneg (Real.sqrt (x.c Γ) - 4 * defectConstant p K * x.eps); have hv := sq_nonneg (|x.d Γ| - 8 * defectConstant p K * x.eps)
  nlinarith
end D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
