/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Heralded exact recovery characterizes positive conditional expansion. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
import D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryUpperBound

/-! A heralded recovery controls the conditional gap through the positive trace
of its success and failure branches. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder
open BellCenteredConditionalTraceGap (bellProjector)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp amp_entry amp_sub_smul E gap partialTraceRight_smul posTrace ptr ptr_amp ptr_sub_smul
    ratios)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open D5.S3.Quantum.Foundation.FiniteKrausChannel (krausRepresentation)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef partialTraceRight partialTraceRight_posSemidef trace_partialTraceRight)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open RHLinalg (rtrace rtrace_sub)
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

open private posTrace_mono from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
open private posTrace_smul from
  D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open private one_kronecker_mulVec_entry from
  D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery

private theorem amplifyKraus_entry {A B R J : Type*} [Fintype A]
    [Fintype R] [DecidableEq R] [Fintype J] (K : J → Matrix B A ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (r s : R) (b d : B) :
    amplifyKraus K X (r, b) (s, d) =
      MatrixMap.of_kraus K K (Matrix.of (fun a a' => X (r, a) (s, a'))) b d := by
  classical
  let Y : Matrix A A ℂ := Matrix.of (fun a a' => X (r, a) (s, a'))
  change amplifyKraus K X (r, b) (s, d) = MatrixMap.of_kraus K K Y b d
  simp only [amplifyKraus, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  let T := (1 : Matrix R R ℂ) ⊗ₖ K j
  have hleft (a' : A) : (T * X) (r, b) (s, a') = (K j * Y) b a' :=
    one_kronecker_mulVec_entry (K j) (X.col (s, a')) r b
  calc
    (T * X * Tᴴ) (r, b) (s, d) = (star (T *ᵥ star ((T * X).row (r, b)))) (s, d) :=
      congrFun (Matrix.vecMul_conjTranspose T ((T * X).row (r, b))) (s, d)
    _ = (K j * Y * (K j)ᴴ) b d := by
      change (star (((1 : Matrix R R ℂ) ⊗ₖ K j) *ᵥ star ((T * X).row (r, b))))
        (s, d) = ∑ a', (K j * Y) b a' * (K j)ᴴ a' d
      rw [Pi.star_apply, one_kronecker_mulVec_entry, star_sum]
      simp only [star_mul, Pi.star_apply, star_star, Matrix.row_apply, hleft,
        Matrix.conjTranspose_apply]

private theorem trace_kraus {A B J : Type*} [Fintype A] [Fintype B]
    [Fintype J] (K : J → Matrix B A ℂ) (X : Matrix A A ℂ) :
    (MatrixMap.of_kraus K K X).trace = ((∑ j, (K j)ᴴ * K j) * X).trace := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [Matrix.trace_mul_comm (K j * X), ← Matrix.mul_assoc])

private theorem ptr_amplifyKraus_entry {A B R J : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R] [Fintype J] (K : J → Matrix B A ℂ)
    (X : Matrix (R × A) (R × A) ℂ) (r s : R) :
    ptr (amplifyKraus K X) r s =
      ((∑ j, (K j)ᴴ * K j) * Matrix.of (fun a a' => X (r, a) (s, a'))).trace := by
  change (∑ b, amplifyKraus K X (r, b) (s, b)) = _
  simp_rw [amplifyKraus_entry]
  exact trace_kraus K (Matrix.of (fun a a' => X (r, a) (s, a')))

private theorem amplifyKraus_psd {A B R J : Type*} [Fintype A] [Finite B]
    [Fintype R] [DecidableEq R] [Fintype J]
    (K : J → Matrix B A ℂ) {X : Matrix (R × A) (R × A) ℂ}
    (hX : X.PosSemidef) : (amplifyKraus K X).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun j _ => hX.mul_mul_conjTranspose_same ((1 : Matrix R R ℂ) ⊗ₖ K j))

private theorem ptr_sub {R T : Type*} [Fintype R] [DecidableEq R]
    [Fintype T] [DecidableEq T] (X Z : Matrix (R × T) (R × T) ℂ) :
    ptr (X - Z) = ptr X - ptr Z := by
  simpa only [one_smul] using ptr_sub_smul (1 : ℝ) X Z

private theorem posTrace_le_rtrace {M : Type*} [Fintype M] [DecidableEq M]
    {X Z : Matrix M M ℂ} (hX : X.IsHermitian) (hZ : Z.PosSemidef) (hXZ : X ≤ Z) :
    posTrace X ≤ rtrace Z := by
  have h := posTrace_mono hX hZ.isHermitian hXZ
  change posTrace X ≤ rtrace (posPart Z) at h
  simpa only [(CFC.posPart_eq_self Z).mpr hZ.nonneg] using h

theorem heralded_recovery_contrast_lower_bound
    {A B R J : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R] [Fintype J]
    (N : QuantumChannel A B) (K : J → Matrix A B ℂ) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (heffect : (∑ j, (K j)ᴴ * K j) ≤ (1 : Matrix B B ℂ))
    (hrec : ∀ X : Matrix A A ℂ, MatrixMap.of_kraus K K (act N X) = (p : ℂ) • X)
    (H : Matrix (R × A) (R × A) ℂ) (hH : H.IsHermitian) :
    p * (posTrace H - posTrace (ptr H)) ≤
      posTrace (amp N H) - posTrace (ptr H) := by
  classical
  let S := amplifyKraus (S := R) K
  let F (X : Matrix (R × B) (R × B) ℂ) := ptr X - ptr (S X)
  let D : Matrix B B ℂ := 1 - ∑ j, (K j)ᴴ * K j
  let C := CFC.sqrt D
  have hD : 0 ≤ D := sub_nonneg.mpr heffect
  have hC : Cᴴ * C = D := by
    have hCpsd : C.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
    rw [hCpsd.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self D hD
  have hF (X : Matrix (R × B) (R × B) ℂ) :
      F X = ptr (amplifyKraus (fun _ : Unit => C) X) := by
    apply Matrix.ext
    intro r s
    let Z : Matrix B B ℂ := fun b d => X (r, b) (s, d)
    change Z.trace - ptr (amplifyKraus K X) r s =
      ptr (amplifyKraus (fun _ : Unit => C) X) r s
    rw [ptr_amplifyKraus_entry K, ptr_amplifyKraus_entry (fun _ : Unit => C)]
    change Z.trace - ((∑ j, (K j)ᴴ * K j) * Z).trace =
      ((∑ _ : Unit, Cᴴ * C) * Z).trace
    simp only [Fintype.sum_unique, hC, D, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  have hSpos {X : Matrix (R × B) (R × B) ℂ} (hX : X.PosSemidef) : (S X).PosSemidef :=
    amplifyKraus_psd K hX
  have hFpos {X : Matrix (R × B) (R × B) ℂ} (hX : X.PosSemidef) : (F X).PosSemidef := by
    rw [hF X]
    exact partialTraceRight_posSemidef (amplifyKraus_psd (fun _ : Unit => C) hX)
  have hSsub (X Z : Matrix (R × B) (R × B) ℂ) : S (X - Z) = S X - S Z := by
    simp only [S, amplifyKraus, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  have hFsub (X Z : Matrix (R × B) (R × B) ℂ) : F (X - Z) = F X - F Z := by
    change ptr (X - Z) - ptr (S (X - Z)) = (ptr X - ptr (S X)) - (ptr Z - ptr (S Z))
    rw [ptr_sub X Z, hSsub, ptr_sub]
    abel
  let Y := amp N H
  have hY : Y.IsHermitian := by
    change (amp N H).IsHermitian
    rw [← CFC.posPart_sub_negPart H hH]
    have h := amp_sub_smul N (1 : ℝ) (posPart H) (negPart H)
    simp only [one_smul] at h
    rw [h]
    exact (amp_psd N (CFC.posPart_nonneg H).posSemidef).isHermitian.sub
      (amp_psd N (CFC.negPart_nonneg H).posSemidef).isHermitian
  have hSY : S Y = p • H := by
    apply Matrix.ext
    rintro ⟨r, a⟩ ⟨s, a'⟩
    change amplifyKraus K (amp N H) (r, a) (s, a') = (p • H) (r, a) (s, a')
    let X : Matrix A A ℂ := Matrix.of (fun u v => H (r, u) (s, v))
    have hblock : Matrix.of (fun b d => amp N H (r, b) (s, d)) = act N X := by
      apply Matrix.ext
      intro b d
      exact amp_entry N H r s b d
    rw [amplifyKraus_entry, hblock, hrec X]
    simp only [X, Matrix.smul_apply, Matrix.of_apply, Complex.real_smul, smul_eq_mul]
  have hFY : F Y = (1 - p) • ptr H := by
    change ptr (amp N H) - ptr (S Y) = _
    rw [ptr_amp, hSY]
    change partialTraceRight H - partialTraceRight (p • H) = (1 - p) • partialTraceRight H
    rw [partialTraceRight_smul, sub_smul, one_smul]
  have hpos : (posPart Y).PosSemidef := (CFC.posPart_nonneg Y).posSemidef
  have hneg : (negPart Y).PosSemidef := (CFC.negPart_nonneg Y).posSemidef
  have hSsplit : S Y = S (posPart Y) - S (negPart Y) :=
    (congrArg S (CFC.posPart_sub_negPart Y hY).symm).trans (hSsub _ _)
  have hFsplit : F Y = F (posPart Y) - F (negPart Y) :=
    (congrArg F (CFC.posPart_sub_negPart Y hY).symm).trans (hFsub _ _)
  have hs : posTrace (S Y) ≤ rtrace (S (posPart Y)) := by
    rw [hSsplit]
    exact posTrace_le_rtrace ((hSpos hpos).isHermitian.sub (hSpos hneg).isHermitian)
      (hSpos hpos) (sub_le_self _ (hSpos hneg).nonneg)
  have hf : posTrace (F Y) ≤ rtrace (F (posPart Y)) := by
    rw [hFsplit]
    exact posTrace_le_rtrace ((hFpos hpos).isHermitian.sub (hFpos hneg).isHermitian)
      (hFpos hpos) (sub_le_self _ (hFpos hneg).nonneg)
  have hsum : rtrace (S (posPart Y)) + rtrace (F (posPart Y)) = posTrace Y := by
    change rtrace (S (posPart Y)) +
      rtrace (partialTraceRight (posPart Y) - partialTraceRight (S (posPart Y))) =
      rtrace (posPart Y)
    rw [rtrace_sub]
    simp only [rtrace, trace_partialTraceRight]
    ring
  rw [hSY, posTrace_smul p hp] at hs
  rw [hFY, posTrace_smul (1 - p) (sub_nonneg.mpr hp₁)] at hf
  calc
    p * (posTrace H - posTrace (ptr H)) =
        (p * posTrace H + (1 - p) * posTrace (ptr H)) - posTrace (ptr H) := by ring
    _ ≤ posTrace Y - posTrace (ptr H) :=
      sub_le_sub_right ((add_le_add hs hf).trans_eq hsum) _

private theorem heralded_recovery_ratio_lower_bound
    {A B R J : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R] [Fintype J]
    (N : QuantumChannel A B) (K : J → Matrix A B ℂ) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (heffect : (∑ j, (K j)ᴴ * K j) ≤ (1 : Matrix B B ℂ))
    (hrec : ∀ X : Matrix A A ℂ, MatrixMap.of_kraus K K (act N X) = (p : ℂ) • X)
    (γ : ℝ) {ρ σ : Matrix (R × A) (R × A) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hgap : 0 < gap γ ρ σ) :
    p ≤ gap γ (amp N ρ) (amp N σ) / gap γ ρ σ := by
  apply (le_div_iff₀ hgap).mpr
  have h := heralded_recovery_contrast_lower_bound N K p hp hp₁ heffect hrec (ρ - γ • σ)
    (hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ)))
  simpa only [gap, E, amp_sub_smul, ptr_amp, ptr_sub_smul] using h

section Coefficients

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Success probabilities of finite trace-nonincreasing Kraus recoveries of `N`. -/
def heraldedRecoveryProbabilities (N : QuantumChannel A B) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ ∃ (J : Type) (fJ : Fintype J),
    letI := fJ
    ∃ K : J → Matrix A B ℂ,
      (∑ j, (K j)ᴴ * K j) ≤ (1 : Matrix B B ℂ) ∧
      ∀ X : Matrix A A ℂ, MatrixMap.of_kraus K K (act N X) = (p : ℂ) • X}

private theorem zero_mem_recovery (N : QuantumChannel A B) :
    0 ∈ heraldedRecoveryProbabilities N := by
  refine ⟨le_rfl, zero_le_one, Unit, inferInstance, fun _ => 0, ?_, ?_⟩
  · simp
  · intro X
    simp [MatrixMap.of_kraus, LinearMap.coe_mk, AddHom.coe_mk]

private theorem recovery_bddAbove (N : QuantumChannel A B) :
    BddAbove (heraldedRecoveryProbabilities N) :=
  ⟨1, fun _ hp => hp.2.1⟩

private theorem recovery_le_ratio (N : QuantumChannel A B) {γ p x : ℝ} {orth : Bool}
    (hp : p ∈ heraldedRecoveryProbabilities N) (hx : x ∈ ratios N γ orth) : p ≤ x := by
  rcases hp with ⟨hp₀, hp₁, J, fJ, K, heffect, hrec⟩
  rcases hx with ⟨R, fR, dR, ρ, σ, hρ, _, hσ, _, _, hg, rfl⟩
  let _ := fJ
  let _ := fR
  let _ := dR
  exact heralded_recovery_ratio_lower_bound N K p hp₀ hp₁ heffect hrec γ hρ hσ hg

theorem heralded_recovery_coefficient_lower_bound (N : QuantumChannel A B) (γ : ℝ)
    (orth : Bool) (hne : (ratios N γ orth).Nonempty) :
    sSup (heraldedRecoveryProbabilities N) ≤ sInf (ratios N γ orth) := by
  exact csSup_le ⟨0, zero_mem_recovery N⟩
    (fun _ hp => le_csInf hne (fun _ hx => recovery_le_ratio N hp hx))

omit [DecidableEq A] in
private theorem kraus_effect_le_one {J : Type} [Fintype J] (K : J → Matrix A B ℂ)
    (hTNI : ∀ X : Matrix B B ℂ, X.PosSemidef →
      rtrace (MatrixMap.of_kraus K K X) ≤ rtrace X) :
    (∑ j, (K j)ᴴ * K j) ≤ (1 : Matrix B B ℂ) := by
  let G : Matrix B B ℂ := ∑ j, (K j)ᴴ * K j
  have hG : G.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun j _ => Matrix.posSemidef_conjTranspose_mul_self (K j))
  have hD : ((1 : Matrix B B ℂ) - G).IsHermitian := Matrix.isHermitian_one.sub hG.isHermitian
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD
  intro v
  let X := Matrix.vecMulVec v (star v)
  have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have htr : rtrace (MatrixMap.of_kraus K K X) = rtrace (G * X) :=
    congrArg (fun z : ℂ => z.re) (trace_kraus K X)
  have h := hTNI X hX
  rw [htr] at h
  have hre : 0 ≤ rtrace ((1 - G) * X) := by
    rw [Matrix.sub_mul, Matrix.one_mul, rtrace_sub]
    exact sub_nonneg.mpr h
  change 0 ≤ (((1 - G) * Matrix.vecMulVec v (star v)).trace).re at hre
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hre
  exact Complex.nonneg_iff.mpr ⟨hre, (hD.im_star_dotProduct_mulVec_self v).symm⟩

/-- The optimal finite Kraus recovery probability controls the infimum of
conditional trace ratios in both directions, with input-dimension factor `d²`. -/
theorem heralded_recovery_coefficient_comparison
    (N : QuantumChannel A B) (hd : 2 ≤ Fintype.card A)
    (γ : ℝ) (hγ : 1 ≤ γ) (orth : Bool) :
    let pRec := sSup (heraldedRecoveryProbabilities N)
    let η := sInf (ratios N γ orth)
    pRec ≤ η ∧ η ≤ (Fintype.card A : ℝ) ^ 2 * pRec ∧
      (0 < η ↔ ∃ q ∈ heraldedRecoveryProbabilities N, 0 < q) := by
  classical
  dsimp only
  let P := bellProjector A
  let Q := 1 - spectralSupport (amp N (1 - P))
  let p : ℝ := rtrace (Q * amp N P) / (Fintype.card A : ℝ) ^ 2
  obtain ⟨hp, hp₁, hBellTNI, hBellRec, hBell⟩ := heralded_recovery_upper_bound N hd
  let representation := krausRepresentation (bellKernelRecovery N)
  let K := representation.val
  have hK (Y : Matrix B B ℂ) :
      CStarMatrix.ofMatrix.symm (bellKernelRecovery N (CStarMatrix.ofMatrix Y)) =
        MatrixMap.of_kraus K K Y := by
    simpa only [K, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
      using representation.property Y
  have hTNI (Y : Matrix B B ℂ) (hY : Y.PosSemidef) :
      rtrace (MatrixMap.of_kraus K K Y) ≤ rtrace Y := by
    rw [← hK Y]
    exact hBellTNI Y hY
  have hrec (X : Matrix A A ℂ) : MatrixMap.of_kraus K K (act N X) = (p : ℂ) • X := by
    rw [← hK (act N X), act, CStarMatrix.ofMatrix.apply_symm_apply]
    exact hBellRec X
  have hp_mem : p ∈ heraldedRecoveryProbabilities N :=
    ⟨hp, hp₁, A × B, inferInstance, K, kraus_effect_le_one K hTNI, hrec⟩
  have hp_le : p ≤ sSup (heraldedRecoveryProbabilities N) :=
    le_csSup (recovery_bddAbove N) hp_mem
  have htransfer := ConditionalHockeyStickOrthogonalReduction.result
  unfold ConditionalHockeyStickOrthogonalReduction.claim at htransfer
  have hsets := htransfer A B N
  have hratio_eq : ratios N γ orth = ratios N 1 true := by
    have ht : ratios N γ false = ratios N 1 true :=
      (hsets.2 γ 1 hγ le_rfl).trans (hsets.1 1 le_rfl)
    cases orth
    · exact ht
    · exact (hsets.1 γ hγ).symm.trans ht
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ∃ x ∈ ratios N γ orth, x < (Fintype.card A : ℝ) ^ 2 * p + ε := by
    obtain ⟨ρ, σ, horth, hgap, hlt⟩ := hBell ε hε
    refine ⟨_, ?_, hlt⟩
    rw [hratio_eq]
    exact ⟨Option A, inferInstance, inferInstance, pairMatrix ρ, pairMatrix σ,
      density_posSemidef ρ, ρ.2.2, density_posSemidef σ, σ.2.2, fun _ => horth, hgap, rfl⟩
  obtain ⟨x, hx, _⟩ := happrox 1 zero_lt_one
  have hbdd : BddBelow (ratios N γ orth) :=
    ⟨0, fun _ hy => recovery_le_ratio N (zero_mem_recovery N) hy⟩
  have hlower := heralded_recovery_coefficient_lower_bound N γ orth ⟨x, hx⟩
  have hupper : sInf (ratios N γ orth) ≤ (Fintype.card A : ℝ) ^ 2 * p := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y, hy, hlt⟩ := happrox ε hε
    exact (csInf_le hbdd hy).trans hlt.le
  refine ⟨hlower, hupper.trans (mul_le_mul_of_nonneg_left hp_le (sq_nonneg _)), ?_⟩
  constructor
  · intro hη
    have hp_pos : 0 < p := by
      by_contra! hn
      exact (not_lt_of_ge (hupper.trans (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hn))) hη
    exact ⟨p, hp_mem, hp_pos⟩
  · rintro ⟨q, hq, hq_pos⟩
    exact hq_pos.trans_le ((le_csSup (recovery_bddAbove N) hq).trans hlower)

end Coefficients

end D5.S3.Quantum.Divergence.ConditionalExpansion
