/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/Entropy/SSA
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/Entropy/SSA.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.Entropy.SSA.Operator

@[expose] public section

set_option relaxedAutoImplicit true

noncomputable section
variable {d d₁ d₂ d₃ m n : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}
open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix MatrixOrder ComplexOrder
open HermitianMat

section SSA_proof

omit [DecidableEq d₁] in
open HermitianMat in
private lemma inner_kron_one_eq_inner_traceRight
    (A : HermitianMat d₁ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪A ⊗ₖ (1 : HermitianMat d₂ ℂ), M⟫ = ⟪A, M.traceRight⟫ := by
  rw [inner_comm];
  -- By definition of partial trace, we have that the trace of M multiplied by (A ⊗ I) is equal to the trace of A multiplied by the partial trace of M.
  have h_partial_trace : Matrix.trace (M.mat * (A.mat ⊗ₖ 1 : Matrix (d₁ × d₂) (d₁ × d₂) ℂ)) = Matrix.trace (A.mat * M.traceRight.mat) := by
    simp [ Matrix.trace, Matrix.mul_apply ];
    simp [ Matrix.traceRight, Matrix.one_apply, mul_comm ];
    simp only [Finset.sum_sigma', Finset.mul_sum _ _ _];
    rw [ ← Finset.sum_filter ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.1, x.fst.1, x.fst.2 ⟩ ) _ _ _ _ <;>
      aesop (add simp [Finset.mem_filter, Sigma.ext_iff, Prod.ext_iff]);
  exact congr_arg Complex.re h_partial_trace

omit [DecidableEq d₂] in
open HermitianMat in
private lemma inner_one_kron_eq_inner_traceLeft
    (B : HermitianMat d₂ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪(1 : HermitianMat d₁ ℂ) ⊗ₖ B, M⟫ = ⟪B, M.traceLeft⟫ := by
  convert! inner_kron_one_eq_inner_traceRight B ( M.reindex ( Equiv.prodComm d₁ d₂ ) ) using 1;
  refine' congr_arg ( fun x : ℂ => x.re ) _;
  refine' Finset.sum_bij ( fun x y => ( x.2, x.1 ) ) _ _ _ _ <;> simp [ Matrix.mul_apply ];
  intro a b; rw [ ← Equiv.sum_comp ( Equiv.prodComm d₁ d₂ ) ]
  simp [mul_comm]
  rfl

open HermitianMat in
private lemma hermitianMat_log_inv_eq_neg
    (A : HermitianMat d₁ ℂ) [A.NonSingular] : A⁻¹.log = -A.log := by
  -- By the property of continuous functional calculus, the logarithm of the inverse of a matrix is the negative of the logarithm of the matrix.
  have h_log_inv : A⁻¹.log = A.cfc (Real.log ∘ (·⁻¹)) := by
    have h_log_inv : A⁻¹ = A.cfc (·⁻¹) := by
      exact Eq.symm HermitianMat.cfc_inv;
    rw [ h_log_inv, HermitianMat.log ];
    exact Eq.symm (HermitianMat.cfc_comp A (fun x => x⁻¹) Real.log);
  simp [ HermitianMat.log ];
  convert! congr_arg ( fun f => A.cfc f ) ( show Real.log ∘ ( fun x => x⁻¹ ) = -Real.log from funext fun x => ?_ ) using 1
  · exact Eq.symm (HermitianMat.cfc_neg A Real.log);
  · by_cases hx : x = 0 <;> simp [ hx, Real.log_inv ]

private lemma PosDef_assoc'_traceRight
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    ρ.assoc'.traceRight.M.mat.PosDef := by
  have _ := ρ.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  apply PosDef_traceRight
  convert! hρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm

set_option backward.isDefEq.respectTransparency false in
private lemma wm_inner_lhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪(-ρ.assoc'.traceRight.M.traceRight.log) ⊗ₖ (1 : HermitianMat (d₂ × d₃) ℂ) +
     (1 : HermitianMat d₁ ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  convert! congr_arg₂ ( · + · ) _ _ using 1;
  convert! inner_add_left _ _ _ using 1;
  · rw [ Sᵥₙ_eq_neg_trace_log ];
    convert! inner_kron_one_eq_inner_traceRight _ _ using 1;
    simp [ HermitianMat.traceRight ];
    congr! 2;
    ext i j; simp [ Matrix.traceRight ] ;
    exact Fintype.sum_prod_type fun x => ρ.m (i, x) (j, x)
  · rw [ Sᵥₙ_eq_neg_trace_log ];
    simp [ inner_one_kron_eq_inner_traceLeft ]

set_option backward.isDefEq.respectTransparency false in
private lemma wm_inner_rhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪((-ρ.assoc'.traceRight.M.log) ⊗ₖ (1 : HermitianMat d₃ ℂ) +
     (1 : HermitianMat (d₁ × d₂) ℂ) ⊗ₖ ρ.traceLeft.M.traceLeft.log).reindex
      (Equiv.prodAssoc d₁ d₂ d₃), ρ.M⟫ =
    Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft := by
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, Sᵥₙ_eq_neg_trace_log ];
  simp [ inner_add_left, inner_one_kron_eq_inner_traceLeft, inner_kron_one_eq_inner_traceRight ];
  congr! 2;
  convert MState.traceLeft_assoc' ρ using 1;
  unfold MState.assoc' MState.traceLeft; aesop;

/-- Weak monotonicity (form 2) for positive definite states:
    S(ρ₁₂) + S(ρ₂₃) ≥ S(ρ₁) + S(ρ₃).
    Proved by applying operator_ineq_SSA, taking log, then inner product with ρ. -/
private lemma Sᵥₙ_wm_pd [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  -- Set up marginals and their PD properties
  have h₁₂ := PosDef_assoc'_traceRight ρ hρ
  have h₂₃ := PosDef_traceLeft ρ.M hρ
  have : ρ.assoc'.traceRight.M.NonSingular := nonSingular_of_posDef h₁₂
  have : ρ.traceLeft.M.NonSingular := nonSingular_of_posDef h₂₃
  have : ρ.assoc'.traceRight.M.traceRight.NonSingular :=
    nonSingular_of_posDef (PosDef_traceRight _ h₁₂)
  have : ρ.traceLeft.M.traceLeft.NonSingular :=
    nonSingular_of_posDef (PosDef_traceLeft _ h₂₃)
  -- Step 1: Operator inequality
  have h_op := operator_ineq_SSA ρ.assoc'.traceRight.M ρ.traceLeft.M h₁₂ h₂₃
  -- Step 2: Take log
  have h_lhs_pd : (ρ.assoc'.traceRight.M.traceRight⁻¹ ⊗ₖ ρ.traceLeft.M).mat.PosDef :=
    HermitianMat.PosDef_kronecker _ _ (PosDef_traceRight _ h₁₂).inv h₂₃
  have h_log := HermitianMat.log_mono h_lhs_pd h_op
  -- Step 3: Simplify logs
  rw [HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  rw [HermitianMat.reindex_log, HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  -- Step 4: Take inner product with ρ.M (≥ 0)
  have h_inner := HermitianMat.inner_mono ρ.nonneg h_log
  -- Step 5: Use commutativity to match wm_inner_lhs/rhs forms
  rw [HermitianMat.inner_comm, HermitianMat.inner_comm ρ.M] at h_inner
  rw [wm_inner_lhs ρ, wm_inner_rhs ρ] at h_inner
  linarith

set_option backward.isDefEq.respectTransparency false in
private lemma MState.approx_by_pd
    (ρ : MState d₁) :
    ∃ (ρn : ℕ → MState d₁), (∀ n, (ρn n).M.mat.PosDef) ∧
      Filter.Tendsto ρn Filter.atTop (nhds ρ) := by
  have h_ne1 := ρ.nonempty
  -- Define the sequence of PD states ρn as the mixture of ρ with the uniform state at weight εn = 1/(n+2).
  set εn : ℕ → ℝ := fun n => 1 / (n + 2)
  set ρn : ℕ → MState d₁ := fun n => Mixable.mix ⟨εn n, by
    exact ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩⟩ (MState.uniform) ρ
  refine' ⟨ ρn, _, _ ⟩;
  · intro n
    have h_pos_def : (ρn n).M = (1 - εn n) • ρ.M + εn n • (MState.uniform (d := d₁)).M := by
      refine' add_comm _ _ |> Eq.trans <| _;
      congr! 1
      aesop;
    have h_pos_def : ∀ (A : Matrix d₁ d₁ ℂ), A.PosSemidef → ∀ (B : Matrix d₁ d₁ ℂ), B.PosDef → ∀ (ε : ℝ), 0 < ε ∧ ε < 1 → (1 - ε) • A + ε • B ∈ {M : Matrix d₁ d₁ ℂ | M.PosDef} := by
      intro A hA B hB ε hε
      simp only [ Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.posDef_iff_dotProduct_mulVec ] at *
      constructor <;> simp_all
      · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
      · intro x hx_ne_zero
        have h_pos : 0 < (1 - ε) * (star x ⬝ᵥ A *ᵥ x) + ε * (star x ⬝ᵥ B *ᵥ x) := by
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| mod_cast hε.2.le ) <| mod_cast hA.2 x ) <| mul_pos ( mod_cast hε.1 ) <| mod_cast hB.2 hx_ne_zero;
        convert h_pos using 1 ; simp [ Matrix.add_mulVec ] ; ring_nf!
        simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, sub_mul, mul_sub ] ; ring!;
    convert! h_pos_def _ _ _ _ _ ⟨ _, _ ⟩ <;> norm_num [ * ];
    congr! 1
    exact psd ρ
    · exact uniform_posDef;
    · exact one_div_pos.mpr ( by linarith );
    · exact div_lt_one ( by positivity ) |>.2 ( by linarith )
  · -- Show that the sequence ρn converges to ρ.
    have h_conv : Filter.Tendsto (fun n => εn n • (MState.uniform : MState d₁).M + (1 - εn n) • ρ.M) Filter.atTop (nhds ρ.M) := by
      exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.smul ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( Filter.Tendsto.smul ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ) ( by simp );
    rw [ tendsto_iff_dist_tendsto_zero ] at *;
    convert h_conv using 1;
    ext n; simp [ρn, Mixable.mix];
    congr! 1

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
private lemma MState.traceLeft_continuous :
    Continuous (MState.traceLeft : MState (d₁ × d₂) → MState d₂) := by
  -- Since the matrix traceLeft is continuous, the function that maps a state to its partial trace is also continuous.
  have h_traceLeft_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂) ℂ => ρ.traceLeft) := by
    have h_cont : Continuous (fun ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ => ρ.traceLeft) := by
      exact continuous_pi fun _ => continuous_pi fun _ => continuous_finsetSum _ fun _ _ => continuous_apply _ |> Continuous.comp <| continuous_apply _ |> Continuous.comp <| continuous_id';
    convert h_cont.comp ( show Continuous fun ρ : HermitianMat ( d₁ × d₂ ) ℂ => ρ.1 from ?_ ) using 1;
    · constructor <;> intro h <;> rw [ continuous_induced_rng ] at * <;> aesop;
    · fun_prop;
  exact continuous_induced_rng.mpr ( by continuity )

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
private lemma MState.traceRight_continuous :
    Continuous (MState.traceRight : MState (d₁ × d₂) → MState d₁) := by
  rw [ continuous_iff_continuousAt ];
  intro ρ
  simp [ContinuousAt] at *;
  rw [ tendsto_nhds ] at *;
  intro s hs hρs;
  rcases hs with ⟨ t, ht, rfl ⟩;
  -- The traceRight map is continuous, so the preimage of an open set under traceRight is open.
  have h_traceRight_cont : Continuous (HermitianMat.traceRight : HermitianMat (d₁ × d₂) ℂ → HermitianMat d₁ ℂ) := by
    -- The traceRight map is a linear map, hence continuous.
    have h_traceRight_linear : ∃ (f : HermitianMat (d₁ × d₂) ℂ →ₗ[ℝ] HermitianMat d₁ ℂ), ∀ A, f A = A.traceRight := by
      refine' ⟨ _, _ ⟩;
      refine' { .. };
      exact fun A => A.traceRight;
      all_goals simp [ HermitianMat.traceRight ];
      · exact fun x y => rfl;
      · aesop
    obtain ⟨ f, hf ⟩ := h_traceRight_linear;
    convert f.continuous_of_finiteDimensional;
    exact funext fun A => hf A ▸ rfl;
  have := h_traceRight_cont.isOpen_preimage t ht;
  exact Filter.mem_of_superset ( this.preimage ( continuous_induced_dom ) |> IsOpen.mem_nhds <| by simpa using hρs ) fun x hx => hx

@[fun_prop]
private lemma MState.assoc'_continuous :
    Continuous (MState.assoc' : MState (d₁ × d₂ × d₃) → MState ((d₁ × d₂) × d₃)) := by
  apply continuous_induced_rng.mpr;
  -- The reindex function is continuous because it is a composition of continuous functions (permutations).
  have h_reindex_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂ × d₃) ℂ => ρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm) := by
    apply continuous_induced_rng.mpr;
    fun_prop (disch := norm_num);
  convert! h_reindex_cont.comp _ using 2;
  exact Continuous_HermitianMat

/-- Weak monotonicity, version with partial traces. -/
lemma Sᵥₙ_wm (ρ : MState (d₁ × d₂ × d₃)) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  have h_ne123 := ρ.nonempty
  obtain ⟨ ρn, hρn_pos, hρn ⟩ := MState.approx_by_pd ρ;
  -- Apply the inequality for each ρn and then take the limit.
  have h_lim : Filter.Tendsto (fun n => Sᵥₙ (ρn n).traceRight + Sᵥₙ (ρn n).traceLeft.traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft)) ∧ Filter.Tendsto (fun n => Sᵥₙ (ρn n).assoc'.traceRight + Sᵥₙ (ρn n).traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft)) := by
    constructor <;> refine' Filter.Tendsto.add _ _;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp hρn );
    · exact Sᵥₙ_continuous.comp ( MState.traceLeft_continuous.comp ( MState.traceLeft_continuous ) ) |> fun h => h.continuousAt.tendsto.comp hρn;
    · convert! Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp ( MState.assoc'_continuous.continuousAt.tendsto.comp hρn ) ) using 1;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceLeft_continuous.continuousAt.tendsto.comp hρn );
  have ⟨_, hn23⟩ := nonempty_prod.mp h_ne123
  have ⟨_, _⟩ := nonempty_prod.mp hn23
  exact le_of_tendsto_of_tendsto' h_lim.1 h_lim.2 fun n => Sᵥₙ_wm_pd _ ( hρn_pos n )

/-- Permutation to relabel (A×B×C)×R as A×(B×C×R). -/
private def perm_A_BCR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ dA × (dB × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (a, (b,c,r))
  invFun x := let (a, (b,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The BCR state: trace out A from the purification of ρ_ABC. -/
private def ρBCR (ρ : MState (dA × dB × dC)) : MState (dB × dC × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel (perm_A_BCR' dA dB dC).symm).traceLeft

set_option backward.isDefEq.respectTransparency false in
private lemma S_BC_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).assoc'.traceRight = Sᵥₙ ρ.traceLeft := by
  -- By definition of ρBCR, we know that its BC-marginal is equal to the BC-marginal of ρ.
  have h_marginal : (ρBCR ρ).assoc'.traceRight = ρ.traceLeft := by
    unfold ρBCR MState.traceLeft MState.traceRight MState.assoc';
    simp [ MState.assoc, MState.SWAP, MState.relabel, MState.pure, perm_A_BCR' ];
    unfold reindex HermitianMat.traceLeft HermitianMat.traceRight; ext
    simp
    simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix ];
    have := ρ.purify_spec;
    replace this := congr_arg ( fun x => x.M.val ) this ; simp_all [ MState.traceRight, MState.pure ];
    simp [ ← this, Matrix.traceRight, Matrix.vecMulVec ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  rw [h_marginal]

/-- Equivalence to relabel the purification as (dA × dB) × (dC × R). -/
private def perm_AB_CR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

set_option backward.isDefEq.respectTransparency false in
/- The CR-marginal of ρBCR equals the traceLeft of the AB|CR-relabeled purification. -/
private lemma BCR_traceLeft_eq_purify_traceLeft (ρ : MState (dA × dB × dC)) :
    (ρBCR ρ).traceLeft =
    ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceLeft := by
  convert MState.ext ?_;
  convert MState.ext ?_;
  any_goals exact ρ.traceLeft.traceLeft;
  · simp [ MState.traceLeft, MState.relabel, perm_AB_CR' ];
    simp [ MState.traceLeft, MState.relabel, ρBCR ];
    unfold HermitianMat.traceLeft
    simp only [mat_reindex, MState.mat_M, Matrix.reindex_apply, mat_mk, Equiv.coe_fn_symm_mk]
    unfold Matrix.traceLeft
    simp
    congr! 2
    ext i₁ j₁
    rw [ ← Finset.sum_product' ]
    simp [ perm_A_BCR' ]
    exact Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) ( by simp ) ( by simp ) ( by simp ) ( by simp );
  · rfl

/- The traceRight of the AB|CR-relabeled purification has same entropy as ρ.assoc'.traceRight. -/
private lemma purify_AB_traceRight_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight =
    Sᵥₙ ρ.assoc'.traceRight := by
  have h_traceRight : ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight = ρ.assoc'.traceRight := by
    have h_traceRight : (MState.pure ρ.purify).traceRight = ρ := by
      exact MState.purify_spec ρ;
    convert congr_arg ( fun m => m.assoc'.traceRight ) h_traceRight using 1;
    ext i j; simp [ MState.traceRight, MState.assoc' ] ;
    simp [ HermitianMat.traceRight, MState.SWAP, MState.assoc ];
    simp [ Matrix.traceRight ];
    congr! 2;
    ext i j; simp [ perm_AB_CR' ] ;
    exact Fintype.sum_prod_type _
  rw [h_traceRight]

/-- The CR-marginal of ρBCR has the same entropy as the AB-marginal of ρ. -/
private lemma S_CR_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft = Sᵥₙ ρ.assoc'.traceRight := by
  rw [BCR_traceLeft_eq_purify_traceLeft]
  rw [Sᵥₙ_pure_complement ρ.purify (perm_AB_CR' dA dB dC).symm]
  exact purify_AB_traceRight_eq ρ

set_option backward.isDefEq.respectTransparency false in
private lemma S_B_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  unfold ρBCR;
  unfold MState.traceLeft MState.traceRight MState.relabel MState.pure;
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, perm_A_BCR' ];
  unfold Matrix.traceLeft Matrix.traceRight; simp [Matrix.vecMulVec ] ;
  -- By definition of purification, we know that ρ.purify is a purification of ρ.m.
  have h_purify : ∀ (i j : dA × dB × dC), ρ.m i j = ∑ r : dA × dB × dC, ρ.purify (i, r) * (starRingEnd ℂ) (ρ.purify (j, r)) := by
    intro i j
    have := ρ.purify_spec;
    replace this := congr_arg ( fun m => m.M i j ) this
    simp_all [MState.traceRight]
    exact this.symm
  simp only [Finset.sum_sigma', h_purify];
  congr! 3;
  ext i₂ j₂
  simp
  ring_nf
  refine' Finset.sum_bij ( fun x _ => ⟨ x.fst.1, x.snd, x.fst.2 ⟩ ) _ _ _ _ <;> simp
  · grind
  · grind

private lemma S_R_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft.traceLeft = Sᵥₙ ρ := by
  have h_trace : (ρBCR ρ).traceLeft.traceLeft = (MState.pure ρ.purify).traceLeft := by
    unfold ρBCR MState.traceLeft;
    ext i j;
    simp [ HermitianMat.traceLeft];
    simp [ perm_A_BCR', Matrix.traceLeft ];
    simp [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ( x.snd.snd, x.snd.fst, x.fst ) ) _ _ _ _ <;> simp
    grind;
  convert Sᵥₙ_of_partial_eq ρ.purify using 1;
  · rw [h_trace];
  · rw [ ρ.purify_spec ]

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  have _ := ρ₁₂₃.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  -- Apply weak monotonicity to ρBCR, then substitute purification identities
  have h_wm := Sᵥₙ_wm (ρBCR ρ₁₂₃)
  rw [S_BC_of_BCR_eq, S_CR_of_BCR_eq, S_B_of_BCR_eq, S_R_of_BCR_eq] at h_wm
  linarith

