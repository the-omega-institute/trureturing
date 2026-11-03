/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/States/Mixed/MState
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/States/Mixed/MState.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.States.Mixed.MState.Basic

@[expose] public section

set_option relaxedAutoImplicit true

noncomputable section
open BigOperators ComplexConjugate HermitianMat
open scoped Matrix ComplexOrder RealInnerProductSpace InnerProductSpace
variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable (ψ φ : Ket d) (ρ σ : MState d)
namespace MState

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, (ρ₁ ⊗ᴹ ρ₂).spectrum (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  --TODO Cleanup
  by_contra! h;
  -- Apply `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal` to $A \otimes B$ and $U_A \otimes U_B$ and the diagonal entries.
  obtain ⟨σ, hσ⟩ : ∃ σ : d₁ × d₂ ≃ d₁ × d₂, (ρ₁.prod ρ₂).M.H.eigenvalues ∘ σ = fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) := by
    have h_unitary : ∃ U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ, U ∈ Matrix.unitaryGroup (d₁ × d₂) ℂ ∧ (ρ₁.prod ρ₂).M = U * Matrix.diagonal (fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) : d₁ × d₂ → ℂ) * Matrix.conjTranspose U := by
      -- Let $U_A$ and $U_B$ be the eigenvector unitaries of $\rho_1$ and $\rho_2$, respectively.
      obtain ⟨U_A, hU_A⟩ : ∃ U_A : Matrix d₁ d₁ ℂ, U_A ∈ Matrix.unitaryGroup d₁ ℂ ∧ ρ₁.M = U_A * Matrix.diagonal (fun i => (ρ₁.spectrum i : ℂ)) * Matrix.conjTranspose U_A := by
        have := ρ₁.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        simp
      obtain ⟨U_B, hU_B⟩ : ∃ U_B : Matrix d₂ d₂ ℂ, U_B ∈ Matrix.unitaryGroup d₂ ℂ ∧ ρ₂.M = U_B * Matrix.diagonal (fun j => (ρ₂.spectrum j : ℂ)) * Matrix.conjTranspose U_B := by
        have := ρ₂.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        simp
      refine' ⟨ Matrix.kroneckerMap ( fun x y => x * y ) U_A U_B, _, _ ⟩;
      · simp_all only [ne_eq, Matrix.mem_unitaryGroup_iff, mat_M, Matrix.star_kron];
        have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = 1 := by
          have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = Matrix.kroneckerMap (fun x y => x * y) (U_A * Star.star U_A) (U_B * Star.star U_B) := by
            ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ Matrix.mul_apply, Matrix.kroneckerMap_apply ]
            ring_nf
            rw [ Fintype.sum_prod_type ]
            simp [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
            exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
          simp_all only [zero_mul, implies_true, mul_zero, mul_one, Matrix.kroneckerMap_one_one]
        exact h_unitary
      · simp_all [ MState.prod, Matrix.mul_assoc, Matrix.mul_kronecker_mul ];
        congr 2;
        · ext ⟨ i, j ⟩ ⟨ i', j' ⟩ ; by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [ hi, hj ];
        · ext i j; simp [ Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply ] ;
    obtain ⟨ U, hU₁, hU₂ ⟩ := h_unitary;
    apply Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal;
    · exact hU₁;
    convert hU₂ using 1;
    norm_num +zetaDelta at *;
  obtain ⟨ i, j, h ⟩ := h σ; have := congr_fun hσ ( i, j ) ; simp_all [ MState.spectrum ] ;
  exact h ( by exact Subtype.ext this )

lemma sInf_spectrum_prod (ρ : MState d) (σ : MState d₂) :
    sInf (_root_.spectrum ℝ (ρ ⊗ᴹ σ).m) = sInf (_root_.spectrum ℝ ρ.m) * sInf (_root_.spectrum ℝ σ.m) := by
  rcases isEmpty_or_nonempty d with _ | _; · simp
  rcases isEmpty_or_nonempty d₂ with _ | _; · simp
  rw [MState.m, MState.prod, HermitianMat.spectrum_prod, ← MState.m, ← MState.m]
  apply csInf_mul_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ ρ.M.H
  · rw [MState.m, ρ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply ρ.eigenvalue_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ σ.M.H
  · rw [MState.m, σ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply σ.eigenvalue_nonneg

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : ProbDistribution ρLRs, --ProbDistribution over those pairs, an ensemble
      ρ.M = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).M ⊗ₖ (Prod.snd ρLR.val).M

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ᴹ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, ProbDistribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp [prod, Unique.eq_default, only]

set_option backward.isDefEq.respectTransparency false in
lemma eq_of_sum_eq_pure {d : Type*} [Fintype d] [DecidableEq d]
    {ι : Type*} {s : Finset ι} {p : ι → ℝ} {ρs : ι → MState d}
    {ρ : MState d} (h_pure : ρ.purity = 1) (h_sum : ρ.M = ∑ i ∈ s, p i • (ρs i).M)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1) (i : ι) (hi : i ∈ s) (hpi : 0 < p i) :
    ρs i = ρ := by
  have h_trace : ∀ j ∈ s, 0 < p j → (⟪ρ.M, (ρs j).M⟫ = 1) := by
    have h_tr_pure : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ = 1 := by
      have h_tr_pure : ⟪ρ.M, ∑ j ∈ s, p j • (ρs j).M⟫ = ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ := by
        simp [ HermitianMat.inner_def, ← val_eq_coe ];
        rw [AddSubgroup.val_finsetSum]
        simp [Finset.mul_sum]
      rw [ ← h_tr_pure, ← h_sum ];
      convert h_pure using 1;
      exact beq_eq_beq.mp rfl;
    have h_tr_le_one : ∀ j ∈ s, ⟪ρ.M, (ρs j).M⟫ ≤ 1 := by
      intro j hj
      have h_tr_le_one_j : ⟪ρ.M, (ρs j).M⟫ ≤ ρ.M.trace * (ρs j).M.trace := by
        apply HermitianMat.inner_le_mul_trace
        · exact ρ.nonneg;
        · exact (ρs j).nonneg;
      simp_all only [smul_eq_mul, tr, mul_one, ge_iff_le]
      exact h_tr_le_one_j.trans ( h_sum ▸ ρ.tr.le );
    intro j hj hj_pos
    by_contra h_contra;
    have h_tr_lt_one : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ < ∑ j ∈ s, p j := by
      apply Finset.sum_lt_sum;
      · exact fun i hi => mul_le_of_le_one_right ( hp_nonneg i hi ) ( h_tr_le_one i hi );
      · exact ⟨ j, hj, mul_lt_of_lt_one_right hj_pos ( lt_of_le_of_ne ( h_tr_le_one j hj ) h_contra ) ⟩;
    linarith;
  have h_eq : ρ.M = (ρs i).M := by
    have h_eq : ⟪ρ.M - (ρs i).M, ρ.M - (ρs i).M⟫ = 0 := by
      have h_eq : ⟪ρ.M - (ρs i).M, ρ.M - (ρs i).M⟫ = ⟪ρ.M, ρ.M⟫ - 2 * ⟪ρ.M, (ρs i).M⟫ + ⟪(ρs i).M, (ρs i).M⟫ := by
        simp only [HermitianMat.inner_def, IsMaximalSelfAdjoint.RCLike_selfadjMap, mat_sub, mat_M,
          RCLike.re_to_complex];
        simp [ Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm ( ρ.m ) ]
        ring
      have h_eq : ⟪ρ.M, ρ.M⟫ = 1 ∧ ⟪(ρs i).M, (ρs i).M⟫ ≤ 1 := by
        have h_eq : ⟪ρ.M, ρ.M⟫ = 1 := by
          convert h_pure using 1;
          exact beq_eq_beq.mp rfl;
        have h_eq : ∀ (A : HermitianMat d ℂ), 0 ≤ A → A.trace = 1 → ⟪A, A⟫ ≤ 1 := by
          intros A hA_nonneg hA_trace
          have h_eq : ⟪A, A⟫ ≤ A.trace * A.trace := by
            apply HermitianMat.inner_le_mul_trace hA_nonneg hA_nonneg;
          aesop;
        exact ⟨ by assumption, h_eq _ ( ρs i |>.2 ) ( ρs i |>.3 ) ⟩;
      linarith [ h_trace i hi hpi, (ρ.M - (ρs i).M).inner_self_nonneg ];
    -- Since the inner product of a matrix with itself is zero if and only if the matrix is zero, we have ρ.M - (ρs i).M = 0.
    have h_zero : ρ.M - (ρs i).M = 0 := by
      apply inner_self_eq_zero.mp h_eq;
    exact eq_of_sub_eq_zero h_zero;
  exact MState.ext h_eq.symm

lemma purity_prod {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).purity = ρ₁.purity * ρ₂.purity := by
  exact prod_inner_prod ρ₁ ρ₁ ρ₂ ρ₂

lemma pure_eq_pure_iff {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    pure ψ = pure φ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • φ.vec := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · -- By definition of pure state, we have that ψ.vec * conj ψ.vec = φ.vec * conj φ.vec.
    have h_eq : ∀ i j, ψ.vec i * starRingEnd ℂ (ψ.vec j) = φ.vec i * starRingEnd ℂ (φ.vec j) := by
      intro i j;
      replace h := congr_arg ( fun ρ => ρ.M.mat i j ) h ; aesop;
    -- Let $k$ be such that $\varphi_k \neq 0$.
    obtain ⟨k, hk⟩ : ∃ k, φ.vec k ≠ 0 := by
      exact φ.exists_ne_zero;
    -- Let $z = \frac{\psi_k}{\varphi_k}$. Then $|z| = 1$.
    obtain ⟨z, hz⟩ : ∃ z : ℂ, ψ.vec k = z * φ.vec k ∧ ‖z‖ = 1 := by
      specialize h_eq k k
      simp_all only [ne_eq]
      refine' ⟨ ψ.vec k / φ.vec k, _, _ ⟩ <;> simp_all [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      rw [ div_eq_iff ] <;> norm_cast at * <;> aesop;
    refine' ⟨ z, hz.2, funext fun i => _ ⟩;
    specialize h_eq i k
    simp_all
    -- Since $\overline{z} \cdot \overline{\varphi_k} \neq 0$, we can divide both sides of the equation by $\overline{z} \cdot \overline{\varphi_k}$.
    have h_div : ψ.vec i * starRingEnd ℂ z = φ.vec i := by
      exact mul_left_cancel₀ ( show starRingEnd ℂ ( φ.vec k ) ≠ 0 from by simpa [ Complex.ext_iff ] using hk ) ( by linear_combination h_eq );
    rw [ ← h_div, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; aesop;
  · cases h
    rename_i h
    obtain ⟨left, right⟩ := h
    -- Since $|w| = 1$, we have $w \overline{w} = 1$, which simplifies the matrix to $\phi \overline{\phi}^T$.
    have h_simp : ∀ i j, ψ.vec i * star (ψ.vec j) = φ.vec i * star (φ.vec j) := by
      simp [ *, Complex.ext_iff ];
      intro i j; rw [ Complex.norm_def ] at left; simp_all [ Complex.normSq ];
      grind +ring;
    exact MState.ext_m ( by ext i j; exact h_simp i j )

/-- Two kets are phase-equivalent if and only if their pure states are equal. -/
theorem PhaseEquiv_iff_pure_eq {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    Ket.PhaseEquiv.r ψ φ ↔ MState.pure ψ = MState.pure φ := by
  exact (pure_eq_pure_iff ψ φ).symm

/-- `MState.pure` descends to the quotient `KetUpToPhase`. -/
def pureQ {d : Type*} [Fintype d] [DecidableEq d] : KetUpToPhase d → MState d :=
  @Quotient.lift _ _ Ket.PhaseEquiv MState.pure (fun a b h => (PhaseEquiv_iff_pure_eq a b).mp h)

@[simp]
lemma pureQ_mk {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    pureQ (Quotient.mk Ket.PhaseEquiv ψ) = MState.pure ψ := rfl

lemma pureQ_injective {d : Type*} [Fintype d] [DecidableEq d] : Function.Injective (pureQ (d := d)) := by
  intro a b h
  induction a using Quotient.ind
  induction b using Quotient.ind
  simp [pureQ] at h
  exact Quotient.sound ((PhaseEquiv_iff_pure_eq _ _).mpr h)

set_option backward.isDefEq.respectTransparency false in
lemma pure_separable_imp_IsProd {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (h : IsSeparable (pure ψ)) : ψ.IsProd := by
  obtain ⟨ ρLRs, ps, hps ⟩ := h;
  -- Since `pure ψ` is pure (`purity = 1`), by `MState.eq_of_sum_eq_pure`, for any `k` with `p_k > 0`, we have `pure ψ = ρL_k ⊗ᴹ ρR_k`.
  obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) ∧ (MState.pure ψ).M = (k.val.1).M ⊗ₖ (k.val.2).M := by
    have h_pure : (MState.pure ψ).purity = 1 := by
      exact ( pure_iff_purity_one _ ).mp ⟨ ψ, rfl ⟩;
    obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) := by
      exact ⟨ Classical.choose ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all ), Classical.choose_spec ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all) ⟩;
    refine' ⟨ k, hk, _ ⟩;
    convert MState.eq_of_sum_eq_pure h_pure _ _ _ k _ _;
    rotate_left;
    · exact Finset.univ;
    · use fun x => ( ps x : ℝ );
    · use fun x => MState.prod x.val.1 x.val.2;
    all_goals norm_cast;
    · exact fun i a => unitInterval.nonneg (ps i);
    · exact ps.2;
    · exact Finset.mem_univ k;
    · obtain ⟨val, property⟩ := k
      obtain ⟨fst, snd⟩ := val
      have fwd : 0 ≤ (ps ⟨(fst, snd), property⟩).1 := le_of_lt hk
      apply Iff.intro
      · intro a
        exact MState.ext_iff.mpr a.symm
      · intro a
        rw [← a]
        rfl
  -- Since `pure ψ` is pure (`purity = 1`), by `MState.pure_iff_purity_one`, `ρL_k = pure ξ` and `ρR_k = pure φ` for some `ξ, φ`.
  obtain ⟨ξ, hξ⟩ : ∃ ξ : MState d₁, k.val.1 = ξ ∧ ξ.purity = 1 := by
    have h_purity : (pure ψ).purity = (k.val.1).purity * (k.val.2).purity := by
      convert MState.purity_prod _ _;
      exact MState.ext hk.2;
    have h_purity_one : (pure ψ).purity = 1 := by
      exact ( pure_iff_purity_one _ ).mp ⟨ ψ, rfl ⟩;
    rw [ h_purity, Prob.mul_eq_one_iff ] at h_purity_one ; aesop
  obtain ⟨φ, hφ⟩ : ∃ φ : MState d₂, k.val.2 = φ ∧ φ.purity = 1 := by
    have h_purity_prod : (pure ψ).purity = (k.val.1).purity * (k.val.2).purity := by
      convert MState.purity_prod _ _;
      exact MState.ext hk.2;
    have h_purity_one : (MState.pure ψ).purity = 1 := by
      exact pure_iff_purity_one _ |>.1 ⟨ ψ, rfl ⟩;
    aesop;
  -- Since `ξ` and `φ` are pure states, we have `ξ = pure ξ'` and `φ = pure φ'` for some `ξ', φ'`.
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : Ket d₁, ξ = MState.pure ξ' := by
    have := MState.pure_iff_purity_one ξ;
    exact this.mpr hξ.2
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Ket d₂, φ = MState.pure φ' := by
    have := MState.pure_iff_purity_one φ; aesop;
  -- Since `pure ψ = pure ξ ⊗ᵠ pure φ`, we have `ψ = ξ ⊗ᵠ φ` up to a global phase `z`.
  have h_eq : (pure ψ).M = (pure (ξ' ⊗ᵠ φ')).M := by
    rw [ hk.2, hξ.1, hξ', hφ.1, hφ', MState.pure_prod_pure ];
    exact rfl;
  -- Since `pure ψ = pure (ξ' ⊗ᵠ φ')`, we have `ψ = ξ' ⊗ᵠ φ'` up to a global phase `z`.
  have h_eq_ket : ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • (ξ' ⊗ᵠ φ').vec := by
    have := MState.pure_eq_pure_iff ψ ( ξ' ⊗ᵠ φ' );
    exact this.mp ( MState.ext h_eq );
  obtain ⟨ z, hz₁, hz₂ ⟩ := h_eq_ket;
  use ⟨ fun i => z * ξ' i, ?_ ⟩, φ';
  · ext ⟨ i, j ⟩ ; simp [ Ket.prod ];
    convert! congr_fun hz₂ ( i, j ) using 1;
    exact mul_assoc _ _ _;
  simp [ hz₁]
  · exact ξ'.normalized'

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  apply Iff.intro
  · exact pure_separable_imp_IsProd ψ
  · rintro ⟨ ξ, φ, rfl ⟩
    rw [pure_prod_pure ξ φ]
    exact IsSeparable_prod _ _;

/--
A mixed state is pure if and only if its rank is 1.
-/
theorem pure_iff_rank_eq_one {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (∃ ψ, ρ = pure ψ) ↔ ρ.m.rank = 1 := by
  constructor <;> intro h;
  · obtain ⟨w, rfl⟩ := h
    -- The rank of the outer product of a vector with itself is 1.
    have h_rank : ∀ (v : d → ℂ), v ≠ 0 → Matrix.rank (Matrix.vecMulVec v (conj v)) = 1 := by
      intro v hv_ne_zero
      have h_outer_product : ∀ (u : d → ℂ), ∃ (c : ℂ), Matrix.mulVec (Matrix.vecMulVec v (conj v)) u = c • v := by
        intro u
        use ∑ i, (starRingEnd ℂ (v i)) * (u i);
        ext i; simp [ Matrix.vecMulVec, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      apply le_antisymm
      · have h_outer_product : LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec v (conj v))) ≤ Submodule.span ℂ {v} := by
          rintro x ⟨ u, rfl ⟩ ; obtain ⟨ c, hc ⟩ := h_outer_product u; aesop;
        exact le_trans ( Submodule.finrank_mono h_outer_product ) ( finrank_span_le_card _ ) |> le_trans <| by simp ;
      · contrapose! hv_ne_zero; simp_all [ Matrix.rank, Submodule.eq_bot_iff ] ;
        ext i; specialize hv_ne_zero ( Pi.single i 1 ) ; simp_all [ Matrix.vecMulVec ] ;
        simpa using congr_fun hv_ne_zero i;
    exact h_rank _ ( fun h => by simpa [ h ] using w.exists_ne_zero );
  · -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
      -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ. Use this fact.
      have h_pure : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
        have h_rank : ρ.m.rank = 1 := h
        have h_herm : ρ.m.IsHermitian := by
          exact ρ.M.property
        have := h_herm.spectral_theorem;
        -- Since the rank of ρ.m is 1, the diagonal matrix in the spectral theorem must have exactly one non-zero entry.
        obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 ∧ ∀ j : d, j ≠ i → h_herm.eigenvalues j = 0 := by
          have h_diag : ∑ i : d, (if h_herm.eigenvalues i = 0 then 0 else 1) = 1 := by
            have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = 1 := by
              have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = Matrix.rank (ρ.m) := by
                exact Eq.symm (Matrix.IsHermitian.rank_eq_rank_diagonal h_herm);
              exact h_diag.trans h_rank;
            rw [ Matrix.rank_diagonal ] at h_diag;
            simp [ Finset.sum_ite ];
            rw [ Fintype.card_subtype ] at h_diag ; exact h_diag;
          obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 := by
            exact not_forall.mp fun h => by simp [ h ] at h_diag;
          rw [ Finset.sum_eq_add_sum_sdiff_singleton i _ (by simp) ] at h_diag;
          exact ⟨i, hi, fun j hj => Classical.not_not.1 fun hj' =>
            absurd h_diag ( by rw [ ite_eq_right hi ] ; exact ne_of_gt ( lt_add_of_pos_right _ ( lt_of_lt_of_le ( by simp [ hj' ] ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_sdiff.2 ⟨ Finset.mem_univ j, by simp [ hj ] ⟩ ) ) ) ) ) ⟩;
        -- Since the diagonal matrix in the spectral theorem has exactly one non-zero entry, we can write ρ.m as |ψ⟩⟨ψ| for some ket ψ.
        use fun j => (h_herm.eigenvectorUnitary : Matrix d d ℂ) j i * Real.sqrt (h_herm.eigenvalues i);
        convert this using 1
        ext j k; simp [ Matrix.mul_apply, Matrix.diagonal ]
        ring_nf
        rw [ Finset.sum_eq_single i ] <;> simp +contextual [ hi ];
        exact Or.inl <| Or.inl <| mod_cast Real.sq_sqrt <| by
          have := ρ.psd.eigenvalues_nonneg i;
          exact this
      exact h_pure;
    have h_norm : ∑ x, Complex.normSq (ψ x) = 1 := by
      have := ρ.tr';
      simp_all [ Complex.ext_iff, Matrix.trace ];
      simpa only [ Complex.normSq_apply, mul_comm ] using this.1;
    use ⟨ψ, by
      simpa [ Complex.normSq_eq_norm_sq ] using h_norm⟩
    generalize_proofs at *;
    refine' MState.ext_m _ ; aesop

/--
A ket on a product space is a product state if and only if its coefficient matrix has rank 1.
-/
theorem Ket.IsProd_iff_rank_eq_one {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) :
    ψ.IsProd ↔ (Matrix.of (fun i j => ψ (i, j))).rank = 1 := by
  rw [ Ket.IsProd_iff_mul_eq_mul ];
  constructor;
  · intro h;
    obtain ⟨ξ, ψ', hξψ'⟩ : ∃ ξ : d₁ → ℂ, ∃ ψ' : d₂ → ℂ, ∀ i j, ψ (i, j) = ξ i * ψ' j := by
      -- Let's choose any $j₀$ such that $\psi(i, j₀) \neq 0$ for some $i$.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀ : d₂, ∃ i₀ : d₁, ψ (i₀, j₀) ≠ 0 := by
        have := ψ.exists_ne_zero;
        exact ⟨ this.choose.2, this.choose.1, this.choose_spec ⟩;
      choose i₀ hi₀ using hj₀;
      exact ⟨ fun i => ψ ( i, j₀ ) / ψ ( i₀, j₀ ), fun j => ψ ( i₀, j ), fun i j => by rw [ div_mul_eq_mul_div, eq_div_iff hi₀ ] ; linear_combination h i i₀ j j₀ ⟩;
    -- Since the matrix is a product of two vectors, its rank is 1.
    have h_rank : Matrix.rank (Matrix.of (fun i j => ξ i * ψ' j)) ≤ 1 := by
      -- The range of the matrix is spanned by the single vector ξ.
      have h_range : LinearMap.range (Matrix.mulVecLin (Matrix.of (fun i j => ξ i * ψ' j))) ≤ Submodule.span ℂ {ξ} := by
        rintro x ⟨ y, rfl ⟩;
        rw [ Submodule.mem_span_singleton ];
        exact ⟨ ∑ j, ψ' j * y j, by ext i; simp [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩;
      exact le_trans ( Submodule.finrank_mono h_range ) ( finrank_span_le_card _ ) |> le_trans <| by norm_num;
    cases h_rank.eq_or_lt <;> simp_all [ Matrix.rank, Submodule.eq_bot_iff ];
    · convert! ‹Module.finrank ℂ ( LinearMap.range ( Matrix.mulVecLin ( Matrix.of fun i j => ξ i * ψ' j ) ) ) = 1› using 3 ; · aesop;
      · aesop;
      · ext; simp [hξψ'];
    · have := ψ.exists_ne_zero
      simp_all only [ne_eq, mul_eq_zero, not_or, Prod.exists, exists_and_left, exists_and_right]
      obtain ⟨left, right⟩ := this
      obtain ⟨w, h_2⟩ := left
      obtain ⟨w_1, h_3⟩ := right
      rename_i h_1
      specialize h_1 ( Pi.single w_1 1 )
      simp_all [ funext_iff]
  · rw [ Matrix.rank ];
    rw [ finrank_eq_one_iff' ]
    intro a i₁ i₂ j₁ j₂
    simp_all only [ne_eq, Subtype.forall, LinearMap.mem_range, Matrix.mulVecBilin_apply, forall_exists_index,
      Subtype.exists, Submodule.mk_eq_zero, SetLike.mk_smul_mk, Subtype.mk.injEq, forall_apply_eq_imp_iff,
      exists_and_left, exists_prop]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w_1, h⟩ := left_1
    subst h
    obtain ⟨ c, hc ⟩ := right ( Pi.single j₁ 1 ) ;
    obtain ⟨ d, hd ⟩ := right ( Pi.single j₂ 1 ) ;
    simp_all only [funext_iff, Matrix.mulVec, Matrix.of_apply, Pi.zero_apply, not_forall,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      Matrix.col_apply]
    rw [ ← hc i₁, ← hd i₁, ← hc i₂, ← hd i₂ ] ; ring

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  have h1 := MState.pure_separable_iff_IsProd ψ;
  have h2 := Ket.IsProd_iff_rank_eq_one ψ;
  have h3 := MState.pure_iff_rank_eq_one ( ( MState.pure ψ ).traceLeft )
  simp_all
  have h4 : Matrix.rank ((MState.pure ψ).traceLeft.m) = Matrix.rank (Matrix.of (fun i j => ψ (i, j))) := by
    have h4 : (MState.pure ψ).traceLeft.m = Matrix.transpose (Matrix.conjTranspose (Matrix.of (fun i j => ψ (i, j))) * Matrix.of (fun i j => ψ (i, j))) := by
      ext i j
      simp [ MState.traceLeft, Matrix.mul_apply ] ;
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _;
    rw [ h4, Matrix.rank_transpose, Matrix.rank_conjTranspose_mul_self ];
  grind

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.psd.eigenvalues_nonneg i
    simp only [Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h₁, Real.sq_sqrt,
      Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀ x, ∑ i : d, ‖ρ.Hermitian.eigenvectorUnitary i x‖ ^ 2 = 1 :=
      Matrix.unitaryGroup_row_norm ρ.Hermitian.eigenvectorUnitary
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, HermitianMat.traceRight, Matrix.traceRight]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, mat_M, pure_apply,
    mat_mk, Matrix.of_apply]
  simp only [Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  -- By definition of eigenvectorUnitary and the properties of the unitary matrix and the eigenvalues, we can show that the matrix constructed from the purification is equal to ρ.
  have h_eigenvectorUnitary : ∀ i j, ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ((ρ.Hermitian.eigenvalues x).sqrt ^ 2) * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x) = ρ.M i j := by
    intro i j
    have h_eigenvectorUnitary : ρ.M = Matrix.of (fun i j => ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ρ.Hermitian.eigenvalues x * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x)) := by
      have := ρ.Hermitian.spectral_theorem;
      convert! this using 1;
      ext i j; simp [ Matrix.mul_apply, Matrix.diagonal ] ;
    replace h_eigenvectorUnitary := congr_fun ( congr_fun h_eigenvectorUnitary i ) j
    simp_all only [mat_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.of_apply]
    congr! 2;
    norm_num [ Complex.ext_iff, sq ];
    exact Or.inl (Real.mul_self_sqrt (ρ.psd.eigenvalues_nonneg _))
  simp_all [ Complex.normSq, sq ];
  have h1 := h_eigenvectorUnitary i j
  convert! h1 using 1;
  simp [mul_assoc]

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

@[simps]
def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ where
  M := ρ.M.reindex e.symm
  nonneg := by simp [zero_le_iff, ρ.psd]
  tr := by simp [trace]

@[simp]
lemma relabel_m (ρ : MState d₁) (e : d₂ ≃ d₁) :
    (ρ.relabel e).m = ρ.m.submatrix e e := by
  rfl

@[simp]
lemma relabel_refl {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.relabel (Equiv.refl d) = ρ := by
  ext
  simp

/-- Relabeling the pure state associated to a ket gives the pure state associated to the
relabeled ket. -/
@[simp]
lemma relabel_pure (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    (pure ψ).relabel e = pure (ψ.relabel e) :=
  rfl

/-- Relabeling a pure state along an equivalence of basis index types yields another pure state. -/
theorem relabel_pure_exists (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    ∃ ψ' : Ket d₂, (pure ψ).relabel e = pure ψ' :=
  ⟨ψ.relabel e, relabel_pure ψ e⟩

@[simp]
lemma relabel_relabel {d d₂ d₃ : Type*}
    [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    (ρ : MState d) (e : d₂ ≃ d) (e₂ : d₃ ≃ d₂) : (ρ.relabel e).relabel e₂ = ρ.relabel (e₂.trans e) := by
  rfl

lemma eq_relabel_iff {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (σ : MState d₂) (h : d₁ ≃ d₂) :
    ρ = σ.relabel h ↔ ρ.relabel h.symm = σ := by
  simp only [MState.ext_iff, HermitianMat.ext_iff, mat_M, relabel_m]
  exact ⟨(by simp[·]), (by simp[← ·])⟩

lemma relabel_comp {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (e : d₂ ≃ d₁) (f : d₃ ≃ d₂) :
    (ρ.relabel e).relabel f = ρ.relabel (f.trans e) := by
  ext
  simp

lemma relabel_cast {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂]
       (ρ : MState d₁) (e : d₂ = d₁) :
    ρ.relabel (Equiv.cast e) = cast (by have := e.symm; congr <;> (apply Subsingleton.helim; congr)) ρ := by
  ext i j
  simp only [relabel_M, mat_reindex, mat_M, Matrix.reindex_apply, Matrix.submatrix_apply]
  subst e
  congr!
  symm
  apply cast_heq

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma spectrum_relabel {ρ : MState d} (e : d₂ ≃ d) :
    _root_.spectrum ℝ (ρ.relabel e).m = _root_.spectrum ℝ ρ.m := by
  ext1 v
  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
  rw [Algebra.algebraMap_eq_smul_one v]
  rw [MState.relabel_m, ← Matrix.submatrix_one_equiv e]
  rw [← Matrix.smul_apply, ← Matrix.submatrix_smul]
  rw [← Matrix.sub_apply, ← Matrix.submatrix_sub]
  rw [Matrix.isUnit_submatrix_equiv]
  rw [← Algebra.algebraMap_eq_smul_one v, ← spectrum.mem_iff]

/-- The purity of a state is invariant under relabeling of the basis. -/
@[simp]
theorem purity_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).purity = ρ.purity := by
  simp [purity, inner_def, -inner_self_eq_norm_sq_to_K]
--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

/--
The multiset of values in the spectrum of a relabeled state is the same as the multiset of values in the spectrum of the original state.
-/
lemma multiset_spectrum_relabel_eq {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Multiset.map (ρ.relabel e).spectrum Finset.univ.val = Multiset.map ρ.spectrum Finset.univ.val := by
  have h_charpoly : Matrix.charpoly (ρ.relabel e).m = Matrix.charpoly ρ.m := by
    exact Matrix.charpoly_reindex e.symm ρ.m
  have h_eigenvalues : Multiset.map (ρ.relabel e).M.H.eigenvalues Finset.univ.val = Multiset.map ρ.M.H.eigenvalues Finset.univ.val := by
    have h_eigenvalues : Polynomial.roots (Matrix.charpoly (ρ.relabel e).m) = Polynomial.roots (Matrix.charpoly ρ.m) := by
      rw [h_charpoly];
    have := ρ.M.H.roots_charpoly_eq_eigenvalues
    have := (ρ.relabel e).M.H.roots_charpoly_eq_eigenvalues
    simp_all only [relabel_m, mat_M, Complex.coe_algebraMap, Function.comp_apply, relabel_M,
      mat_reindex, Matrix.reindex_apply, Equiv.symm_symm]
    replace this := congr_arg ( fun m => m.map ( fun x => x.re ) ) this
    aesop;
  unfold MState.spectrum;
  ext
  rename_i a
  simp_all only [relabel_m, relabel_M, mat_reindex, mat_M, Matrix.reindex_apply, Equiv.symm_symm]
  obtain ⟨val, property⟩ := a
  obtain ⟨left, right⟩ := property
  convert congr_arg ( fun m => Multiset.count val m ) h_eigenvalues using 1;
  · rw [ Multiset.count_map, Multiset.count_map ];
    simp [ Subtype.ext_iff ];
    congr! 2;
  · rw [ Multiset.count_map, Multiset.count_map ];
    congr! 2;
    exact beq_eq_beq.mp rfl

lemma spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  -- Apply the lemma exists_equiv_of_multiset_map_eq with the appropriate parameters.
  obtain ⟨w, h⟩ := exists_equiv_of_multiset_map_eq (fun p => ρ.spectrum p) (fun p => ρ.SWAP.spectrum p)
    (ρ.multiset_spectrum_relabel_eq (Equiv.prodComm _ _).symm ▸ rfl)
  use w
  ext x
  simp_rw [h]
  rfl

@[simp]
lemma SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  rfl

@[simp]
lemma traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight :=
  rfl

@[simp]
lemma traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft :=
  rfl

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
lemma assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  rfl

@[simp]
lemma assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  rfl

@[simp]
lemma traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  exact Finset.sum_comm

@[simp]
lemma traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
lemma traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  ext : 3
  apply Finset.sum_product

@[simp]
lemma traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  convert! ρ.SWAP.assoc.SWAP.traceRight_assoc
  simp

@[simp]
lemma traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  simp [← traceLeft_assoc']

@[simp]
lemma traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

--TODO: This naming is very inconsistent. Should be better about "prod" vs "kron"

lemma relabel_kron (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₁) :
    ((ρ.relabel e) ⊗ᴹ σ) = (ρ ⊗ᴹ σ).relabel (e.prodCongr (Equiv.refl d₂)) := by
  rfl --is this defeq abuse? I don't know

lemma kron_relabel (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₂) :
    (ρ ⊗ᴹ σ.relabel e) = (ρ ⊗ᴹ σ).relabel ((Equiv.refl d₁).prodCongr e) := by
  rfl

lemma prod_assoc (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ᴹ (σ ⊗ᴹ τ)) = (ρ ⊗ᴹ σ ⊗ᴹ τ).relabel (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  ext : 2
  simp [-Matrix.kronecker_assoc']
  exact (Matrix.kronecker_assoc' ρ.m σ.m τ.m).symm

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance : TopologicalSpace (MState d) :=
  TopologicalSpace.induced MState.M inferInstance

/-- The projection from mixed states to their Hermitian matrices is an embedding -/
theorem toMat_IsEmbedding : Topology.IsEmbedding (MState.M (d := d)) where
  eq_induced := rfl
  injective := @MState.ext _ _ _

instance : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

instance : CompactSpace (MState d) := by
  constructor
  rw [(Topology.IsInducing.induced MState.M).isCompact_iff]
  suffices IsCompact (Set.Icc 0 1 ∩ { m | m.trace = 1} : Set (HermitianMat d ℂ)) by
    convert this
    ext1 m
    constructor
    · rintro ⟨ρ, _, rfl⟩
      simp [ρ.nonneg, ρ.le_one]
    · simpa using fun m_pos _ m_tr ↦ ⟨⟨m, m_pos, m_tr⟩, rfl⟩
  apply isCompact_Icc.inter_right
  refine isClosed_eq ?_ continuous_const
  rw [funext trace_eq_re_trace]
  fun_prop

noncomputable instance : MetricSpace (MState d) :=
  MetricSpace.induced MState.M MState.M_Injective inferInstance

lemma dist_eq (x y : MState d) : dist x y = dist x.M y.M := by
  rfl

set_option backward.isDefEq.respectTransparency false in
instance : BoundedSpace (MState d) where
  bounded_univ :=
    CompactSpace.isCompact_univ.isBounded

@[fun_prop]
lemma Continuous_HermitianMat : Continuous (MState.M (d := d)) :=
  continuous_iff_le_induced.mpr fun _ => id

@[fun_prop]
lemma Continuous_Matrix : Continuous (MState.m (d := d)) := by
  show Continuous (fun ρ : MState d => ρ.M.mat)
  fun_prop

lemma image_M_isBounded (S : Set (MState d)) : Bornology.IsBounded (MState.M '' S) := by
  rw [← Bornology.isBounded_induced]
  exact Bornology.IsBounded.all S

end topology

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]

set_option backward.isDefEq.respectTransparency false in
def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) where
  M := {
    val := Matrix.piProd (fun i ↦ (ρi i).m)
    property := Matrix.IsHermitian.piProd (fun i ↦ (ρi i).Hermitian)
  }
  nonneg := by
    rw [zero_le_iff]
    exact Matrix.PosSemidef.piProd (fun i => psd (ρi i))
  tr := by simp [trace, Matrix.trace_piProd]

/-- The pure state of `Ket.piProd ψ` is `MState.piProd` of the pure states `pure (ψ i)`,
generalizing `MState.pure_prod_pure`. -/
lemma pure_piProd (ψ : (i : ι) → Ket (dI i)) :
    pure (Ket.piProd ψ) = piProd (fun i ↦ pure (ψ i)) := by
  ext : 3
  simp [piProd, Matrix.piProd, -mat_apply, Finset.prod_mul_distrib]

/-- With at least one party, a ket satisfies `Ket.IsPiProd` if and only if its associated
pure state `MState.pure ψ` is an `MState.piProd` of pure states. -/
lemma isPiProd_iff_exists_pure_eq_piProd [Nonempty ι] (ψ : Ket ((i : ι) → dI i)) :
    ψ.IsPiProd ↔ ∃ φ : (i : ι) → Ket (dI i), pure ψ = piProd (fun i ↦ pure (φ i)) := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, pure_piProd φ⟩
  · rintro ⟨φ, h⟩
    rw [← pure_piProd φ, ← PhaseEquiv_iff_pure_eq] at h
    exact (Ket.isPiProd_piProd φ).of_phaseEquiv h

/-- The n-copy "power" of a mixed state, with the standard basis indexed by pi types. -/
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d) :=
  piProd (fun _ ↦ ρ)

@[inherit_doc]
infixl:110 " ⊗ᴹ^ " => MState.npow

end finprod

section posdef

lemma PosDef.kron {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {σ₁ : MState d₁} {σ₂ : MState d₂} (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) : (σ₁ ⊗ᴹ σ₂).m.PosDef :=
  hσ₁.kron hσ₂

lemma PosDef.relabel {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {ρ : MState d₁} (hρ : ρ.m.PosDef) (e : d₂ ≃ d₁) : (ρ.relabel e).m.PosDef :=
  Matrix.PosDef.reindex hρ e.symm

/-- If both states positive definite, so is their mixture. -/
theorem PosDef_mix {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) (p : Prob) : (p [σ₁ ↔ σ₂]).m.PosDef :=
  Matrix.PosDef.Convex hσ₁ hσ₂ p.zero_le (1 - p).zero_le (by simp)

/-- If one state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (p : Prob) (hp : p ≠ 0) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [← zero_lt_iff] at hp
  exact (hσ₁.smul hp).add_posSemidef (σ₂.psd.rsmul (1 - p).zero_le)

/-- If the second state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_one {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₂ : σ₂.m.PosDef) (p : Prob) (hp : p ≠ 1) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  have : 0 < 1 - p := by
    --TODO this is ridiculous, move to Prob
    contrapose! hp
    have : (1 : ℝ) - (p : ℝ) = (0 : ℝ) := by
      have := le_antisymm hp (1 - p).zero_le
      rw [Subtype.ext_iff] at this
      simpa using this
    ext
    change (p : ℝ) = 1
    linarith
  exact (hσ₂.smul this).posSemidef_add (σ₁.psd.rsmul p.zero_le)

lemma uniform_posDef {d : Type*} [Nonempty d] [Fintype d] [DecidableEq d] :
    (uniform (d := d)).m.PosDef := by
  simp [uniform, ofClassical, m, HermitianMat.diagonal]
  exact Fintype.card_pos

lemma posDef_of_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) [Unique d] : ρ.m.PosDef := by
  rw [Subsingleton.allEq ρ uniform]
  exact uniform_posDef

end posdef

end MState
