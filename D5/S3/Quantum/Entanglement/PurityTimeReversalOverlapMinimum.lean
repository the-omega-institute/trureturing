/- GID: D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pure-state min of Tr(rho_A^2) + R(rho_A) is max(2^(1-k), 2^(k-N)) (2507.12680). -/

/-
proof_shape: result: bind-only (the Frobenius identity, `sq_sum_le_card_mul_sum_sq` and trace
  cyclicity for the two lower bounds, and coefficient computations for the two explicit states;
  every step is a local `have` of `result`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11730)
Direct frozen dependencies: D5/S3/Quantum/FiniteDimensional (`qubitX`, `qubitZ`),
  D5/S3/Quantum/Information/PartialTraceMutualInformation (`partialTraceRight`)
-/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum

/-!
E. Serrano-Ensástiga, O. Giraud and J. Martin, *Multiqubit monogamy relations beyond shadow
inequalities*, arXiv:2507.12680 (Phys. Rev. A 113 (2026) 012415), Conjecture 2: for a bipartition
`A | Ā` of `N` qubits with `|A| = k`, the minimum of `Tr(ρ_A²) + Tr(ρ_A ρ̃_A)` over pure states,
with `ρ̃ = σ_y^{⊗k} ρ^* σ_y^{⊗k}`, is `2^{k-N}` if `2k > N` and `2^{1-k}` if `2k ≤ N`. It holds.
Write `ρ_A = M Mᴴ` and `ρ̃_A = Φ Φᴴ` with `Φ = Y M̄`, `Y = σ_y^{⊗k}` Hermitian and unitary. Then
`Tr(ρ_A ρ̃_A) ≥ 0` and `Tr ρ_A² = Tr (MᴴM)² ≥ (Tr MᴴM)²/2^{N-k}`, while
`2 (Tr ρ_A² + Tr ρ_A ρ̃_A) = Tr (ρ_A + ρ̃_A)² ≥ (Tr (ρ_A + ρ̃_A))²/2^k = 4/2^k`. A maximally
entangled state attains `2^{1-k}`, and when `2k > N` a state supported on configurations of `A`
that vanish at a fixed qubit, where `σ_y(0,0) = 0` kills the overlap, attains `2^{k-N}`.
-/

open Matrix D5.S3.Quantum.FiniteDimensional D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The qubits outside `A`. -/
abbrev Outside {N : ℕ} (A : Finset (Fin N)) : Type := {i : Fin N // i ∉ A}

/-- The configuration of `N` qubits with `x` on `A` and `z` outside `A`. -/
def join {N : ℕ} (A : Finset (Fin N)) (x : A → Fin 2) (z : Outside A → Fin 2) : Fin N → Fin 2 :=
  (Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ => Fin 2)).symm (x, z)

/-- The reduced density matrix `ρ_A = Tr_Ā |ψ⟩⟨ψ|`: the partial trace over the qubits outside `A`
of the pure state written on `(A → Fin 2) × (Outside A → Fin 2)`. -/
noncomputable def reducedState {N : ℕ} (A : Finset (Fin N)) (ψ : (Fin N → Fin 2) → ℂ) :
    Matrix (A → Fin 2) (A → Fin 2) ℂ :=
  partialTraceRight (Matrix.of fun p q : (A → Fin 2) × (Outside A → Fin 2) =>
    ψ (join A p.1 p.2) * star (ψ (join A q.1 q.2)))

/-- `σ_y^{⊗k}` on the qubits of `A`, with `σ_y = i X Z` for the qubit `X` and `Z`. -/
def sigmaYTensor {N : ℕ} (A : Finset (Fin N)) : Matrix (A → Fin 2) (A → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, (Complex.I • (qubitX * qubitZ)) (x i) (y i)

/-- The time-reversed state `ρ̃ = σ_y^{⊗k} ρ^* σ_y^{⊗k}`. -/
def timeReversed {N : ℕ} (A : Finset (Fin N)) (ρ : Matrix (A → Fin 2) (A → Fin 2) ℂ) :
    Matrix (A → Fin 2) (A → Fin 2) ℂ :=
  sigmaYTensor A * ρ.map star * sigmaYTensor A

/-- `Tr(ρ_A²) + R_{ρ_A}` with `R_ρ = Tr(ρ ρ̃)`, as a real number. -/
noncomputable def purityPlusOverlap {N : ℕ} (A : Finset (Fin N)) (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  (trace (reducedState A ψ * reducedState A ψ) +
    trace (reducedState A ψ * timeReversed A (reducedState A ψ))).re

/-- The conjectured minimum: `2^{k-N}` if `2k > N` and `2^{1-k}` if `2k ≤ N`. -/
noncomputable def conjecturedMin (N k : ℕ) : ℝ := if N < 2 * k then 2 ^ k / 2 ^ N else 2 / 2 ^ k

/-- Conjecture 2 of arXiv:2507.12680: for every bipartition `A | Ā` of `N` qubits into non-empty
parts, the minimum of `Tr(ρ_A²) + R_{ρ_A}` over pure states is `conjecturedMin N |A|`. -/
def claim : Prop :=
  ∀ (N : ℕ) (A : Finset (Fin N)), 1 ≤ A.card → A.card < N →
    (∀ ψ : (Fin N → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 →
      conjecturedMin N A.card ≤ purityPlusOverlap A ψ) ∧
    ∃ ψ : (Fin N → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 ∧
      purityPlusOverlap A ψ = conjecturedMin N A.card

set_option maxHeartbeats 4000000 in
-- `result` is one declaration that contains every lemma of the proof as a local `have`.
/-- The conjecture holds. -/
theorem result : claim := by
  intro N A hk1 hkN
  classical
  set e := Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ : Fin N => Fin 2) with he
  set Y := sigmaYTensor A with hY
  -- the Frobenius identity and the Cauchy–Schwarz bound on the trace
  have hfrob : ∀ {m n : Type} [Fintype m] [Fintype n] (G : Matrix m n ℂ),
      trace (G * Gᴴ) = ((∑ i, ∑ j, ‖G i j‖ ^ 2 : ℝ) : ℂ) := by
    intro m n _ _ G
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hcs : ∀ {n : Type} [Fintype n] (P : Matrix n n ℂ),
      ‖trace P‖ ^ 2 ≤ Fintype.card n * ∑ i, ∑ j, ‖P i j‖ ^ 2 := by
    intro n _ P
    have h1 : ‖trace P‖ ≤ ∑ i, ‖P i i‖ := norm_sum_le _ _
    have h2 : (∑ i, ‖P i i‖) ^ 2 ≤ Fintype.card n * ∑ i, ‖P i i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ∑ i, ‖P i i‖ ^ 2 ≤ ∑ i, ∑ j, ‖P i j‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖P i j‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
    calc ‖trace P‖ ^ 2 ≤ (∑ i, ‖P i i‖) ^ 2 := by gcongr
      _ ≤ _ := h2
      _ ≤ _ := by gcongr
  -- `Y` is Hermitian and unitary
  have hσH : ∀ a b : Fin 2, star ((Complex.I • (qubitX * qubitZ)) b a) =
      (Complex.I • (qubitX * qubitZ)) a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [qubitX, qubitZ]
  have hσσ : ∀ a c : Fin 2, ∑ b, (Complex.I • (qubitX * qubitZ)) a b *
      (Complex.I • (qubitX * qubitZ)) b c = if a = c then 1 else 0 := by
    intro a c
    fin_cases a <;> fin_cases c <;> simp [qubitX, qubitZ, Fin.sum_univ_two]
  have hYH : Yᴴ = Y := by
    ext x y
    simp only [hY, sigmaYTensor, conjTranspose_apply, of_apply, star_prod, hσH]
  have hYY : Y * Y = 1 := by
    ext x y
    simp only [hY, sigmaYTensor, mul_apply, of_apply, one_apply]
    rw [show (∑ u : A → Fin 2, (∏ i, (Complex.I • (qubitX * qubitZ)) (x i) (u i)) *
        ∏ i, (Complex.I • (qubitX * qubitZ)) (u i) (y i)) =
        ∏ i, ∑ b, (Complex.I • (qubitX * qubitZ)) (x i) b *
          (Complex.I • (qubitX * qubitZ)) b (y i) by
      rw [Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]]
    simp only [hσσ, Fintype.prod_boole]
    simp only [funext_iff]
  -- the matrix of `ψ` across the bipartition
  set Mof : ((Fin N → Fin 2) → ℂ) → Matrix (A → Fin 2) (Outside A → Fin 2) ℂ :=
    fun ψ => Matrix.of fun x z => ψ (join A x z) with hMof
  have hρ : ∀ ψ, reducedState A ψ = Mof ψ * (Mof ψ)ᴴ := by
    intro ψ
    ext x y
    simp [reducedState, partialTraceRight, hMof, mul_apply, conjTranspose_apply]
  have hnorm : ∀ ψ : (Fin N → Fin 2) → ℂ,
      ∑ w, ‖ψ w‖ ^ 2 = ∑ x, ∑ z, ‖Mof ψ x z‖ ^ 2 := by
    intro ψ
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    rfl
  -- the two traces in terms of `M` and `Φ = Y M̄`
  have hmapmul : ∀ {l m n : Type} [Fintype m] (P : Matrix l m ℂ) (Q : Matrix m n ℂ),
      (P * Q).map star = P.map star * Q.map star := by
    intro l m n _ P Q
    ext i j
    simp [mul_apply]
  have hmapH : ∀ {m n : Type} (P : Matrix m n ℂ), (Pᴴ).map star = (P.map star)ᴴ := by
    intro m n P
    ext i j
    simp [conjTranspose_apply]
  have htilde : ∀ M : Matrix (A → Fin 2) (Outside A → Fin 2) ℂ,
      timeReversed A (M * Mᴴ) = (Y * M.map star) * (Y * M.map star)ᴴ := by
    intro M
    rw [timeReversed, ← hY, conjTranspose_mul, hYH, hmapmul, hmapH]
    simp only [Matrix.mul_assoc]
  have hstarTr : ∀ {n : Type} [Fintype n] (P : Matrix n n ℂ),
      trace (P.map star) = star (trace P) := by
    intro n _ P
    simp [trace, star_sum]
  have hΦΦ : ∀ M : Matrix (A → Fin 2) (Outside A → Fin 2) ℂ,
      (Y * M.map star)ᴴ * (Y * M.map star) = (Mᴴ * M).map star := by
    intro M
    rw [conjTranspose_mul, hYH, Matrix.mul_assoc, ← Matrix.mul_assoc Y Y, hYY, Matrix.one_mul,
      hmapmul, hmapH]
  have hcyc4 : ∀ {m n : Type} [Fintype m] [Fintype n] (P : Matrix m n ℂ) (Q : Matrix n m ℂ)
      (R : Matrix m n ℂ) (T : Matrix n m ℂ),
      trace (P * Q * (R * T)) = trace (Q * R * (T * P)) := by
    intro m n _ _ P Q R T
    simp only [Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  -- `F` is the purity of `MᴴM` plus the Frobenius norm of `Mᴴ Φ`
  have hF : ∀ ψ, purityPlusOverlap A ψ =
      (trace ((Mof ψ)ᴴ * Mof ψ * ((Mof ψ)ᴴ * Mof ψ))).re +
      (trace ((Mof ψ)ᴴ * (Y * (Mof ψ).map star) *
        ((Y * (Mof ψ).map star)ᴴ * Mof ψ))).re := by
    intro ψ
    rw [purityPlusOverlap, hρ, htilde, Complex.add_re, hcyc4, hcyc4 (Mof ψ)]
  -- dimensions
  have hcardA : Fintype.card (A → Fin 2) = 2 ^ A.card := by
    simp
  have hcardB : Fintype.card (Outside A → Fin 2) = 2 ^ (N - A.card) := by
    simp [Outside, Fintype.card_subtype_compl]
  have hcA : ((Fintype.card (A → Fin 2) : ℕ) : ℝ) = 2 ^ A.card := by
    rw [hcardA]; push_cast; ring
  have hcB : ((Fintype.card (Outside A → Fin 2) : ℕ) : ℝ) = 2 ^ (N - A.card) := by
    rw [hcardB]; push_cast; ring
  have hpow : (2 : ℝ) ^ N = 2 ^ A.card * 2 ^ (N - A.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hkN.le]
  have hre : ∀ {m n : Type} [Fintype m] [Fintype n] (G : Matrix m n ℂ),
      (trace (G * Gᴴ)).re = ∑ i, ∑ j, ‖G i j‖ ^ 2 := by
    intro m n _ _ G
    rw [hfrob, Complex.ofReal_re]
  -- the two lower bounds
  have hlow : ∀ ψ : (Fin N → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 →
      1 / (2 : ℝ) ^ (N - A.card) ≤ purityPlusOverlap A ψ ∧
      2 / (2 : ℝ) ^ A.card ≤ purityPlusOverlap A ψ := by
    intro ψ hψ
    have hM1 : ∑ x, ∑ z, ‖Mof ψ x z‖ ^ 2 = 1 := (hnorm ψ).symm.trans hψ
    have htrMM : trace ((Mof ψ)ᴴ * Mof ψ) = 1 := by
      rw [trace_mul_comm, hfrob, hM1, Complex.ofReal_one]
    have htrρ : trace (Mof ψ * (Mof ψ)ᴴ) = 1 := by
      rw [hfrob, hM1, Complex.ofReal_one]
    have htrρt : trace ((Y * (Mof ψ).map star) * (Y * (Mof ψ).map star)ᴴ) = 1 := by
      rw [trace_mul_comm, hΦΦ, hstarTr, htrMM, star_one]
    have hKH : ((Mof ψ)ᴴ * Mof ψ)ᴴ = (Mof ψ)ᴴ * Mof ψ := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
    constructor
    · -- `F ≥ 1/r`
      rw [hF ψ]
      have hK := hcs ((Mof ψ)ᴴ * Mof ψ)
      rw [htrMM, norm_one, one_pow, hcB] at hK
      have hKK : (trace ((Mof ψ)ᴴ * Mof ψ * ((Mof ψ)ᴴ * Mof ψ))).re =
          ∑ i, ∑ j, ‖((Mof ψ)ᴴ * Mof ψ) i j‖ ^ 2 := by
        rw [show (Mof ψ)ᴴ * Mof ψ * ((Mof ψ)ᴴ * Mof ψ) =
          ((Mof ψ)ᴴ * Mof ψ) * ((Mof ψ)ᴴ * Mof ψ)ᴴ by rw [hKH]]
        exact hre _
      have h2 : 0 ≤ (trace ((Mof ψ)ᴴ * (Y * (Mof ψ).map star) *
          ((Y * (Mof ψ).map star)ᴴ * Mof ψ))).re := by
        have := hre ((Mof ψ)ᴴ * (Y * (Mof ψ).map star))
        rw [conjTranspose_mul, conjTranspose_conjTranspose] at this
        rw [this]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hr : (0 : ℝ) < 2 ^ (N - A.card) := by positivity
      rw [hKK, div_le_iff₀ hr]
      have h3 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h2 :
        ∑ i, ∑ j, ‖((Mof ψ)ᴴ * Mof ψ) i j‖ ^ 2 ≤ _) hr.le
      linarith
    · -- `F ≥ 2/d`
      set M := Mof ψ with hM
      set Φ := Y * M.map star with hΦ
      set S := M * Mᴴ + Φ * Φᴴ with hS
      have hSH : Sᴴ = S := by
        rw [hS, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
          conjTranspose_mul, conjTranspose_conjTranspose]
      have htrS : trace S = 2 := by
        rw [hS, trace_add, htrρ, htrρt]; norm_num
      have hSS : (trace (S * S)).re = 2 * purityPlusOverlap A ψ := by
        rw [purityPlusOverlap, hρ, htilde, ← hM, ← hΦ, hS]
        simp only [add_mul, mul_add, trace_add, Complex.add_re]
        have h1 : trace (Φ * Φᴴ * (M * Mᴴ)) = trace (M * Mᴴ * (Φ * Φᴴ)) := trace_mul_comm _ _
        have h2 : (trace (Φ * Φᴴ * (Φ * Φᴴ))).re = (trace (M * Mᴴ * (M * Mᴴ))).re := by
          rw [hcyc4 Φ, hcyc4 M, hΦΦ, ← hmapmul, hstarTr, Complex.star_def, Complex.conj_re]
        rw [h1, h2]
        ring
      have hcs' := hcs S
      rw [htrS, hcA, Complex.norm_two] at hcs'
      have hSre : (trace (S * S)).re = ∑ i, ∑ j, ‖S i j‖ ^ 2 := by
        rw [show S * S = S * Sᴴ by rw [hSH]]
        exact hre _
      have hd : (0 : ℝ) < 2 ^ A.card := by positivity
      rw [div_le_iff₀ hd]
      rw [← hSre, hSS] at hcs'
      linarith
  have hcardAt : Fintype.card A = A.card := Fintype.card_coe A
  have hcardBt : Fintype.card (Outside A) = N - A.card := by
    simp [Outside, Fintype.card_subtype_compl]
  have hMjoin : ∀ f : (A → Fin 2) → (Outside A → Fin 2) → ℂ,
      Mof (fun w => f (e w).1 (e w).2) = Matrix.of f := by
    intro f
    ext x z
    simp only [hMof, of_apply, join, ← he, Equiv.apply_symm_apply]
  -- `‖c‖² = 1/n` for `c = n^{-1/2}`
  have hcnorm : ∀ n : ℕ, 0 < n →
      ‖(((Real.sqrt n)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / n ∧
      star (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = ((1 / n : ℝ) : ℂ) := by
    intro n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsq : (Real.sqrt n)⁻¹ ^ 2 = 1 / n := by
      rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
    constructor
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq, hsq]
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hlow ψ hψ
    unfold conjecturedMin
    split_ifs with h
    · calc (2 : ℝ) ^ A.card / 2 ^ N = 1 / 2 ^ (N - A.card) := by
            rw [hpow]; field_simp
        _ ≤ _ := h1
    · exact h2
  unfold conjecturedMin
  split_ifs with h
  · -- `2k > N`: a state supported on configurations of `A` vanishing at `i₀`
    have hlt : Fintype.card (Outside A) < Fintype.card A := by
      rw [hcardAt, hcardBt]; omega
    obtain ⟨κ⟩ := Function.Embedding.nonempty_of_card_le hlt.le
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : A, ∀ j, κ j ≠ i₀ := by
      by_contra hcon
      push Not at hcon
      exact absurd (Fintype.card_le_of_surjective κ hcon) (not_le.mpr hlt)
    set g : (Outside A → Fin 2) → (A → Fin 2) := fun z => Function.extend κ z 0 with hg
    have hg_inj : Function.Injective g := by
      intro z z' hzz
      funext j
      have := congrFun hzz (κ j)
      simpa [hg, κ.injective.extend_apply] using this
    have hg0 : ∀ z, g z i₀ = 0 := by
      intro z
      simp only [hg]
      rw [Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact hi₀ j hj)]
      rfl
    have hr0 : 0 < 2 ^ (N - A.card) := by positivity
    obtain ⟨hcn, hcc⟩ := hcnorm (2 ^ (N - A.card)) hr0
    set c : ℂ := (((Real.sqrt ((2 ^ (N - A.card) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) with hc
    set Mf : (A → Fin 2) → (Outside A → Fin 2) → ℂ := fun x z => if x = g z then c else 0 with hMf
    refine ⟨fun w => Mf (e w).1 (e w).2, ?_, ?_⟩
    · rw [hnorm, hMjoin Mf, Finset.sum_comm]
      have : ∀ z : Outside A → Fin 2, ∑ x : A → Fin 2, ‖Matrix.of Mf x z‖ ^ 2 = ‖c‖ ^ 2 := by
        intro z
        rw [Finset.sum_eq_single (g z)]
        · simp [hMf]
        · intro x _ hx; simp [hMf, hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [Finset.sum_congr rfl fun z _ => this z, Finset.sum_const, Finset.card_univ, hcardB,
        nsmul_eq_mul, hcn]
      push_cast
      field_simp
    · rw [hF, hMjoin Mf]
      have hK : (Matrix.of Mf)ᴴ * Matrix.of Mf =
          ((1 / (2 ^ (N - A.card) : ℕ) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
        ext z z'
        simp only [mul_apply, conjTranspose_apply, of_apply, hMf, Matrix.smul_apply, one_apply,
          smul_eq_mul]
        rw [Finset.sum_eq_single (g z)]
        · by_cases hzz : z = z'
          · subst hzz
            have hcc' : (starRingEnd ℂ) c * c = ((2 : ℂ) ^ (N - A.card))⁻¹ := by
              rw [← Complex.star_def, hcc]; push_cast; ring
            simp [hcc']
          · have : g z ≠ g z' := fun h' => hzz (hg_inj h')
            simp [hzz, this]
        · intro x _ hx; simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hG : (Matrix.of Mf)ᴴ * (Y * (Matrix.of Mf).map star) = 0 := by
        ext z z'
        simp only [mul_apply, conjTranspose_apply, of_apply, map_apply, hMf, Matrix.zero_apply]
        rw [Finset.sum_eq_single (g z)]
        · rw [Finset.sum_eq_single (g z')]
          · have hY0 : Y (g z) (g z') = 0 := by
              simp only [hY, sigmaYTensor, of_apply]
              exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by
                rw [hg0, hg0]; simp [qubitX, qubitZ])
            simp [hY0]
          · intro u _ hu; simp [hu]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro x _ hx; simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hK, hG, Matrix.zero_mul, trace_zero, Complex.zero_re, add_zero, smul_mul_smul_comm,
        Matrix.one_mul, trace_smul, trace_one, hcardB]
      simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im]
      rw [hpow]
      push_cast
      field_simp
      ring
  · -- `2k ≤ N`: a maximally entangled state
    have hle : Fintype.card A ≤ Fintype.card (Outside A) := by
      rw [hcardAt, hcardBt]; omega
    obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hle
    set g : (A → Fin 2) → (Outside A → Fin 2) := fun x => Function.extend ι x 0 with hg
    have hg_inj : Function.Injective g := by
      intro x x' hxx
      funext i
      have := congrFun hxx (ι i)
      simpa [hg, ι.injective.extend_apply] using this
    have hd0 : 0 < 2 ^ A.card := by positivity
    obtain ⟨hcn, hcc⟩ := hcnorm (2 ^ A.card) hd0
    set c : ℂ := (((Real.sqrt ((2 ^ A.card : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) with hc
    set Mf : (A → Fin 2) → (Outside A → Fin 2) → ℂ := fun x z => if z = g x then c else 0 with hMf
    refine ⟨fun w => Mf (e w).1 (e w).2, ?_, ?_⟩
    · rw [hnorm, hMjoin Mf]
      have : ∀ x : A → Fin 2, ∑ z : Outside A → Fin 2, ‖Matrix.of Mf x z‖ ^ 2 = ‖c‖ ^ 2 := by
        intro x
        rw [Finset.sum_eq_single (g x)]
        · simp [hMf]
        · intro z _ hz; simp [hMf, hz]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const, Finset.card_univ, hcardA,
        nsmul_eq_mul, hcn]
      push_cast
      field_simp
    · have hρ1 : reducedState A (fun w => Mf (e w).1 (e w).2) =
          ((1 / (2 ^ A.card : ℕ) : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
        rw [hρ, hMjoin Mf]
        ext x y
        simp only [mul_apply, conjTranspose_apply, of_apply, hMf, Matrix.smul_apply, one_apply,
          smul_eq_mul]
        rw [Finset.sum_eq_single (g x)]
        · by_cases hxy : x = y
          · subst hxy
            have hcc' : c * (starRingEnd ℂ) c = ((2 : ℂ) ^ A.card)⁻¹ := by
              rw [mul_comm, ← Complex.star_def, hcc]; push_cast; ring
            simp [hcc']
          · have : g x ≠ g y := fun h' => hxy (hg_inj h')
            simp [hxy, this]
        · intro z _ hz; simp [hz]
        · intro h; exact absurd (Finset.mem_univ _) h
      set s : ℝ := 1 / (2 ^ A.card : ℕ) with hs
      have hT : timeReversed A ((s : ℂ) • (1 : Matrix (A → Fin 2) (A → Fin 2) ℂ)) =
          (s : ℂ) • (1 : Matrix (A → Fin 2) (A → Fin 2) ℂ) := by
        have hmap1 : ((s : ℂ) • (1 : Matrix (A → Fin 2) (A → Fin 2) ℂ)).map star =
            (s : ℂ) • (1 : Matrix (A → Fin 2) (A → Fin 2) ℂ) := by
          ext x y
          rw [map_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
          split_ifs <;> simp only [mul_one, mul_zero, star_zero, Complex.star_def,
            Complex.conj_ofReal]
        rw [timeReversed, ← hY, hmap1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hYY]
      rw [purityPlusOverlap, hρ1, hT]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, trace_smul, trace_one, hcardA,
        smul_eq_mul]
      have hval : (s : ℂ) * ((s : ℂ) * ((2 ^ A.card : ℕ) : ℂ)) +
          (s : ℂ) * ((s : ℂ) * ((2 ^ A.card : ℕ) : ℂ)) =
          ((2 * s * s * (2 ^ A.card : ℕ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hval, Complex.ofReal_re, hs]
      push_cast
      field_simp

end D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
