/- GID: D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.claim; result=D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.result; claim=D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.claim
   digest: C3 multiplicity two refutes the twirling phase index conjecture. -/

/-
admission_basis: open-problem-resolution (#15229; Refuted)
proof_shape: result: bind-only (explicit instance, character orthogonality, dimension bounds and
    coordinate normalization).
escape_witness: none
Direct frozen dependencies: none
proof_shape: chi_unit: bind-only; consumer: rho; escape_witness: none; Direct frozen dependencies:
    none
proof_shape: chi_mul: bind-only; consumer: rho; escape_witness: none; Direct frozen dependencies:
    none
proof_shape: rho_irreducible: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: rho_inequivalent: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: pi_diagonal: bind-only; consumer: twirl_is_pinching, blockProj_fourier, beta_ge_two;
    escape_witness: none; Direct frozen dependencies: none
proof_shape: chi_orthogonal: bind-only; consumer: twirl_is_pinching, blockProj_fourier;
    escape_witness: none; Direct frozen dependencies: none
proof_shape: twirl_is_pinching: bind-only; consumer: encoding_phase_retrievable; escape_witness:
    none; Direct frozen dependencies: none
proof_shape: scale_ne: bind-only; consumer: overlapping_pair_operator_injective; escape_witness:
    none; Direct frozen dependencies: none
proof_shape: scale_normSq: bind-only; consumer: encoding_energy; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: encoding_energy: bind-only; consumer: encoding_norm; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: encoding_norm: bind-only; consumer: encoding_injective; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: encoding_injective: bind-only; consumer: pr_ge_three; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: V_mulVec: bind-only; consumer: V_outer; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: V_compression: bind-only; consumer: overlapping_pair_operator_injective;
    escape_witness: none; Direct frozen dependencies: none
proof_shape: overlapping_pair_operator_injective: bind-only; consumer: overlap_outer_injective;
    escape_witness: none; Direct frozen dependencies: none
proof_shape: V_outer: bind-only; consumer: overlap_outer_injective; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: overlap_outer_injective: bind-only; consumer: encoding_phase_retrievable;
    escape_witness: none; Direct frozen dependencies: none
proof_shape: encoding_phase_retrievable: bind-only; consumer: pr_ge_three; escape_witness: none;
    Direct frozen dependencies: none
proof_shape: pr_ge_three: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: blockProj_sum: bind-only; consumer: code_dim_le_two; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: blockProj_idempotent: bind-only; consumer: beta_ge_two; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: blockProj_star: bind-only; consumer: beta_ge_two; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: blockProj_fourier: bind-only; consumer: code_compressions; escape_witness: none;
    Direct frozen dependencies: none
proof_shape: code_compressions: bind-only; consumer: code_dim_le_two; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: code_dim_le_two: bind-only; consumer: beta_le_two, beta_ge_two; escape_witness: none;
    Direct frozen dependencies: none
proof_shape: beta_le_two: bind-only; consumer: beta_eq_two; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: blockEncoding_injective: bind-only; consumer: beta_ge_two; escape_witness: none;
    Direct frozen dependencies: none
proof_shape: block_range: bind-only; consumer: beta_ge_two; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: beta_ge_two: bind-only; consumer: beta_eq_two; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: beta_eq_two: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: cross_zero: bind-only; consumer: no_three_frame; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: equal_norm_add_sub: bind-only; consumer: no_three_frame; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: no_three_frame: bind-only; consumer: no_short_frame; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: no_short_frame: bind-only; consumer: frame_two_gt_three; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: four_frame: bind-only; consumer: frame_two_gt_three; escape_witness: none; Direct
    frozen dependencies: none
proof_shape: frame_two_gt_three: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
proof_shape: frame_one_le_three: bind-only; consumer: result; escape_witness: none; Direct frozen
    dependencies: none
The public result is the designated refutation result (`basis=refutes`) and is exempt from
    four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option linter.unusedSimpArgs false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample

variable {G I : Type} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

def twirl (pi : G →* Matrix.unitaryGroup I ℂ) (X : Matrix I I ℂ) : Matrix I I ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (pi g : Matrix I I ℂ) * X * star (pi g : Matrix I I ℂ)

def PhaseRetrievable (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (M : Submodule ℂ (I → ℂ)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M,
    Phi (vecMulVec x (star x)) = Phi (vecMulVec y (star y)) →
      vecMulVec x (star x) = vecMulVec y (star y)

def pr (Phi : Matrix I I ℂ → Matrix I I ℂ) : ℕ :=
  sSup {k | ∃ M : Submodule ℂ (I → ℂ),
    Module.finrank ℂ M = k ∧ PhaseRetrievable Phi M}

def IsCode (pi : G →* Matrix.unitaryGroup I ℂ) (M : Submodule ℂ (I → ℂ)) : Prop :=
  ∃ P : Matrix I I ℂ, star P = P ∧ P * P = P ∧ LinearMap.range P.mulVecLin = M ∧
    ∃ c : G → G → ℂ, ∀ g h,
      P * star (pi g : Matrix I I ℂ) * (pi h : Matrix I I ℂ) * P = c g h • P

def beta (pi : G →* Matrix.unitaryGroup I ℂ) : ℕ :=
  sSup {k | ∃ M : Submodule ℂ (I → ℂ), Module.finrank ℂ M = k ∧ IsCode pi M}

def frameLength (k : ℕ) : ℕ :=
  sInf {n | ∃ f : Fin n → (Fin k → ℂ), ∀ x y : Fin k → ℂ,
    (∀ j, ‖dotProduct x (star (f j))‖ = ‖dotProduct y (star (f j))‖) →
      vecMulVec x (star x) = vecMulVec y (star y)}

def Irreducible {n : ℕ} (rho : G →* Matrix.unitaryGroup (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ M : Submodule ℂ (Fin n → ℂ),
    (∀ g x, x ∈ M → (rho g : Matrix (Fin n) (Fin n) ℂ) *ᵥ x ∈ M) → M = ⊥ ∨ M = ⊤

def Inequivalent {n k : ℕ} (rho : G →* Matrix.unitaryGroup (Fin n) ℂ)
    (sigma : G →* Matrix.unitaryGroup (Fin k) ℂ) : Prop :=
  ¬ ∃ T : (Fin n → ℂ) ≃ₗ[ℂ] (Fin k → ℂ), ∀ g x,
    T ((rho g : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) =
      (sigma g : Matrix (Fin k) (Fin k) ℂ) *ᵥ T x

def blockRep {d : ℕ} {n : Fin d → ℕ}
    (rho : ∀ i, G →* Matrix.unitaryGroup (Fin (n i)) ℂ) (m : Fin d → ℕ) :
    G →* Matrix.unitaryGroup (Σ i, Fin (m i) × Fin (n i)) ℂ where
  toFun g := ⟨blockDiagonal' (fun i =>
    (1 : Matrix (Fin (m i)) (Fin (m i)) ℂ) ⊗ₖ (rho i g : Matrix _ _ ℂ)), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simp only [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.blockDiagonal'_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    simp only [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp (rho _ g).property,
        Matrix.one_kronecker_one]
    change blockDiagonal' (1 : ∀ i : Fin d, Matrix (Fin (m i) × Fin (n i)) (Fin (m i) × Fin (n i))
        ℂ) = 1
    exact Matrix.blockDiagonal'_one⟩
  map_one' := by
    apply Subtype.ext
    simp only [MonoidHom.map_one, Submonoid.coe_one, Matrix.one_kronecker_one]
    change blockDiagonal' (1 : ∀ i : Fin d, Matrix (Fin (m i) × Fin (n i)) (Fin (m i) × Fin (n i))
        ℂ) = 1
    exact Matrix.blockDiagonal'_one
  map_mul' g h := by
    apply Subtype.ext
    simp only [map_mul, Submonoid.coe_mul, ← Matrix.blockDiagonal'_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]

def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (d : ℕ) (n m : Fin d → ℕ)
    (rho : ∀ i, G →* Matrix.unitaryGroup (Fin (n i)) ℂ),
    (∀ i, Irreducible (rho i)) →
    (∀ i j, i ≠ j → Inequivalent (rho i) (rho j)) →
    (∀ i, 1 ≤ m i) → ∀ k : ℕ,
    frameLength k ≤ d → d < frameLength (k + 1) →
    pr (twirl (blockRep rho m)) = max (beta (blockRep rho m)) k


theorem chi_unit (i : Fin 3) (g : (Multiplicative (ZMod 3))) : star ((ZMod.stdAddChar
    ((ZMod.finEquiv 3 i) * g.toAdd))) * (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd)) = 1 :=
    by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp [AddChar.norm_apply]

private theorem chi_mul (i : Fin 3) (g h : (Multiplicative (ZMod 3))) : (ZMod.stdAddChar
    ((ZMod.finEquiv 3 i) * (g*h).toAdd)) = (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd)) *
    (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * h.toAdd)) := by
  simp only [toAdd_mul, mul_add, AddChar.map_add_eq_mul]

private def rho (i : Fin 3) : (Multiplicative (ZMod 3)) →* Matrix.unitaryGroup (Fin 1) ℂ where
  toFun g := ⟨diagonal (fun _ => (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd))), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext a b; fin_cases a; fin_cases b
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply] using chi_unit i g⟩
  map_one' := by
    apply Subtype.ext; ext a b; fin_cases a; fin_cases b
    simp [AddChar.map_zero_eq_one]
  map_mul' g h := by
    apply Subtype.ext; ext a b; fin_cases a; fin_cases b
    simpa [Matrix.mul_apply] using chi_mul i g h


private def pinching (X : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1) ℂ) :
    Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1) ℂ :=
  fun a b => if a.1 = b.1 then X a b else 0

private theorem rho_irreducible (i : Fin 3) : Irreducible (rho i) := by
  refine ⟨by norm_num, fun M _ => ?_⟩
  by_cases h : M = ⊥
  · exact Or.inl h
  · right
    apply Submodule.eq_top_of_finrank_eq
    have hl : Module.finrank ℂ M ≤ 1 := by
      simpa using M.finrank_le
    have hp : 0 < Module.finrank ℂ M :=
      Submodule.one_le_finrank_iff.mpr h
    simpa using (show Module.finrank ℂ M = 1 by omega)

private theorem rho_inequivalent (i j : Fin 3) (hij : i ≠ j) :
    Inequivalent (rho i) (rho j) := by
  intro hh
  obtain ⟨T,hT⟩ := hh
  let e : Fin 1 → ℂ := fun _ => 1
  have he : e ≠ 0 := by intro h; have hh := congrFun h 0; norm_num [e] at hh
  have hTe : T e ≠ 0 := fun h => he (T.injective (by simpa using h))
  have hT0 : T e 0 ≠ 0 := by
    intro h
    apply hTe
    ext a; fin_cases a; exact h
  let g : (Multiplicative (ZMod 3)) := Multiplicative.ofAdd (1 : ZMod 3)
  have hg : ∀ a, (rho a g : Matrix (Fin 1) (Fin 1) ℂ) =
      diagonal (fun _ => (ZMod.stdAddChar ((ZMod.finEquiv 3 a) * g.toAdd))) := fun _ => rfl
  have hh := congrFun (hT g e) 0
  have hn : (rho i g : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ e = (ZMod.stdAddChar ((ZMod.finEquiv 3 i) *
      g.toAdd)) • e := by
    ext a; fin_cases a; simp [hg, e]
  rw [hn, T.map_smul] at hh
  simp [hg, Matrix.mulVec_diagonal] at hh
  have hchi : (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd)) = (ZMod.stdAddChar ((ZMod.finEquiv
      3 j) * g.toAdd)) := hh.resolve_right hT0
  apply hij
  apply (ZMod.finEquiv 3).injective
  apply ZMod.injective_stdAddChar
  simpa [g] using hchi

private theorem pi_diagonal (g : (Multiplicative (ZMod 3))) :
    ((blockRep rho (fun _ => 2)) g : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin
        1) ℂ) = diagonal (fun a => (ZMod.stdAddChar ((ZMod.finEquiv 3 a.1) * g.toAdd))) := by
  ext ⟨i,a,b⟩ ⟨j,c,d⟩
  fin_cases b; fin_cases d
  by_cases hij : i=j
  · subst j
    simp [blockRep, rho, Matrix.blockDiagonal'_apply', Matrix.kronecker_apply,
      Matrix.one_apply, Matrix.diagonal_apply]
  · simp [blockRep, rho, Matrix.blockDiagonal'_apply', Matrix.diagonal_apply, hij,
      Matrix.one_apply, Matrix.kronecker_apply]

private theorem chi_orthogonal (i j : Fin 3) :
    ∑ g : (Multiplicative (ZMod 3)), (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd)) * star
        ((ZMod.stdAddChar ((ZMod.finEquiv 3 j) * g.toAdd))) = if i = j then (3 : ℂ) else 0 := by
  have hm (g : (Multiplicative (ZMod 3))) : (ZMod.stdAddChar ((ZMod.finEquiv 3 i) * g.toAdd)) *
      star ((ZMod.stdAddChar ((ZMod.finEquiv 3 j) * g.toAdd))) =
    ZMod.stdAddChar (g.toAdd * (ZMod.finEquiv 3 i - ZMod.finEquiv 3 j)) := by
      simp only [Complex.star_def, ← AddChar.map_neg_eq_conj,
        ← AddChar.map_add_eq_mul]
      congr 1; ring
  simp only [hm]
  rw [Fintype.sum_equiv Multiplicative.toAdd
    (fun g : (Multiplicative (ZMod 3)) => ZMod.stdAddChar (g.toAdd * (ZMod.finEquiv 3 i -
        ZMod.finEquiv 3 j)))
    (fun g : ZMod 3 => ZMod.stdAddChar (g * (ZMod.finEquiv 3 i - ZMod.finEquiv 3 j)))
    (fun _ => rfl)]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar 3)]
  have he : ZMod.finEquiv 3 i - ZMod.finEquiv 3 j = 0 ↔ i = j := by
    rw [sub_eq_zero, (ZMod.finEquiv 3).injective.eq_iff]
  simp [he]

private theorem twirl_is_pinching (X : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 ×
    Fin 1) ℂ) : twirl (blockRep rho (fun _ => 2)) X = pinching X := by
  ext a b
  simp only [twirl, pi_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Pi.star_apply]
  have ht : ∑ g : (Multiplicative (ZMod 3)), (ZMod.stdAddChar ((ZMod.finEquiv 3 a.1) * g.toAdd)) *
      X a b * star ((ZMod.stdAddChar ((ZMod.finEquiv 3 b.1) * g.toAdd))) =
    (∑ g : (Multiplicative (ZMod 3)), (ZMod.stdAddChar ((ZMod.finEquiv 3 a.1) * g.toAdd)) * star
        ((ZMod.stdAddChar ((ZMod.finEquiv 3 b.1) * g.toAdd)))) * X a b := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro g _; ring
  rw [ht, chi_orthogonal]
  have hcard : Fintype.card (Multiplicative (ZMod 3)) = 3 := Fintype.card_congr
      Multiplicative.toAdd
    |>.trans (ZMod.card 3)
  simp [hcard, pinching]

private def coord : Fin 3 → Fin 2 → Fin 3 := ![![0,1], ![0,2], ![1,2]]

private theorem scale_ne : ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)

private def encoding : (Fin 3 → ℂ) →ₗ[ℂ] ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • LinearMap.pi (fun a => LinearMap.proj (coord a.1 a.2.1))

theorem scale_normSq : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℝ) := by
  rw [map_inv₀]
  simp only [Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem encoding_energy (x : Fin 3 → ℂ) :
    ∑ a : (Σ _ : Fin 3, Fin 2 × Fin 1), Complex.normSq (encoding x a) = ∑ i : Fin 3,
        Complex.normSq (x i) := by
  calc
    _ = ∑ a : (Σ _ : Fin 3, Fin 2 × Fin 1),
        (1 / 2 : ℝ) * Complex.normSq (x (coord a.1 a.2.1)) := by
      apply Finset.sum_congr rfl
      intro a _
      change Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹) * x (coord a.1 a.2.1)) = _
      rw [map_mul, scale_normSq]
    _ = _ := by
      simp [Fintype.sum_sigma, Fintype.sum_prod_type, Fin.sum_univ_succ, coord]
      ring

private theorem encoding_norm (x : Fin 3 → ℂ) :
    ‖WithLp.toLp 2 (encoding x)‖ = ‖WithLp.toLp 2 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,
    ← Complex.normSq_eq_norm_sq]
  exact encoding_energy x

private theorem encoding_injective : Function.Injective encoding := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hh := encoding_norm x
  rw [hx] at hh
  have hn : ‖WithLp.toLp 2 x‖ = 0 := by simpa using hh.symm
  have hz := norm_eq_zero.mp hn
  exact congrArg WithLp.ofLp hz


private theorem V_mulVec (x : Fin 3 → ℂ) : (LinearMap.toMatrix' encoding) *ᵥ x = encoding x := by
  exact LinearMap.toMatrix'_mulVec encoding x

private theorem V_compression (X : Matrix (Fin 3) (Fin 3) ℂ) (a b : (Σ _ : Fin 3, Fin 2 × Fin 1)) :
    ((LinearMap.toMatrix' encoding) * X * (LinearMap.toMatrix' encoding)ᴴ) a b = ((Real.sqrt 2 :
        ℂ)⁻¹) * X (coord a.1 a.2.1) (coord b.1 b.2.1) * star ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [LinearMap.toMatrix'_apply, encoding, Pi.single_apply, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    ite_mul, mul_ite, eq_comm, mul_assoc, apply_ite]

private theorem overlapping_pair_operator_injective :
    Function.Injective (fun X : Matrix (Fin 3) (Fin 3) ℂ => pinching ((LinearMap.toMatrix'
        encoding) * X * (LinearMap.toMatrix' encoding)ᴴ)) := by
  intro X Y h
  have hp (i : Fin 3) (a b : Fin 2) : X (coord i a) (coord i b) = Y (coord i a) (coord i b) := by
    have hh := congrFun (congrFun h ⟨i,a,0⟩) ⟨i,b,0⟩
    simp only [pinching, if_true, V_compression] at hh
    have hs := star_ne_zero.mpr scale_ne
    exact mul_left_cancel₀ scale_ne (mul_right_cancel₀ hs hh)
  ext a b
  fin_cases a <;> fin_cases b <;>
    first | simpa [coord] using hp 0 0 0
          | simpa [coord] using hp 0 0 1
          | simpa [coord] using hp 0 1 0
          | simpa [coord] using hp 0 1 1
          | simpa [coord] using hp 1 0 1
          | simpa [coord] using hp 1 1 0
          | simpa [coord] using hp 1 1 1
          | simpa [coord] using hp 2 0 1
          | simpa [coord] using hp 2 1 0

private theorem V_outer (x : Fin 3 → ℂ) :
    (LinearMap.toMatrix' encoding) * vecMulVec x (star x) * (LinearMap.toMatrix' encoding)ᴴ =
        vecMulVec (encoding x) (star (encoding x)) := by
  rw [← V_mulVec]
  simp only [star_mulVec, mul_vecMulVec, vecMulVec_mul, Matrix.star_eq_conjTranspose]

private theorem overlap_outer_injective (x y : Fin 3 → ℂ)
    (h : pinching (vecMulVec (encoding x) (star (encoding x))) =
         pinching (vecMulVec (encoding y) (star (encoding y)))) :
    vecMulVec x (star x) = vecMulVec y (star y) := by
  apply overlapping_pair_operator_injective
  simpa only [V_outer] using h

private theorem encoding_phase_retrievable :
    PhaseRetrievable (twirl (blockRep rho (fun _ => 2))) (LinearMap.range encoding) := by
  intro x hx y hy h
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  rw [twirl_is_pinching, twirl_is_pinching] at h
  have he := overlap_outer_injective u v h
  ext a b
  have hh := congrFun (congrFun he (coord a.1 a.2.1)) (coord b.1 b.2.1)
  simp only [vecMulVec_apply, Pi.star_apply] at hh ⊢
  change ((Real.sqrt 2 : ℂ)⁻¹) * u (coord a.1 a.2.1) * star (((Real.sqrt 2 : ℂ)⁻¹) * u (coord b.1
      b.2.1)) =
    ((Real.sqrt 2 : ℂ)⁻¹) * v (coord a.1 a.2.1) * star (((Real.sqrt 2 : ℂ)⁻¹) * v (coord b.1
        b.2.1))
  simp only [star_mul]
  linear_combination (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * hh

private theorem pr_ge_three : 3 ≤ pr (twirl (blockRep rho (fun _ => 2))) := by
  apply le_csSup (show BddAbove {k | ∃ M : Submodule ℂ ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ),
      Module.finrank ℂ M = k ∧ PhaseRetrievable (twirl (blockRep rho (fun _ => 2))) M} from ?_) ?_
  · refine ⟨6, ?_⟩
    intro k hk
    obtain ⟨M,hM,_⟩ := hk
    rw [← hM]
    simpa [Module.finrank_pi] using M.finrank_le
  · refine ⟨LinearMap.range encoding, ?_, encoding_phase_retrievable⟩
    simpa using LinearMap.finrank_range_of_inj encoding_injective

private def blockProj (i : Fin 3) : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin
    1) ℂ :=
  diagonal (fun a => if a.1 = i then 1 else 0)

private theorem blockProj_sum : ∑ i : Fin 3, blockProj i = 1 := by
  ext a b
  simp [blockProj, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply, eq_comm]

private theorem blockProj_idempotent (i : Fin 3) : blockProj i * blockProj i = blockProj i := by
  ext a b
  by_cases h : a=b
  · subst b; simp [blockProj, Matrix.diagonal_mul, Matrix.diagonal_apply]
  · simp [blockProj, Matrix.diagonal_mul, Matrix.diagonal_apply, h]

private theorem blockProj_star (i : Fin 3) : star (blockProj i) = blockProj i := by
  ext a b
  by_cases h : a=b
  · subst b; simp [blockProj, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_apply]
  · simp [blockProj, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_apply, h, Ne.symm h]

private theorem blockProj_fourier (i : Fin 3) :
    blockProj i = (3 : ℂ)⁻¹ • ∑ g : (Multiplicative (ZMod 3)), star ((ZMod.stdAddChar
        ((ZMod.finEquiv 3 i) * g.toAdd))) • ((blockRep rho (fun _ => 2)) g : Matrix (Σ _ : Fin 3,
        Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1) ℂ) := by
  ext a b
  simp only [pi_diagonal, blockProj, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  by_cases h : a=b
  · subst b
    simp only [if_true, mul_one]
    have he : ∑ g : (Multiplicative (ZMod 3)), star ((ZMod.stdAddChar ((ZMod.finEquiv 3 i) *
        g.toAdd))) * (ZMod.stdAddChar ((ZMod.finEquiv 3 a.1) * g.toAdd)) = if a.1=i then (3 : ℂ)
        else 0 := by
      simpa only [mul_comm] using chi_orthogonal a.1 i
    rw [he]
    split_ifs <;> norm_num
  · simp [h]

private theorem code_compressions (P : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 ×
    Fin 1) ℂ)
    (c : (Multiplicative (ZMod 3)) → (Multiplicative (ZMod 3)) → ℂ)
    (hc : ∀ g h, P * star ((blockRep rho (fun _ => 2)) g : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ
        _ : Fin 3, Fin 2 × Fin 1) ℂ) * ((blockRep rho (fun _ => 2)) h : Matrix (Σ _ : Fin 3, Fin 2
        × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1) ℂ) * P =
      c g h • P) : ∃ alpha : Fin 3 → ℂ, ∀ i,
      P * blockProj i * P = alpha i • P := by
  have hKL (g : (Multiplicative (ZMod 3))) : P * ((blockRep rho (fun _ => 2)) g : Matrix (Σ _ :
      Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1) ℂ) * P = c 1 g • P := by
    simpa using hc 1 g
  refine ⟨fun i => (3 : ℂ)⁻¹ * ∑ g : (Multiplicative (ZMod 3)), star ((ZMod.stdAddChar
      ((ZMod.finEquiv 3 i) * g.toAdd))) * c 1 g, fun i => ?_⟩
  rw [blockProj_fourier]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [hKL]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, smul_smul]

private theorem code_dim_le_two (M : Submodule ℂ ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ)) (hM : IsCode
    (blockRep rho (fun _ => 2)) M) :
    Module.finrank ℂ M ≤ 2 := by
  classical
  obtain ⟨P,hPs,hPP,hRange,c,hc⟩ := hM
  obtain ⟨alpha,ha⟩ := code_compressions P c hc
  by_cases hbot : M = ⊥
  · rw [hbot]; norm_num
  have hP : P ≠ 0 := by
    intro h
    apply hbot
    rw [← hRange,h]
    simpa only [Matrix.mulVecLin_zero] using (LinearMap.range_zero : LinearMap.range (0 : ((Σ _ :
        Fin 3, Fin 2 × Fin 1) → ℂ) →ₗ[ℂ] ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ)) = ⊥)
  have hs : ∑ i : Fin 3, P * blockProj i * P = P := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, blockProj_sum, Matrix.mul_one, hPP]
  obtain ⟨i,hi⟩ : ∃ i, alpha i ≠ 0 := by
    by_contra h
    have hzero : ∀ i, alpha i = 0 := by simpa using h
    simp_rw [ha, hzero, zero_smul] at hs
    exact hP (by simpa using hs.symm)
  have hPx (x : M) : P *ᵥ (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) = x := by
    have hx : (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) ∈ LinearMap.range P.mulVecLin := by
      rw [hRange]; exact x.property
    obtain ⟨v,hv⟩ := hx
    rw [← hv]
    change P *ᵥ (P.mulVecLin v) = P.mulVecLin v
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPP]
  let F : M →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun x a => (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) ⟨i,a,0⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hF : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hQx : blockProj i *ᵥ (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) = 0 := by
      ext ⟨j,a,b⟩; fin_cases b
      simp only [blockProj, Matrix.mulVec_diagonal]
      by_cases h : j=i
      · subst j
        have hh := congrFun hx a
        simpa [F] using hh
      · simp [h]
    have hh := congrArg (fun A : Matrix (Σ _ : Fin 3, Fin 2 × Fin 1) (Σ _ : Fin 3, Fin 2 × Fin 1)
        ℂ => A *ᵥ (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ)) (ha i)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPx, hQx, Matrix.mulVec_zero,
      Matrix.smul_mulVec, hPx] at hh
    have hz : (x : (Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) = 0 := (smul_eq_zero.mp hh.symm).resolve_left
        hi
    exact Subtype.ext hz
  have hd := LinearMap.finrank_le_finrank_of_injective hF
  simpa using hd

private theorem beta_le_two : beta (blockRep rho (fun _ => 2)) ≤ 2 := by
  apply csSup_le'
  intro k hk
  obtain ⟨M,hk,hM⟩ := hk
  rw [← hk]
  exact code_dim_le_two M hM

private def blockEncoding : (Fin 2 → ℂ) →ₗ[ℂ] ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ) :=
  LinearMap.pi (fun a => if a.1 = 0 then LinearMap.proj a.2.1 else 0)

private theorem blockEncoding_injective : Function.Injective blockEncoding := by
  intro x y h
  ext a
  have hh := congrFun h ⟨0,a,0⟩
  simpa [blockEncoding] using hh

private theorem block_range : LinearMap.range (blockProj 0).mulVecLin = LinearMap.range
    blockEncoding := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨fun a => y ⟨0,a,0⟩, ?_⟩
    ext ⟨i,a,b⟩; fin_cases b
    by_cases h : i=0
    · subst i; simp [blockEncoding, blockProj, Matrix.mulVec_diagonal]
    · simp [blockEncoding, blockProj, Matrix.mulVec_diagonal, h]
  · rintro ⟨y,rfl⟩
    refine ⟨blockEncoding y, ?_⟩
    ext a
    by_cases h : a.1=0 <;> simp [blockEncoding, blockProj, Matrix.mulVec_diagonal, h]

private theorem beta_ge_two : 2 ≤ beta (blockRep rho (fun _ => 2)) := by
  apply le_csSup (show BddAbove {k | ∃ M : Submodule ℂ ((Σ _ : Fin 3, Fin 2 × Fin 1) → ℂ),
      Module.finrank ℂ M = k ∧ IsCode (blockRep rho (fun _ => 2)) M} from ?_) ?_
  · refine ⟨2, ?_⟩
    intro k hk; obtain ⟨M,hk,hM⟩ := hk
    rw [← hk]; exact code_dim_le_two M hM
  · refine ⟨LinearMap.range blockEncoding, ?_, ?_⟩
    · simpa using LinearMap.finrank_range_of_inj blockEncoding_injective
    · refine ⟨blockProj 0, blockProj_star 0, blockProj_idempotent 0, block_range,
        fun g h => star ((ZMod.stdAddChar ((ZMod.finEquiv 3 0) * g.toAdd))) * (ZMod.stdAddChar
            ((ZMod.finEquiv 3 0) * h.toAdd)), ?_⟩
      intro g h
      ext a b
      simp only [pi_diagonal, blockProj, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply, Matrix.smul_apply, Pi.star_apply, smul_eq_mul]
      by_cases hab : a=b
      · subst b
        by_cases ha : a.1=0
        · simp [ha]
        · simp [ha]
      · simp [hab]

private theorem beta_eq_two : beta (blockRep rho (fun _ => 2)) = 2 := le_antisymm beta_le_two
    beta_ge_two

private theorem cross_zero (x y : Fin 2 → ℂ) (hx : x ≠ 0)
    (hi : (dotProduct y (star x)).im = 0)
    (hc : ∀ i j, x i * star (y j) + y i * star (x j) = 0) : y = 0 := by
  let z := dotProduct y (star x)
  have hzstar : star z = z := Complex.conj_eq_iff_im.mpr hi
  have hzsum : z + star z = 0 := by
    calc
      z + star z = (x 0 * star (y 0) + y 0 * star (x 0)) +
        (x 1 * star (y 1) + y 1 * star (x 1)) := by
          simp only [z, dotProduct, Fin.sum_univ_two, star_add, star_mul, Pi.star_apply,
            star_star]; ring
      _ = 0 := by rw [hc 0 0, hc 1 1]; ring
  have hz : z = 0 := by rw [hzstar] at hzsum; linear_combination (1/2 : ℂ) * hzsum
  have hn : dotProduct x (star x) ≠ 0 := by
    exact mt dotProduct_self_star_eq_zero.mp hx
  ext i
  apply (mul_eq_zero.mp (show y i * dotProduct x (star x) = 0 from ?_)).resolve_right hn
  calc
    y i * dotProduct x (star x) =
      (x i * star (y 0) + y i * star (x 0)) * x 0 +
      (x i * star (y 1) + y i * star (x 1)) * x 1 - x i * star z := by
        simp only [z, dotProduct, Fin.sum_univ_two, star_add, star_mul, Pi.star_apply,
          star_star]; ring
    _ = 0 := by rw [hc i 0, hc i 1, hz]; simp

private theorem equal_norm_add_sub (a b : ℂ) (h : (a * star b).re = 0) :
    ‖a + b‖ = ‖a - b‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rw [Complex.normSq_add, Complex.normSq_sub]
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im] at h ⊢
  linarith

private theorem no_three_frame (f : Fin 3 → (Fin 2 → ℂ)) : ¬ (∀ x y, (∀ j, ‖dotProduct x (star (f
    j))‖ = ‖dotProduct y (star (f j))‖) → vecMulVec x (star x) = vecMulVec y (star y)) := by
  classical
  intro hf
  have hex : ∃ x : Fin 2 → ℂ, x ≠ 0 ∧ dotProduct x (star (f 0)) = 0 := by
    by_cases h : f 0 = 0
    · refine ⟨![1,0], by simp, ?_⟩
      simp [h]
    · refine ⟨![star (f 0 1), -star (f 0 0)], ?_, ?_⟩
      · intro he
        apply h
        ext i
        fin_cases i
        · have hh := congrFun he 1; simpa using hh
        · have hh := congrFun he 0; simpa using hh
      · simp [dotProduct, Fin.sum_univ_two, mul_comm]
  obtain ⟨x,hx,hxf⟩ := hex
  let L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun y => ![(dotProduct x (star (f 1)) * star (dotProduct y (star (f 1)))).re,
        (dotProduct x (star (f 2)) * star (dotProduct y (star (f 2)))).re,
        (dotProduct y (star x)).im]
      map_add' := by
        intro y z; ext j; fin_cases j <;>
          simp [add_dotProduct, star_add, mul_add]
      map_smul' := by
        intro r y; ext j; fin_cases j <;>
          simp [smul_dotProduct, star_smul, mul_smul_comm, Complex.smul_re,
            Complex.smul_im] <;> ring }
  have hdim : Module.finrank ℝ (Fin 3 → ℝ) < Module.finrank ℝ (Fin 2 → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  have hLy : L y = 0 := hy
  have hi : (dotProduct y (star x)).im = 0 := congrFun hLy 2
  have hc (j : Fin 3) :
      (dotProduct x (star (f j)) * star (dotProduct y (star (f j)))).re = 0 := by
    fin_cases j
    · simpa [hxf]
    · exact congrFun hLy 0
    · exact congrFun hLy 1
  have he := hf (x+y) (x-y) (fun j => by
    rw [add_dotProduct, sub_dotProduct]
    exact equal_norm_add_sub _ _ (hc j))
  have hz : ∀ i j, x i * star (y j) + y i * star (x j) = 0 := by
    intro i j
    have h := congrFun (congrFun he i) j
    simp only [vecMulVec_apply, Pi.star_apply, Pi.add_apply, Pi.sub_apply,
      star_add, star_sub] at h
    linear_combination (1/2 : ℂ) * h
  exact hy0 (cross_zero x y hx hi hz)

private theorem no_short_frame {n : ℕ} (hn : n ≤ 3) (f : Fin n → (Fin 2 → ℂ)) :
    ¬ (∀ x y, (∀ j, ‖dotProduct x (star (f j))‖ = ‖dotProduct y (star (f j))‖) → vecMulVec x (star
        x) = vecMulVec y (star y)) := by
  classical
  intro hf
  let F : Fin 3 → (Fin 2 → ℂ) := fun j => if h : j.val < n then f ⟨j.val,h⟩ else 0
  apply no_three_frame F
  intro x y hxy
  apply hf x y
  intro j
  have h := hxy (Fin.castLE hn j)
  simpa [F, j.isLt] using h

private theorem four_frame : ∃ f : Fin 4 → (Fin 2 → ℂ), (∀ x y, (∀ j, ‖dotProduct x (star (f j))‖
    = ‖dotProduct y (star (f j))‖) → vecMulVec x (star x) = vecMulVec y (star y)) := by
  refine ⟨![![1,0], ![0,1], ![1,1], ![1,Complex.I]], ?_⟩
  intro x y h
  have hsq (j : Fin 4) := congrArg (fun r : ℝ => r^2) (h j)
  have h0 := hsq 0; have h1 := hsq 1; have h2 := hsq 2; have h3 := hsq 3
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, star_zero,
    star_one, Complex.star_def, Complex.conj_I, mul_one, mul_zero, zero_add,
    add_zero, ← Complex.normSq_eq_norm_sq] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  have hc : x 0 * star (x 1) = y 0 * star (y 1) := by
    apply Complex.ext <;>
      simp only [Complex.star_def] at * <;>
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im] at * <;> nlinarith
  ext i j; fin_cases i <;> fin_cases j
  · simpa [vecMulVec, Complex.star_def, Complex.mul_conj] using congrArg Complex.ofReal h0
  · exact hc
  · have hh := congrArg star hc; simpa [vecMulVec, mul_comm] using hh
  · simpa [vecMulVec, Complex.star_def, Complex.mul_conj] using congrArg Complex.ofReal h1

private theorem frame_two_gt_three : 3 < frameLength 2 := by
  have hmem : frameLength 2 ∈ {n | ∃ f : Fin n → (Fin 2 → ℂ), (∀ x y, (∀ j, ‖dotProduct x (star (f
      j))‖ = ‖dotProduct y (star (f j))‖) → vecMulVec x (star x) = vecMulVec y (star y))} :=
    csInf_mem ⟨4, four_frame⟩
  by_contra h
  obtain ⟨f,hf⟩ := hmem
  exact no_short_frame (Nat.le_of_not_gt h) f hf

private theorem frame_one_le_three : frameLength 1 ≤ 3 := by
  apply le_trans (csInf_le' (show (1 : ℕ) ∈ {n | ∃ f : Fin n → (Fin 1 → ℂ), (∀ x y, (∀ j,
      ‖dotProduct x (star (f j))‖ = ‖dotProduct y (star (f j))‖) → vecMulVec x (star x) =
      vecMulVec y (star y))} from ?_))
    (by norm_num)
  refine ⟨fun _ _ => 1, ?_⟩
  intro x y h
  have hh := congrArg (fun r : ℝ => r^2) (h 0)
  simp [dotProduct, Fin.sum_univ_one, ← Complex.normSq_eq_norm_sq] at hh
  ext i j; fin_cases i; fin_cases j
  simpa [vecMulVec, Complex.star_def, Complex.mul_conj] using congrArg Complex.ofReal hh


theorem result : ¬ claim := by
  intro h
  have he := h (Multiplicative (ZMod 3)) 3 (fun _ => 1) (fun _ => 2) rho
    rho_irreducible rho_inequivalent (fun _ => by norm_num) 1
    frame_one_le_three frame_two_gt_three
  change pr (twirl (blockRep rho (fun _ => 2))) = max (beta (blockRep rho (fun _ => 2))) 1 at he
  rw [beta_eq_two] at he
  have hp := pr_ge_three
  norm_num at he
  omega

end D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample
