/- GID: D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Diagonal phase gates have equal multipartite entangling and disentangling powers. -/

/-
proof_shape: result: bind-only; consumer: settlement of claim.
escape_witness: none
admission_basis: open-problem-resolution (#19700; Proved)
Direct frozen dependencies: none (all declarations).
Source definitions (no proof claim): IsFullySeparable, IsBiseparable, G, E, D, claim.
  isFullySeparable_star: proof_shape: bind-only; escape_witness: none; consumer: E_diag_eq.
  isBiseparable_star: proof_shape: bind-only; escape_witness: none; consumer: G_star.
  G_star: proof_shape: bind-only; escape_witness: none; consumer: E_diag_eq.
  diagonal_intertwining: proof_shape: bind-only; escape_witness: none; consumer: E_diag_eq.
  E_diag_eq: proof_shape: bind-only; escape_witness: none; consumer: result.
Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/19821.
The normalization condition is inlined rather than duplicating
MultiEntropyPositivityRefutation.IsUnitState. The overlap uses dotProduct;
conjugation and its subtype equivalences use star and Equiv.Perm.star.subtypeEquiv.
The preregistered amplitude expressions are unchanged after expanding these owners.
The utility record is none: no finite computation, enumeration or certified instance
occurs in the proof; all suprema are reindexed by conjugation.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The generalized geometric measure and the two powers are those of
Samanta, Mondal and Sen (De), arXiv:2505.18539v1, Eqs. (1)–(2) and Appendix A.1.
Their maxima are represented by suprema. Conjugation identifies the value families,
so the equality does not require an attainment hypothesis. -/

namespace D5.S3.Quantum.Entanglement.DiagonalUnitary.SamantaMondalSenDiagonalPowers

open Complex

/-- `S_N`: normalized fully separable states `⊗_{i=1}^{N} |ψ_i⟩`. -/
def IsFullySeparable {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) : Prop :=
  (∑ x, Complex.normSq (ψ x) = 1) ∧ ∃ p : Fin N → Fin 2 → ℂ, ∀ x, ψ x = ∏ i, p i (x i)

/-- Normalized states that factor across a bipartition `A | Aᶜ` with both parts nonempty. -/
def IsBiseparable {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) : Prop :=
  (∑ x, Complex.normSq (ψ x) = 1) ∧ ∃ A : Finset (Fin N), A.Nonempty ∧ Aᶜ.Nonempty ∧
    ∃ a : (A → Fin 2) → ℂ, ∃ b : ((Aᶜ : Finset (Fin N)) → Fin 2) → ℂ,
      ∀ x, ψ x = a (fun i => x i) * b (fun i => x i)

/-- The generalized geometric measure `G(|ψ⟩) = 1 − max_{|φ⟩ ∈ S_nG} |⟨φ|ψ⟩|²`. -/
noncomputable def G {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) : ℝ :=
  1 - ⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ}, Complex.normSq (star φ.1 ⬝ᵥ ψ)

/-- Eq. (1): `E_N(U) = max_{|ψ⟩ ∈ S_N} G(U|ψ⟩)`. -/
noncomputable def E {N : ℕ} (U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) : ℝ :=
  ⨆ ψ : {ψ : (Fin N → Fin 2) → ℂ // IsFullySeparable ψ}, G (U.mulVec ψ.1)

/-- Eq. (2): `D_N(U) = E_N(U†)`. -/
noncomputable def D {N : ℕ} (U : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) : ℝ :=
  E U.conjTranspose

/-- The closing statement of Appendix B.3: for every number `N` of qubits and every diagonal unitary
`U = diag(e^{iθ_x})`, `E_N(U) = D_N(U)`. -/
def claim : Prop :=
  ∀ (N : ℕ) (θ : (Fin N → Fin 2) → ℝ),
    E (Matrix.diagonal fun x => Complex.exp (θ x * Complex.I)) =
      D (Matrix.diagonal fun x => Complex.exp (θ x * Complex.I))

private theorem isFullySeparable_star {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) :
    IsFullySeparable (star ψ) ↔ IsFullySeparable ψ := by
  constructor
  · rintro ⟨hψ, p, hp⟩
    refine ⟨(by simpa using hψ), fun i b => star (p i b), ?_⟩
    intro x
    simpa using congrArg star (hp x)
  · rintro ⟨hψ, p, hp⟩
    refine ⟨(by simpa using hψ), fun i b => star (p i b), ?_⟩
    intro x
    simpa using congrArg star (hp x)

private theorem isBiseparable_star {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) :
    IsBiseparable (star ψ) ↔ IsBiseparable ψ := by
  constructor
  · rintro ⟨hψ, A, hA, hAc, a, b, hp⟩
    refine ⟨(by simpa using hψ), A, hA, hAc, fun y => star (a y),
      fun z => star (b z), ?_⟩
    intro x
    simpa using congrArg star (hp x)
  · rintro ⟨hψ, A, hA, hAc, a, b, hp⟩
    refine ⟨(by simpa using hψ), A, hA, hAc, fun y => star (a y),
      fun z => star (b z), ?_⟩
    intro x
    simpa using congrArg star (hp x)

private theorem G_star {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ) : G (star ψ) = G ψ := by
  let e := (Equiv.Perm.star : Equiv.Perm ((Fin N → Fin 2) → ℂ)).subtypeEquiv
    (fun ψ => (isBiseparable_star ψ).symm)
  have hsup :
      (⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ}, Complex.normSq (star φ.1 ⬝ᵥ star ψ)) =
        ⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ}, Complex.normSq (star φ.1 ⬝ᵥ ψ) := by
    calc
      (⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ}, Complex.normSq (star φ.1 ⬝ᵥ star ψ)) =
          ⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ},
            Complex.normSq (star (star φ.1) ⬝ᵥ star ψ) := by
              symm
              exact e.iSup_congr (fun φ => rfl)
      _ = ⨆ φ : {φ : (Fin N → Fin 2) → ℂ // IsBiseparable φ}, Complex.normSq (star φ.1 ⬝ᵥ ψ) := by
        apply iSup_congr
        intro φ
        rw [star_star, Matrix.dotProduct_star, Complex.star_def, Complex.normSq_conj,
          dotProduct_comm]
  simp only [G]
  rw [hsup]

private theorem diagonal_intertwining {N : ℕ} (θ : (Fin N → Fin 2) → ℝ) (p : (Fin N → Fin 2) → ℂ) :
    (Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).conjTranspose.mulVec
        (star p) =
      star ((Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).mulVec p) := by
  funext x
  simpa [Matrix.diagonal_conjTranspose, Matrix.mulVec_diagonal, Matrix.vecMul_diagonal,
    mul_comm] using congrFun
    (Matrix.star_mulVec (Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))) p).symm x

private theorem E_diag_eq {N : ℕ} (θ : (Fin N → Fin 2) → ℝ) :
    E (Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))) =
      E (Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).conjTranspose := by
  let e := (Equiv.Perm.star : Equiv.Perm ((Fin N → Fin 2) → ℂ)).subtypeEquiv
    (fun ψ => (isFullySeparable_star ψ).symm)
  change
    (⨆ ψ : {ψ : (Fin N → Fin 2) → ℂ // IsFullySeparable ψ},
      G ((Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).mulVec ψ.1)) =
      ⨆ ψ : {ψ : (Fin N → Fin 2) → ℂ // IsFullySeparable ψ},
        G ((Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).conjTranspose.mulVec ψ.1)
  exact e.iSup_congr (fun ψ => by
    change G ((Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).conjTranspose.mulVec
        (star ψ.1)) =
      G ((Matrix.diagonal (fun x => Complex.exp (θ x * Complex.I))).mulVec ψ.1)
    rw [diagonal_intertwining]
    exact G_star _)

theorem result : claim := by
  intro N θ
  exact E_diag_eq θ

end D5.S3.Quantum.Entanglement.DiagonalUnitary.SamantaMondalSenDiagonalPowers
