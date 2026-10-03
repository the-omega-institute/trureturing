/- GID: D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/BinaryStabilizerLocalInequivalence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.claim; result=D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.result; claim=D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.claim
   digest: A binary-stabilized 6-qubit state is not LU-equivalent to a Pauli stabilizer state. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: inside its proof, the local
  facts `expectation_trichotomy` (a Pauli word either has expectation `0` or maps a state
  stabilized by phased Pauli words to `±` itself) and `pairPurity_local` (the two-qubit pair
  purity `Σ |⟨φ, (g ⊗ h ⊗ 𝟙^{⊗4}) φ⟩|²` is invariant under local unitaries), and the
  kernel-checked stabilization and purity computations for the witness
admission_basis: open-problem-resolution (issue #11565; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
  (`Pauli`, `pauliMatrix`, `tensorOp`, `wordOp`, `sgn`, `anticomm`); `qubitX`, `qubitZ` of
  D5/S3/Quantum/FiniteDimensional through that import
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

open Complex Matrix D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open scoped Kronecker

/-!
É. Descamps, B. Dakić, *On the stabilizer formalism and its generalization*, arXiv:2309.09815
(J. Phys. A 57, 455301 (2024)). A state of `N` qubits is stabilized by a stabilizing set `𝒜` of
single-qubit unitaries when it is, up to a factor, the unique common `+1` eigenvector of finitely
many tensor products of elements of `𝒜`. The paper conjectures that every state stabilized by the
binary operators `A_{θ,φ} = cos θ Z + sin θ (cos φ X + sin φ Y)` and the identity is locally
equivalent to a standard stabilizer state, one stabilized by `𝒫 = {±1, ±i}·{𝟙, X, Y, Z}`.
The six-qubit state `v = Σ_j (|e_j⟩ - |ē_j⟩)` is the unique common `+1` eigenvector of
`(-X) ⊗ X^{⊗5}`, `(-Z) ⊗ Z^{⊗5}`, `H^{⊗6}` and `K^{⊗6}` (`H = (X+Z)/√2`, `K = (X+Y)/√2`). For a
standard stabilizer state every Pauli word has expectation `0` or `±‖φ‖²`, so
`Σ_{g,h} |⟨φ, (g ⊗ h ⊗ 𝟙^{⊗4}) φ⟩|²` is an integer multiple of `‖φ‖⁴`; this sum is invariant
under local unitaries, and for `v` it is `192 = (4/3)·12²`.
-/

/-! ## The statement -/

/-- The binary operator `A_{θ,φ} = cos θ Z + sin θ (cos φ X + sin φ Y)`. -/
def binaryOp (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos θ : ℂ) • pauliMatrix .Z +
    (Real.sin θ : ℂ) • ((Real.cos φ : ℂ) • pauliMatrix .X + (Real.sin φ : ℂ) • pauliMatrix .Y)

/-- The stabilizing set `{A_{θ,φ}, 𝟙₂}`. -/
def binarySet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | (∃ θ φ, A = binaryOp θ φ) ∨ A = 1}

/-- The Pauli matrices with a phase in `{±1, ±i}`: the set `𝒫` of the paper. -/
def pauliSet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | ∃ c ∈ ({1, -1, I, -I} : Set ℂ), ∃ p, A = c • pauliMatrix p}

/-- `ψ` is stabilized by the stabilizing set `S`: it is nonzero and, up to a complex factor, the
unique common `+1` eigenvector of finitely many tensor products of elements of `S`. -/
def StabilizedBy {N : ℕ} (S : Set (Matrix (Fin 2) (Fin 2) ℂ)) (ψ : (Fin N → Fin 2) → ℂ) :
    Prop :=
  ψ ≠ 0 ∧ ∃ (k : ℕ) (O : Fin k → Fin N → Matrix (Fin 2) (Fin 2) ℂ), (∀ a i, O a i ∈ S) ∧
    ∀ w, (∀ a, tensorOp (O a) *ᵥ w = w) ↔ ∃ c : ℂ, w = c • ψ

/-- Local equivalence: `ψ = (U₁ ⊗ ⋯ ⊗ U_N) φ` with every `U_i ∈ U(2)`. -/
def LocallyEquivalent {N : ℕ} (ψ φ : (Fin N → Fin 2) → ℂ) : Prop :=
  ∃ U : Fin N → Matrix (Fin 2) (Fin 2) ℂ, (∀ i, U i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
    ψ = tensorOp U *ᵥ φ

/-- The conjecture of arXiv:2309.09815: every state stabilized by binary operators and the
identity is locally equivalent to a standard (Pauli) stabilizer state. -/
def claim : Prop :=
  ∀ (N : ℕ) (ψ : (Fin N → Fin 2) → ℂ), StabilizedBy binarySet ψ →
    ∃ φ, StabilizedBy pauliSet φ ∧ LocallyEquivalent ψ φ

/-! Pauli words commute or anticommute. -/

/-! ## The two-qubit marginal -/

/-- The basis label whose first two qubits are `p` and whose last four are `r`. -/
private def glue (p : Fin 2 × Fin 2) (r : Fin 4 → Fin 2) : Fin 6 → Fin 2 :=
  Fin.cons p.1 (Fin.cons p.2 r)

/-- The unnormalized reduced state of qubits `1, 2`. -/
private def marginal (φ : (Fin 6 → Fin 2) → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => ∑ r, φ (glue p r) * star (φ (glue q r))

/-- `A ⊗ B ⊗ 𝟙^{⊗4}`. -/
private def pairOp (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 6 → Fin 2) (Fin 6 → Fin 2) ℂ :=
  tensorOp ![A, B, 1, 1, 1, 1]

/-! ## Pauli completeness on two qubits -/

/-- The real Pauli-type basis `𝟙, X, XZ, Z`; `Y = i · XZ`. -/
private def tau : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, qubitX, qubitX * qubitZ, qubitZ]

/-- The Pauli labels in the order `𝟙, X, Y, Z`. -/
private def plab : Fin 4 → Pauli := ![.I, .X, .Y, .Z]

/-- The phase with `pauliMatrix (plab a) = ph a • tau a`. -/
private def ph : Fin 4 → ℂ := ![1, 1, I, 1]

/-! ## Local-unitary invariance of the pair purity -/

/-- `Σ_{g,h} |⟨φ, (g ⊗ h ⊗ 𝟙^{⊗4}) φ⟩|²` over the sixteen two-qubit Pauli words. -/
private def pairPurity (φ : (Fin 6 → Fin 2) → ℂ) : ℝ :=
  ∑ a, ∑ b, ‖star φ ⬝ᵥ (pairOp (pauliMatrix (plab a)) (pauliMatrix (plab b)) *ᵥ φ)‖ ^ 2

/-- The coefficient matrix `Φ p r = φ (p, r)`, with `marginal φ = Φ Φᴴ`. -/
private def coeffs (φ : (Fin 6 → Fin 2) → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 4 → Fin 2) ℂ :=
  Matrix.of fun p r => φ (glue p r)

/-! ## Diagonal and antidiagonal tensor products -/

/-- The complementary basis label. -/
private def flip {n : ℕ} (x : Fin n → Fin 2) : Fin n → Fin 2 := fun i => x i + 1

/-! ## The six binary operators of the witness -/

/-- `√2 / 2`. -/
private def s2 : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- `H = (X + Z)/√2`. -/
private def hadamard : Matrix (Fin 2) (Fin 2) ℂ := s2 • (pauliMatrix .X + pauliMatrix .Z)

/-- `K = (X + Y)/√2`. -/
private def kmat : Matrix (Fin 2) (Fin 2) ℂ := s2 • (pauliMatrix .X + pauliMatrix .Y)

/-- The four stabilizing operators `(-X) ⊗ X^{⊗5}`, `(-Z) ⊗ Z^{⊗5}`, `H^{⊗6}`, `K^{⊗6}`. -/
private def ops : Fin 4 → Fin 6 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![fun i => if i = 0 then -pauliMatrix .X else pauliMatrix .X,
    fun i => if i = 0 then -pauliMatrix .Z else pauliMatrix .Z,
    fun _ => hadamard,
    fun _ => kmat]

/-! ## The witness and its integer model -/

/-- Integer coefficients: `1` on weight-one labels, `-1` on weight-five labels. -/
private def vZ (x : Fin 6 → Fin 2) : ℤ :=
  if ∑ i, (x i : ℕ) = 1 then 1 else if ∑ i, (x i : ℕ) = 5 then -1 else 0

/-- `v = Σ_j (|e_j⟩ - |ē_j⟩)`. -/
private def witness (x : Fin 6 → Fin 2) : ℂ := (vZ x : ℂ)

/-- The weight-one label `e_j`. -/
private def ebasis (j : Fin 6) : Fin 6 → Fin 2 := fun i => if i = j then 1 else 0

private def zZ (a : Fin 2) : ℤ := if a = 0 then 1 else -1
private def kG (a : Fin 2) : GaussianInt := if a = 0 then ⟨1, -1⟩ else ⟨1, 1⟩
private def hZ (a b : Fin 2) : ℤ := if a = 1 ∧ b = 1 then -1 else 1

/-! ## The witness is stabilized by the four operators -/

private def hp (y x : Fin 6 → Fin 2) : ℤ := ∏ i, hZ (y i) (x i)

set_option maxHeartbeats 4000000 in
-- `result` is one declaration that contains every lemma of the proof as a local `have`.
/-- The conjecture fails: `v = Σ_j (|e_j⟩ - |ē_j⟩)` is stabilized by the binary operators
`(-X) ⊗ X^{⊗5}`, `(-Z) ⊗ Z^{⊗5}`, `H^{⊗6}`, `K^{⊗6}`, but no standard stabilizer state is locally
equivalent to it: its pair purity `192` is not an integer multiple of `‖v‖⁴ = 144`. -/
theorem result : ¬ claim := by
  have tensorOp_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      tensorOp M * tensorOp N = tensorOp fun i => M i * N i := by
    ext x z
    simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.prod_mul_distrib]
  have tensorOp_one {n : ℕ} :
      tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    ext x y
    simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have tensorOp_conjTranspose {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      (tensorOp M)ᴴ = tensorOp fun i => (M i)ᴴ := by
    ext x y
    simp [tensorOp, Matrix.conjTranspose_apply]
  have tensorOp_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := by
    ext x y
    simp [tensorOp, Finset.prod_mul_distrib]
  have pauliMatrix_comm (p q : Pauli) :
      pauliMatrix p * pauliMatrix q = (sgn p q : ℂ) • (pauliMatrix q * pauliMatrix p) := by
    cases p <;> cases q <;>
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliMatrix, sgn, anticomm, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  have sgn_sq (p q : Pauli) : (sgn p q : ℂ) * (sgn p q : ℂ) = 1 := by
    have h : sgn p q * sgn p q = 1 := by cases p <;> cases q <;> decide
    exact_mod_cast h
  have pauliMatrix_mul_self (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
    cases p <;>
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliMatrix, qubitX, qubitZ]
  have pauliMatrix_conjTranspose (p : Pauli) : (pauliMatrix p)ᴴ = pauliMatrix p := by
    cases p <;>
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [pauliMatrix, qubitX, qubitZ,
            Matrix.conjTranspose_apply]
  have wordOp_comm {n : ℕ} (g h : Fin n → Pauli) :
      wordOp g * wordOp h = (∏ i, (sgn (g i) (h i) : ℂ)) • (wordOp h * wordOp g) := by
    simp only [wordOp, tensorOp_mul]
    rw [← tensorOp_smul]
    congr 1
    funext i
    exact pauliMatrix_comm _ _
  have wordOp_mul_self {n : ℕ} (g : Fin n → Pauli) : wordOp g * wordOp g = 1 := by
    simp only [wordOp, tensorOp_mul, pauliMatrix_mul_self, tensorOp_one]
  have wordOp_conjTranspose {n : ℕ} (g : Fin n → Pauli) : (wordOp g)ᴴ = wordOp g := by
    simp only [wordOp, tensorOp_conjTranspose, pauliMatrix_conjTranspose]
  have sign_prod_sq {n : ℕ} (g h : Fin n → Pauli) :
      (∏ i, (sgn (g i) (h i) : ℂ)) * (∏ i, (sgn (g i) (h i) : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => sgn_sq _ _
  have phase_unit {c : ℂ} (hc : c ∈ ({1, -1, I, -I} : Set ℂ)) : star c * c = 1 := by
    rcases hc with rfl | rfl | rfl | rfl <;> simp
  have sq_eq_one_cases {s : ℂ} (hs : s * s = 1) : s = 1 ∨ s = -1 := by
    have h : (s - 1) * (s + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp h with h | h
    · left; linear_combination h
    · right; linear_combination h
  have expectation_trichotomy {N : ℕ} {φ : (Fin N → Fin 2) → ℂ}
      (hφ : StabilizedBy pauliSet φ) (g : Fin N → Pauli) :
      star φ ⬝ᵥ (wordOp g *ᵥ φ) = 0 ∨ wordOp g *ᵥ φ = φ ∨ wordOp g *ᵥ φ = -φ := by
    obtain ⟨hne, k, O, hO, hstab⟩ := hφ
    choose c hc p hp using hO
    have hT : ∀ a, tensorOp (O a) = (∏ i, c a i) • wordOp (p a) := by
      intro a
      rw [show O a = fun i => c a i • pauliMatrix (p a i) from funext (hp a), tensorOp_smul]
      rfl
    have hfix : ∀ a, tensorOp (O a) *ᵥ φ = φ := (hstab φ).2 ⟨1, (one_smul ℂ φ).symm⟩
    by_cases hcomm : ∀ a, ∏ i, (sgn (g i) (p a i) : ℂ) = 1
    · have hPT : ∀ a, wordOp g * tensorOp (O a) = tensorOp (O a) * wordOp g := by
        intro a
        rw [hT, Matrix.mul_smul, Matrix.smul_mul, wordOp_comm, hcomm a, one_smul]
      have hPφ : ∀ a, tensorOp (O a) *ᵥ (wordOp g *ᵥ φ) = wordOp g *ᵥ φ := by
        intro a
        rw [Matrix.mulVec_mulVec, ← hPT, ← Matrix.mulVec_mulVec, hfix]
      obtain ⟨d, hd⟩ := (hstab _).1 hPφ
      have h1 : wordOp g *ᵥ (wordOp g *ᵥ φ) = φ := by
        rw [Matrix.mulVec_mulVec, wordOp_mul_self, Matrix.one_mulVec]
      rw [hd, Matrix.mulVec_smul, hd, smul_smul] at h1
      have hd2 : d * d = 1 := by
        by_contra hne'
        have h0 : (d * d - 1) • φ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        exact hne ((smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne'))
      rcases sq_eq_one_cases hd2 with rfl | rfl
      · exact Or.inr (Or.inl (by rw [hd, one_smul]))
      · exact Or.inr (Or.inr (by rw [hd, neg_one_smul]))
    · obtain ⟨a, ha⟩ := not_forall.mp hcomm
      have hsign : ∏ i, (sgn (g i) (p a i) : ℂ) = -1 :=
        (sq_eq_one_cases (sign_prod_sq g (p a))).resolve_left ha
      have hPT : wordOp g * tensorOp (O a) = -(tensorOp (O a) * wordOp g) := by
        rw [hT, Matrix.mul_smul, Matrix.smul_mul, wordOp_comm, hsign, neg_one_smul, smul_neg]
      have hc1 : star (∏ i, c a i) * ∏ i, c a i = 1 := by
        rw [star_prod, ← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => phase_unit (hc a i)
      have hTT : (tensorOp (O a))ᴴ * tensorOp (O a) = 1 := by
        rw [hT, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          wordOp_conjTranspose, wordOp_mul_self, hc1, one_smul]
      left
      have e1 : star φ ⬝ᵥ (wordOp g *ᵥ φ) =
          star (tensorOp (O a) *ᵥ φ) ⬝ᵥ (wordOp g *ᵥ (tensorOp (O a) *ᵥ φ)) := by
        rw [hfix a]
      have key : star φ ⬝ᵥ (wordOp g *ᵥ φ) = -(star φ ⬝ᵥ (wordOp g *ᵥ φ)) := by
        conv_lhs => rw [e1]
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Matrix.mul_assoc, hPT, Matrix.mul_neg, ← Matrix.mul_assoc, hTT,
          Matrix.one_mul,
          Matrix.neg_mulVec, dotProduct_neg]
      have h2 : (2 : ℂ) * (star φ ⬝ᵥ (wordOp g *ᵥ φ)) = 0 := by linear_combination key
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have sum_glue (f : (Fin 6 → Fin 2) → ℂ) : ∑ x, f x = ∑ p, ∑ r, f (glue p r) := by
    rw [← (Fin.consEquiv fun _ : Fin 6 => Fin 2).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (Fin.consEquiv fun _ : Fin 5 => Fin 2).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl
  have tensorOp_glue (M : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ) (p q : Fin 2 × Fin 2)
      (r s : Fin 4 → Fin 2) :
      tensorOp M (glue p r) (glue q s) =
        (M 0 ⊗ₖ M 1) p q * tensorOp (fun t : Fin 4 => M t.succ.succ) r s := by
    simp [tensorOp, glue, Fin.prod_univ_succ]
    simp only [mul_assoc]
    rfl
  have expectation_pairOp (φ : (Fin 6 → Fin 2) → ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
      star φ ⬝ᵥ (pairOp A B *ᵥ φ) = trace ((A ⊗ₖ B) * marginal φ) := by
    have hrest : tensorOp (fun t : Fin 4 => (![A, B, 1, 1, 1, 1] : Fin 6 → _) t.succ.succ) =
        (1 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ) := by
      rw [← tensorOp_one]
      congr 1
      funext t
      fin_cases t <;> rfl
    have hent : ∀ p q r s, pairOp A B (glue p r) (glue q s) =
        (A ⊗ₖ B) p q * (if r = s then 1 else 0) := by
      intro p q r s
      rw [pairOp, tensorOp_glue, hrest, Matrix.one_apply]
      rfl
    have hmv : ∀ x, (pairOp A B *ᵥ φ) x =
        ∑ q, ∑ s, pairOp A B x (glue q s) * φ (glue q s) := fun x =>
      sum_glue (fun y => pairOp A B x y * φ y)
    calc star φ ⬝ᵥ (pairOp A B *ᵥ φ)
        = ∑ p, ∑ r, star (φ (glue p r)) * (pairOp A B *ᵥ φ) (glue p r) := by
          rw [dotProduct, sum_glue]
          rfl
      _ = ∑ p, ∑ r, ∑ q, star (φ (glue p r)) * ((A ⊗ₖ B) p q * φ (glue q r)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
          rw [hmv, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [hent, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
            Finset.mem_univ, if_true]
      _ = ∑ p, ∑ q, (A ⊗ₖ B) p q * ∑ r, φ (glue q r) * star (φ (glue p r)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ = trace ((A ⊗ₖ B) * marginal φ) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, marginal, Matrix.of_apply]
  have pauliMatrix_plab (a : Fin 4) : pauliMatrix (plab a) = ph a • tau a := by
    fin_cases a <;> simp [plab, ph, tau, pauliMatrix]
  have norm_ph (a : Fin 4) : ‖ph a‖ = 1 := by fin_cases a <;> simp [ph]
  have tau_completeness (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      ∑ a, ∑ b, ‖trace ((tau a ⊗ₖ tau b) * M)‖ ^ 2 = 4 * ∑ p, ∑ q, ‖M p q‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp [Fin.sum_univ_four, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace,
      Matrix.mul_apply, tau, qubitX, qubitZ]
    ring
  have pauli_completeness (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      ∑ a, ∑ b, ‖trace ((pauliMatrix (plab a) ⊗ₖ pauliMatrix (plab b)) * M)‖ ^ 2 =
        4 * ∑ p, ∑ q, ‖M p q‖ ^ 2 := by
    rw [← tau_completeness]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pauliMatrix_plab, pauliMatrix_plab, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_mul, norm_ph,
      norm_ph, one_mul, one_mul]
  have pairPurity_eq (φ : (Fin 6 → Fin 2) → ℂ) :
      pairPurity φ = 4 * ∑ p, ∑ q, ‖marginal φ p q‖ ^ 2 := by
    simp only [pairPurity, expectation_pairOp]
    exact pauli_completeness _
  have frobenius_eq_trace (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      ((∑ p, ∑ q, ‖M p q‖ ^ 2 : ℝ) : ℂ) = trace (M * Mᴴ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj]
    rfl
  have frobenius_unitary (V M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (hV : Vᴴ * V = 1) :
      ∑ p, ∑ q, ‖(V * M * Vᴴ) p q‖ ^ 2 = ∑ p, ∑ q, ‖M p q‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [frobenius_eq_trace, frobenius_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    have h : V * M * Vᴴ * (V * (Mᴴ * Vᴴ)) = V * (M * Mᴴ) * Vᴴ := by
      calc V * M * Vᴴ * (V * (Mᴴ * Vᴴ)) = V * M * (Vᴴ * V) * Mᴴ * Vᴴ := by
            simp only [Matrix.mul_assoc]
        _ = V * (M * Mᴴ) * Vᴴ := by
            rw [hV, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have unitary_ctm {U : Matrix (Fin 2) (Fin 2) ℂ}
      (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
      Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have tensorOp_unitary {n : ℕ} (u : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin 2) ℂ) : (tensorOp u)ᴴ * tensorOp u = 1 := by
    rw [tensorOp_conjTranspose, tensorOp_mul]
    simp_rw [unitary_ctm (hu _)]
    exact tensorOp_one
  have marginal_eq (φ : (Fin 6 → Fin 2) → ℂ) : marginal φ = coeffs φ * (coeffs φ)ᴴ := by
    ext p q
    simp [marginal, coeffs, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have coeffs_local (u : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ) (φ : (Fin 6 → Fin 2) → ℂ) :
      coeffs (tensorOp u *ᵥ φ) =
        (u 0 ⊗ₖ u 1) * coeffs φ * (tensorOp fun t : Fin 4 => u t.succ.succ)ᵀ := by
    ext p r
    have h1 : coeffs (tensorOp u *ᵥ φ) p r = ∑ q, ∑ s, (u 0 ⊗ₖ u 1) p q *
        ((tensorOp fun t : Fin 4 => u t.succ.succ) r s * φ (glue q s)) := by
      change (tensorOp u *ᵥ φ) (glue p r) = _
      rw [Matrix.mulVec, dotProduct, sum_glue]
      simp only [tensorOp_glue, mul_assoc]
    rw [h1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, coeffs, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have marginal_local (u : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ)
      (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin 2) ℂ) (φ : (Fin 6 → Fin 2) → ℂ) :
      marginal (tensorOp u *ᵥ φ) = (u 0 ⊗ₖ u 1) * marginal φ * (u 0 ⊗ₖ u 1)ᴴ := by
    set R := tensorOp fun t : Fin 4 => u t.succ.succ
    have hR : Rᵀ * (Rᵀ)ᴴ = 1 := by
      have h := tensorOp_unitary (fun t : Fin 4 => u t.succ.succ) fun t => hu _
      have hT : (Rᵀ)ᴴ = (Rᴴ)ᵀ := by
        ext i j
        simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
      rw [hT, ← Matrix.transpose_mul, h, Matrix.transpose_one]
    rw [marginal_eq, marginal_eq, coeffs_local, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (u 0 ⊗ₖ u 1) * coeffs φ * Rᵀ * ((Rᵀ)ᴴ * ((coeffs φ)ᴴ * (u 0 ⊗ₖ u 1)ᴴ))
        = (u 0 ⊗ₖ u 1) * coeffs φ * (Rᵀ * (Rᵀ)ᴴ) * (coeffs φ)ᴴ * (u 0 ⊗ₖ u 1)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = (u 0 ⊗ₖ u 1) * (coeffs φ * (coeffs φ)ᴴ) * (u 0 ⊗ₖ u 1)ᴴ := by
          rw [hR, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have pairPurity_local (u : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ)
      (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin 2) ℂ) (φ : (Fin 6 → Fin 2) → ℂ) :
      pairPurity (tensorOp u *ᵥ φ) = pairPurity φ := by
    have hV : (u 0 ⊗ₖ u 1)ᴴ * (u 0 ⊗ₖ u 1) = 1 := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, unitary_ctm (hu 0),
        unitary_ctm (hu 1), Matrix.one_kronecker_one]
    rw [pairPurity_eq, pairPurity_eq, marginal_local u hu, frobenius_unitary _ _ hV]
  have norm_local {n : ℕ} (u : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (hu : ∀ i, u i ∈ Matrix.unitaryGroup (Fin 2) ℂ) (φ : (Fin n → Fin 2) → ℂ) :
      star (tensorOp u *ᵥ φ) ⬝ᵥ (tensorOp u *ᵥ φ) = star φ ⬝ᵥ φ := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      tensorOp_unitary u hu, Matrix.one_mulVec]
  have pairOp_word (a b : Fin 4) : pairOp (pauliMatrix (plab a)) (pauliMatrix (plab b)) =
        wordOp ![plab a, plab b, .I, .I, .I, .I] := by
    simp only [pairOp, wordOp]
    congr 1
    funext i
    fin_cases i <;> rfl
  have sum_dichotomy (f : Fin 4 → Fin 4 → ℝ) (c : ℝ) (hf : ∀ a b, f a b = 0 ∨ f a b = c) :
      ∃ m : ℕ, ∑ a, ∑ b, f a b = m * c := by
    refine ⟨∑ a, ∑ b, if f a b = c then 1 else 0, ?_⟩
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases hf a b with h | h
    · by_cases hc : f a b = c
      · simp [hc]
      · simp [h]
    · simp [h]
  have pairPurity_stabilizer {φ : (Fin 6 → Fin 2) → ℂ} (hφ : StabilizedBy pauliSet φ) :
      ∃ m : ℕ, pairPurity φ = m * ‖star φ ⬝ᵥ φ‖ ^ 2 := by
    apply sum_dichotomy
    intro a b
    rw [pairOp_word]
    rcases expectation_trichotomy hφ ![plab a, plab b, .I, .I, .I, .I] with h | h | h
    · left; rw [h, norm_zero]; ring
    · right; rw [h]
    · right; rw [h, dotProduct_neg, norm_neg]
  have mulVec_tensorOp_diag {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (hM : ∀ i a b, a ≠ b → M i a b = 0) (w : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) :
      (tensorOp M *ᵥ w) x = (∏ i, M i (x i) (x i)) * w x := by
    simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply]
    rw [Finset.sum_eq_single x]
    · intro y _ hy
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hM i _ _ (Ne.symm hi)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have fin2_eq_or (a b : Fin 2) : b = a ∨ b = a + 1 := by
    fin_cases a <;> fin_cases b <;> decide
  have mulVec_tensorOp_anti {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (hM : ∀ i a, M i a a = 0) (w : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) :
      (tensorOp M *ᵥ w) x = (∏ i, M i (x i) (x i + 1)) * w (flip x) := by
    simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply]
    rw [Finset.sum_eq_single (flip x)]
    · rfl
    · intro y _ hy
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      have h : y i = x i := (fin2_eq_or (x i) (y i)).resolve_right hi
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; exact hM i _), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have s2_sq : s2 ^ 2 = 1 / 2 := by
    simp only [s2]
    push_cast
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have s2_pow_six : s2 ^ 6 = 1 / 8 := by
    calc s2 ^ 6 = (s2 ^ 2) ^ 3 := by ring
      _ = 1 / 8 := by rw [s2_sq]; norm_num
  have ops_mem (a : Fin 4) (i : Fin 6) : ops a i ∈ binarySet := by
    left
    fin_cases a
    · by_cases h : i = 0
      · refine ⟨Real.pi / 2, Real.pi, ?_⟩
        simp [ops, h, binaryOp]
      · refine ⟨Real.pi / 2, 0, ?_⟩
        simp [ops, h, binaryOp]
    · by_cases h : i = 0
      · refine ⟨Real.pi, 0, ?_⟩
        simp [ops, h, binaryOp]
      · refine ⟨0, 0, ?_⟩
        simp [ops, h, binaryOp]
    · refine ⟨Real.pi / 4, 0, ?_⟩
      simp only [ops, hadamard, binaryOp, s2, Real.cos_pi_div_four, Real.sin_pi_div_four,
        Real.cos_zero, Real.sin_zero]
      simp [smul_add, add_comm]
    · refine ⟨Real.pi / 2, Real.pi / 4, ?_⟩
      simp [ops, kmat, binaryOp, s2, Real.cos_pi_div_four, Real.sin_pi_div_four, smul_add]
  have vZ_flip : ∀ x : Fin 6 → Fin 2, vZ (flip x) = -vZ x := by decide +kernel
  have vZ_parity : ∀ x : Fin 6 → Fin 2, (1 + ∏ i, zZ (x i)) * vZ x = 0 := by
    decide +kernel
  have vZ_kmat : ∀ x : Fin 6 → Fin 2,
      (∏ i, kG (x i)) * (vZ (flip x) : GaussianInt) = 8 * vZ x := by decide +kernel
  have vZ_hadamard : ∀ x : Fin 6 → Fin 2,
      ∑ y, (∏ i, hZ (x i) (y i)) * vZ y = 8 * vZ x := by decide +kernel
  have classify : ∀ x : Fin 6 → Fin 2, (∏ i, zZ (x i) = 1) ∨ (∏ i, kG (x i) = 8) ∨
      (∃ j, x = ebasis j) ∨ (∃ j, x = flip (ebasis j)) := by decide +kernel
  have flip_flip : ∀ x : Fin 6 → Fin 2, flip (flip x) = x := by decide +kernel
  have vZ_norm : ∑ x, vZ x * vZ x = 12 := by decide +kernel
  have vZ_pair :
      ∑ p, ∑ q, (∑ r, vZ (glue p r) * vZ (glue q r)) ^ 2 = 48 := by decide +kernel
  have zZ_cast (a : Fin 2) : pauliMatrix .Z a a = (zZ a : ℂ) := by
    fin_cases a <;> simp [pauliMatrix, qubitZ, zZ]
  have x_anti (a : Fin 2) : pauliMatrix .X a (a + 1) = 1 := by
    fin_cases a <;> simp [pauliMatrix, qubitX]
  have kmat_anti (a : Fin 2) : kmat a (a + 1) = s2 * GaussianInt.toComplex (kG a) := by
    fin_cases a <;> simp [kmat, kG, pauliMatrix, qubitX, qubitZ,
      GaussianInt.toComplex_def]
  have hadamard_entry (a b : Fin 2) : hadamard a b = s2 * (hZ a b : ℂ) := by
    fin_cases a <;> fin_cases b <;> simp [hadamard, hZ, pauliMatrix, qubitX, qubitZ]
  have ops0_anti (i : Fin 6) (a : Fin 2) : ops 0 i a a = 0 := by
    by_cases h : i = 0 <;> fin_cases a <;> simp [ops, h, pauliMatrix, qubitX]
  have ops1_diag (i : Fin 6) (a b : Fin 2) (hab : a ≠ b) : ops 1 i a b = 0 := by
    clear * - hab
    by_cases h : i = 0 <;> fin_cases a <;> fin_cases b <;> simp_all [ops, pauliMatrix, qubitZ]
  have ops3_anti (i : Fin 6) (a : Fin 2) : ops 3 i a a = 0 := by
    have hk : kmat = s2 • (pauliMatrix .X + pauliMatrix .Y) := rfl
    have hX : ∀ b : Fin 2, pauliMatrix .X b b = 0 := by
      intro b; fin_cases b <;> simp [pauliMatrix, qubitX]
    have hY : ∀ b : Fin 2, pauliMatrix .Y b b = 0 := by
      intro b
      fin_cases b <;> simp [pauliMatrix, qubitX, qubitZ]
    change kmat a a = 0
    rw [hk, Matrix.smul_apply, Matrix.add_apply, hX, hY, add_zero, smul_zero]
  have prod_ops0 (x : Fin 6 → Fin 2) : ∏ i, ops 0 i (x i) (x i + 1) = -1 := by
    rw [Fin.prod_univ_succ]
    simp [ops, x_anti, Fin.succ_ne_zero]
  have prod_ops1 (x : Fin 6 → Fin 2) :
      ∏ i, ops 1 i (x i) (x i) = -((∏ i, zZ (x i) : ℤ) : ℂ) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ (fun i => zZ (x i))]
    simp [ops, zZ_cast, Fin.succ_ne_zero]
  have entry_ops2' (y x : Fin 6 → Fin 2) :
      tensorOp (ops 2) y x = 1 / 8 * ((hp y x : ℤ) : ℂ) := by
    have h : ∀ i, ops 2 i (y i) (x i) = s2 * (hZ (y i) (x i) : ℂ) := fun i => hadamard_entry _ _
    simp only [tensorOp, Matrix.of_apply, hp]
    rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, s2_pow_six]
    push_cast
    rfl
  have prod_ops3' (x : Fin 6 → Fin 2) :
      ∏ i, ops 3 i (x i) (x i + 1) = 1 / 8 * GaussianInt.toComplex (∏ i, kG (x i)) := by
    have h : ∀ i, ops 3 i (x i) (x i + 1) = s2 * GaussianInt.toComplex (kG (x i)) :=
      fun i => kmat_anti (x i)
    rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, s2_pow_six, map_prod]
  have vZ_zero_parity : ∀ x : Fin 6 → Fin 2, ∏ i, zZ (x i) = 1 → vZ x = 0 := by
    decide +kernel
  have vZ_zero_three : ∀ x : Fin 6 → Fin 2, ∏ i, kG (x i) = 8 → vZ x = 0 := by
    decide +kernel
  have vZ_ebasis : ∀ j, vZ (ebasis j) = 1 := by decide +kernel
  have vZ_flip_ebasis : ∀ j, vZ (flip (ebasis j)) = -1 := by decide +kernel
  have ebasis_inj : ∀ j k, ebasis j = ebasis k → j = k := by decide +kernel
  have flip_ebasis_inj : ∀ j k, flip (ebasis j) = flip (ebasis k) → j = k := by
    decide +kernel
  have ebasis_ne_flip : ∀ j k, ebasis j ≠ flip (ebasis k) := by decide +kernel
  have witness_fixed (a : Fin 4) : tensorOp (ops a) *ᵥ witness = witness := by
    funext x
    fin_cases a
    · change (tensorOp (ops 0) *ᵥ witness) x = witness x
      rw [mulVec_tensorOp_anti _ ops0_anti, prod_ops0]
      simp [witness, vZ_flip x]
    · change (tensorOp (ops 1) *ᵥ witness) x = witness x
      rw [mulVec_tensorOp_diag _ ops1_diag, prod_ops1]
      have hc : ((1 + ∏ i, zZ (x i) : ℤ) : ℂ) * (vZ x : ℂ) = 0 := by exact_mod_cast vZ_parity x
      rw [Int.cast_add, Int.cast_one] at hc
      simp only [witness]
      linear_combination (-1 : ℂ) * hc
    · change (tensorOp (ops 2) *ᵥ witness) x = witness x
      have hc : ∑ y, ((hp x y : ℤ) : ℂ) * (vZ y : ℂ) = 8 * (vZ x : ℂ) := by
        exact_mod_cast vZ_hadamard x
      simp only [Matrix.mulVec, dotProduct, entry_ops2', witness, mul_assoc]
      rw [← Finset.mul_sum, hc]
      ring
    · change (tensorOp (ops 3) *ᵥ witness) x = witness x
      rw [mulVec_tensorOp_anti _ ops3_anti, prod_ops3']
      have hc := congrArg GaussianInt.toComplex (vZ_kmat x)
      simp only [map_mul, map_intCast, map_ofNat] at hc
      simp only [witness]
      linear_combination (1 / 8 : ℂ) * hc
  have witness_unique (w : (Fin 6 → Fin 2) → ℂ) (hw : ∀ a, tensorOp (ops a) *ᵥ w = w) :
      ∃ c : ℂ, w = c • witness := by
    have hA : ∀ x, -w (flip x) = w x := by
      intro x
      have h := congrFun (hw 0) x
      rwa [mulVec_tensorOp_anti _ ops0_anti, prod_ops0, neg_one_mul] at h
    have hB : ∀ x, -((∏ i, zZ (x i) : ℤ) : ℂ) * w x = w x := by
      intro x
      have h := congrFun (hw 1) x
      rwa [mulVec_tensorOp_diag _ ops1_diag, prod_ops1] at h
    have hC : ∀ x, 1 / 8 * GaussianInt.toComplex (∏ i, kG (x i)) * w (flip x) = w x := by
      intro x
      have h := congrFun (hw 3) x
      rwa [mulVec_tensorOp_anti _ ops3_anti, prod_ops3'] at h
    have hD : ∀ y, ∑ x, 1 / 8 * ((hp y x : ℤ) : ℂ) * w x = w y := by
      intro y
      have h := congrFun (hw 2) y
      simpa only [Matrix.mulVec, dotProduct, entry_ops2'] using h
    have hz1 : ∀ x, ∏ i, zZ (x i) = 1 → w x = 0 := by
      intro x h
      have h' := hB x
      rw [h, Int.cast_one] at h'
      linear_combination (-1 / 2 : ℂ) * h'
    have hz2 : ∀ x, ∏ i, kG (x i) = 8 → w x = 0 := by
      intro x h
      have h' := hC x
      rw [h, map_ofNat] at h'
      linear_combination (-1 / 2 : ℂ) * h' + (-1 / 2 : ℂ) * hA x
    have hfl : ∀ j, w (flip (ebasis j)) = -w (ebasis j) := by
      intro j
      have h := hA (flip (ebasis j))
      rw [flip_flip] at h
      linear_combination -h
    -- the sum over the support
    have hsupp : ∀ f : (Fin 6 → Fin 2) → ℂ, (∀ x, ∏ i, zZ (x i) = 1 → f x = 0) →
        (∀ x, ∏ i, kG (x i) = 8 → f x = 0) →
        ∑ x, f x = ∑ j, f (ebasis j) + ∑ j, f (flip (ebasis j)) := by
      intro f h1 h2
      have himg : ∑ x, f x = ∑ x ∈ (Finset.univ.image ebasis ∪ Finset.univ.image (flip ∘ ebasis)),
          f x := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
        rcases classify x with h | h | ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact h1 x h
        · exact h2 x h
        · exact absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))) hx
        · exact absurd (Finset.mem_union_right _
            (Finset.mem_image_of_mem (flip ∘ ebasis) (Finset.mem_univ j))) hx
      rw [himg, Finset.sum_union, Finset.sum_image fun j _ k _ h => ebasis_inj j k h,
        Finset.sum_image (g := flip ∘ ebasis) fun j _ k _ h => flip_ebasis_inj j k h]
      · rfl
      · rw [Finset.disjoint_left]
        rintro x hx hx'
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx'
        exact ebasis_ne_flip j k hk.symm
    have hsum : ∀ y, ∑ x, 1 / 8 * ((hp y x : ℤ) : ℂ) * w x =
        1 / 8 * ∑ j, ((hp y (ebasis j) - hp y (flip (ebasis j)) : ℤ) : ℂ) * w (ebasis j) := by
      intro y
      rw [hsupp _ (fun x h => by rw [hz1 x h, mul_zero]) (fun x h => by rw [hz2 x h, mul_zero]),
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfl j]
      push_cast
      ring
    have heq : ∀ (y : Fin 6 → Fin 2) (c : Fin 6 → ℤ), ∏ i, kG (y i) = 8 →
        (fun j => hp y (ebasis j) - hp y (flip (ebasis j))) = c →
        ∑ j, (c j : ℂ) * w (ebasis j) = 0 := by
      intro y c hy hc
      have hcj : ∀ j, hp y (ebasis j) - hp y (flip (ebasis j)) = c j := fun j => congrFun hc j
      have h := hD y
      rw [hsum y, hz2 y hy] at h
      simp only [hcj] at h
      linear_combination 8 * h
    have e1 := heq ![1, 1, 1, 0, 0, 0] ![-2, -2, -2, 2, 2, 2]
      (by decide +kernel) (by decide +kernel)
    have e2 := heq ![1, 1, 0, 1, 0, 0] ![-2, -2, 2, -2, 2, 2]
      (by decide +kernel) (by decide +kernel)
    have e3 := heq ![1, 1, 0, 0, 1, 0] ![-2, -2, 2, 2, -2, 2]
      (by decide +kernel) (by decide +kernel)
    have e4 := heq ![1, 1, 0, 0, 0, 1] ![-2, -2, 2, 2, 2, -2]
      (by decide +kernel) (by decide +kernel)
    have e5 := heq ![1, 0, 1, 1, 0, 0] ![-2, 2, -2, -2, 2, 2]
      (by decide +kernel) (by decide +kernel)
    have e6 := heq ![0, 1, 1, 1, 0, 0] ![2, -2, -2, -2, 2, 2]
      (by decide +kernel) (by decide +kernel)
    simp only [Int.reduceNeg, Fin.sum_univ_six, Fin.isValue, cons_val_zero, Int.cast_neg,
      Int.cast_ofNat, neg_mul, cons_val_one, cons_val] at e1 e2 e3 e4 e5 e6
    have h1 : w (ebasis 1) = w (ebasis 0) := by linear_combination (e5 - e6) / 4
    have h2 : w (ebasis 2) = w (ebasis 0) := by linear_combination (e2 - e5) / 4 + h1
    have h3 : w (ebasis 3) = w (ebasis 0) := by linear_combination (e1 - e2) / 4 + h2
    have h4 : w (ebasis 4) = w (ebasis 0) := by linear_combination (e2 - e3) / 4 + h3
    have h5 : w (ebasis 5) = w (ebasis 0) := by linear_combination (e3 - e4) / 4 + h4
    have hall : ∀ j, w (ebasis j) = w (ebasis 0) := by
      intro j
      fin_cases j
      exacts [rfl, h1, h2, h3, h4, h5]
    refine ⟨w (ebasis 0), funext fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, witness]
    rcases classify x with h | h | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hz1 x h, vZ_zero_parity x h, Int.cast_zero, mul_zero]
    · rw [hz2 x h, vZ_zero_three x h, Int.cast_zero, mul_zero]
    · rw [vZ_ebasis, Int.cast_one, mul_one, hall j]
    · rw [vZ_flip_ebasis, hfl, hall j]
      push_cast
      ring
  have witness_ne_zero : witness ≠ 0 := by
    intro h
    have h' := congrFun h (ebasis 0)
    simp [witness, vZ_ebasis] at h'
  have witness_stabilized : StabilizedBy binarySet witness :=
    ⟨witness_ne_zero, 4, ops, ops_mem, fun w =>
      ⟨witness_unique w, by rintro ⟨c, rfl⟩ a; rw [Matrix.mulVec_smul, witness_fixed]⟩⟩
  have witness_norm : star witness ⬝ᵥ witness = 12 := by
    have h : ∑ x, ((vZ x : ℤ) : ℂ) * (vZ x : ℂ) = 12 := by exact_mod_cast vZ_norm
    simpa [dotProduct, witness] using h
  have witness_pairPurity : pairPurity witness = 192 := by
    have hm : ∀ p q, marginal witness p q =
        ((∑ r, vZ (glue p r) * vZ (glue q r) : ℤ) : ℂ) := by
      intro p q
      simp [marginal, witness]
    have h48 : ∑ p, ∑ q, ((∑ r, vZ (glue p r) * vZ (glue q r) : ℤ) : ℝ) ^ 2 = 48 := by
      exact_mod_cast vZ_pair
    rw [pairPurity_eq]
    simp only [hm, Complex.norm_intCast, sq_abs]
    rw [h48]
    norm_num
  intro h
  obtain ⟨φ, hφ, u, hu, hv⟩ := h 6 witness witness_stabilized
  obtain ⟨m, hm⟩ := pairPurity_stabilizer hφ
  have h1 : pairPurity φ = 192 := by rw [← witness_pairPurity, hv, pairPurity_local u hu]
  have h2 : star φ ⬝ᵥ φ = 12 := by rw [← witness_norm, hv, norm_local u hu]
  have h3 : ‖(12 : ℂ)‖ ^ 2 = 144 := by norm_num
  rw [hm, h2, h3] at h1
  have h4 : m * 144 = 192 := by exact_mod_cast h1
  omega

end D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
