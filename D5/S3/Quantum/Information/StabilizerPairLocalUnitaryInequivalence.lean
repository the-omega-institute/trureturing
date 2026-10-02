/- GID: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.claim; result=D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result; claim=D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.claim
   digest: The Question 5.4 code pairs of arXiv:2607.26214 are not LU+permutation equivalent. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the transport of the spans
  `outerSpan` under invertible product operators and qubit permutations (`outer_transport`,
  `unitary_data`), the deficiency criterion (`outer_deficient`), the fullness criterion from
  normalizer words (`full_of_local`, `outer_full`), and the kernel-checked tables `checksA`,
  `checksM`, `SA_fixed`, `Splus_fixed`
admission_basis: open-problem-resolution (issue #11210)
Direct frozen dependencies: D5/S3/Quantum/FiniteDimensional (module statement_id
  sha256:8448b6959a48d5c232600cbaa512d3eae6aadd57de71f1e30aad67fde1d1b63d):
  `qubitX` (sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7),
  `qubitZ` (sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c),
  `qubit_weyl_star` (sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d)
-/

import D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

open Matrix D5.S3.Quantum.FiniteDimensional

/-!
A. A. Mahmoud, *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer
Codes*, arXiv:2607.26214v1, Theorem 5.3 (ii) and (iii), Question 5.4: are the codespaces of
`S_A = ⟨ZZZZI, XXIIX, IIXXX⟩` and `S_B = ⟨ZZIZX, XIZXI, IXXYI⟩`, or those of
`S+ = ⟨XXIIXX, IIXXXX, ZZZZIX⟩` and `S− = ⟨XXZXII, ZZXYII, IZZZXX⟩`, mapped to one another by
some product unitary `U₁ ⊗ ⋯ ⊗ Uₙ` composed with a qubit permutation? The answer is no for
both pairs. For a qubit set `T` let `outerSpan T C` be the span of `M ψ`, `ψ ∈ C`, `M` a product
operator that is the identity on `T`; it is the whole space exactly when the reduced state of
`C` on `T` has full rank, and it is carried along by product operators and permutations. The
proof shows that `C_A` is full on every triple other than `{0,1,4}`, `{2,3,4}`, while `C_B` is
not full on `{0,2,3}` and `{1,2,3}`, which share two qubits; and that `C−` is full on every
4-set other than `{0,1,2,3}`, while `C+` is not full on `{0,1,2,3}`, `{0,1,4,5}`, `{2,3,4,5}`.
-/

/-- The single-qubit Pauli labels. -/
inductive Pauli
  | I | X | Y | Z
  deriving DecidableEq

/-- The four Pauli labels form a finite type. -/
instance : Fintype Pauli := ⟨{.I, .X, .Y, .Z}, fun p => by cases p <;> simp⟩

/-- The Pauli matrices: `X`, `Z` are the frozen `qubitX`, `qubitZ`, and `Y = i X Z`. -/
noncomputable def pauliMatrix : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => qubitX
  | .Y => Complex.I • (qubitX * qubitZ)
  | .Z => qubitZ

/-- The tensor product `M₀ ⊗ ⋯ ⊗ M_{n-1}` on `(Fin n → Fin 2) → ℂ`. -/
def tensorOp {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, M i (x i) (y i)

/-- The operator of a Pauli word. -/
noncomputable def wordOp {n : ℕ} (g : Fin n → Pauli) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  tensorOp fun i => pauliMatrix (g i)

/-- The qubit permutation `(P_σ ψ)(x) = ψ(x ∘ σ)`. -/
def qubitPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => if y = x ∘ σ then 1 else 0

/-- The codespace of `⟨S 0, S 1, S 2⟩`: the joint `+1` eigenspace of the three generators. -/
noncomputable def codespace {n : ℕ} (S : Fin 3 → Fin n → Pauli) :
    Submodule ℂ ((Fin n → Fin 2) → ℂ) where
  carrier := {ψ | ∀ j, wordOp (S j) *ᵥ ψ = ψ}
  add_mem' := by
    intro a b ha hb j
    rw [Matrix.mulVec_add, ha j, hb j]
  zero_mem' := by
    intro j
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c a ha j
    rw [Matrix.mulVec_smul, ha j]

open Pauli in
/-- `S_A = ⟨ZZZZI, XXIIX, IIXXX⟩` (Theorem 5.3 (ii)). -/
def SA : Fin 3 → Fin 5 → Pauli := ![![Z, Z, Z, Z, I], ![X, X, I, I, X], ![I, I, X, X, X]]

open Pauli in
/-- `S_B = ⟨ZZIZX, XIZXI, IXXYI⟩` (Theorem 5.3 (ii)). -/
def SB : Fin 3 → Fin 5 → Pauli := ![![Z, Z, I, Z, X], ![X, I, Z, X, I], ![I, X, X, Y, I]]

open Pauli in
/-- `S+ = ⟨XXIIXX, IIXXXX, ZZZZIX⟩` (Theorem 5.3 (iii)). -/
def Splus : Fin 3 → Fin 6 → Pauli :=
  ![![X, X, I, I, X, X], ![I, I, X, X, X, X], ![Z, Z, Z, Z, I, X]]

open Pauli in
/-- `S− = ⟨XXZXII, ZZXYII, IZZZXX⟩` (Theorem 5.3 (iii)). -/
def Sminus : Fin 3 → Fin 6 → Pauli :=
  ![![X, X, Z, X, I, I], ![Z, Z, X, Y, I, I], ![I, Z, Z, Z, X, X]]

/-- The positive answer to Question 5.4, first part: one of the two pairs of codespaces is
related by a product unitary composed with a qubit permutation. -/
def claim : Prop :=
  (∃ (U : Fin 5 → Matrix.unitaryGroup (Fin 2) ℂ) (σ : Equiv.Perm (Fin 5)),
      (codespace SA).map (Matrix.toLin' (tensorOp (fun i => (U i : Matrix (Fin 2) (Fin 2) ℂ)) *
        qubitPermutation σ)) = codespace SB) ∨
    (∃ (U : Fin 6 → Matrix.unitaryGroup (Fin 2) ℂ) (σ : Equiv.Perm (Fin 6)),
      (codespace Splus).map (Matrix.toLin' (tensorOp (fun i => (U i : Matrix (Fin 2) (Fin 2) ℂ)) *
        qubitPermutation σ)) = codespace Sminus)

/-- Whether two single-qubit Paulis anticommute. -/
def anticomm : Pauli → Pauli → Bool
  | .I, _ => false
  | _, .I => false
  | a, b => a != b

/-- The commutation sign of two single-qubit Paulis. -/
def sgn (a b : Pauli) : ℤ := if anticomm a b then -1 else 1

/-- The span of `M ψ` over `ψ ∈ C` and product operators `M` that are the identity on `T`. -/
private noncomputable def outerSpan {n : ℕ} (T : Finset (Fin n))
    (C : Submodule ℂ ((Fin n → Fin 2) → ℂ)) : Submodule ℂ ((Fin n → Fin 2) → ℂ) :=
  Submodule.span ℂ {v | ∃ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, (∀ i ∈ T, M i = 1) ∧
    ∃ ψ ∈ C, v = tensorOp M *ᵥ ψ}

/-- The single-qubit operator `A` acting on qubit `j`. -/
private noncomputable def localOp {n : ℕ} (j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  tensorOp (Function.update (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j A)

/-- The bit flipped by a Pauli. -/
private def flipBit : Pauli → Fin 2
  | .I => 0
  | .X => 1
  | .Y => 1
  | .Z => 0

/-- The sign of a real Pauli (`I`, `X`, `Z`) at a basis bit. -/
def phaseZ : Pauli → Fin 2 → ℤ
  | .Z, 1 => -1
  | _, _ => 1

/-- Every word of `L` commutes with the three generators `S`. -/
private def commCheck {n : ℕ} (S : Fin 3 → Fin n → Pauli) (L : List (Fin n → Pauli)) : Bool :=
  L.all fun w => (List.finRange 3).all fun k => (List.ofFn fun i => sgn (w i) (S k i)).prod == 1

/-- On `T`, the restrictions of the words of `L` include every `X_j` and `Z_j` with `j ∈ T`. -/
private def coverCheck {n : ℕ} (L : List (Fin n → Pauli)) (T : Finset (Fin n)) : Bool :=
  (List.finRange n).all fun j => !(decide (j ∈ T)) ||
    [Pauli.X, Pauli.Z].all fun P => L.any fun w =>
      (List.finRange n).all fun i => !(decide (i ∈ T)) || w i == (if i = j then P else Pauli.I)

/-- The support `x₀ = x₁`, `x₂ = x₃`, `x₄ = x₀ + x₂` of the codewords used below. -/
private def inSupp {n : ℕ} (x : Fin (n + 5) → Fin 2) : Bool :=
  x 0 == x 1 && x 2 == x 3 && x 4 == x 0 + x 2

open Pauli in
/-- Normalizer words of `S_A` covering the full triples. -/
private def LA : List (Fin 5 → Pauli) :=
  [![I, I, X, X, I], ![I, I, Z, Z, I], ![X, X, I, I, I], ![Z, Z, I, I, I], ![I, I, I, I, X],
   ![I, Z, I, Z, Z], ![I, Z, Z, I, Z], ![Z, I, I, Z, Z], ![Z, I, Z, I, Z], ![I, X, I, X, I],
   ![I, X, X, I, I], ![X, I, I, X, I], ![X, I, X, I, I]]

open Pauli in
/-- Normalizer words of `S−` covering the full 4-sets. -/
private def LM : List (Fin 6 → Pauli) :=
  [![I, I, I, I, I, X], ![I, I, I, I, X, I], ![I, I, I, I, Z, Z], ![I, X, I, X, I, I],
   ![X, I, Z, I, I, I], ![Z, Z, I, I, I, I], ![I, I, X, Y, I, I], ![Y, I, I, Z, I, I],
   ![I, I, Z, X, I, Z], ![I, I, Z, X, Z, I], ![I, X, Z, I, I, Z], ![I, X, Z, I, Z, I],
   ![I, Z, Z, Z, I, I], ![X, I, I, X, I, Z], ![X, I, I, X, Z, I], ![X, X, I, I, I, Z],
   ![X, X, I, I, Z, I], ![Z, I, X, I, I, Z], ![Z, I, X, I, Z, I], ![I, Y, I, Z, I, Z],
   ![I, Y, I, Z, Z, I], ![I, Z, X, I, I, Y], ![I, Z, X, I, Y, I], ![Y, X, X, I, I, I],
   ![Z, I, Y, X, I, I], ![I, I, Y, Z, I, Y], ![I, I, Y, Z, Y, I], ![I, Z, I, Y, I, Y],
   ![I, Z, I, Y, Y, I], ![X, Y, I, Y, I, I], ![Z, I, I, Y, I, Y], ![Z, I, I, Y, Y, I]]

/-- The triples other than `{0,1,4}` and `{2,3,4}`. -/
private def fullA : List (Finset (Fin 5)) :=
  [{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}]

/-- The 4-sets other than `{0,1,2,3}`. -/
private def fullM : List (Finset (Fin 6)) :=
  [{0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1, 3, 4}, {0, 1, 3, 5}, {0, 1, 4, 5}, {0, 2, 3, 4},
   {0, 2, 3, 5}, {0, 2, 4, 5}, {0, 3, 4, 5}, {1, 2, 3, 4}, {1, 2, 3, 5}, {1, 2, 4, 5},
   {1, 3, 4, 5}, {2, 3, 4, 5}]

/-- The negative answer to Question 5.4, first part, for both pairs. -/
theorem result : ¬ claim := by
  have tensor_mul : ∀ {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      tensorOp M * tensorOp N = tensorOp fun i => M i * N i := by
    intro n M N
    ext x z
    simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
    simp_rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have tensor_one : ∀ {n : ℕ},
      tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    intro n
    ext x y
    simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hc; exact h (funext fun i => not_not.1 fun hi => hc ⟨i, hi⟩)
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have perm_tensor : ∀ {n : ℕ} (τ : Equiv.Perm (Fin n)) (N : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      qubitPermutation τ * tensorOp N = tensorOp (fun i => N (τ.symm i)) * qubitPermutation τ := by
    intro n τ N
    ext x z
    simp only [qubitPermutation, tensorOp, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one,
      mul_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (x ∘ τ)]
    have : ∀ y : Fin n → Fin 2, (z = y ∘ τ) ↔ (y = z ∘ τ.symm) := by
      intro y; constructor
      · rintro rfl; funext i; simp
      · rintro rfl; funext i; simp
    simp_rw [this]
    rw [Finset.sum_ite_eq' Finset.univ (z ∘ τ.symm)]
    simp only [Finset.mem_univ, if_true, Function.comp_apply]
    rw [← Equiv.prod_comp τ.symm]
    simp
  have perm_mul_apply : ∀ {n : ℕ} (τ : Equiv.Perm (Fin n))
      (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x z : Fin n → Fin 2),
      (qubitPermutation τ * A) x z = A (x ∘ τ) z := by
    intro n τ A x z
    simp only [qubitPermutation, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (x ∘ τ)]
    simp
  have perm_mul_inv : ∀ {n : ℕ} (τ : Equiv.Perm (Fin n)),
      qubitPermutation τ * qubitPermutation τ.symm = 1 := by
    intro n τ
    ext x z
    rw [perm_mul_apply]
    simp only [qubitPermutation, Matrix.of_apply, Matrix.one_apply]
    have : (z = (x ∘ τ) ∘ τ.symm) ↔ x = z := by
      constructor
      · intro h; rw [h]; funext i; simp
      · intro h; rw [h]; funext i; simp
    simp only [this]
  have pauli_sq : ∀ p : Pauli, pauliMatrix p * pauliMatrix p = 1 := by
    obtain ⟨-, -, -, hX, hZ⟩ := qubit_weyl_star
    intro p
    cases p
    · exact mul_one 1
    · rw [← pow_two]; exact hX
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply]
    · rw [← pow_two]; exact hZ
  have pauli_comm : ∀ a b : Pauli,
      pauliMatrix a * pauliMatrix b = ((sgn a b : ℤ) : ℂ) • (pauliMatrix b * pauliMatrix a) := by
    intro a b
    cases a <;> cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, sgn, anticomm]
  have tensor_smul : ∀ {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      tensorOp (fun i => c i • M i) = (∏ i, c i) • tensorOp M := by
    intro n c M
    ext x y
    simp [tensorOp, Finset.prod_mul_distrib]
  have word_comm : ∀ {n : ℕ} (a b : Fin n → Pauli), ∏ i, sgn (a i) (b i) = 1 →
      wordOp a * wordOp b = wordOp b * wordOp a := by
    intro n a b h
    unfold wordOp
    rw [tensor_mul, tensor_mul]
    simp_rw [pauli_comm (a _) (b _)]
    rw [tensor_smul, ← Int.cast_prod, h, Int.cast_one, one_smul]
  have outer_transport : ∀ {n : ℕ} (W W' : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
      W * W' = 1 → ∀ σ : Equiv.Perm (Fin n),
      (∀ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, ∃ M' : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ i, M i = 1 → M' (σ i) = 1) ∧ W * tensorOp M = tensorOp M' * W) →
      ∀ (T : Finset (Fin n)) (C : Submodule ℂ ((Fin n → Fin 2) → ℂ)), outerSpan T C = ⊤ →
      outerSpan (T.map σ.toEmbedding) (C.map (Matrix.toLin' W)) = ⊤ := by
    intro n W W' hWW' σ hW T C h
    have key : ∀ u ∈ outerSpan T C,
        W *ᵥ u ∈ outerSpan (T.map σ.toEmbedding) (C.map (Matrix.toLin' W)) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨M, hM, ψ, hψ, rfl⟩ := hx
        obtain ⟨M', hM', hc⟩ := hW M
        apply Submodule.subset_span
        refine ⟨M', ?_, W *ᵥ ψ, Submodule.mem_map_of_mem hψ, ?_⟩
        · intro i hi
          obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hi
          exact hM' k (hM k hk)
        · rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
    rw [eq_top_iff]
    intro v _
    have hv : v = W *ᵥ (W' *ᵥ v) := by rw [Matrix.mulVec_mulVec, hWW', Matrix.one_mulVec]
    rw [hv]
    exact key _ (h ▸ Submodule.mem_top)
  have outer_deficient : ∀ {n : ℕ} (g : Fin n → Pauli) (T : Finset (Fin n))
      (C : Submodule ℂ ((Fin n → Fin 2) → ℂ)), (∀ i ∉ T, g i = Pauli.I) →
      (∀ ψ ∈ C, wordOp g *ᵥ ψ = ψ) → ∀ i0 : Fin n, (g i0 = Pauli.X ∨ g i0 = Pauli.Y) →
      outerSpan T C ≠ ⊤ := by
    intro n g T C hsupp hfix i0 hi0
    have key : ∀ u ∈ outerSpan T C, wordOp g *ᵥ u = u := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨M, hM, ψ, hψ, rfl⟩ := hx
        have hc : wordOp g * tensorOp M = tensorOp M * wordOp g := by
          unfold wordOp
          rw [tensor_mul, tensor_mul]
          congr 1
          funext i
          by_cases hi : i ∈ T
          · rw [hM i hi, mul_one, one_mul]
          · rw [hsupp i hi]; simp [pauliMatrix]
        rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hfix ψ hψ]
      | zero => exact Matrix.mulVec_zero _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
      | smul a x _ hx => rw [Matrix.mulVec_smul, hx]
    intro htop
    have h1 := key (Pi.single 0 1) (htop ▸ Submodule.mem_top)
    have h2 := congrFun h1 0
    rw [Matrix.mulVec_single_one] at h2
    simp only [Matrix.col_apply] at h2
    have h3 : wordOp g 0 0 = 0 := by
      simp only [wordOp, tensorOp, Matrix.of_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ i0)
      rcases hi0 with h | h <;> rw [h] <;>
        simp [pauliMatrix, qubitX, qubitZ]
    rw [h3, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  have tensor_update_apply : ∀ {n : ℕ} (N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (j : Fin n)
      (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin n → Fin 2),
      tensorOp (Function.update N j A) x y =
        A (x j) (y j) * ∏ i ∈ Finset.univ.erase j, N i (x i) (y i) := by
    intro n N j A x y
    simp only [tensorOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have localOp_add : ∀ {n : ℕ} (j : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ),
      localOp j (A + B) = localOp j A + localOp j B := by
    intro n j A B
    ext x y
    simp only [localOp, tensor_update_apply, Matrix.add_apply, add_mul]
  have localOp_smul : ∀ {n : ℕ} (j : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ),
      localOp j (c • A) = c • localOp j A := by
    intro n j c A
    ext x y
    simp only [localOp, tensor_update_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  have localOp_mul : ∀ {n : ℕ} (j : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ),
      localOp j A * localOp j B = localOp j (A * B) := by
    intro n j A B
    unfold localOp
    rw [tensor_mul]
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  have localOp_one : ∀ {n : ℕ} (j : Fin n), localOp j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    intro n j
    unfold localOp
    rw [Function.update_eq_self_iff.2 rfl, tensor_one]
  have qubit_decomp : ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      A = ((A 0 0 + A 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((A 0 1 + A 1 0) / 2) • qubitX +
        ((A 0 0 - A 1 1) / 2) • qubitZ + ((A 1 0 - A 0 1) / 2) • (qubitX * qubitZ) := by
    intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitX, qubitZ] <;> ring
  have full_of_local : ∀ {n : ℕ} (V : Submodule ℂ ((Fin n → Fin 2) → ℂ)) (T : Finset (Fin n)),
      (∀ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, (∀ i ∈ T, M i = 1) →
        ∀ v ∈ V, tensorOp M *ᵥ v ∈ V) →
      (∀ j ∈ T, ∀ v ∈ V, localOp j qubitX *ᵥ v ∈ V) →
      (∀ j ∈ T, ∀ v ∈ V, localOp j qubitZ *ᵥ v ∈ V) → V ≠ ⊥ → V = ⊤ := by
    intro n V T h1 hX hZ hne
    have ha : ∀ j ∈ T, ∀ A, ∀ v ∈ V, localOp j A *ᵥ v ∈ V := by
      intro j hj A v hv
      rw [qubit_decomp A, localOp_add, localOp_add, localOp_add, localOp_smul, localOp_smul,
        localOp_smul, localOp_smul, ← localOp_mul, localOp_one]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      exact V.add_mem (V.add_mem (V.add_mem (V.smul_mem _ hv) (V.smul_mem _ (hX j hj v hv)))
        (V.smul_mem _ (hZ j hj v hv))) (V.smul_mem _ (hX j hj _ (hZ j hj v hv)))
    have hb : ∀ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, ∀ v ∈ V, tensorOp M *ᵥ v ∈ V := by
      intro M
      have hS : ∀ S : Finset (Fin n), S ⊆ T → ∀ v ∈ V,
          tensorOp (fun i => if i ∈ S then M i else 1) *ᵥ v ∈ V := by
        intro S
        induction S using Finset.induction_on with
        | empty =>
          intro _ v hv
          simpa [tensor_one] using hv
        | insert j S hj ih =>
          intro hST v hv
          have e : tensorOp (fun i => if i ∈ insert j S then M i else 1) =
              localOp j (M j) * tensorOp (fun i => if i ∈ S then M i else 1) := by
            unfold localOp
            rw [tensor_mul]
            congr 1
            funext i
            by_cases hij : i = j
            · subst hij; simp [hj]
            · simp [hij]
          rw [e, ← Matrix.mulVec_mulVec]
          exact ha j (hST (Finset.mem_insert_self j S)) _ _
            (ih (fun x hx => hST (Finset.mem_insert_of_mem hx)) v hv)
      intro v hv
      have e : tensorOp M = tensorOp (fun i => if i ∈ T then 1 else M i) *
          tensorOp (fun i => if i ∈ T then M i else 1) := by
        rw [tensor_mul]
        congr 1
        funext i
        by_cases hi : i ∈ T <;> simp [hi]
      rw [e, ← Matrix.mulVec_mulVec]
      exact h1 _ (fun i hi => by simp [hi]) _ (hS T subset_rfl v hv)
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a, ha0⟩ : ∃ a, φ a ≠ 0 := by
      by_contra h
      exact hφ0 (funext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
    have hdelta : ∀ z, Pi.single z (1 : ℂ) ∈ V := by
      intro z
      have hR := hb (fun i => Matrix.single (z i) (a i) (1 : ℂ)) φ hφ
      have hcomp :
          tensorOp (fun i => Matrix.single (z i) (a i) (1 : ℂ)) *ᵥ φ = φ a • Pi.single z 1 := by
        funext x
        simp only [Matrix.mulVec, dotProduct, tensorOp, Matrix.of_apply, Matrix.single_apply,
          Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single a]
        · by_cases hx : x = z
          · subst hx; simp
          · obtain ⟨i, hi⟩ : ∃ i, x i ≠ z i := by
              by_contra hc
              exact hx (funext fun i => not_not.1 fun h => hc ⟨i, h⟩)
            rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])]
            simp [hx]
        · intro y _ hy
          obtain ⟨i, hi⟩ : ∃ i, y i ≠ a i := by
            by_contra hc
            exact hy (funext fun i => not_not.1 fun h => hc ⟨i, h⟩)
          rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi]), zero_mul]
        · intro h; exact absurd (Finset.mem_univ a) h
      rw [hcomp] at hR
      have := V.smul_mem (φ a)⁻¹ hR
      rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    apply Submodule.sum_mem
    intro z _
    have : Pi.single z (v z) = v z • Pi.single z (1 : ℂ) := by
      funext x
      by_cases hx : x = z
      · subst hx; simp
      · simp [hx]
    rw [this]
    exact V.smul_mem _ (hdelta z)
  have outer_ge : ∀ {n : ℕ} (T : Finset (Fin n)) (C : Submodule ℂ ((Fin n → Fin 2) → ℂ)),
      C ≤ outerSpan T C := by
    intro n T C ψ hψ
    apply Submodule.subset_span
    exact ⟨fun _ => 1, fun _ _ => rfl, ψ, hψ, by rw [tensor_one, Matrix.one_mulVec]⟩
  have outer_tensor_inv : ∀ {n : ℕ} (T : Finset (Fin n)) (C : Submodule ℂ ((Fin n → Fin 2) → ℂ))
      (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ), (∀ i ∈ T, M i = 1) →
      ∀ v ∈ outerSpan T C, tensorOp M *ᵥ v ∈ outerSpan T C := by
    intro n T C M hM v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN, ψ, hψ, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨fun i => M i * N i, fun i hi => show M i * N i = 1 by rw [hM i hi, hN i hi, mul_one],
        ψ, hψ, ?_⟩
      rw [Matrix.mulVec_mulVec, tensor_mul]
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
  have outer_word_inv : ∀ {n : ℕ} (T : Finset (Fin n)) (C : Submodule ℂ ((Fin n → Fin 2) → ℂ))
      (w : Fin n → Pauli), (∀ ψ ∈ C, wordOp w *ᵥ ψ ∈ C) →
      ∀ v ∈ outerSpan T C,
        wordOp (fun i => if i ∈ T then w i else Pauli.I) *ᵥ v ∈ outerSpan T C := by
    intro n T C w hw v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN, ψ, hψ, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨fun i => N i * pauliMatrix (if i ∈ T then Pauli.I else w i), fun i hi => by
        simp [hN i hi, hi, pauliMatrix], wordOp w *ᵥ ψ, hw ψ hψ, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      unfold wordOp
      rw [tensor_mul, tensor_mul]
      congr 2
      funext i
      by_cases hi : i ∈ T
      · simp [hi, hN i hi, pauliMatrix]
      · simp only [hi, if_false]
        rw [mul_assoc, pauli_sq, mul_one, show pauliMatrix Pauli.I = 1 from rfl, one_mul]
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
  have word_single : ∀ {n : ℕ} (j : Fin n) (P : Pauli),
      wordOp (Function.update (fun _ : Fin n => Pauli.I) j P) = localOp j (pauliMatrix P) := by
    intro n j P
    unfold wordOp localOp
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h, pauliMatrix]
  have normalizer_preserves : ∀ {n : ℕ} (S : Fin 3 → Fin n → Pauli) (w : Fin n → Pauli),
      (∀ k, ∏ i, sgn (w i) (S k i) = 1) → ∀ ψ ∈ codespace S, wordOp w *ᵥ ψ ∈ codespace S := by
    intro n S w hw ψ hψ k
    rw [Matrix.mulVec_mulVec, ← word_comm w (S k) (hw k), ← Matrix.mulVec_mulVec, hψ k]
  have outer_full : ∀ {n : ℕ} (S : Fin 3 → Fin n → Pauli) (T : Finset (Fin n)),
      codespace S ≠ ⊥ → ∀ L : List (Fin n → Pauli), (∀ w ∈ L, ∀ k, ∏ i, sgn (w i) (S k i) = 1) →
      (∀ j ∈ T, ∀ P ∈ [Pauli.X, Pauli.Z], ∃ w ∈ L,
        (fun i => if i ∈ T then w i else Pauli.I) = Function.update (fun _ => Pauli.I) j P) →
      outerSpan T (codespace S) = ⊤ := by
    intro n S T hne L hL hcov
    have hloc : ∀ j ∈ T, ∀ P ∈ [Pauli.X, Pauli.Z], ∀ v ∈ outerSpan T (codespace S),
        localOp j (pauliMatrix P) *ᵥ v ∈ outerSpan T (codespace S) := by
      intro j hj P hP v hv
      obtain ⟨w, hwL, hwe⟩ := hcov j hj P hP
      rw [← word_single, ← hwe]
      exact outer_word_inv T _ w (normalizer_preserves S w (hL w hwL)) v hv
    apply full_of_local _ T (fun M hM => outer_tensor_inv T _ M hM)
      (fun j hj => hloc j hj Pauli.X (by simp)) (fun j hj => hloc j hj Pauli.Z (by simp))
    intro h
    apply hne
    rw [eq_bot_iff]
    exact (outer_ge T _).trans h.le
  have pauli_entry_real : ∀ p : Pauli, p ≠ Pauli.Y → ∀ r c : Fin 2,
      pauliMatrix p r c = if c = r + flipBit p then ((phaseZ p r : ℤ) : ℂ) else 0 := by
    intro p hp r c
    cases p <;> fin_cases r <;> fin_cases c <;>
      simp [pauliMatrix, qubitX, qubitZ, flipBit, phaseZ] at hp ⊢
  have word_apply_real : ∀ {n : ℕ} (g : Fin n → Pauli), (∀ i, g i ≠ Pauli.Y) →
      ∀ (ψ : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2),
      (wordOp g *ᵥ ψ) x =
        (∏ i, ((phaseZ (g i) (x i) : ℤ) : ℂ)) * ψ (fun i => x i + flipBit (g i)) := by
    intro n g hg ψ x
    simp only [Matrix.mulVec, dotProduct, wordOp, tensorOp, Matrix.of_apply]
    simp_rw [pauli_entry_real _ (hg _)]
    rw [Finset.sum_eq_single (fun i => x i + flipBit (g i))]
    · simp
    · intro y _ hy
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i + flipBit (g i) := by
        by_contra hc
        exact hy (funext fun i => not_not.1 fun h => hc ⟨i, h⟩)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have commCheck_sound : ∀ {n : ℕ} (S : Fin 3 → Fin n → Pauli) (L : List (Fin n → Pauli)),
      commCheck S L = true → ∀ w ∈ L, ∀ k, ∏ i, sgn (w i) (S k i) = 1 := by
    intro n S L h w hw k
    simp only [commCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
    rw [← List.prod_ofFn]
    exact h w hw k
  have coverCheck_sound : ∀ {n : ℕ} (L : List (Fin n → Pauli)) (T : Finset (Fin n)),
      coverCheck L T = true → ∀ j ∈ T, ∀ P ∈ [Pauli.X, Pauli.Z], ∃ w ∈ L,
        (fun i => if i ∈ T then w i else Pauli.I) = Function.update (fun _ => Pauli.I) j P := by
    intro n L T h j hj P hP
    simp only [coverCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, beq_iff_eq] at h
    rcases h j with h | h
    · exact absurd hj h
    obtain ⟨w, hw, hw'⟩ := h P hP
    refine ⟨w, hw, funext fun i => ?_⟩
    by_cases hi : i ∈ T
    · rcases hw' i with h' | h'
      · exact absurd hi h'
      · rw [if_pos hi, h']
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
    · rw [if_neg hi]
      have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Function.update_of_ne hij]
  have SA_fixed : ∀ k : Fin 3, ∀ x : Fin 5 → Fin 2,
      (∏ i, phaseZ (SA k i) (x i)) *
          (if inSupp (n := 0) (fun i => x i + flipBit (SA k i)) then 1 else 0) =
        (if inSupp (n := 0) x then 1 else 0 : ℤ) := by
    decide +kernel
  have Splus_fixed : ∀ k : Fin 3, ∀ x : Fin 6 → Fin 2,
      (∏ i, phaseZ (Splus k i) (x i)) *
          (if inSupp (n := 1) (fun i => x i + flipBit (Splus k i)) then 1 else 0) =
        (if inSupp (n := 1) x then 1 else 0 : ℤ) := by
    decide +kernel
  have checksA : commCheck SA LA = true ∧ fullA.all (coverCheck LA) = true := by
    decide +kernel
  have checksM : commCheck Sminus LM = true ∧ fullM.all (coverCheck LM) = true := by
    decide +kernel
  have fullA_complete : ∀ T : Finset (Fin 5), T.card = 3 → T ≠ {0, 1, 4} → T ≠ {2, 3, 4} →
      T ∈ fullA := by
    decide
  have fullM_complete : ∀ T : Finset (Fin 6), T.card = 4 → T ≠ {0, 1, 2, 3} → T ∈ fullM := by
    decide
  have unitary_data : ∀ {n : ℕ} (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (σ : Equiv.Perm (Fin n)),
      (∀ i, V i * star (V i) = 1) → (∀ i, star (V i) * V i = 1) →
      (tensorOp V * qubitPermutation σ) *
          (qubitPermutation σ.symm * tensorOp (fun i => star (V i))) = 1 ∧
        (qubitPermutation σ.symm * tensorOp (fun i => star (V i))) *
          (tensorOp V * qubitPermutation σ) = 1 ∧
        (∀ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, ∃ M' : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
          (∀ i, M i = 1 → M' (σ i) = 1) ∧
            (tensorOp V * qubitPermutation σ) * tensorOp M =
              tensorOp M' * (tensorOp V * qubitPermutation σ)) ∧
        (∀ M : Fin n → Matrix (Fin 2) (Fin 2) ℂ, ∃ M' : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
          (∀ i, M i = 1 → M' (σ.symm i) = 1) ∧
            (qubitPermutation σ.symm * tensorOp (fun i => star (V i))) * tensorOp M =
              tensorOp M' * (qubitPermutation σ.symm * tensorOp (fun i => star (V i)))) := by
    intro n V σ hr hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc (qubitPermutation σ), perm_mul_inv, one_mul, tensor_mul]
      simp only [hr]
      exact tensor_one
    · rw [mul_assoc, ← mul_assoc (tensorOp _), tensor_mul]
      simp only [hl]
      rw [tensor_one, one_mul]
      have := perm_mul_inv σ.symm
      rwa [Equiv.symm_symm] at this
    · intro M
      refine ⟨fun i => V i * M (σ.symm i) * star (V i), fun i hi => ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply, hi, mul_one, hr]
      · rw [mul_assoc, perm_tensor, ← mul_assoc, ← mul_assoc, tensor_mul, tensor_mul]
        congr 2
        funext i
        rw [mul_assoc, hl, mul_one]
    · intro M
      refine ⟨fun i => star (V (σ i)) * M (σ i) * V (σ i), fun i hi => ?_, ?_⟩
      · simp only [Equiv.apply_symm_apply, hi, mul_one, hl]
      · rw [mul_assoc, tensor_mul, perm_tensor, perm_tensor, ← mul_assoc, tensor_mul]
        simp only [Equiv.symm_symm]
        congr 2
        funext i
        rw [mul_assoc, hr, mul_one]
  have mem_codespace : ∀ {n : ℕ} (S : Fin 3 → Fin n → Pauli) (ψ : (Fin n → Fin 2) → ℂ),
      ψ ∈ codespace S ↔ ∀ j, wordOp (S j) *ᵥ ψ = ψ :=
    fun _ _ => Iff.rfl
  have codeword_ne_bot : ∀ {m : ℕ} (S : Fin 3 → Fin (m + 5) → Pauli), (∀ k i, S k i ≠ Pauli.Y) →
      (∀ k : Fin 3, ∀ x : Fin (m + 5) → Fin 2,
        (∏ i, phaseZ (S k i) (x i)) * (if inSupp (fun i => x i + flipBit (S k i)) then 1 else 0) =
          (if inSupp x then 1 else 0 : ℤ)) →
      codespace S ≠ ⊥ := by
    intro m S hY hfix hb
    let ψ : (Fin (m + 5) → Fin 2) → ℂ := fun x => if inSupp x then 1 else 0
    have hψ : ψ ∈ codespace S := by
      rw [mem_codespace]
      intro k
      funext x
      rw [word_apply_real _ (hY k)]
      have h2 := congrArg (Int.cast : ℤ → ℂ) (hfix k x)
      push_cast at h2
      exact h2
    rw [hb, Submodule.mem_bot] at hψ
    have h0 := congrFun hψ 0
    simp [ψ, inSupp] at h0
  rintro (⟨U, σ, h⟩ | ⟨U, σ, h⟩)
  · obtain ⟨hWW', -, hW, -⟩ := unitary_data (fun i => (U i : Matrix (Fin 2) (Fin 2) ℂ)) σ
      (fun i => Matrix.mem_unitaryGroup_iff.1 (U i).2)
      (fun i => Matrix.mem_unitaryGroup_iff'.1 (U i).2)
    have hneA : codespace SA ≠ ⊥ :=
      codeword_ne_bot (m := 0) SA (by decide) SA_fixed
    have key : ∀ T : Finset (Fin 5), T.card = 3 → outerSpan T (codespace SB) ≠ ⊤ →
        T.map σ.symm.toEmbedding = {0, 1, 4} ∨ T.map σ.symm.toEmbedding = {2, 3, 4} := by
      intro T hc hT
      by_contra hne
      rw [not_or] at hne
      apply hT
      have hmem := fullA_complete (T.map σ.symm.toEmbedding) (by rw [Finset.card_map, hc])
        hne.1 hne.2
      have hfull := outer_full SA _ hneA LA (commCheck_sound SA LA checksA.1)
        (coverCheck_sound LA _ (List.all_eq_true.1 checksA.2 _ hmem))
      have := outer_transport _ _ hWW' σ hW _ _ hfull
      rwa [Finset.map_map, show σ.symm.toEmbedding.trans σ.toEmbedding =
          Function.Embedding.refl _ by ext; simp, Finset.map_refl, h] at this
    have d1 : outerSpan {0, 2, 3} (codespace SB) ≠ ⊤ :=
      outer_deficient (SB 1) _ _ (by decide) (fun ψ hψ => (mem_codespace SB ψ).1 hψ 1) 0
        (Or.inl rfl)
    have d2 : outerSpan {1, 2, 3} (codespace SB) ≠ ⊤ :=
      outer_deficient (SB 2) _ _ (by decide) (fun ψ hψ => (mem_codespace SB ψ).1 hψ 2) 1
        (Or.inl rfl)
    have h1 := key _ rfl d1
    have h2 := key _ rfl d2
    have hinter : ((({0, 2, 3} : Finset (Fin 5)).map σ.symm.toEmbedding) ∩
        (({1, 2, 3} : Finset (Fin 5)).map σ.symm.toEmbedding)).card = 2 := by
      rw [← Finset.map_inter, Finset.card_map]
      decide
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hinter <;>
      revert hinter <;> decide
  · obtain ⟨hWW', hW'W, -, hW'⟩ := unitary_data (fun i => (U i : Matrix (Fin 2) (Fin 2) ℂ)) σ
      (fun i => Matrix.mem_unitaryGroup_iff.1 (U i).2)
      (fun i => Matrix.mem_unitaryGroup_iff'.1 (U i).2)
    have hneP : codespace Splus ≠ ⊥ :=
      codeword_ne_bot (m := 1) Splus (by decide) Splus_fixed
    have hneM : codespace Sminus ≠ ⊥ := by
      rw [← h]
      intro hb
      apply hneP
      rw [eq_bot_iff]
      intro ψ hψ
      have hm := Submodule.mem_map_of_mem (f := Matrix.toLin' (tensorOp (fun i =>
        (U i : Matrix (Fin 2) (Fin 2) ℂ)) * qubitPermutation σ)) hψ
      rw [hb, Submodule.mem_bot, Matrix.toLin'_apply] at hm
      rw [Submodule.mem_bot]
      have := congrArg (fun v => (qubitPermutation σ.symm * tensorOp (fun i =>
        star (U i : Matrix (Fin 2) (Fin 2) ℂ))) *ᵥ v) hm
      simp only [Matrix.mulVec_mulVec, hW'W, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    have back : ∀ T : Finset (Fin 6), T.card = 4 → outerSpan T (codespace Splus) ≠ ⊤ →
        T.map σ.toEmbedding = {0, 1, 2, 3} := by
      intro T hc hT
      by_contra hne
      apply hT
      have hmem := fullM_complete (T.map σ.toEmbedding) (by rw [Finset.card_map, hc]) hne
      have hfull := outer_full Sminus _ hneM LM (commCheck_sound Sminus LM checksM.1)
        (coverCheck_sound LM _ (List.all_eq_true.1 checksM.2 _ hmem))
      have := outer_transport _ _ hW'W σ.symm hW' _ _ hfull
      rwa [Finset.map_map, show σ.toEmbedding.trans σ.symm.toEmbedding =
          Function.Embedding.refl _ by ext; simp, Finset.map_refl, ← h, ← Submodule.map_comp,
        ← Matrix.toLin'_mul, hW'W, Matrix.toLin'_one, Submodule.map_id] at this
    have hXX : qubitX * qubitX = 1 := pauli_sq Pauli.X
    have e0 : wordOp ![Pauli.X, Pauli.X, Pauli.X, Pauli.X, Pauli.I, Pauli.I] =
        wordOp (Splus 0) * wordOp (Splus 1) := by
      unfold wordOp
      rw [tensor_mul]
      congr 1
      funext i
      fin_cases i <;> simp [Splus, pauliMatrix, hXX]
    have d0 : outerSpan {0, 1, 2, 3} (codespace Splus) ≠ ⊤ :=
      outer_deficient ![Pauli.X, Pauli.X, Pauli.X, Pauli.X, Pauli.I, Pauli.I] _ _ (by decide)
        (fun ψ hψ => by
        rw [e0, ← Matrix.mulVec_mulVec, (mem_codespace Splus ψ).1 hψ 1,
          (mem_codespace Splus ψ).1 hψ 0]) 0 (Or.inl rfl)
    have d1 : outerSpan {0, 1, 4, 5} (codespace Splus) ≠ ⊤ :=
      outer_deficient (Splus 0) _ _ (by decide) (fun ψ hψ => (mem_codespace Splus ψ).1 hψ 0) 0
        (Or.inl rfl)
    have b0 := back _ rfl d0
    have b1 := back _ rfl d1
    have := b0.trans b1.symm
    rw [Finset.map_inj] at this
    exact absurd this (by decide)

end D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
