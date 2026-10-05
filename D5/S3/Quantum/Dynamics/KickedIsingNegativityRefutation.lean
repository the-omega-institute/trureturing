/- GID: D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/KickedIsingNegativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.claim; result=D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.result; claim=D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.claim
   digest: Pathak's generic-state negativity identity fails on a four-site kicked Ising chain. -/

/-
proof_shape: result: bind-only (literal matrix exponentials, pinned spectral and trace
  identities, explicit similarity certificates, and finite normalization)
escape_witness: none
admission_basis: open-problem-resolution (#13296; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/FiniteDimensional (qubitX, qubitZ, qubit_weyl_star);
    statement_id: sha256:8448b6959a48d5c232600cbaa512d3eae6aadd57de71f1e30aad67fde1d1b63d
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence (localOp, tensorOp);
    statement_id: sha256:846c275369c21d39da3e6b45a6afc81f012eb06968afa6b9e2d50546ac42f34c
  D5/S3/Quantum/Information/PartialTraceMutualInformation (partialTraceLeft, partialTraceRight);
    statement_id: sha256:b0ff98d7c7f04df0208d92f8f2cf8e39c0d7b5b5f43944b80e7320848a03e918
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum (Outside);
    statement_id: sha256:87c4a3cae46e43203f1199d25a532167e7f7081fce502b7a09424e459bcfdfae
  D5/S3/Quantum/Foundation/FiniteTraceDistance (traceNorm);
    statement_id: sha256:9b295fcfd5b3b568c1df1d53f97c9cef0dc418f471d270157fc9be6a66e7db1a
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation (fourEquiv, singleEquiv, outEquiv);
    statement_id: sha256:e7efbd1d60f0205eef68cba24dd2ef797a820ce4f439f21f7bc4166b3b7eafa9
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation (partialTransposeB);
    statement_id: sha256:9e510b8c5b18a5e69ee1ce5140fa22b275f3f952eb0a2a8a7e232294c214129c
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (localOp tensorOp)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum (Outside)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation
  (fourEquiv singleEquiv outEquiv)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (partialTransposeB)

/-- The Ising Hamiltonian at J = π/4. -/
noncomputable def hIsing {L : ℕ} (h : Fin L → ℝ) :
    Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  ((Real.pi / 4 : ℝ) : ℂ) • (∑ i, localOp i qubitZ * localOp (finRotate L i) qubitZ) +
    ∑ i, (h i : ℂ) • localOp i qubitZ

/-- The kick Hamiltonian at b = -π/4. -/
noncomputable def hKick (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  ((-Real.pi / 4 : ℝ) : ℂ) • ∑ i : Fin L, localOp i qubitX

/-- U = exp(-i H_K) exp(-i H_I). -/
noncomputable def floquet {L : ℕ} (h : Fin L → ℝ) :
    Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  NormedSpace.exp (-Complex.I • hKick L) * NormedSpace.exp (-Complex.I • hIsing h)

/-- The product-state amplitudes in the computational basis. -/
noncomputable def initial {L : ℕ} (θ φ : Fin L → ℝ) : (Fin L → Fin 2) → ℂ :=
  fun x => ∏ i, if x i = 0 then (Real.cos (θ i / 2) : ℂ)
    else Complex.exp (Complex.I * (φ i : ℂ)) * (Real.sin (θ i / 2) : ℂ)

/-- Neither the transverse class nor the longitudinal class. -/
def generic {L : ℕ} (θ : Fin L → ℝ) : Prop :=
  ¬ (∀ i, θ i = Real.pi / 2) ∧ ¬ (∀ i, θ i = 0 ∨ θ i = Real.pi)

/-- Half-order Rényi entropy: twice the logarithm of the trace of the matrix square root. -/
noncomputable def renyiHalf {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ :=
  2 * Real.log (Matrix.trace (cfc Real.sqrt ρ)).re

/-- A contiguous cyclic partition, with two cuts after a and b sites. -/
def contiguous {L : ℕ} (A B C : Finset (Fin L)) : Prop :=
  ∃ o a b : ℕ, 0 < a ∧ a < b ∧ b < L ∧
    A = Finset.univ.filter (fun i => ((finRotate L ^ o) i).val < a) ∧
    B = Finset.univ.filter (fun i => a ≤ ((finRotate L ^ o) i).val ∧
      ((finRotate L ^ o) i).val < b) ∧
    C = Finset.univ.filter (fun i => b ≤ ((finRotate L ^ o) i).val)

/-- Join A, B and the traced-out complement in the computational basis. -/
def joinParts {L : ℕ} (A B : Finset (Fin L))
    (x : A → Fin 2) (y : B → Fin 2) (z : Outside (A ∪ B) → Fin 2) : Fin L → Fin 2 :=
  fun i => if hA : i ∈ A then x ⟨i,hA⟩ else
    if hB : i ∈ B then y ⟨i,hB⟩ else
      z ⟨i,Finset.notMem_union.mpr ⟨hA,hB⟩⟩

/-- The joint reduced state, using the frozen subsystem partial trace. -/
noncomputable def reducedAB {L : ℕ} (A B : Finset (Fin L))
    (ψ : (Fin L → Fin 2) → ℂ) :
    Matrix ((A → Fin 2) × (B → Fin 2)) ((A → Fin 2) × (B → Fin 2)) ℂ :=
  partialTraceRight (vecMulVec
    (fun p : ((A → Fin 2) × (B → Fin 2)) × (Outside (A ∪ B) → Fin 2) =>
      ψ (joinParts A B p.1.1 p.1.2 p.2))
    (star (fun p : ((A → Fin 2) × (B → Fin 2)) × (Outside (A ∪ B) → Fin 2) =>
      ψ (joinParts A B p.1.1 p.1.2 p.2))))

/-- Partial transposition on the B factor, allowing unequal factor dimensions. -/
def partialTranspose {A B : Type*} (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun p q => ρ (p.1,q.2) (q.1,p.2)

/-- The state after integer Floquet time t. -/
noncomputable def evolved {L : ℕ} (h θ φ : Fin L → ℝ) (t : ℤ) :
    (Fin L → Fin 2) → ℂ := (floquet h ^ t) *ᵥ initial θ φ

/-- Logarithmic negativity of a bipartite state. -/
noncomputable def logNegativity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.log (traceNorm (partialTranspose ρ))

/-- Half-order Rényi mutual information. -/
noncomputable def mutualHalf {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  renyiHalf (partialTraceRight ρ) + renyiHalf (partialTraceLeft ρ) - renyiHalf ρ

/-- Conjecture 1 at α=1/2 for the periodic dual-unitary kicked Ising chain. -/
def claim : Prop :=
  ∀ (L : ℕ) (h θ φ : Fin L → ℝ) (A B C : Finset (Fin L)) (t : ℤ),
    contiguous A B C → generic θ →
      2 * logNegativity (reducedAB A B (evolved h θ φ t)) =
        mutualHalf (reducedAB A B (evolved h θ φ t))

private noncomputable def witnessTheta : Fin 4 → ℝ :=
  ![Real.pi/2,Real.pi/2,2*Real.arctan (1/2),2*Real.arctan (1/2)]

private noncomputable def psiInitial : (Fin 4 → Fin 2) → ℂ :=
  fun x => ((if x 2 = 0 then 2 else 1) * (if x 3 = 0 then 2 else 1) : ℂ) / 10

private noncomputable def graphOp : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  diagonal (fun x => ∏ i : Fin 4, (if x i = 1 ∧ x (finRotate 4 i) = 1 then -1 else 1))

private noncomputable def singleGate : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX) *
    NormedSpace.exp (-Complex.I • qubitZ) * qubitZ

private noncomputable def sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => (!![1/4,3/20,3/20,-9/100; 3/20,1/4,9/100,-3/20;
    3/20,9/100,1/4,-3/20; -9/100,-3/20,-3/20,1/4] : Matrix (Fin 4) (Fin 4) ℂ)
    (finProdFinEquiv x) (finProdFinEquiv y)

private noncomputable def graphBasis : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x.1 = 0 then (if x.2 = 0 then 1 else if y.2 = 0 then 1 else -1)
    else if x.2 = 0 then (if y.1 = 0 then 1 else -1)
    else if y.1 = y.2 then -1 else 1

private noncomputable def sigmaValues : Fin 2 × Fin 2 → ℝ :=
  fun x => if x = (0,0) then 16/25 else if x = (1,1) then 1/25 else 4/25

private noncomputable def ptValues : Fin 2 × Fin 2 → ℝ :=
  fun x => if x = (0,0) then 23/50 else if x = (1,1) then -7/50 else 17/50

private noncomputable def blockEquiv : (Fin 4 → Fin 2) ≃ (Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
  fourEquiv.trans (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)).symm

private noncomputable def singlePair :
    ((↥({0} : Finset (Fin 4)) → Fin 2) × (↥({1} : Finset (Fin 4)) → Fin 2)) ≃
      Fin 2 × Fin 2 := Equiv.prodCongr (singleEquiv 0) (singleEquiv 1)

private noncomputable def psiGraph : (Fin 4 → Fin 2) → ℂ := graphOp *ᵥ psiInitial

set_option maxHeartbeats 4000000 in
/-- The four-site generic product state violates Conjecture 1 at α = 1/2. -/
theorem result : ¬ claim := by
  classical
  let zValue (a : Fin 2) : ℂ := if a = 0 then 1 else -1
  let graphPhase (a b : Fin 2) : ℂ := if a = 1 ∧ b = 1 then -1 else 1
  let realSpectrum {n : Type} [Fintype n] [DecidableEq n]
      (ρ : Matrix n n ℂ) : Multiset ℝ :=
    if h : ρ.IsHermitian then Finset.univ.val.map h.eigenvalues else 0
  have witness_generic : generic witnessTheta := by
    constructor
    · intro h
      have hi := h 2
      have ht : Real.arctan (1/2 : ℝ) < Real.pi/4 := by
        rw [← Real.arctan_one]
        exact Real.arctan_strictMono (by norm_num)
      change 2 * Real.arctan (1/2 : ℝ) = Real.pi/2 at hi
      linarith
    · intro h
      have hi := h 0
      simp only [witnessTheta, Matrix.cons_val_zero] at hi
      rcases hi with hi | hi <;> linarith [Real.pi_pos]
  have initial_witness :
      initial witnessTheta (fun _ => 0) = psiInitial := by
    have hroot5 : Real.sqrt (5/4 : ℝ) = Real.sqrt 5 / 2 := by
      rw [Real.sqrt_div (by norm_num), show Real.sqrt (4 : ℝ) = 2 by norm_num]
    have hc : Real.cos (Real.arctan (1/2 : ℝ)) = 2 / Real.sqrt 5 := by
      rw [Real.cos_arctan]
      norm_num [Real.sqrt_div] <;> ring
    have hs : Real.sin (Real.arctan (1/2 : ℝ)) = 1 / Real.sqrt 5 := by
      rw [Real.sin_arctan]
      norm_num [Real.sqrt_div] <;> ring
    simp only [one_div] at hc hs
    have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hsq5 : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    have hne5 : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)))
    have hcos (i : Fin 4) : Real.cos (witnessTheta i / 2) =
        if i = 0 ∨ i = 1 then Real.sqrt 2 / 2 else 2 / Real.sqrt 5 := by
      fin_cases i <;> simp [witnessTheta,Matrix.vecHead,Matrix.vecTail,
        Matrix.cons_val_two,Matrix.cons_val_three,
        show Real.pi/2/2 = Real.pi/4 by ring,
        Real.cos_pi_div_four,hc]
    have hsin (i : Fin 4) : Real.sin (witnessTheta i / 2) =
        if i = 0 ∨ i = 1 then Real.sqrt 2 / 2 else 1 / Real.sqrt 5 := by
      fin_cases i <;> simp [witnessTheta,Matrix.vecHead,Matrix.vecTail,
        Matrix.cons_val_two,Matrix.cons_val_three,
        show Real.pi/2/2 = Real.pi/4 by ring,
        Real.sin_pi_div_four,hs]
    ext x
    simp only [initial,Fin.prod_univ_four,hcos,hsin]
    by_cases h2 : x 2 = 0 <;> by_cases h3 : x 3 = 0 <;>
      simp [psiInitial,h2,h3] <;> push_cast <;> field_simp <;>
      ring_nf <;> norm_num [hsq2,hsq5]
  have tensor_mul {n : ℕ} (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      tensorOp M * tensorOp N = tensorOp (fun i => M i * N i) := by
    ext x z
    simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
    simp_rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have tensor_one {n : ℕ} :
      tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    ext x y
    simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hc
        exact h (funext fun i => not_not.1 fun hi => hc ⟨i, hi⟩)
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have tensor_star {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      (tensorOp M)ᴴ = tensorOp (fun i => (M i)ᴴ) := by
    ext x y
    simp [tensorOp, Matrix.conjTranspose_apply, star_prod]
  have tensor_update_apply {n : ℕ} (N : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin n → Fin 2) :
      tensorOp (Function.update N j A) x y =
        A (x j) (y j) * ∏ i ∈ Finset.univ.erase j, N i (x i) (y i) := by
    simp only [tensorOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have local_add {n : ℕ} (j : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
      localOp j (A + B) = localOp j A + localOp j B := by
    ext x y
    simp only [localOp, tensor_update_apply, Matrix.add_apply, add_mul]
  have local_smul {n : ℕ} (j : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
      localOp j (c • A) = c • localOp j A := by
    ext x y
    simp only [localOp, tensor_update_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  have local_mul {n : ℕ} (j : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
      localOp j A * localOp j B = localOp j (A * B) := by
    unfold localOp
    rw [tensor_mul]
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  have local_one {n : ℕ} (j : Fin n) :
      localOp j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    unfold localOp
    rw [Function.update_eq_self_iff.2 rfl, tensor_one]
  let siteHom {n : ℕ} (j : Fin n) :
      Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    {
      toFun := localOp j,
      map_zero' := by ext x y; simp [localOp, tensor_update_apply],
      map_one' := local_one j,
      map_mul' := fun A B => (local_mul j A B).symm,
      map_add' := local_add j,
      commutes' := by
        intro c
        rw [Algebra.algebraMap_eq_smul_one, local_smul, local_one]
        exact (Algebra.algebraMap_eq_smul_one c).symm
    }
  have exp_local {n : ℕ} (j : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
      NormedSpace.exp (localOp j A) = localOp j (NormedSpace.exp A) := by
    letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    exact (NormedSpace.map_exp (siteHom j)
      ((siteHom j).toLinearMap.continuous_of_finiteDimensional) A).symm
  have local_commute {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
      (A B : Matrix (Fin 2) (Fin 2) ℂ) : Commute (localOp j A) (localOp k B) := by
    unfold Commute SemiconjBy localOp
    rw [tensor_mul, tensor_mul]
    congr 1
    funext i
    by_cases hij : i = j
    · subst i; simp [Function.update_of_ne hjk]
    · by_cases hik : i = k
      · subst i; simp [Function.update_of_ne (Ne.symm hjk)]
      · simp [Function.update_of_ne hij, Function.update_of_ne hik]
  have four_local_product (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
      localOp (0 : Fin 4) A * localOp 1 B * localOp 2 C * localOp 3 D =
        tensorOp ![A,B,C,D] := by
    unfold localOp
    rw [tensor_mul, tensor_mul, tensor_mul]
    congr 1
    funext i
    fin_cases i <;> simp
  have kick_factor :
      NormedSpace.exp (-Complex.I • hKick 4) =
        tensorOp (fun _ : Fin 4 => NormedSpace.exp
          ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX)) := by
    letI : NormedAlgebra ℚ (Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    set K := (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX
    have heq : -Complex.I • hKick 4 =
        localOp 0 K + localOp 1 K + localOp 2 K + localOp 3 K := by
      have hc : -Complex.I * ((-Real.pi / 4 : ℝ) : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      simp only [hKick, Fin.sum_univ_four, smul_add, smul_smul, hc, ← local_smul, K]
    rw [heq]
    have h01 := local_commute (0 : Fin 4) 1 (by decide) K K
    have h02 := local_commute (0 : Fin 4) 2 (by decide) K K
    have h03 := local_commute (0 : Fin 4) 3 (by decide) K K
    have h12 := local_commute (1 : Fin 4) 2 (by decide) K K
    have h13 := local_commute (1 : Fin 4) 3 (by decide) K K
    have h23 := local_commute (2 : Fin 4) 3 (by decide) K K
    rw [NormedSpace.exp_add_of_commute ((h03.add_left h13).add_left h23),
      NormedSpace.exp_add_of_commute (h02.add_left h12),
      NormedSpace.exp_add_of_commute h01, exp_local, exp_local, exp_local, exp_local,
      four_local_product]
    rfl
  have local_diagonal {n : ℕ} (j : Fin n) (v : Fin 2 → ℂ) :
      localOp j (diagonal v) = diagonal (fun x => v (x j)) := by
    ext x y
    simp only [localOp, tensorOp, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst y
      simp only [ite_true]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      simp only [Function.update_self, Matrix.diagonal_apply_eq]
      have ht : ∏ i ∈ Finset.univ.erase j,
          Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j (diagonal v) i (x i) (x i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        simp
      rw [ht, mul_one]
    · rw [if_neg h]
      obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hc
        exact h (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_cases hij : i = j
      · subst i; simp [hi]
      · rw [Function.update_of_ne hij]; simp [hi]
  have qubitZ_diagonal : qubitZ = diagonal zValue := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [qubitZ,zValue,diagonal]
  have ising_diagonal {L : ℕ} (h : Fin L → ℝ) :
      hIsing h = diagonal (fun x : Fin L → Fin 2 =>
        ((Real.pi / 4 : ℝ) : ℂ) * (∑ i, zValue (x i) * zValue (x (finRotate L i))) +
          ∑ i, (h i : ℂ) * zValue (x i)) := by
    simp only [hIsing, qubitZ_diagonal, local_diagonal, diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst y; simp [Matrix.diagonal, Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum]
    · simp [Matrix.diagonal, Matrix.sum_apply, Matrix.of_apply, hxy]
  have rotate4 (i : Fin 4) : finRotate 4 i = ![1,2,3,0] i := by
    fin_cases i <;> decide
  have four_ising_phase (x : Fin 4 → Fin 2) :
      Complex.exp (-Complex.I * ((Real.pi / 4 : ℝ) : ℂ) *
          (∑ i : Fin 4, zValue (x i) * zValue (x (finRotate 4 i)))) =
        -(∏ i : Fin 4, zValue (x i)) *
          (∏ i : Fin 4, graphPhase (x i) (x (finRotate 4 i))) := by
    have hplus : Complex.exp (-Complex.I * ((Real.pi / 4 : ℝ) : ℂ) * 4) = -1 := by
      have he : -Complex.I * ((Real.pi / 4 : ℝ) : ℂ) * 4 = -(Real.pi * Complex.I) := by
        push_cast; ring
      rw [he]; exact Complex.exp_neg_pi_mul_I
    have hminus : Complex.exp (-Complex.I * ((Real.pi / 4 : ℝ) : ℂ) * (-4)) = -1 := by
      have he : -Complex.I * ((Real.pi / 4 : ℝ) : ℂ) * (-4) = Real.pi * Complex.I := by
        push_cast; ring
      rw [he]; exact Complex.exp_pi_mul_I
    norm_num at hplus hminus
    have hx : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [Fin.sum_univ_four, Fin.prod_univ_four, zValue, graphPhase, rotate4,
        Matrix.cons_val_two, Matrix.cons_val_three, hplus,hminus] <;>
        first | exact hplus | exact hminus |
          (ring_nf; simp [mul_comm, Complex.exp_neg_pi_mul_I, Complex.exp_pi_mul_I])
  have ising_factor :
      NormedSpace.exp (-Complex.I • hIsing (fun _ : Fin 4 => (1 : ℝ))) =
        -tensorOp (fun _ : Fin 4 => NormedSpace.exp (-Complex.I • qubitZ) * qubitZ) *
          graphOp := by
    have hd : -Complex.I • hIsing (fun _ : Fin 4 => (1 : ℝ)) =
        diagonal (fun x : Fin 4 → Fin 2 =>
          -Complex.I * (((Real.pi / 4 : ℝ) : ℂ) *
            (∑ i, zValue (x i) * zValue (x (finRotate 4 i))) + ∑ i, zValue (x i))) := by
      rw [ising_diagonal, ← Matrix.diagonal_smul]
      simp
    rw [hd,Matrix.exp_diagonal]
    have htd : tensorOp (fun _ : Fin 4 => NormedSpace.exp (-Complex.I • qubitZ) * qubitZ) =
        diagonal (fun x => ∏ i : Fin 4, Complex.exp (-Complex.I * zValue (x i)) * zValue (x i)) := by
      rw [qubitZ_diagonal]
      simp only [← diagonal_smul, exp_diagonal, diagonal_mul_diagonal]
      ext x y
      by_cases h : x = y
      · subst y
        simp [tensorOp,Matrix.diagonal,zValue,← Complex.exp_eq_exp_ℂ]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hx : x i = 0 <;> simp [hx]
      · obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
          by_contra hc
          exact h (funext fun i => not_not.1 fun hi => hc ⟨i,hi⟩)
        simp only [tensorOp,Matrix.of_apply,Matrix.diagonal_apply,if_neg h]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [htd]
    simp only [graphOp, Matrix.neg_mul, diagonal_mul_diagonal]
    rw [Matrix.diagonal_neg]
    congr 1
    funext x
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    change Complex.exp (-Complex.I *
      (((Real.pi / 4 : ℝ) : ℂ) * (∑ i, zValue (x i) * zValue (x (finRotate 4 i))) +
        ∑ i, zValue (x i))) = _
    have hf : Complex.exp (-Complex.I * (∑ i : Fin 4, zValue (x i))) =
        ∏ i : Fin 4, Complex.exp (-Complex.I * zValue (x i)) := by
      rw [Finset.mul_sum, Complex.exp_sum]
    rw [mul_add, Complex.exp_add, hf, ← mul_assoc (-Complex.I),
      four_ising_phase, Finset.prod_mul_distrib]
    ring
  have floquet_factor :
      floquet (fun _ : Fin 4 => (1 : ℝ)) =
        -tensorOp (fun _ : Fin 4 => singleGate) * graphOp := by
    rw [floquet,kick_factor,ising_factor,← Matrix.mul_assoc,
      Matrix.mul_neg, tensor_mul]
    simp only [singleGate,Matrix.mul_assoc]
  have singleGate_unitary : singleGateᴴ * singleGate = 1 := by
    let : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    have hK : (NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX))ᴴ *
        NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX) = 1 := by
      have hself : IsSelfAdjoint qubitX := qubit_weyl_star.2.1
      have hsk : (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX ∈
          skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
        hself.smul_mem_skewAdjoint (by
          change star (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
            -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
          simp [Complex.star_def])
      exact (Unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hsk)).1
    have hF : (NormedSpace.exp (-Complex.I • qubitZ))ᴴ *
        NormedSpace.exp (-Complex.I • qubitZ) = 1 := by
      have hself : IsSelfAdjoint qubitZ := qubit_weyl_star.2.2.1
      have hsk : -Complex.I • qubitZ ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
        hself.smul_mem_skewAdjoint (by
          change star (-Complex.I) = -(-Complex.I)
          simp [Complex.star_def])
      exact (Unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hsk)).1
    have hZ : qubitZᴴ * qubitZ = 1 := by
      rw [show qubitZᴴ = qubitZ from qubit_weyl_star.2.2.1,← pow_two]
      exact qubit_weyl_star.2.2.2.2
    simp only [singleGate,Matrix.conjTranspose_mul]
    calc
      _ = qubitZᴴ * ((NormedSpace.exp (-Complex.I • qubitZ))ᴴ *
        ((NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX))ᴴ *
          NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • qubitX)) *
            NormedSpace.exp (-Complex.I • qubitZ)) * qubitZ := by
              simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hK,Matrix.mul_one,hF,Matrix.mul_one,hZ]
  have spectralBridge {n : Type} [Fintype n] [DecidableEq n]
      (A Q R : Matrix n n ℂ) (hA : A.IsHermitian) (v : n → ℝ)
      (hRQ : R * Q = 1) (hdiag : Q * diagonal (fun i => (v i : ℂ)) * R = A) :
      realSpectrum A = Finset.univ.val.map v := by
    have hc : A.charpoly = (diagonal (fun i => (v i : ℂ))).charpoly := by
      rw [← hdiag, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hRQ, Matrix.one_mul]
    have hroots : (diagonal (fun i => (v i : ℂ))).charpoly.roots =
        Finset.univ.val.map (fun i => (v i : ℂ)) := by
      rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
    have hr := congrArg (Multiset.map Complex.re)
      (hA.roots_charpoly_eq_eigenvalues.symm.trans
        ((congrArg Polynomial.roots hc).trans hroots))
    simpa [realSpectrum, hA, Multiset.map_map, Function.comp_def] using hr
  have sigma_spectra :
      realSpectrum sigma = ({16/25,4/25,4/25,1/25} : Multiset ℝ) ∧
      realSpectrum (partialTransposeB sigma) = ({23/50,17/50,17/50,-7/50} : Multiset ℝ) := by
    have hRQ : ((1/4 : ℂ) • graphBasisᴴ) * graphBasis = 1 := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [graphBasis, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
          Matrix.one_apply]
    have hH : sigma.IsHermitian := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [sigma, finProdFinEquiv]
    have hTH : (partialTransposeB sigma).IsHermitian := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [sigma, partialTransposeB, finProdFinEquiv]
    have hD : graphBasis * diagonal (fun i => (sigmaValues i : ℂ)) *
        ((1/4 : ℂ) • graphBasisᴴ) = sigma := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [sigma, finProdFinEquiv, sigmaValues, graphBasis, Matrix.mul_apply, Matrix.mul_diagonal,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    have hTD : graphBasis * diagonal (fun i => (ptValues i : ℂ)) *
        ((1/4 : ℂ) • graphBasisᴴ) = partialTransposeB sigma := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [sigma, finProdFinEquiv, partialTransposeB, ptValues, graphBasis, Matrix.mul_apply,
          Matrix.mul_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two]
    have hu : (Finset.univ : Finset (Fin 2 × Fin 2)).val =
        ({(0,0),(0,1),(1,0),(1,1)} : Multiset (Fin 2 × Fin 2)) := by decide
    constructor
    · rw [spectralBridge sigma graphBasis _ hH sigmaValues hRQ hD, hu]
      norm_num [sigmaValues]
    · rw [spectralBridge _ graphBasis _ hTH ptValues hRQ hTD, hu]
      norm_num [ptValues]
  have renyi_spectrum {n : Type} [Fintype n] [DecidableEq n]
      (A : Matrix n n ℂ) :
      renyiHalf A = 2 * Real.log (((realSpectrum A).map Real.sqrt).sum) := by
    classical
    by_cases h : A.IsHermitian
    · rw [renyiHalf, Matrix.IsHermitian.cfc_eq h, Matrix.IsHermitian.cfc]
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      simp [realSpectrum, h, Multiset.map_map, Function.comp_def]
    · have hcfc : cfc Real.sqrt A = 0 :=
        cfc_apply_of_not_predicate A (show ¬ IsSelfAdjoint A from h)
      simp [renyiHalf, realSpectrum, h, hcfc]
  have traceNorm_spectrum {n : Type} [Fintype n] [DecidableEq n]
      (A : Matrix n n ℂ) (hA : A.IsHermitian) :
      traceNorm A = ((realSpectrum A).map abs).sum := by
    unfold traceNorm
    rw [← Matrix.star_eq_conjTranspose, ← CFC.abs, CFC.abs_eq_cfc_norm A hA,
      Matrix.IsHermitian.cfc_eq hA, Matrix.IsHermitian.cfc]
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp [realSpectrum, hA, Multiset.map_map, Function.comp_def, Real.norm_eq_abs]
  have sigma_measures :
      traceNorm (partialTransposeB sigma) = 32 / 25 ∧
      renyiHalf sigma = 2 * Real.log (9 / 5) ∧
      renyiHalf (partialTraceRight sigma) = Real.log 2 ∧
      renyiHalf (partialTraceLeft sigma) = Real.log 2 := by
    have hH : (partialTransposeB sigma).IsHermitian := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [sigma, partialTransposeB, finProdFinEquiv]
    have hsr : partialTraceRight sigma = diagonal (fun _ : Fin 2 => (1/2 : ℂ)) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [partialTraceRight, sigma, Fin.sum_univ_two, finProdFinEquiv, Matrix.diagonal]
    have hsl : partialTraceLeft sigma = diagonal (fun _ : Fin 2 => (1/2 : ℂ)) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [partialTraceLeft, sigma, Fin.sum_univ_two, finProdFinEquiv, Matrix.diagonal]
    have hsp : realSpectrum (diagonal (fun _ : Fin 2 => (1/2 : ℂ))) =
        ({1/2,1/2} : Multiset ℝ) := by
      have hdiag : (diagonal (fun _ : Fin 2 => (1/2 : ℂ))).IsHermitian := by
        exact Matrix.isHermitian_diagonal_iff.mpr (by intro i; simp)
      rw [spectralBridge _ 1 1 hdiag (fun _ => 1/2) (by simp) (by simp)]
      have hu : (Finset.univ : Finset (Fin 2)).val = ({0,1} : Multiset (Fin 2)) := by decide
      rw [hu]
      simp
    have hsqrt (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a ^ 2) = a := by
      rw [Real.sqrt_sq ha]
    have hroot16 : Real.sqrt (16/25 : ℝ) = 4/5 := by
      convert hsqrt (4/5) (by norm_num) using 1 <;> norm_num
    have hroot4 : Real.sqrt (4/25 : ℝ) = 2/5 := by
      convert hsqrt (2/5) (by norm_num) using 1 <;> norm_num
    have hroot1 : Real.sqrt (1/25 : ℝ) = 1/5 := by
      convert hsqrt (1/5) (by norm_num) using 1 <;> norm_num
    have hmarg : renyiHalf (diagonal (fun _ : Fin 2 => (1/2 : ℂ))) = Real.log 2 := by
      rw [renyi_spectrum, hsp]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton]
      have hp : 0 < Real.sqrt (1/2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      have he : (Real.sqrt (1/2 : ℝ) + Real.sqrt (1/2 : ℝ)) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
      have hl := Real.log_pow (Real.sqrt (1/2 : ℝ) + Real.sqrt (1/2 : ℝ)) 2
      rw [he] at hl
      simpa using hl.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [traceNorm_spectrum _ hH, sigma_spectra.2]
      norm_num
    · rw [renyi_spectrum, sigma_spectra.1]
      norm_num [hroot16, hroot4, hroot1]
    · rw [hsr]; exact hmarg
    · rw [hsl]; exact hmarg
  have sigma_obstruction :
      2 * Real.log (traceNorm (partialTransposeB sigma)) ≠
        renyiHalf (partialTraceRight sigma) + renyiHalf (partialTraceLeft sigma) -
          renyiHalf sigma := by
    obtain ⟨hN,hS,hA,hB⟩ := sigma_measures
    rw [hN,hS,hA,hB]
    have hE : 2 * Real.log (32/25 : ℝ) = Real.log (1024/625 : ℝ) := by
      have hp := Real.log_pow (32/25 : ℝ) 2
      norm_num at hp
      exact hp.symm
    have hI : Real.log (2 : ℝ) + Real.log 2 - 2 * Real.log (9/5 : ℝ) =
        Real.log (100/81 : ℝ) := by
      have hp := Real.log_pow (10/9 : ℝ) 2
      norm_num at hp
      have hd : Real.log (10/9 : ℝ) = Real.log 2 - Real.log (9/5) := by
        rw [show (10/9 : ℝ) = 2 / (9/5) by norm_num]
        exact Real.log_div (by norm_num) (by norm_num)
      rw [hd] at hp
      linarith
    rw [hE,hI]
    intro h
    have heq : (1024/625 : ℝ) = 100/81 :=
      Real.log_injOn_pos (by norm_num) (by norm_num) h
    have hcross : (20736 : ℝ) = 15625 := by linarith
    have hne : (20736 : ℝ) ≠ 15625 := by norm_num
    exact hne hcross
  have spectrum_conjugate {n : Type} [Fintype n] [DecidableEq n]
      (A V : Matrix n n ℂ) (hA : A.IsHermitian) (hV : Vᴴ * V = 1) :
      realSpectrum (V * A * Vᴴ) = realSpectrum A := by
    have hH := Matrix.isHermitian_mul_mul_conjTranspose V hA
    have hc : (V * A * Vᴴ).charpoly = A.charpoly := by
      rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    have he := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hH hA).mpr hc
    simp [realSpectrum,hH,hA,he]
  have renyi_conjugate {n : Type} [Fintype n] [DecidableEq n]
      (A V : Matrix n n ℂ) (hA : A.IsHermitian) (hV : Vᴴ * V = 1) :
      renyiHalf (V * A * Vᴴ) = renyiHalf A := by
    rw [renyi_spectrum, renyi_spectrum, spectrum_conjugate A V hA hV]
  have norm_conjugate {n : Type} [Fintype n] [DecidableEq n]
      (A V : Matrix n n ℂ) (hA : A.IsHermitian) (hV : Vᴴ * V = 1) :
      traceNorm (V * A * Vᴴ) = traceNorm A := by
    rw [traceNorm_spectrum _ (Matrix.isHermitian_mul_mul_conjTranspose V hA),
      traceNorm_spectrum A hA, spectrum_conjugate A V hA hV]
  have pt_local (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (U V : Matrix (Fin 2) (Fin 2) ℂ) :
      partialTransposeB ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) =
        (U ⊗ₖ V.map star) * partialTransposeB ρ * (U ⊗ₖ V.map star)ᴴ := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp [partialTransposeB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have conjugate_unitary {n : Type} [Fintype n] [DecidableEq n]
      (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
      (U.map star)ᴴ * U.map star = 1 := by
    have hs : (U.map star)ᴴ = (Uᴴ).map star := by
      ext a b
      simp [Matrix.conjTranspose_apply]
    rw [hs]
    have he := congrArg (fun A : Matrix n n ℂ => A.map (starRingEnd ℂ)) hU
    change (Uᴴ).map (starRingEnd ℂ) * U.map (starRingEnd ℂ) = 1
    simpa [Matrix.map_mul] using he
  have tensor_pair_unitary {a b : Type} [Fintype a] [Fintype b]
      [DecidableEq a] [DecidableEq b]
      (U : Matrix a a ℂ) (V : Matrix b b ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
      (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
      Matrix.one_kronecker_one]
  have trace_conjugate_right {a b : Type} [Fintype a] [Fintype b]
      [DecidableEq a] [DecidableEq b]
      (ρ : Matrix (a × b) (a × b) ℂ) (V : Matrix b b ℂ) (hV : Vᴴ * V = 1) :
      partialTraceRight (((1 : Matrix a a ℂ) ⊗ₖ V) * ρ *
        ((1 : Matrix a a ℂ) ⊗ₖ V)ᴴ) = partialTraceRight ρ := by
    ext i j
    have htr : trace (V * (ρ.submatrix (fun k => (i,k)) (fun k => (j,k))) * Vᴴ) =
        trace (ρ.submatrix (fun k => (i,k)) (fun k => (j,k))) := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    simpa [partialTraceRight, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_kronecker, Matrix.one_apply, Fintype.sum_prod_type] using htr
  have trace_conjugate_left {a b : Type} [Fintype a] [Fintype b]
      [DecidableEq a] [DecidableEq b]
      (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ) :
      partialTraceRight ((U ⊗ₖ (1 : Matrix b b ℂ)) * ρ *
        (U ⊗ₖ (1 : Matrix b b ℂ))ᴴ) = U * partialTraceRight ρ * Uᴴ := by
    ext i j
    simp only [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_kronecker,
      Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply,
      Matrix.conjTranspose_one, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext k
    rw [Finset.sum_comm]
    congr 1
    funext l
    congr 1
    funext m
    simp only [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_mul]
  have trace_local_right {a b : Type} [Fintype a] [Fintype b]
      [DecidableEq a] [DecidableEq b]
      (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ) (V : Matrix b b ℂ)
      (hV : Vᴴ * V = 1) :
      partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) =
        U * partialTraceRight ρ * Uᴴ := by
    have hf : U ⊗ₖ V = (U ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ V) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hf,Matrix.conjTranspose_mul]
    have he : (((U ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ V)) * ρ) *
        (((1 : Matrix a a ℂ) ⊗ₖ V)ᴴ * (U ⊗ₖ (1 : Matrix b b ℂ))ᴴ) =
        (U ⊗ₖ (1 : Matrix b b ℂ)) *
          (((1 : Matrix a a ℂ) ⊗ₖ V) * ρ * ((1 : Matrix a a ℂ) ⊗ₖ V)ᴴ) *
            (U ⊗ₖ (1 : Matrix b b ℂ))ᴴ := by simp only [Matrix.mul_assoc]
    rw [he,trace_conjugate_left,trace_conjugate_right ρ V hV]
  have trace_local_left {a b : Type} [Fintype a] [Fintype b]
      [DecidableEq a] [DecidableEq b]
      (ρ : Matrix (a × b) (a × b) ℂ) (U : Matrix a a ℂ) (V : Matrix b b ℂ)
      (hU : Uᴴ * U = 1) :
      partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) =
        V * partialTraceLeft ρ * Vᴴ := by
    let F := Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm a b)
    have hp (M : Matrix (a × b) (a × b) ℂ) :
        partialTraceLeft M = partialTraceRight (F M) := by ext i j; rfl
    have hv : F (U ⊗ₖ V) = V ⊗ₖ U := by
      ext ⟨i,j⟩ ⟨k,l⟩
      change U j l * V i k = V i k * U j l
      ring
    have hs (M : Matrix (a × b) (a × b) ℂ) : F Mᴴ = (F M)ᴴ := rfl
    rw [hp,map_mul,map_mul,hs,hv,trace_local_right _ V U hU,← hp]
  have local_invariance (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (U V : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.IsHermitian)
      (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
      traceNorm (partialTransposeB ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) =
        traceNorm (partialTransposeB ρ) ∧
      renyiHalf ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) = renyiHalf ρ ∧
      renyiHalf (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) =
        renyiHalf (partialTraceRight ρ) ∧
      renyiHalf (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) =
        renyiHalf (partialTraceLeft ρ) := by
    have hpt : (partialTransposeB ρ).IsHermitian := by
      ext ⟨a,b⟩ ⟨c,d⟩
      exact hρ.apply (a,d) (c,b)
    have hA : (partialTraceRight ρ).IsHermitian := by
      ext a b
      simp only [partialTraceRight, Matrix.conjTranspose_apply, star_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hρ.apply (a,i) (b,i)
    have hB : (partialTraceLeft ρ).IsHermitian := by
      ext a b
      simp only [partialTraceLeft, Matrix.conjTranspose_apply, star_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hρ.apply (i,a) (i,b)
    refine ⟨?_,?_,?_,?_⟩
    · rw [pt_local]
      exact norm_conjugate _ _ hpt (tensor_pair_unitary U (V.map star) hU
        (conjugate_unitary V hV))
    · exact renyi_conjugate ρ _ hρ (tensor_pair_unitary U V hU hV)
    · rw [trace_local_right _ U V hV]
      exact renyi_conjugate _ U hA hU
    · rw [trace_local_left _ U V hU]
      exact renyi_conjugate _ V hB hV
  have blockEquiv_symm (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
      blockEquiv.symm x = ![x.1.1,x.1.2,x.2.1,x.2.2] := rfl
  have block_tensor (W : Matrix (Fin 2) (Fin 2) ℂ) :
      reindex blockEquiv blockEquiv (tensorOp (fun _ : Fin 4 => W)) =
        (W ⊗ₖ W) ⊗ₖ (W ⊗ₖ W) := by
    ext ⟨⟨a,b⟩,⟨c,d⟩⟩ ⟨⟨e,f⟩,⟨g,h⟩⟩
    simp [tensorOp,reindex_apply,blockEquiv_symm,Fin.prod_univ_four,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,mul_assoc]
  have graph_reduced :
      partialTraceRight (reindex blockEquiv blockEquiv (vecMulVec psiGraph (star psiGraph))) =
        sigma := by
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [partialTraceRight,reindex_apply,blockEquiv_symm,vecMulVec_apply,
        psiGraph,graphOp,mulVec_diagonal,psiInitial,graphPhase,rotate4,
        Fin.prod_univ_four,Fin.sum_univ_two,Fintype.sum_prod_type,sigma,finProdFinEquiv,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
        map_mul,map_div₀,map_inv₀,map_ofNat]
  have physical_reduction (ψ : (Fin 4 → Fin 2) → ℂ) :
      reindex singlePair singlePair (reducedAB ({0} : Finset (Fin 4)) {1} ψ) =
        partialTraceRight (reindex blockEquiv blockEquiv (vecMulVec ψ (star ψ))) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [reindex_apply,submatrix_apply,reducedAB,partialTraceRight,vecMulVec_apply]
    erw [← Equiv.sum_comp (outEquiv 0 1 2 3 (by decide) (by decide) (by decide)
      (by intro i hi; fin_cases i <;> simp_all)).symm]
    rw [Fintype.sum_prod_type]
    have hk (a b c d : Fin 2) :
        joinParts ({0} : Finset (Fin 4)) {1} ((singleEquiv 0).symm a)
          ((singleEquiv 1).symm b)
          ((outEquiv 0 1 2 3 (by decide) (by decide) (by decide)
            (by intro i hi; fin_cases i <;> simp_all)).symm (c,d)) = ![a,b,c,d] := by
      funext i
      fin_cases i <;> simp [joinParts,singleEquiv,outEquiv,Equiv.symm_mk] <;> rfl
    have hs (a b : Fin 2) : singlePair.symm (a,b) =
        ((singleEquiv 0).symm a,(singleEquiv 1).symm b) := rfl
    simp only [hs,Pi.star_apply,hk,blockEquiv_symm,Fintype.sum_prod_type]
  have spectrum_reindex {n m : Type} [Fintype n] [Fintype m]
      [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A : Matrix n n ℂ) :
      realSpectrum (reindex e e A) = realSpectrum A := by
    classical
    by_cases hA : A.IsHermitian
    · have hB := hA.reindex e
      have hr := congrArg (Multiset.map Complex.re)
        (hB.roots_charpoly_eq_eigenvalues.symm.trans
          ((congrArg Polynomial.roots (Matrix.charpoly_reindex e A)).trans
            hA.roots_charpoly_eq_eigenvalues))
      simpa [realSpectrum,hA,hB,Multiset.map_map,Function.comp_def] using hr
    · have hB : ¬ (reindex e e A).IsHermitian := by
        simpa only [Matrix.isHermitian_reindex_iff] using hA
      simp [realSpectrum,hA,hB]
  have renyi_reindex {n m : Type} [Fintype n] [Fintype m]
      [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A : Matrix n n ℂ) :
      renyiHalf (reindex e e A) = renyiHalf A := by
    rw [renyi_spectrum,renyi_spectrum,spectrum_reindex]
  have norm_reindex {n m : Type} [Fintype n] [Fintype m]
      [DecidableEq n] [DecidableEq m] (e : n ≃ m) (A : Matrix n n ℂ)
      (hA : A.IsHermitian) : traceNorm (reindex e e A) = traceNorm A := by
    rw [traceNorm_spectrum _ (hA.reindex e),traceNorm_spectrum A hA,spectrum_reindex]
  have reducedAB_hermitian {L : ℕ} (A B : Finset (Fin L))
      (ψ : (Fin L → Fin 2) → ℂ) : (reducedAB A B ψ).IsHermitian := by
    ext p q
    simp [reducedAB,partialTraceRight,vecMulVec_apply,Matrix.conjTranspose_apply,
      Pi.star_apply,star_sum,mul_comm]
  have pt_hermitian {a b : Type} (ρ : Matrix (a × b) (a × b) ℂ)
      (hρ : ρ.IsHermitian) : (partialTranspose ρ).IsHermitian := by
    ext ⟨a,b⟩ ⟨c,d⟩
    exact hρ.apply (a,d) (c,b)
  have traceRight_reindex {a b c d : Type}
      [Fintype a] [Fintype b] [Fintype c] [Fintype d]
      (e : a ≃ c) (f : b ≃ d) (ρ : Matrix (a × b) (a × b) ℂ) :
      partialTraceRight (reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) ρ) =
        reindex e e (partialTraceRight ρ) := by
    ext i j
    simp only [partialTraceRight,reindex_apply,submatrix_apply,
      Equiv.prodCongr_symm,Equiv.prodCongr_apply]
    exact Equiv.sum_comp f.symm (fun k => ρ (e.symm i,k) (e.symm j,k))
  have traceLeft_reindex {a b c d : Type}
      [Fintype a] [Fintype b] [Fintype c] [Fintype d]
      (e : a ≃ c) (f : b ≃ d) (ρ : Matrix (a × b) (a × b) ℂ) :
      partialTraceLeft (reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) ρ) =
        reindex f f (partialTraceLeft ρ) := by
    ext i j
    simp only [partialTraceLeft,reindex_apply,submatrix_apply,
      Equiv.prodCongr_symm,Equiv.prodCongr_apply]
    exact Equiv.sum_comp e.symm (fun k => ρ (k,f.symm i) (k,f.symm j))
  have measures_reindex {a b c d : Type}
      [Fintype a] [Fintype b] [Fintype c] [Fintype d]
      [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
      (e : a ≃ c) (f : b ≃ d) (ρ : Matrix (a × b) (a × b) ℂ)
      (hρ : ρ.IsHermitian) :
      logNegativity (reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) ρ) =
        logNegativity ρ ∧
      mutualHalf (reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) ρ) = mutualHalf ρ := by
    have hp : partialTranspose (reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) ρ) =
        reindex (Equiv.prodCongr e f) (Equiv.prodCongr e f) (partialTranspose ρ) := rfl
    constructor
    · unfold logNegativity
      rw [hp,norm_reindex _ _ (pt_hermitian ρ hρ)]
    · unfold mutualHalf
      rw [traceRight_reindex,traceLeft_reindex,renyi_reindex,renyi_reindex,renyi_reindex]
  have density_mulVec {n : Type} [Fintype n]
      (M : Matrix n n ℂ) (ψ : n → ℂ) :
      vecMulVec (M *ᵥ ψ) (star (M *ᵥ ψ)) = M * vecMulVec ψ (star ψ) * Mᴴ := by
    rw [mul_vecMulVec,vecMulVec_mul,star_mulVec]
  have density_neg {n : Type} (ψ : n → ℂ) :
      vecMulVec (-ψ) (star (-ψ)) = vecMulVec ψ (star ψ) := by
    ext i j
    simp
  have evolved_reduction :
      reindex singlePair singlePair
        (reducedAB ({0} : Finset (Fin 4)) {1}
          (evolved (fun _ => 1) witnessTheta (fun _ => 0) 1)) =
        (singleGate ⊗ₖ singleGate) * sigma * (singleGate ⊗ₖ singleGate)ᴴ := by
    rw [physical_reduction]
    have he : evolved (fun _ => 1) witnessTheta (fun _ => 0) 1 =
        -(tensorOp (fun _ : Fin 4 => singleGate) *ᵥ psiGraph) := by
      rw [evolved,zpow_one,initial_witness,floquet_factor,← Matrix.mulVec_mulVec]
      simp [psiGraph,Matrix.neg_mulVec]
    rw [he,density_neg,density_mulVec]
    let F := Matrix.reindexAlgEquiv ℂ ℂ blockEquiv
    change partialTraceRight (F
      (tensorOp (fun _ : Fin 4 => singleGate) * vecMulVec psiGraph (star psiGraph) *
        (tensorOp (fun _ : Fin 4 => singleGate))ᴴ)) = _
    rw [map_mul,map_mul]
    change partialTraceRight
      (reindex blockEquiv blockEquiv (tensorOp (fun _ : Fin 4 => singleGate)) *
        reindex blockEquiv blockEquiv (vecMulVec psiGraph (star psiGraph)) *
          reindex blockEquiv blockEquiv (tensorOp (fun _ : Fin 4 => singleGate))ᴴ) = _
    rw [← Matrix.conjTranspose_reindex,block_tensor,
      trace_local_right _ _ _ (tensor_pair_unitary _ _ singleGate_unitary singleGate_unitary),
      graph_reduced]
  intro h
  have hc := h 4 (fun _ => 1) witnessTheta (fun _ => 0) {0} {1} {2,3} 1
    (by refine ⟨0,1,2,by norm_num,by norm_num,by norm_num,?_,?_,?_⟩ <;> decide)
    witness_generic
  have hm := measures_reindex (singleEquiv 0) (singleEquiv 1)
    (reducedAB ({0} : Finset (Fin 4)) {1}
      (evolved (fun _ => 1) witnessTheta (fun _ => 0) 1))
    (reducedAB_hermitian _ _ _)
  have hc' : 2 * logNegativity (reindex singlePair singlePair
      (reducedAB ({0} : Finset (Fin 4)) {1}
        (evolved (fun _ => 1) witnessTheta (fun _ => 0) 1))) =
      mutualHalf (reindex singlePair singlePair
      (reducedAB ({0} : Finset (Fin 4)) {1}
        (evolved (fun _ => 1) witnessTheta (fun _ => 0) 1))) := by
    rw [show singlePair = Equiv.prodCongr (singleEquiv 0) (singleEquiv 1) from rfl,
      hm.1,hm.2]
    exact hc
  rw [evolved_reduction] at hc'
  have hσ : sigma.IsHermitian := by
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [sigma,finProdFinEquiv]
  have hi := local_invariance sigma singleGate singleGate hσ
    singleGate_unitary singleGate_unitary
  change 2 * Real.log (traceNorm (partialTransposeB
      ((singleGate ⊗ₖ singleGate) * sigma * (singleGate ⊗ₖ singleGate)ᴴ))) =
    renyiHalf (partialTraceRight
      ((singleGate ⊗ₖ singleGate) * sigma * (singleGate ⊗ₖ singleGate)ᴴ)) +
    renyiHalf (partialTraceLeft
      ((singleGate ⊗ₖ singleGate) * sigma * (singleGate ⊗ₖ singleGate)ᴴ)) -
    renyiHalf ((singleGate ⊗ₖ singleGate) * sigma * (singleGate ⊗ₖ singleGate)ᴴ) at hc'
  rw [hi.1,hi.2.1,hi.2.2.1,hi.2.2.2] at hc'
  exact sigma_obstruction hc'

end D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

#print axioms D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.result
