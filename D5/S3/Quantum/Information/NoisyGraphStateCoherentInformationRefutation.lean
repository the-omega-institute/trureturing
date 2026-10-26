/- GID: D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim; result=D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result; claim=D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim
   digest: A noisy graph state on five plus four qubits reverses subsystem coherent information. -/

import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation
import D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation

/-! Uniformly dephased graph states can reverse the subsystem-size entropy ordering. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation

open scoped BigOperators Matrix ComplexOrder CStarAlgebra
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

/-- Independent dephasing of the state `|+⟩`, with survival probability `P`. -/
noncomputable def noisyQubit (P : ℝ) : Matrix Bool Bool ℂ :=
  let plus : Bool → ℂ := fun b =>
    D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.plusState 1 (fun _ => b)
  let minus : Bool → ℂ := fun b => (if b then -1 else 1) * plus b
  (P : ℂ) • Matrix.vecMulVec plus (star plus) +
    ((1 - P : ℝ) : ℂ) • Matrix.vecMulVec minus (star minus)

/-- The product of the diagonal controlled-Z entries over every graph edge. -/
noncomputable def czPhase {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (x : Fin nA ⊕ Fin nB → Bool) : ℂ :=
  ∏ e ∈ G.edgeFinset,
    D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase
      (e.map finSumFinEquiv) (x ∘ finSumFinEquiv.symm)

/-- The uniformly dephased graph state, in the product computational basis. -/
noncomputable def graphState {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) :
    Matrix ((Fin nA → Bool) × (Fin nB → Bool))
      ((Fin nA → Bool) × (Fin nB → Bool)) ℂ :=
  fun x y => czPhase G (Sum.elim x.1 x.2) *
    (∏ v, noisyQubit P (Sum.elim x.1 x.2 v) (Sum.elim y.1 y.2 v)) *
    star (czPhase G (Sum.elim y.1 y.2))

/-- Base-two von Neumann entropy, using the continuous functional calculus logarithm. -/
noncomputable def entropy2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : Matrix ι ι ℂ) : ℝ :=
  -(Matrix.trace (CStarMatrix.ofMatrix rho * CFC.log (CStarMatrix.ofMatrix rho))).re /
    Real.log 2

noncomputable def coherentInfoA {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) : ℝ :=
  entropy2 (partialTraceRight (graphState G P)) - entropy2 (graphState G P)

noncomputable def coherentInfoB {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) : ℝ :=
  entropy2 (partialTraceLeft (graphState G P)) - entropy2 (graphState G P)

/-- The subsystem-size conjecture for every graph and uniform dephasing probability. -/
def claim : Prop :=
  ∀ (nA nB : ℕ), nB < nA →
    ∀ (G : SimpleGraph (Fin nA ⊕ Fin nB)) [DecidableRel G.Adj] (P : ℝ),
      P ∈ Set.Icc 0 1 → coherentInfoB G P ≤ coherentInfoA G P

private def bipartiteGraph {m n : ℕ} (M : Fin m → Fin n → Bool) :
    SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inr j => M i j = true
    | Sum.inr j, Sum.inl i => M i j = true
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

private instance bipartiteDecidable {m n : ℕ} (M : Fin m → Fin n → Bool) :
    DecidableRel (bipartiteGraph M).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp only [bipartiteGraph] <;> infer_instance

private lemma noisyQubit_entry (P : ℝ) (x y : Bool) :
    noisyQubit P x y = (1 / 2 : ℂ) * (if x = y then 1 else 2 * (P : ℂ) - 1) := by
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv_rev]
    have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [h]
    norm_num
  unfold noisyQubit
  cases x <;> cases y <;>
    simp only [D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.plusState,
      pow_one, Complex.ofReal_inv, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_inv, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, one_mul,
      neg_mul,
      mul_neg, neg_neg, map_neg, Complex.ofReal_sub, Complex.ofReal_one] <;>
    rw [hs] <;> ring

private lemma character_sum {n : ℕ} (k : Fin n → ℕ) :
    (∑ b : Fin n → Bool, ∏ j, (-1 : ℂ) ^ (k j * (b j).toNat)) =
      if ∀ j, Even (k j) then (2 : ℂ) ^ n else 0 := by
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : Bool) => (-1 : ℂ) ^ (k j * b.toNat))]
  have hterm (j : Fin n) : (∑ b : Bool, (-1 : ℂ) ^ (k j * b.toNat)) =
      if Even (k j) then 2 else 0 := by
    simp only [Fintype.sum_bool, Bool.toNat_false, Bool.toNat_true,
      Nat.mul_zero, Nat.mul_one, neg_one_pow_eq_ite]
    split_ifs <;> norm_num at *
  simp_rw [hterm]
  rw [Fintype.prod_ite_zero]
  simp

private lemma bipartite_phase {m n : ℕ} (N : Fin m → Fin n → Bool)
    (a : Fin m → Bool) (b : Fin n → Bool) :
    czPhase (bipartiteGraph N) (Sum.elim a b) =
      ∏ i, ∏ j, (-1 : ℂ) ^ ((N i j && a i && b j).toNat) := by
  have hedges : (bipartiteGraph N).edgeFinset =
      ((Finset.univ : Finset (Fin m × Fin n)).filter fun ij => N ij.1 ij.2 = true).image
        (fun ij => s(Sum.inl ij.1, Sum.inr ij.2)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      cases x <;> cases y <;>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] <;>
        dsimp only [bipartiteGraph] <;>
        simp
  unfold czPhase
  rw [hedges, Finset.prod_image]
  · rw [Finset.prod_filter, Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    simp only [Sym2.map_mk,
      D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase,
      Sym2.lift_mk, Function.comp_apply, Equiv.symm_apply_apply]
    cases hN : N i j <;> cases ha : a i <;> cases hb : b j <;>
      simp [ha, hb]
  · intro x _ y _ h
    simpa only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, false_and, or_false, Prod.ext_iff] using h

private lemma qubit_product {n : ℕ} (P : ℝ) (x y : Fin n → Bool) :
    (∏ i, noisyQubit P (x i) (y i)) =
      (2 : ℂ)⁻¹ ^ n * (2 * (P : ℂ) - 1) ^ hammingDist x y := by
  simp_rw [noisyQubit_entry]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div]
  congr 1
  unfold hammingDist
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i <;> simp [h]

private lemma phase_pair_A {m n : ℕ} (N : Fin m → Fin n → Bool)
    (a a' : Fin m → Bool) (b : Fin n → Bool) :
    czPhase (bipartiteGraph N) (Sum.elim a b) *
        star (czPhase (bipartiteGraph N) (Sum.elim a' b)) =
      ∏ j, (-1 : ℂ) ^ ((∑ i, (N i j && Bool.xor (a i) (a' i)).toNat) *
        (b j).toNat) := by
  rw [bipartite_phase, bipartite_phase]
  simp only [star_prod, star_pow, star_neg, star_one]
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ i, ∏ j, (-1 : ℂ) ^
        ((N i j && Bool.xor (a i) (a' i)).toNat * (b j).toNat) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      cases N i j <;> cases a i <;> cases a' i <;> cases b j <;> norm_num
    _ = _ := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro j _
      rw [Finset.prod_pow_eq_pow_sum, Finset.sum_mul]

private lemma phase_pair_B {m n : ℕ} (N : Fin m → Fin n → Bool)
    (a : Fin m → Bool) (b b' : Fin n → Bool) :
    czPhase (bipartiteGraph N) (Sum.elim a b) *
        star (czPhase (bipartiteGraph N) (Sum.elim a b')) =
      ∏ i, (-1 : ℂ) ^ ((∑ j, (N i j && Bool.xor (b j) (b' j)).toNat) *
        (a i).toNat) := by
  rw [bipartite_phase, bipartite_phase]
  simp only [star_prod, star_pow, star_neg, star_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib, Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases N i j <;> cases a i <;> cases b j <;> cases b' j <;> norm_num

private lemma reduced_A {m n : ℕ} (M : Fin m → Fin n → Bool) (P : ℝ)
    (a a' : Fin m → Bool) :
    partialTraceRight (graphState (bipartiteGraph M) P) a a' =
      (2 : ℂ)⁻¹ ^ m * (2 * (P : ℂ) - 1) ^ hammingDist a a' *
        (if ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
          then 1 else 0) := by
  unfold partialTraceRight
  have hentry (b : Fin n → Bool) : graphState (bipartiteGraph M) P (a, b) (a', b) =
      ((2 : ℂ)⁻¹ ^ m * (2 * (P : ℂ) - 1) ^ hammingDist a a' * (2 : ℂ)⁻¹ ^ n) *
        ∏ j, (-1 : ℂ) ^ ((∑ i, (M i j && Bool.xor (a i) (a' i)).toNat) *
          (b j).toNat) := by
    unfold graphState
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    rw [qubit_product, qubit_product, hammingDist_self b, pow_zero,
      mul_one]
    rw [show czPhase (bipartiteGraph M) (Sum.elim a b) *
        ((2 : ℂ)⁻¹ ^ m * (2 * (P : ℂ) - 1) ^ hammingDist a a' * (2 : ℂ)⁻¹ ^ n) *
        star (czPhase (bipartiteGraph M) (Sum.elim a' b)) =
      ((2 : ℂ)⁻¹ ^ m * (2 * (P : ℂ) - 1) ^ hammingDist a a' * (2 : ℂ)⁻¹ ^ n) *
        (czPhase (bipartiteGraph M) (Sum.elim a b) *
          star (czPhase (bipartiteGraph M) (Sum.elim a' b))) by ring,
      phase_pair_A]
  have hsum := Finset.sum_congr rfl
    (fun (b : Fin n → Bool) (_ : b ∈ Finset.univ) => hentry b)
  rw [hsum, ← Finset.mul_sum, character_sum]
  split_ifs <;> simp [mul_assoc]

private lemma reduced_B {m n : ℕ} (M : Fin m → Fin n → Bool) (P : ℝ)
    (b b' : Fin n → Bool) :
    partialTraceLeft (graphState (bipartiteGraph M) P) b b' =
      (2 : ℂ)⁻¹ ^ n * (2 * (P : ℂ) - 1) ^ hammingDist b b' *
        (if ∀ i, Even (∑ j, (M i j && Bool.xor (b j) (b' j)).toNat)
          then 1 else 0) := by
  unfold partialTraceLeft
  have hentry (a : Fin m → Bool) : graphState (bipartiteGraph M) P (a, b) (a, b') =
      ((2 : ℂ)⁻¹ ^ n * (2 * (P : ℂ) - 1) ^ hammingDist b b' * (2 : ℂ)⁻¹ ^ m) *
        ∏ i, (-1 : ℂ) ^ ((∑ j, (M i j && Bool.xor (b j) (b' j)).toNat) *
          (a i).toNat) := by
    unfold graphState
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    rw [qubit_product, qubit_product, hammingDist_self a, pow_zero,
      mul_one]
    calc
      _ = ((2 : ℂ)⁻¹ ^ n * (2 * (P : ℂ) - 1) ^ hammingDist b b' * (2 : ℂ)⁻¹ ^ m) *
          (czPhase (bipartiteGraph M) (Sum.elim a b) *
            star (czPhase (bipartiteGraph M) (Sum.elim a b'))) := by ring
      _ = _ := by rw [phase_pair_B]
  have hsum := Finset.sum_congr rfl
    (fun (a : Fin m → Bool) (_ : a ∈ Finset.univ) => hentry a)
  rw [hsum, ← Finset.mul_sum, character_sum]
  split_ifs <;> simp [mul_assoc]

private def M : Fin 5 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, true, false, false],
    ![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true]]

private def projectionA : Matrix (Fin 5 → Bool) (Fin 5 → Bool) ℂ :=
  fun a a' => if ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
    then 1 / 4 else 0

private lemma bitFlipMatrix_apply (b b' : Fin 4 → Bool) :
    Equiv.Perm.permMatrix ℂ (Equiv.piCongrRight (fun _ : Fin 4 => Equiv.boolNot)) b b' =
      if ∀ i, b i ≠ b' i then 1 else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  change (if (fun i => !(b i)) = b' then (1 : ℂ) else 0) =
    if ∀ i, b i ≠ b' i then 1 else 0
  simp only [funext_iff, Bool.not_eq_iff]

private def projectionB : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℂ :=
  (1 / 2 : ℂ) •
    (1 + Equiv.Perm.permMatrix ℂ (Equiv.piCongrRight (fun _ : Fin 4 => Equiv.boolNot)))

private def u : ℝ := (127 / 128) ^ 2
private def a₁ : ℝ := (1 + 3 * u) / 32
private def a₂ : ℝ := (1 - u) / 32
private def b₁ : ℝ := (1 + u ^ 2) / 16
private def b₂ : ℝ := (1 - u ^ 2) / 16

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
-- The rational projection identity checks all thirty-two computational basis states.
private lemma projectionA_is_projection :
    IsStarProjection (CStarMatrix.ofMatrix projectionA) := by
  let q : Matrix (Fin 5 → Bool) (Fin 5 → Bool) ℚ :=
    fun a a' => if ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
      then 1 / 4 else 0
  have hq : q * q = q := by
    apply Matrix.ext
    decide +kernel
  have hmap : projectionA = (Rat.castHom ℂ).mapMatrix q := by
    ext a a'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    dsimp only [projectionA, q]
    split_ifs <;> norm_num
  constructor
  · change projectionA * projectionA = projectionA
    rw [hmap, ← map_mul, hq]
  · change projectionAᴴ = projectionA
    ext a a'
    rw [Matrix.conjTranspose_apply]
    dsimp only [projectionA]
    simp only [Bool.xor_comm]
    split_ifs <;> norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
-- The rational projection identity checks all sixteen computational basis states.
private lemma projectionB_is_projection :
    IsStarProjection (CStarMatrix.ofMatrix projectionB) := by
  let q : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℚ :=
    fun b b' => ((if b = b' then 1 else 0) +
      (if ∀ i, b i ≠ b' i then 1 else 0)) / 2
  have hq : q * q = q := by
    apply Matrix.ext
    decide +kernel
  have hmap : projectionB = (Rat.castHom ℂ).mapMatrix q := by
    ext b b'
    simp only [projectionB, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      bitFlipMatrix_apply]
    change (1 / 2 : ℂ) * ((if b = b' then 1 else 0) +
        (if ∀ i, b i ≠ b' i then 1 else 0)) = (q b b' : ℂ)
    dsimp only [q]
    split_ifs <;> norm_num
  constructor
  · change projectionB * projectionB = projectionB
    rw [hmap, ← map_mul, hq]
  · change projectionBᴴ = projectionB
    ext b b'
    rw [Matrix.conjTranspose_apply]
    dsimp only [projectionB]
    simp only [Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply, bitFlipMatrix_apply]
    simp only [eq_comm, ne_comm]
    split_ifs <;> norm_num

private lemma projection_traces : Matrix.trace projectionA = 8 ∧ Matrix.trace projectionB = 8 := by
  have hA (a : Fin 5 → Bool) : projectionA a a = 1 / 4 := by
    dsimp only [projectionA]
    simp
  have hB (b : Fin 4 → Bool) : projectionB b b = 1 / 2 := by
    dsimp only [projectionB]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, bitFlipMatrix_apply]
    simp
  constructor <;> simp [Matrix.trace, Matrix.diag_apply, hA, hB] <;> norm_num

private lemma marginal_A_spectral :
    partialTraceRight (graphState (bipartiteGraph M) (255 / 256)) =
      a₁ • projectionA + a₂ • (1 - projectionA) := by
  have hweight : ∀ a a' : Fin 5 → Bool,
      (∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)) →
        a = a' ∨ hammingDist a a' = 2 := by decide +kernel
  ext a a'
  rw [reduced_A]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases heq : a = a'
  · subst a'
    dsimp only [projectionA, a₁, a₂, u]
    simp <;> norm_num
  · by_cases hk : ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
    · have hd := (hweight a a' hk).resolve_left heq
      dsimp only [projectionA, a₁, a₂, u]
      simp [hk, heq, hd] <;> norm_num
    · dsimp only [projectionA]
      simp [hk, heq]

private lemma marginal_B_spectral :
    partialTraceLeft (graphState (bipartiteGraph M) (255 / 256)) =
      b₁ • projectionB + b₂ • (1 - projectionB) := by
  have hkernel : ∀ b b' : Fin 4 → Bool,
      (∀ i, Even (∑ j, (M i j && Bool.xor (b j) (b' j)).toNat)) ↔
        b = b' ∨ ∀ i, b i ≠ b' i := by decide +kernel
  ext b b'
  rw [reduced_B]
  simp only [hkernel, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  dsimp only [projectionB]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, bitFlipMatrix_apply]
  by_cases heq : b = b'
  · subst b'
    dsimp only [b₁, b₂, u]
    simp <;> norm_num
  · by_cases hf : ∀ i, b i ≠ b' i
    · have hd : hammingDist b b' = 4 := by unfold hammingDist; simp [hf]
      dsimp only [b₁, b₂, u]
      simp [heq, hf, hd] <;> norm_num
    · simp [heq, hf]

private lemma spectral_data :
    IsStarProjection (CStarMatrix.ofMatrix projectionA) ∧
    Matrix.trace projectionA = 8 ∧
    IsStarProjection (CStarMatrix.ofMatrix projectionB) ∧
    Matrix.trace projectionB = 8 ∧
    partialTraceRight (graphState (bipartiteGraph M) (255 / 256)) =
      a₁ • projectionA + a₂ • (1 - projectionA) ∧
    partialTraceLeft (graphState (bipartiteGraph M) (255 / 256)) =
      b₁ • projectionB + b₂ • (1 - projectionB) := by
  exact ⟨projectionA_is_projection, projection_traces.1, projectionB_is_projection,
    projection_traces.2, marginal_A_spectral, marginal_B_spectral⟩

private lemma two_projection_entropy {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : IsStarProjection (CStarMatrix.ofMatrix Q))
    (r s : ℝ) :
    entropy2 (r • Q + s • (1 - Q)) =
      (-(Matrix.trace Q).re * r * Real.log r -
        (Fintype.card ι - (Matrix.trace Q).re) * s * Real.log s) / Real.log 2 := by
  have hQQ : Q * Q = Q := hQ.isIdempotentElem
  have hsa : IsSelfAdjoint Q := hQ.isSelfAdjoint
  have hlog' : cfc Real.log (r • Q + s • (1 - Q)) =
      Real.log r • Q + Real.log s • (1 - Q) := by
    have harg : s • (1 : Matrix ι ι ℂ) + (r - s) • Q =
        r • Q + s • (1 - Q) := by module
    have hlog := FullwoodParzygnatSubadditivityRefutation.projection_cfc
      Q hsa hQQ Real.log s (r - s)
    rw [harg, show s + (r - s) = r by ring] at hlog
    rw [hlog]
    module
  have hA : IsSelfAdjoint (r • Q + s • (1 - Q)) :=
    ((IsSelfAdjoint.all r).smul hsa).add
      ((IsSelfAdjoint.all s).smul (Matrix.isHermitian_one.sub hsa))
  have htransport : CStarMatrix.ofMatrix (cfc Real.log (r • Q + s • (1 - Q))) =
      CFC.log (CStarMatrix.ofMatrix (r • Q + s • (1 - Q))) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log _
      ((r • Q + s • (1 - Q)).finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hA hA
  unfold entropy2
  rw [← htransport]
  change -(Matrix.trace ((r • Q + s • (1 - Q)) *
    cfc Real.log (r • Q + s • (1 - Q)))).re / Real.log 2 = _
  rw [hlog']
  have hmul : (r • Q + s • (1 - Q)) *
      (Real.log r • Q + Real.log s • (1 - Q)) =
      (r * Real.log r) • Q + (s * Real.log s) • (1 - Q) := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_sub, sub_mul,
      mul_one, one_mul, hQQ, smul_sub, smul_smul]
    module
  rw [hmul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_one]
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, Complex.natCast_re,
    smul_eq_mul]
  ring

private lemma witness_entropies :
    entropy2 (partialTraceRight (graphState (bipartiteGraph M) (255 / 256))) =
      (-8 * a₁ * Real.log a₁ - 24 * a₂ * Real.log a₂) / Real.log 2 ∧
    entropy2 (partialTraceLeft (graphState (bipartiteGraph M) (255 / 256))) =
      (-8 * b₁ * Real.log b₁ - 8 * b₂ * Real.log b₂) / Real.log 2 := by
  obtain ⟨hQA, htA, hQB, htB, hA, hB⟩ := spectral_data
  rw [hA, hB]
  constructor
  · rw [two_projection_entropy projectionA hQA a₁ a₂, htA]
    norm_num
  · rw [two_projection_entropy projectionB hQB b₁ b₂, htB]
    norm_num

private lemma numerical_inequality :
    -8 * a₁ * Real.log a₁ - 24 * a₂ * Real.log a₂ <
      -8 * b₁ * Real.log b₁ - 8 * b₂ * Real.log b₂ := by
  have h1 : Real.log a₁ = Real.log ((1 + 3 * u) / 4) - 3 * Real.log 2 := by
    unfold a₁
    rw [show (1 + 3 * u) / 32 = ((1 + 3 * u) / 4) / 2 ^ 3 by ring,
      Real.log_div (by unfold u; norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h2 : Real.log a₂ = Real.log (1 - u) - 5 * Real.log 2 := by
    unfold a₂
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num,
      Real.log_div (by unfold u; norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h3 : Real.log b₁ = Real.log ((1 + u ^ 2) / 2) - 3 * Real.log 2 := by
    unfold b₁
    rw [show (1 + u ^ 2) / 16 = ((1 + u ^ 2) / 2) / 2 ^ 3 by ring,
      Real.log_div (by unfold u; norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h4 : Real.log b₂ = Real.log (1 - u) + Real.log (1 + u) - 4 * Real.log 2 := by
    unfold b₂
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num,
      Real.log_div (by unfold u; norm_num) (by norm_num), Real.log_pow,
      show 1 - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.log_mul (by unfold u; norm_num) (by unfold u; norm_num)]
    norm_num
  have hc := Real.one_sub_inv_le_log_of_pos
    (show 0 < (1 + 3 * u) / 4 by unfold u; norm_num)
  have hd := Real.log_le_sub_one_of_pos
    (show 0 < (1 + u ^ 2) / 2 by unfold u; norm_num)
  have he : Real.log (1 - u) ≤ -6 * Real.log 2 := by
    have h := Real.log_le_log (by unfold u; norm_num : 0 < 1 - u)
      (by unfold u; norm_num : 1 - u ≤ 1 / 64)
    have hlog : Real.log (1 / 64 : ℝ) = -6 * Real.log 2 := by
      rw [show (1 / 64 : ℝ) = (2 ^ 6)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      ring
    rwa [hlog] at h
  have hf := Real.log_le_log (by unfold u; norm_num : 0 < 1 + u)
    (by unfold u; norm_num : 1 + u ≤ 2)
  rw [h1, h2, h3, h4]
  dsimp only [a₁, a₂, b₁, b₂, u] at hc hd he hf ⊢
  norm_num at hc hd he hf ⊢
  nlinarith [Real.log_two_lt_d9]

private lemma witness_entropy_comparison :
    entropy2 (partialTraceRight (graphState (bipartiteGraph M) (255 / 256))) <
      entropy2 (partialTraceLeft (graphState (bipartiteGraph M) (255 / 256))) := by
  rw [witness_entropies.1, witness_entropies.2]
  exact div_lt_div_of_pos_right numerical_inequality (Real.log_pos (by norm_num))

/-- A nine-qubit bipartite graph reverses the proposed ordering. -/
theorem result : ¬ claim := by
  intro h
  have hle := h 5 4 (by norm_num) (bipartiteGraph M) (255 / 256) (by norm_num)
  unfold coherentInfoA coherentInfoB at hle
  exact (not_le_of_gt witness_entropy_comparison) ((sub_le_sub_iff_right _).mp hle)

end

end D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation
