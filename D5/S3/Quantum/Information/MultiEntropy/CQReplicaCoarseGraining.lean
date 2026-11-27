/- GID: D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Positive replica moments and Rényi coarse graining for classical–quantum marginals. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
import D5.S3.Quantum.NormCompression.UpperBranchReduction
import D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly
import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound

/-!
For a finite classical–quantum marginal, the tripartite replica moment is
a trace of a power of a positive tensor sum. This gives all three
coarse-graining inequalities for the original replica contraction of
Gadde et al., arXiv:2308.16247, section 1.2, and its real logarithm.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace CQReplicaRegroupingSupplier

variable {A B I R : Type*}

/-- Ordered product of a finite matrix word. -/
def word [Semiring R] (F : A → R) {n : ℕ} (w : Fin n → A) : R :=
  (List.ofFn (fun i => F (w i))).prod

private lemma word_succ [Semiring R] (F : A → R) {n : ℕ} (w : Fin (n + 1) → A) :
    word F w = F (w 0) * word F (fun i : Fin n => w i.succ) := by
  simp [word, List.ofFn_succ]

/-- Ordered noncommutative expansion of a finite sum power. -/
private theorem sum_pow_words [Semiring R] [Fintype A] [DecidableEq A]
    (F : A → R) (n : ℕ) :
    (∑ a, F a) ^ n = ∑ w : Fin n → A, word F w := by
  induction n with
  | zero =>
      simp [word]
  | succ n ih =>
      rw [pow_succ', ih]
      let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) := Fin.consEquiv (fun _ => A)
      calc
        (∑ a, F a) * (∑ w, word F w) =
            ∑ a, ∑ w, F a * word F w := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rfl
        _ = ∑ p : A × (Fin n → A), F p.1 * word F p.2 :=
          by
            exact (Fintype.sum_prod_type
              (fun p : A × (Fin n → A) => F p.1 * word F p.2)).symm
        _ = ∑ w : Fin (n + 1) → A, word F w := by
          refine Fintype.sum_equiv e
            (fun p : A × (Fin n → A) => F p.1 * word F p.2)
            (fun w : Fin (n + 1) → A => word F w) ?_
          intro p
          simp [e, word]

/-- Entrywise n-fold tensor product over an arbitrary finite factor set. -/
def tensorOp [Fintype I] [Fintype B] [CommSemiring R] (M : I → Matrix B B R) :
    Matrix (I → B) (I → B) R :=
  Matrix.of fun x y => ∏ i, M i (x i) (y i)

private lemma tensor_one [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] [CommSemiring R] :
    tensorOp (fun _ : I => (1 : Matrix B B R)) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorOp, Matrix.one_apply]
  · have h' : ¬ ∀ i, x i = y i := by
      intro hall
      exact h (funext hall)
    simp [tensorOp, Matrix.one_apply, Fintype.prod_boole, h, h']

private lemma tensor_mul [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] [CommSemiring R]
    (M N : I → Matrix B B R) :
    tensorOp M * tensorOp N = tensorOp (fun i => M i * N i) := by
  classical
  ext x z
  simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private lemma tensor_trace [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] [CommSemiring R]
    (M : I → Matrix B B R) :
    Matrix.trace (tensorOp M) = ∏ i, Matrix.trace (M i) := by
  classical
  simp only [Matrix.trace, Matrix.diag, tensorOp, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private lemma tensor_word [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] [CommSemiring R]
    (T : A → Matrix B B R) {n : ℕ} (w : Fin n → A) :
    word (fun a => tensorOp (fun _ : I => T a)) w =
      tensorOp (fun _i : I => word T w) := by
  induction n with
  | zero =>
      simp [word, tensor_one]
  | succ n ih =>
      rw [word_succ, word_succ, ih, tensor_mul]

/--
The finite CQ contraction after the classical A-labels have been regrouped into
one label per A-cycle. It is the sum of n-th powers of cyclic block-word traces.
-/
def cqWordContraction [Fintype A] [Fintype B] [DecidableEq B] [Semiring R]
    (T : A → Matrix B B R) (n : ℕ) : R :=
  ∑ w : Fin n → A, (Matrix.trace (word T w)) ^ n

/--
The operator `Σ_a T_a^{⊗ n}` on the n-fold finite tensor basis.
-/
def cqTensorSum [Fintype A] [Fintype B] [DecidableEq B] [CommSemiring R]
    (T : A → Matrix B B R) (n : ℕ) :
    Matrix (Fin n → B) (Fin n → B) R :=
  ∑ a, tensorOp (fun _ : Fin n => T a)

/--
Index-regrouping identity. The right side is exactly
`Tr[(Σ_a T_a^{⊗n})^n]`, while the left side is the cyclic CQ word sum.
No commutativity of the individual blocks is assumed.
-/
private theorem cq_word_contraction_eq_trace_tensor_sum_pow
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [CommSemiring R]
    (T : A → Matrix B B R) (n : ℕ) :
    cqWordContraction T n = Matrix.trace ((cqTensorSum T n) ^ n) := by
  unfold cqWordContraction cqTensorSum
  rw [sum_pow_words]
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [tensor_word, tensor_trace]
  simp [Finset.prod_const, Fintype.card_fin]

end CQReplicaRegroupingSupplier

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse (shift)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open CQReplicaRegroupingSupplier

noncomputable section

variable {L : Fin 3 → Type*}

/-- The product basis for the three local spaces of the owner contraction. -/
def stateEquiv : ((i : Fin 3) → L i) ≃ (L 0 × L 1) × L 2 where
  toFun x := ((x 0, x 1), x 2)
  invFun x := Fin.cons x.1.1 (Fin.cons x.1.2 (Fin.cons x.2 (fun i => Fin.elim0 i)))
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := rfl

/-- The AB marginal in the entry convention of the owner contraction. -/
def reducedAB [Fintype (L 2)] (ψ : ((i : Fin 3) → L i) → ℂ) :
    Matrix (L 0 × L 1) (L 0 × L 1) ℂ :=
  partialTraceRight (Matrix.vecMulVec
    (fun p : (L 0 × L 1) × L 2 => star (ψ (stateEquiv.symm p)))
    (fun p : (L 0 × L 1) × L 2 => ψ (stateEquiv.symm p)))

private theorem shift_two (n : ℕ) (r : Fin 2 → ZMod n) : shift n 3 2 r = r := by
  funext i
  fin_cases i <;> rfl

open private sum_unshifted from D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

private theorem trace_unshifted (n : ℕ) [NeZero n] [∀ i, Fintype (L i)]
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    E n 3 ψ = ∑ ab : (Fin 2 → ZMod n) → L 0 × L 1, ∏ r : Fin 2 → ZMod n,
      reducedAB ψ (ab r) ((ab (shift n 3 0 r)).1, (ab (shift n 3 1 r)).2) := by
  classical
  unfold E
  let e := Equiv.piCongrRight (fun _ : Fin 2 → ZMod n => stateEquiv (L := L))
  rw [← Equiv.sum_comp e.symm]
  have h (x : (Fin 2 → ZMod n) → (L 0 × L 1) × L 2) :
      (∏ r : Fin 2 → ZMod n, star (ψ (e.symm x r)) *
        ψ (fun i => e.symm x (shift n 3 i r) i)) =
      ∏ r : Fin 2 → ZMod n, star (ψ (stateEquiv.symm (x r))) *
        ψ (stateEquiv.symm
          (((x (shift n 3 0 r)).1.1, (x (shift n 3 1 r)).1.2), (x r).2)) := by
    apply Finset.prod_congr rfl
    intro r _
    apply congrArg (star (ψ (stateEquiv.symm (x r))) * ·)
    apply congrArg ψ
    funext i
    fin_cases i
    · rfl
    · rfl
    · change (x (shift n 3 2 r)).2 = (x r).2
      rw [shift_two]
  simp_rw [h]
  exact sum_unshifted
    (fun (r : Fin 2 → ZMod n) (ab : (Fin 2 → ZMod n) → L 0 × L 1) (k : L 2) =>
      star (ψ (stateEquiv.symm (ab r, k))) *
        ψ (stateEquiv.symm (((ab (shift n 3 0 r)).1, (ab (shift n 3 1 r)).2), k)))

/-- The mixed AB contraction on the two independent cyclic coordinates.
The first grid coordinate shifts B and the second shifts A. -/
def torus {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
    (n : ℕ) [NeZero n] (ρ : Matrix (A × B) (A × B) R) : R :=
  ∑ a : Fin n → Fin n → A, ∑ b : Fin n → Fin n → B,
    ∏ i, ∏ j, ρ (a i j, b i j) (a i (j + 1), b (i + 1) j)

private def gridEquiv (n : ℕ) [NeZero n] : (Fin 2 → ZMod n) ≃ Fin n × Fin n :=
  (finTwoArrowEquiv (ZMod n)).trans ((Equiv.prodComm _ _).trans
    (Equiv.prodCongr (ZMod.finEquiv n).symm.toEquiv (ZMod.finEquiv n).symm.toEquiv))

private theorem grid_shift_zero (n : ℕ) [NeZero n] (r : Fin 2 → ZMod n) :
    gridEquiv n (shift n 3 0 r) = ((gridEquiv n r).1, (gridEquiv n r).2 + 1) := by
  change ((ZMod.finEquiv n).symm (r 1), (ZMod.finEquiv n).symm (r 0 + 1)) =
    ((ZMod.finEquiv n).symm (r 1), (ZMod.finEquiv n).symm (r 0) + 1)
  rw [map_add, map_one]

private theorem grid_shift_one (n : ℕ) [NeZero n] (r : Fin 2 → ZMod n) :
    gridEquiv n (shift n 3 1 r) = ((gridEquiv n r).1 + 1, (gridEquiv n r).2) := by
  change ((ZMod.finEquiv n).symm (r 1 + 1), (ZMod.finEquiv n).symm (r 0)) =
    ((ZMod.finEquiv n).symm (r 1) + 1, (ZMod.finEquiv n).symm (r 0))
  rw [map_add, map_one]

/-- The original pure-state replica contraction with the purifying indices traced out. -/
private theorem E_eq_reducedAB_torus (n : ℕ) [NeZero n] [∀ i, Fintype (L i)]
    (ψ : ((i : Fin 3) → L i) → ℂ) : E n 3 ψ = torus n (reducedAB ψ) := by
  classical
  rw [trace_unshifted]
  let g := gridEquiv n
  let e : ((Fin 2 → ZMod n) → L 0 × L 1) ≃
      ((Fin n → Fin n → L 0) × (Fin n → Fin n → L 1)) :=
    (Equiv.arrowCongr g (Equiv.refl (L 0 × L 1))).trans
      ((Equiv.arrowProdEquivProdArrow (Fin n × Fin n) (fun _ => L 0) (fun _ => L 1)).trans
        (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.curry _ _ _)))
  unfold torus
  rw [← Fintype.sum_prod_type
    (fun p : (Fin n → Fin n → L 0) × (Fin n → Fin n → L 1) => ∏ i, ∏ j,
      reducedAB ψ (p.1 i j, p.2 i j) (p.1 i (j + 1), p.2 (i + 1) j))]
  apply Fintype.sum_equiv e _ _
  intro ab
  rw [← Fintype.prod_prod_type (fun p : Fin n × Fin n =>
    reducedAB ψ ((e ab).1 p.1 p.2, (e ab).2 p.1 p.2)
      ((e ab).1 p.1 (p.2 + 1), (e ab).2 (p.1 + 1) p.2))]
  apply Fintype.prod_equiv g
  intro r
  change reducedAB ψ (ab r) ((ab (shift n 3 0 r)).1, (ab (shift n 3 1 r)).2) =
    reducedAB ψ ((ab (g.symm (g r))).1, (ab (g.symm (g r))).2)
      ((ab (g.symm ((g r).1, (g r).2 + 1))).1,
        (ab (g.symm ((g r).1 + 1, (g r).2))).2)
  have h₀ : g (shift n 3 0 r) = ((g r).1, (g r).2 + 1) := grid_shift_zero n r
  have h₁ : g (shift n 3 1 r) = ((g r).1 + 1, (g r).2) := grid_shift_one n r
  simp only [← h₀, ← h₁, Equiv.symm_apply_apply, Prod.eta]

section Cycles

variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]

open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
  (sum_fin_cons)

/-- A classical A marginal index cannot change across a nonzero matrix entry. -/
def IsBlockDiagonalOnA (ρ : Matrix (A × B) (A × B) R) : Prop :=
  ∀ a c b d, a ≠ c → ρ (a, b) (c, d) = 0

/-- The quantum matrices on the diagonal A blocks. -/
def blocks (ρ : Matrix (A × B) (A × B) R) (a : A) : Matrix B B R :=
  fun b d => ρ (a, b) (a, d)

private def constantRowsEquiv (n : ℕ) [NeZero n] :
    { a : Fin n → Fin n → A // ∀ i j, a i j = a i (j + 1) } ≃ (Fin n → A) where
  toFun a i := a.val i 0
  invFun w := ⟨fun i _ => w i, fun _ _ => rfl⟩
  left_inv a := by
    apply Subtype.ext
    funext i j
    change a.val i 0 = a.val i j
    cases n with
    | zero => exact Fin.elim0 j
    | succ m =>
      induction j using Fin.induction with
      | zero => rfl
      | succ j ih =>
        rw [← Fin.coeSucc_eq_succ, ← a.property i j.castSucc]
        exact ih
  right_inv _ := rfl

private theorem torus_eq_block_cycles (n : ℕ) [NeZero n]
    (ρ : Matrix (A × B) (A × B) R) (hρ : IsBlockDiagonalOnA ρ) :
    torus n ρ = ∑ w : Fin n → A, ∏ _j : Fin n,
      ∑ b : Fin n → B, ∏ i, blocks ρ (w i) (b i) (b (i + 1)) := by
  classical
  let valid (a : Fin n → Fin n → A) := ∀ i j, a i j = a i (j + 1)
  let f (a : Fin n → Fin n → A) := ∑ b : Fin n → Fin n → B,
    ∏ i, ∏ j, ρ (a i j, b i j) (a i (j + 1), b (i + 1) j)
  calc
    torus n ρ = ∑ a ∈ Finset.univ.filter valid, f a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hbad : ¬valid a := fun hv => ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ a i (j + 1) := by
        simpa only [valid, not_forall] using hbad
      apply Finset.sum_eq_zero
      intro b _
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (Finset.prod_eq_zero (Finset.mem_univ j) (hρ _ _ _ _ hij))
    _ = ∑ a : Subtype valid, f a.val := Finset.sum_subtype _ (by simp [valid]) f
    _ = ∑ w : Fin n → A, f (fun i _ => w i) :=
      ((constantRowsEquiv (A := A) n).symm.sum_comp (fun a : Subtype valid => f a.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      let swap : (Fin n → Fin n → B) ≃ (Fin n → Fin n → B) :=
        ⟨fun b j i => b i j, fun b i j => b j i, fun _ => rfl, fun _ => rfl⟩
      calc
        f (fun i _ => w i) =
            ∑ b : Fin n → Fin n → B, ∏ j, ∏ i, blocks ρ (w i) (b j i) (b j (i + 1)) := by
          apply Fintype.sum_equiv swap _ _
          intro b
          exact Finset.prod_comm
        _ = _ := (Fintype.prod_sum
          (fun (_j : Fin n) (b : Fin n → B) => ∏ i, blocks ρ (w i) (b i) (b (i + 1)))).symm

private def pathProd {m : ℕ} (M : Fin (m + 1) → Matrix B B R)
    (v : Fin (m + 2) → B) : R :=
  ∏ i, M i (v i.castSucc) (v i.succ)

omit [Fintype B] in
private theorem pathProd_cons {m : ℕ} (M : Fin (m + 2) → Matrix B B R)
    (x : B) (v : Fin (m + 2) → B) :
    pathProd M (Fin.cons x v) =
      M 0 x (v 0) * pathProd (fun i => M i.succ) v := by
  rw [pathProd, Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]
  rfl

private theorem word_apply_eq_path_sum [DecidableEq B] {m : ℕ}
    (M : Fin (m + 1) → Matrix B B R) (x y : B) :
    word id M x y =
      ∑ u : Fin m → B, pathProd M (Fin.cons x (Fin.snoc u y)) := by
  induction m generalizing x y with
  | zero =>
    have hlast (u : Fin 0 → B) : @Fin.snoc 0 (fun _ => B) u y 0 = y := by
      simpa only [Fin.last_zero] using (@Fin.snoc_last 0 (fun _ => B) y u)
    simp [word, List.ofFn_succ, pathProd, hlast]
  | succ m ih =>
    rw [word_succ, Matrix.mul_apply, sum_fin_cons]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Fin.cons_snoc_eq_snoc_cons z u y, pathProd_cons, Fin.cons_zero, id_eq]

/-- A cycle sum of matrix entries is the trace of the ordered matrix word. -/
private theorem trace_word_eq_cycle_sum [DecidableEq B] (n : ℕ) [NeZero n]
    (M : Fin n → Matrix B B R) :
    Matrix.trace (word id M) = ∑ b : Fin n → B, ∏ i, M i (b i) (b (i + 1)) := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m =>
    simp only [Matrix.trace, Matrix.diag, word_apply_eq_path_sum]
    rw [sum_fin_cons]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro u _
    let b : Fin (m + 1) → B := Fin.cons x u
    rw [Fin.cons_snoc_eq_snoc_cons]
    change pathProd M (Fin.snoc b (b 0)) = ∏ i, M i (b i) (b (i + 1))
    unfold pathProd
    apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
    congr 1
    cases i using Fin.lastCases with
    | last => rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
    | cast i => rw [Fin.coeSucc_eq_succ, ← Fin.castSucc_succ, Fin.snoc_castSucc]

/-- The mixed CQ torus is a sum of powers of ordered block-word traces. -/
private theorem torus_eq_cqWordContraction [DecidableEq B] (n : ℕ) [NeZero n]
    (ρ : Matrix (A × B) (A × B) R) (hρ : IsBlockDiagonalOnA ρ) :
    torus n ρ = cqWordContraction (blocks ρ) n := by
  rw [torus_eq_block_cycles n ρ hρ]
  unfold cqWordContraction
  apply Finset.sum_congr rfl
  intro w _
  rw [← trace_word_eq_cycle_sum n (fun i => blocks ρ (w i))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end Cycles

/-- The reduced density in the usual ket-bra convention. -/
def densityAB [Fintype (L 2)] (ψ : ((i : Fin 3) → L i) → ℂ) :
    Matrix (L 0 × L 1) (L 0 × L 1) ℂ :=
  (reducedAB ψ).transpose

private theorem densityAB_apply [Fintype (L 2)] (ψ : ((i : Fin 3) → L i) → ℂ)
    (a c : L 0 × L 1) :
    densityAB ψ a c = ∑ k : L 2,
      ψ (stateEquiv.symm (a, k)) * star (ψ (stateEquiv.symm (c, k))) := by
  simp only [densityAB, reducedAB, Matrix.transpose_apply, partialTraceRight, Matrix.vecMulVec]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private theorem cqTensorSum_transpose {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [CommSemiring R] (T : A → Matrix B B R) (n : ℕ) :
    cqTensorSum (fun a => (T a).transpose) n = (cqTensorSum T n).transpose := by
  unfold cqTensorSum
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- The original tripartite contraction equals the trace of the n-th power of the
sum of n-fold tensor powers of the CQ blocks. The blocks may fail to commute. -/
theorem E_eq_trace_tensor_sum_pow (n : ℕ) [NeZero n] [∀ i, Fintype (L i)]
    [DecidableEq (L 1)] (ψ : ((i : Fin 3) → L i) → ℂ)
    (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    E n 3 ψ = Matrix.trace ((cqTensorSum (blocks (densityAB ψ)) n) ^ n) := by
  classical
  have hρ' : IsBlockDiagonalOnA (reducedAB ψ) :=
    fun a c b d h => hρ c a d b (Ne.symm h)
  have hblocks : blocks (reducedAB ψ) = fun a => (blocks (densityAB ψ) a).transpose := rfl
  rw [E_eq_reducedAB_torus, torus_eq_cqWordContraction n _ hρ',
    cq_word_contraction_eq_trace_tensor_sum_pow, hblocks, cqTensorSum_transpose,
    ← Matrix.transpose_pow, Matrix.trace_transpose]

open RHLinalg (rtrace)
open CQReplicaRegroupingSupplier
open D5.S3.Quantum.NormCompression.UpperBranchReduction
  (schattenNorm schattenNorm_nonneg schattenNorm_rpow schattenPow_eq_eigenPow eigenPow)

open private schattenNorm_triangle from D5.S3.Quantum.NormCompression.UpperBranchReduction
open private trace_power_spectral from D5.S3.Quantum.Entanglement.HiguchiSudbery.HS4Assembly

private theorem rtrace_sum {I d : Type*} [Fintype d] (s : Finset I)
    (M : I → Matrix d d ℂ) : rtrace (∑ i ∈ s, M i) = ∑ i ∈ s, rtrace (M i) := by
  change (Matrix.trace (∑ i ∈ s, M i)).re = _
  rw [Matrix.trace_sum, Complex.re_sum]
  rfl

private theorem trace_eq_ofReal_rtrace {d : Type*} [Fintype d]
    {M : Matrix d d ℂ} (hM : M.IsHermitian) : M.trace = (rtrace M : ℂ) := by
  classical
  rw [RHLinalg.rtrace_eq_sum_eigenvalues hM, hM.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
  rfl

private theorem rtrace_pow_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {M : Matrix d d ℂ} (hM : M.PosSemidef) (k : ℕ) : 0 ≤ rtrace (M ^ k) := by
  change 0 ≤ (M ^ k).trace.re
  rw [trace_power_spectral M hM.isHermitian]
  exact Finset.sum_nonneg fun i _ => pow_nonneg (hM.eigenvalues_nonneg i) _

private theorem rtrace_pow_pos {d : Type*} [Fintype d] [DecidableEq d]
    {M : Matrix d d ℂ} (hM : M.PosSemidef) (hne : M ≠ 0) (k : ℕ) :
    0 < rtrace (M ^ k) := by
  have he : ∃ i, 0 < hM.isHermitian.eigenvalues i := by
    by_contra! h
    apply hne
    apply hM.isHermitian.eigenvalues_eq_zero_iff.mp
    funext i
    exact le_antisymm (h i) (hM.eigenvalues_nonneg i)
  obtain ⟨i, hi⟩ := he
  change 0 < (M ^ k).trace.re
  rw [trace_power_spectral M hM.isHermitian]
  exact Finset.sum_pos' (fun j _ => pow_nonneg (hM.eigenvalues_nonneg j) _)
    ⟨i, Finset.mem_univ _, pow_pos hi _⟩

private theorem tensor_posSemidef {I d : Type*} [Fintype I] [Fintype d]
    (M : I → Matrix d d ℂ) (hM : ∀ i, (M i).PosSemidef) :
    (tensorOp M).PosSemidef := by
  classical
  choose G hG using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg
  have hstar : (tensorOp G)ᴴ = tensorOp (fun i => (G i)ᴴ) := by
    ext x y
    simp [tensorOp, Matrix.conjTranspose_apply]
  have he : tensorOp M = (tensorOp G)ᴴ * tensorOp G := by
    rw [hstar, tensor_mul]
    congr 1
    funext i
    exact hG i
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

private theorem tensor_pow {I d : Type*} [Fintype I] [DecidableEq I]
    [Fintype d] [DecidableEq d] (M : I → Matrix d d ℂ) (k : ℕ) :
    tensorOp M ^ k = tensorOp (fun i => M i ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (tensor_one (I := I) (B := d) (R := ℂ)).symm
  | succ k ih => simp only [pow_succ, ih, tensor_mul]

private theorem rtrace_tensor_constant {d : Type*} [Fintype d]
    {M : Matrix d d ℂ} (hM : M.IsHermitian) (n : ℕ) :
    rtrace (tensorOp (fun _ : Fin n => M)) = (rtrace M) ^ n := by
  classical
  change (Matrix.trace (tensorOp (fun _ : Fin n => M))).re = _
  rw [tensor_trace, trace_eq_ofReal_rtrace hM, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem rtrace_pow_blockDiagonal {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : IsBlockDiagonalOnA ρ) (n : ℕ) :
    rtrace (ρ ^ n) = ∑ a, rtrace (blocks ρ a ^ n) := by
  let e : A × B ≃ B × A := Equiv.prodComm A B
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have hf : f ρ = Matrix.blockDiagonal (blocks ρ) := by
    ext ⟨b, a⟩ ⟨d, c⟩
    change ρ (a, b) (c, d) = (Matrix.blockDiagonal (blocks ρ)) (b, a) (d, c)
    by_cases h : a = c
    · subst c
      simp [Matrix.blockDiagonal_apply, blocks]
    · simp [Matrix.blockDiagonal_apply, h, hρ a c b d h]
  have htrace (M : Matrix (A × B) (A × B) ℂ) : (f M).trace = M.trace := by
    exact e.symm.sum_comp (fun p => M p p)
  unfold rtrace
  rw [← htrace (ρ ^ n), map_pow, hf, ← Matrix.blockDiagonal_pow,
    Matrix.trace_blockDiagonal, map_sum]
  rfl

private theorem schattenNorm_sum_le {I d : Type*} [Fintype d] [DecidableEq d]
    (s : Finset I) (M : I → Matrix d d ℂ) (hM : ∀ i, (M i).PosSemidef)
    {p : ℝ} (hp : 1 ≤ p) :
    schattenNorm p (∑ i ∈ s, M i) ≤ ∑ i ∈ s, schattenNorm p (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hp' : 0 < p := zero_lt_one.trans_le hp
    simp [schattenNorm, D5.S3.Quantum.NormCompression.UpperBranchReduction.schattenPow,
      Real.zero_rpow (inv_ne_zero hp'.ne')]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hsum : (∑ j ∈ s, M j).PosSemidef :=
      Matrix.posSemidef_sum s (fun j _ => hM j)
    calc
      _ ≤ schattenNorm p (M i) + schattenNorm p (∑ j ∈ s, M j) :=
        schattenNorm_triangle (hM i) hsum hp
      _ ≤ _ := add_le_add_right ih (schattenNorm p (M i))

private theorem schattenNorm_nat_pow {d : Type*} [Fintype d] [DecidableEq d]
    {M : Matrix d d ℂ} (hM : M.PosSemidef) {n : ℕ} (hn : 0 < n) :
    schattenNorm (n : ℝ) M ^ n = rtrace (M ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast, schattenNorm_rpow hn', schattenPow_eq_eigenPow _ hn' _ hM,
    eigenPow, dite_eq_left hM.isHermitian]
  change _ = (M ^ n).trace.re
  rw [trace_power_spectral M hM.isHermitian]
  simp only [Real.rpow_natCast]

private theorem cqTensorSum_posSemidef {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : A → Matrix B B ℂ) (hT : ∀ a, (T a).PosSemidef) (n : ℕ) :
    (cqTensorSum T n).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ => tensor_posSemidef _ (fun _ => hT a)

private theorem rtrace_cqTensorSum_pow_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : A → Matrix B B ℂ) (hT : ∀ a, (T a).PosSemidef) {n : ℕ} (hn : 0 < n) :
    rtrace ((cqTensorSum T n) ^ n) ≤ (∑ a, rtrace (T a ^ n)) ^ n := by
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnrm (a : A) :
      schattenNorm (n : ℝ) (tensorOp (fun _ : Fin n => T a)) = rtrace (T a ^ n) := by
    apply (pow_left_inj₀ (schattenNorm_nonneg _ _) (rtrace_pow_nonneg (hT a) n) hn.ne').mp
    have hTa := tensor_posSemidef (fun _ : Fin n => T a) (fun _ => hT a)
    rw [schattenNorm_nat_pow hTa hn, tensor_pow,
      rtrace_tensor_constant ((hT a).pow n).isHermitian]
  rw [← schattenNorm_nat_pow (cqTensorSum_posSemidef T hT n) hn]
  apply pow_le_pow_left₀ (schattenNorm_nonneg _ _) _ n
  unfold cqTensorSum
  simpa only [hnrm] using schattenNorm_sum_le Finset.univ
    (fun a => tensorOp (fun _ : Fin n => T a))
    (fun a => tensor_posSemidef _ (fun _ => hT a)) hp

section State

variable {L : Fin 3 → Type*} [∀ i, Fintype (L i)]

private theorem blocks_densityAB_posSemidef (ψ : ((i : Fin 3) → L i) → ℂ) (a : L 0) :
    (blocks (densityAB ψ) a).PosSemidef := by
  let v (k : L 2) (b : L 1) := ψ (stateEquiv.symm ((a, b), k))
  have hv : blocks (densityAB ψ) a = ∑ k, Matrix.vecMulVec (v k) (star (v k)) := by
    apply Matrix.ext
    intro b d
    rw [Matrix.sum_apply]
    exact densityAB_apply ψ (a, b) (a, d)
  rw [hv]
  exact Matrix.posSemidef_sum _ (fun k _ => Matrix.posSemidef_vecMulVec_self_star (v k))

private theorem rtrace_densityAB (ψ : ((i : Fin 3) → L i) → ℂ) (hψ : IsUnitState ψ) :
    rtrace (densityAB ψ) = 1 := by
  change (∑ x, Complex.normSq (ψ x)) = 1 at hψ
  rw [← stateEquiv.symm.sum_comp (fun x => Complex.normSq (ψ x))] at hψ
  change (∑ ab : L 0 × L 1, densityAB ψ ab ab).re = 1
  simp only [Complex.re_sum, densityAB_apply]
  have hre (z : ℂ) : (z * star z).re = Complex.normSq z := by
    rw [mul_comm]
    rw [← show (Complex.normSq z : ℂ) = star z * z from Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re]
  simp only [hre]
  exact (Fintype.sum_prod_type
    (fun p : (L 0 × L 1) × L 2 => Complex.normSq (ψ (stateEquiv.symm p)))).symm.trans hψ

/-- The actual tripartite replica moment is positive real and is bounded by the
merged AB moment to the n-th power for a normalized state with a CQ AB marginal. -/
private theorem E_coarseGraining_AB (n : ℕ) [NeZero n] [DecidableEq (L 0)] [DecidableEq (L 1)]
    (hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ) (hψ : IsUnitState ψ)
    (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    (E n 3 ψ).im = 0 ∧ 0 < (E n 3 ψ).re ∧
      (E n 3 ψ).re ≤ (rtrace ((densityAB ψ) ^ n)) ^ n := by
  let T := blocks (densityAB ψ)
  have hT : ∀ a, (T a).PosSemidef := blocks_densityAB_posSemidef ψ
  have hF := cqTensorSum_posSemidef T hT n
  have hsum : ∑ a, rtrace (T a) = 1 := by
    simpa only [pow_one, rtrace_densityAB ψ hψ] using (rtrace_pow_blockDiagonal hρ 1).symm
  have hsome : ∃ a, 0 < rtrace (T a) := by
    by_contra! h
    have hle : ∑ a, rtrace (T a) ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith
  obtain ⟨a, ha⟩ := hsome
  have hFpos : 0 < rtrace (cqTensorSum T n) := by
    unfold cqTensorSum
    rw [rtrace_sum]
    have ht (b : L 0) := rtrace_tensor_constant (hT b).isHermitian n
    simp_rw [ht]
    exact Finset.sum_pos' (fun b _ => pow_nonneg (by simpa using rtrace_pow_nonneg (hT b) 1) _)
      ⟨a, Finset.mem_univ _, pow_pos ha _⟩
  have hFne : cqTensorSum T n ≠ 0 := by
    intro h
    simp [h, rtrace] at hFpos
  rw [E_eq_trace_tensor_sum_pow n ψ hρ]
  change ((cqTensorSum T n ^ n).trace).im = 0 ∧
    0 < rtrace (cqTensorSum T n ^ n) ∧
    rtrace (cqTensorSum T n ^ n) ≤ _
  refine ⟨?_, rtrace_pow_pos hF hFne n, ?_⟩
  · rw [trace_eq_ofReal_rtrace (hF.pow n).isHermitian, Complex.ofReal_im]
  · rw [rtrace_pow_blockDiagonal hρ]
    exact rtrace_cqTensorSum_pow_le T hT (by omega)

end State

private theorem rtrace_pow_le_trace_pow {d : Type*} [Fintype d] [DecidableEq d]
    {M : Matrix d d ℂ} (hM : M.PosSemidef) {n : ℕ} (hn : 0 < n) :
    rtrace (M ^ n) ≤ (rtrace M) ^ n := by
  let eigenvalues := hM.isHermitian.eigenvalues
  let s := ∑ i, eigenvalues i
  change (M ^ n).trace.re ≤ _
  rw [trace_power_spectral M hM.isHermitian, RHLinalg.rtrace_eq_sum_eigenvalues hM.isHermitian]
  cases n with
  | zero => omega
  | succ n =>
    change ∑ i, eigenvalues i ^ (n + 1) ≤ s ^ (n + 1)
    simp only [pow_succ']
    rw [show s * s ^ n = (∑ i, eigenvalues i) * s ^ n from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hM.eigenvalues_nonneg i)
        (Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)) _)
      (hM.eigenvalues_nonneg i)

private theorem rtrace_pow_mono {d : Type*} [Fintype d] [DecidableEq d]
    {M N : Matrix d d ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hMN : (N - M).PosSemidef) (n : ℕ) : rtrace (M ^ n) ≤ rtrace (N ^ n) := by
  change (M ^ n).trace.re ≤ (N ^ n).trace.re
  rw [trace_power_spectral M hM.isHermitian, trace_power_spectral N hN.isHermitian,
    RHLinalg.sum_eigenvalues_reindex _ (fun x => x ^ n),
    RHLinalg.sum_eigenvalues_reindex _ (fun x => x ^ n)]
  apply Finset.sum_le_sum
  intro j _
  have hj : 0 ≤ hM.isHermitian.eigenvalues₀ j := by
    rw [← RHLinalg.eigenvalues_eigEquiv hM.isHermitian]
    exact hM.eigenvalues_nonneg _
  exact pow_le_pow_left₀ hj
    (D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_mono_finite
      hM.isHermitian hN.isHermitian hMN j) n

private theorem tensor_sum_expansion {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (T : A → Matrix B B ℂ) :
    tensorOp (fun _ : I => ∑ a, T a) = ∑ w : I → A, tensorOp (fun i => T (w i)) := by
  classical
  apply Matrix.ext
  intro x y
  simp only [Matrix.sum_apply, tensorOp, Matrix.of_apply]
  exact Fintype.prod_sum (fun i a => T a (x i) (y i))

private theorem tensor_sum_sub_cq_posSemidef {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (T : A → Matrix B B ℂ) (hT : ∀ a, (T a).PosSemidef)
    (n : ℕ) [NeZero n] :
    (tensorOp (fun _ : Fin n => ∑ a, T a) - cqTensorSum T n).PosSemidef := by
  classical
  let e : A ↪ (Fin n → A) := ⟨fun a _ => a, fun _ _ h => congrFun h 0⟩
  let s : Finset (Fin n → A) := Finset.univ.map e
  let f (w : Fin n → A) := tensorOp (fun i => T (w i))
  have hs : ∑ w ∈ s, f w = cqTensorSum T n := by
    rw [Finset.sum_map]
    rfl
  have hex : tensorOp (fun _ : Fin n => ∑ a, T a) = ∑ w, f w := tensor_sum_expansion T
  have hsub : (∑ w ∈ Finset.univ \ s, f w) + ∑ w ∈ s, f w = ∑ w, f w :=
    Finset.sum_sdiff (Finset.subset_univ s)
  rw [hex, ← hs, ← hsub, add_sub_cancel_right]
  exact Matrix.posSemidef_sum _ (fun w _ => tensor_posSemidef _ (fun i => hT (w i)))

/-- The usual marginal on the first local space, obtained from the AB density. -/
def densityA {L : Fin 3 → Type*} [Fintype (L 1)] [Fintype (L 2)]
    (ψ : ((i : Fin 3) → L i) → ℂ) : Matrix (L 0) (L 0) ℂ :=
  fun a c => ∑ b, densityAB ψ (a, b) (c, b)

/-- The usual marginal on the second local space, obtained from the AB density. -/
def densityB {L : Fin 3 → Type*} [Fintype (L 0)] [Fintype (L 2)]
    (ψ : ((i : Fin 3) → L i) → ℂ) : Matrix (L 1) (L 1) ℂ :=
  ∑ a, blocks (densityAB ψ) a

section OtherMergers

variable {L : Fin 3 → Type*} [∀ i, Fintype (L i)]

private theorem densityA_eq_diagonal [DecidableEq (L 0)]
    (ψ : ((i : Fin 3) → L i) → ℂ) (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    densityA ψ = Matrix.diagonal (fun a => (blocks (densityAB ψ) a).trace) := by
  apply Matrix.ext
  intro a c
  by_cases h : a = c
  · subst c
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.sum_eq_zero (fun b _ => hρ a c b b h)

/-- For the BC merger the complementary A marginal supplies the bipartite moment. -/
private theorem E_coarseGraining_BC (n : ℕ) [NeZero n] [DecidableEq (L 0)]
    (hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ) (hψ : IsUnitState ψ)
    (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    (E n 3 ψ).re ≤ (rtrace ((densityA ψ) ^ n)) ^ n := by
  classical
  let T := blocks (densityAB ψ)
  have hT : ∀ a, (T a).PosSemidef := blocks_densityAB_posSemidef ψ
  refine (E_coarseGraining_AB n hn ψ hψ hρ).2.2.trans ?_
  rw [rtrace_pow_blockDiagonal hρ, densityA_eq_diagonal ψ hρ, Matrix.diagonal_pow]
  apply pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => rtrace_pow_nonneg (hT a) n) _ n
  change (∑ a, rtrace (T a ^ n)) ≤ (Matrix.trace (Matrix.diagonal (fun a => (T a).trace ^ n))).re
  rw [Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [trace_eq_ofReal_rtrace (hT a).isHermitian, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact rtrace_pow_le_trace_pow (hT a) (by omega)

/-- For the AC merger the complementary B marginal supplies the bipartite moment. -/
private theorem E_coarseGraining_AC (n : ℕ) [NeZero n] [DecidableEq (L 1)]
    (ψ : ((i : Fin 3) → L i) → ℂ) (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    (E n 3 ψ).re ≤ (rtrace ((densityB ψ) ^ n)) ^ n := by
  let T := blocks (densityAB ψ)
  have hT : ∀ a, (T a).PosSemidef := blocks_densityAB_posSemidef ψ
  have hB : (densityB ψ).PosSemidef := Matrix.posSemidef_sum _ (fun a _ => hT a)
  rw [E_eq_trace_tensor_sum_pow n ψ hρ]
  change rtrace (cqTensorSum T n ^ n) ≤ _
  calc
    _ ≤ rtrace ((tensorOp (fun _ : Fin n => densityB ψ)) ^ n) :=
      rtrace_pow_mono (cqTensorSum_posSemidef T hT n) (tensor_posSemidef _ fun _ => hB)
        (tensor_sum_sub_cq_posSemidef T hT n) n
    _ = _ := by rw [tensor_pow, rtrace_tensor_constant (hB.pow n).isHermitian]

end OtherMergers

section Bipartite

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse (shift)
open private sum_unshifted from D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

/-- The density of the first factor of a bipartite pure amplitude. -/
private def bipartiteDensity {K : Fin 2 → Type*} [Fintype (K 1)]
    (ψ : ((i : Fin 2) → K i) → ℂ) : Matrix (K 0) (K 0) ℂ :=
  fun a c => ∑ b, ψ ((piFinTwoEquiv K).symm (a, b)) *
    star (ψ ((piFinTwoEquiv K).symm (c, b)))

private theorem word_constant {R : Type*} [Semiring R] (M : R) (n : ℕ) :
    word id (fun _ : Fin n => M) = M ^ n := by
  induction n with
  | zero => simp [word]
  | succ n ih => rw [word_succ, ih, pow_succ', id_eq]

/-- The actual two-party replica contraction is the trace moment of its first marginal. -/
private theorem E_two_eq_trace_density (n : ℕ) [NeZero n] {K : Fin 2 → Type*}
    [∀ i, Fintype (K i)] [DecidableEq (K 0)] (ψ : ((i : Fin 2) → K i) → ℂ) :
    E n 2 ψ = (bipartiteDensity ψ ^ n).trace := by
  classical
  let g : (Fin 1 → ZMod n) ≃ Fin n :=
    ⟨fun r => (ZMod.finEquiv n).symm (r 0), fun i _ => ZMod.finEquiv n i,
      fun r => by funext j; fin_cases j; simp, fun i => by simp⟩
  have hzero (r : Fin 1 → ZMod n) : g (shift n 2 0 r) = g r + 1 := by
    change (ZMod.finEquiv n).symm (r 0 + 1) = (ZMod.finEquiv n).symm (r 0) + 1
    rw [map_add, map_one]
  have hone (r : Fin 1 → ZMod n) : shift n 2 1 r = r := by
    funext j
    fin_cases j
    rfl
  let p := piFinTwoEquiv K
  let e := Equiv.arrowCongr g p
  have h (x : Fin n → K 0 × K 1) :
      (∏ r : Fin 1 → ZMod n, star (ψ (e.symm x r)) *
        ψ (fun a => e.symm x (shift n 2 a r) a)) =
      ∏ i : Fin n, star (ψ (p.symm (x i))) * ψ (p.symm ((x (i + 1)).1, (x i).2)) := by
    apply Fintype.prod_equiv g
    intro r
    apply congrArg (star (ψ (p.symm (x (g r)))) * ·)
    apply congrArg ψ
    funext a
    fin_cases a
    · change (x (g (shift n 2 0 r))).1 = (x (g r + 1)).1
      rw [hzero]
    · change (x (g (shift n 2 1 r))).2 = (x (g r)).2
      rw [hone]
  unfold E
  rw [← e.symm.sum_comp]
  simp_rw [h]
  let M := (bipartiteDensity ψ).transpose
  calc
    _ = ∑ a : Fin n → K 0, ∏ i : Fin n, M (a i) (a (i + 1)) := by
      have hsum := sum_unshifted (fun (i : Fin n) (a : Fin n → K 0) (b : K 1) =>
        star (ψ (p.symm (a i, b))) * ψ (p.symm (a (i + 1), b)))
      refine hsum.trans (Finset.sum_congr rfl fun a _ => ?_)
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      exact mul_comm _ _
    _ = _ := by
      rw [← trace_word_eq_cycle_sum n (fun _ : Fin n => M), word_constant]
      exact (congrArg Matrix.trace (Matrix.transpose_pow (bipartiteDensity ψ) n)).symm.trans
        (Matrix.trace_transpose _)

end Bipartite

section MergedStates

universe u

/-- View an amplitude on a product basis as a two-party pure state. -/
def pairAmplitude {A B : Type u} (ψ : A × B → ℂ)
    (x : (i : Fin 2) → ![A, B] i) : ℂ :=
  ψ (x 0, x 1)

private instance fintypePairAmplitude {A B : Type u} [Fintype A] [Fintype B] (i : Fin 2) :
    Fintype (![A, B] i) := by
  refine Fin.cases (motive := fun j => Fintype (![A, B] j)) ‹Fintype A› ?_ i
  intro j
  exact Fin.cases (motive := fun k => Fintype (![A, B] k.succ)) ‹Fintype B› (fun k => Fin.elim0 k) j

variable {L : Fin 3 → Type*} [∀ i, Fintype (L i)]

/-- Group A and B into one party, with C as the second party. -/
def mergeAB (ψ : ((i : Fin 3) → L i) → ℂ) :=
  pairAmplitude (fun p : (L 0 × L 1) × L 2 => ψ (stateEquiv.symm p))

/-- Keep A as the first party and group B and C into the second party. -/
def mergeBC (ψ : ((i : Fin 3) → L i) → ℂ) :=
  pairAmplitude (fun p : L 0 × (L 1 × L 2) => ψ (stateEquiv.symm ((p.1, p.2.1), p.2.2)))

/-- Keep B as the first party and group A and C into the second party. -/
def mergeAC (ψ : ((i : Fin 3) → L i) → ℂ) :=
  pairAmplitude (fun p : L 1 × (L 0 × L 2) => ψ (stateEquiv.symm ((p.2.1, p.1), p.2.2)))

private theorem bipartiteDensity_mergeAB (ψ : ((i : Fin 3) → L i) → ℂ) :
    bipartiteDensity (mergeAB ψ) = densityAB ψ := by
  apply Matrix.ext
  intro a c
  change (∑ k : L 2, ψ (stateEquiv.symm (a, k)) * star (ψ (stateEquiv.symm (c, k)))) = _
  exact (densityAB_apply ψ a c).symm

private theorem bipartiteDensity_mergeBC (ψ : ((i : Fin 3) → L i) → ℂ) :
    bipartiteDensity (mergeBC ψ) = densityA ψ := by
  apply Matrix.ext
  intro a c
  let f (p : L 1 × L 2) :=
    ψ (stateEquiv.symm ((a, p.1), p.2)) * star (ψ (stateEquiv.symm ((c, p.1), p.2)))
  change (∑ p, f p) = ∑ b, densityAB ψ (a, b) (c, b)
  simpa only [densityAB_apply] using Fintype.sum_prod_type f

private theorem bipartiteDensity_mergeAC (ψ : ((i : Fin 3) → L i) → ℂ) :
    bipartiteDensity (mergeAC ψ) = densityB ψ := by
  apply Matrix.ext
  intro b d
  change L 1 at b d
  let f (p : L 0 × L 2) :=
    ψ (stateEquiv.symm ((p.1, b), p.2)) * star (ψ (stateEquiv.symm ((p.1, d), p.2)))
  change (∑ p, f p) = (∑ a, blocks (densityAB ψ) a) b d
  rw [Fintype.sum_prod_type f, Matrix.sum_apply]
  simp only [f, blocks, densityAB_apply]

/-- All three coarse-graining inequalities expressed in terms of the same owner
contraction, applied to the original state and the three grouped states. -/
theorem E_coarseGraining_all_mergers (n : ℕ) [NeZero n]
    (hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ) (hψ : IsUnitState ψ)
    (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    (E n 3 ψ).im = 0 ∧ 0 < (E n 3 ψ).re ∧
      (E n 3 ψ).re ≤ (E n 2 (mergeAB ψ)).re ^ n ∧
      (E n 3 ψ).re ≤ (E n 2 (mergeBC ψ)).re ^ n ∧
      (E n 3 ψ).re ≤ (E n 2 (mergeAC ψ)).re ^ n := by
  classical
  obtain ⟨hi, hp, hab⟩ := E_coarseGraining_AB n hn ψ hψ hρ
  rw [@E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 0 × L 1))) (mergeAB ψ),
    @E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 0))) (mergeBC ψ),
    @E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 1))) (mergeAC ψ),
    bipartiteDensity_mergeAB, bipartiteDensity_mergeBC, bipartiteDensity_mergeAC]
  change (E n 3 ψ).im = 0 ∧ 0 < (E n 3 ψ).re ∧
    (E n 3 ψ).re ≤ rtrace (densityAB ψ ^ n) ^ n ∧
    (E n 3 ψ).re ≤ rtrace (densityA ψ ^ n) ^ n ∧
    (E n 3 ψ).re ≤ rtrace (densityB ψ ^ n) ^ n
  exact ⟨hi, hp, hab, E_coarseGraining_BC n hn ψ hψ hρ, E_coarseGraining_AC n ψ hρ⟩

/--
info: 'D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.E_coarseGraining_all_mergers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms E_coarseGraining_all_mergers

private theorem E_two_re_nonneg (n : ℕ) [NeZero n] {K : Fin 2 → Type*}
    [∀ i, Fintype (K i)] (ψ : ((i : Fin 2) → K i) → ℂ) : 0 ≤ (E n 2 ψ).re := by
  classical
  rw [E_two_eq_trace_density]
  let v (b : K 1) (a : K 0) := ψ ((piFinTwoEquiv K).symm (a, b))
  have hv : bipartiteDensity ψ = ∑ b, Matrix.vecMulVec (v b) (star (v b)) := by
    apply Matrix.ext
    intro a c
    rw [Matrix.sum_apply]
    rfl
  change 0 ≤ rtrace (bipartiteDensity ψ ^ n)
  rw [hv]
  exact rtrace_pow_nonneg
    (Matrix.posSemidef_sum _ (fun b _ => Matrix.posSemidef_vecMulVec_self_star (v b))) n

private theorem renyi_le_of_moment_le (n : ℕ) (hn : 2 ≤ n) {x y : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (h : x ≤ y ^ n) :
    0 < y ∧ -Real.log y / ((n : ℝ) - 1) ≤
      -Real.log x / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnp : 0 < n := by omega
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hpos : 0 < y := by
    by_contra! hzero
    have he : y = 0 := le_antisymm hzero hy
    have hp := hx.trans_le h
    rw [he, zero_pow hnp.ne'] at hp
    exact (lt_irrefl 0) hp
  have hlog := Real.log_le_log hx h
  rw [Real.log_pow] at hlog
  refine ⟨hpos, ?_⟩
  have hd : 0 < (n : ℝ) - 1 := sub_pos.mpr hn'
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans hn'
  apply (le_div_iff₀ (mul_pos hnpos hd)).mpr
  rw [mul_comm (n : ℝ), ← mul_assoc, div_mul_cancel₀ _ hd.ne']
  linarith

/-- Each bipartite merger has a positive replica moment and Rényi entropy at
most the tripartite Rényi multi-entropy for a classical–quantum AB marginal. -/
theorem renyi_coarseGraining_all_mergers (n : ℕ) [NeZero n]
    (hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ) (hψ : IsUnitState ψ)
    (hρ : IsBlockDiagonalOnA (densityAB ψ)) :
    ∀ y ∈ [(E n 2 (mergeAB ψ)).re, (E n 2 (mergeBC ψ)).re, (E n 2 (mergeAC ψ)).re],
      0 < y ∧ -Real.log y / ((n : ℝ) - 1) ≤
        -Real.log (E n 3 ψ).re / ((n : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨_, hp, hab, hbc, hac⟩ := E_coarseGraining_all_mergers n hn ψ hψ hρ
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact renyi_le_of_moment_le n hn hp (E_two_re_nonneg n (mergeAB ψ)) hab
  · exact renyi_le_of_moment_le n hn hp (E_two_re_nonneg n (mergeBC ψ)) hbc
  · exact renyi_le_of_moment_le n hn hp (E_two_re_nonneg n (mergeAC ψ)) hac

/--
info: 'D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.renyi_coarseGraining_all_mergers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms renyi_coarseGraining_all_mergers

end MergedStates

end

end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica
