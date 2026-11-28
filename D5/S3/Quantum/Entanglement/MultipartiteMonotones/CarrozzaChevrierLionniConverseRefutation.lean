/- GID: D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.claim; result=D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.result; claim=D5/S3/Quantum/Entanglement/MultipartiteMonotones/CarrozzaChevrierLionniConverseRefutation.claim
   digest: A four-qubit cluster state refutes both converses of Corollary 7. -/

/- result
   proof_shape: content
   escape_witness: The normalized cluster tensor has no proper-support factorization
   under common local isometries. The prime singleton ranks and rank-one stripping
   force a proper cut of rank at most one, contrary to the explicit cluster minors.
   admission_basis: open-problem-resolution (#35139)
   Direct frozen dependencies: none in result's declaration or proof term. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.VecNotation

/-! The converse questions after Corollary 7 of arXiv:2611.27660v1 in finite coordinates. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.MultipartiteMonotones.CarrozzaChevrierLionniConverseRefutation

open Matrix Module
open scoped BigOperators Matrix TensorProduct Kronecker
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
  (rectangle_finrank)

private abbrev Bits := Fin 4 → Fin 2
private abbrev BitPair := Fin 2 × Fin 2

private def cluster (s : Bits) : ℚ :=
  if s 0 = s 1 ∧ s 2 = s 3 then
    if s 0 = 1 ∧ s 2 = 1 then -(1 / 2) else 1 / 2
  else 0

private def setPair (a b : Fin 4) (x y : Fin 2) (s : Bits) : Bits :=
  fun i => if i = a then x else if i = b then y else s i

/-- The normalized complex cluster amplitude. -/
private noncomputable def clusterState (s : Bits) : ℂ := cluster s

private abbrev Coordinate {D : ℕ} (d : Fin D → ℕ) := (i : Fin D) → Fin (d i)

private abbrev Tensor {D : ℕ} (d : Fin D → ℕ) := Coordinate d → ℂ

private abbrev Wire {D : ℕ} (d : Fin D → ℕ) (i : Fin D) := Fin (d i) × Fin (d i)

private abbrev qubits : Fin 4 → ℕ := fun _ => 2

private theorem positiveQubits : ∀ i, 0 < qubits i := fun _ => Nat.zero_lt_succ _

private def fill {D : ℕ} {d : Fin D → ℕ} (a b : Fin D)
    (x : Fin (d a)) (y : Fin (d b)) (z : Coordinate d) : Coordinate d :=
  fun i => if h : i = a then h.symm ▸ x else if h : i = b then h.symm ▸ y else z i

/-- One column pair contributes the reduced density of its two incident strand colors. -/
private noncomputable def marginalEntry {D : ℕ} {d : Fin D → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (a b : Fin D) (p : Wire d a) (q : Wire d b) : ℂ :=
  ∑ z : Coordinate d, if z a = ⟨0, hd a⟩ ∧ z b = ⟨0, hd b⟩ then
    ψ (fill a b p.1 q.1 z) * star (ψ (fill a b p.2 q.2 z))
  else 0

noncomputable section

/-- Eq. (9) in finite orthonormal bases, allowing two independent local embeddings. -/
private def ReducibleTensor {D : ℕ} {d : Fin D → ℕ} (ψ : Tensor d) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Finset (Fin D)) (dims : Fin k → Fin D → ℕ)
    (η : (j : Fin k) → Tensor (dims j)) (common : Fin D → ℕ)
    (U : (i : Fin D) → Matrix (Fin (common i)) (Fin (d i)) ℂ)
    (V : (i : Fin D) → Matrix (Fin (common i)) ((j : Fin k) → Fin (dims j i)) ℂ),
    (∀ j, S j ≠ Finset.univ) ∧
    (∀ j i, i ∉ S j → dims j i = 1) ∧
    (∀ j, ∑ x, Complex.normSq (η j x) = 1) ∧
    (∀ i, (U i)ᴴ * U i = 1) ∧ (∀ i, (V i)ᴴ * V i = 1) ∧
    productMap (fun i => Fin (d i)) U *ᵥ ψ =
      productMap (fun i => (j : Fin k) → Fin (dims j i)) V *ᵥ
        (fun x => ∏ j, η j (fun i => x i j))

/-- Eq. (24) for D = k+3. Each column pair traces all colors other than the
two strand colors incident to it. Internal strands carry top–bottom pairs. -/
private def contraction (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (σ : Equiv.Perm (Fin (k + 3))) :
    Matrix (Wire d (σ (Fin.last (k + 2)))) (Wire d (σ 0)) ℂ :=
  fun out input =>
    ∑ wire : (i : Fin (k + 3)) → Wire d (σ i),
      if wire 0 = input ∧ wire (Fin.last (k + 2)) = (if (k + 3) % 2 = 0 then out.swap else out)
      then ∏ i : Fin (k + 2),
        if i.val % 2 = 0 then
          marginalEntry hd ψ (σ i.castSucc) (σ i.succ) (wire i.castSucc) (wire i.succ)
        else marginalEntry hd ψ (σ i.castSucc) (σ i.succ) (wire i.castSucc).swap (wire i.succ).swap
      else 0

private def ordered (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (σ : Equiv.Perm (Fin (k + 3))) (n : ℕ) : ℝ :=
  let A := contraction k hd ψ σ
  let X := A * Aᴴ
  (-Real.log ((X ^ n).trace.re / X.trace.re ^ n))

private def averaged (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (n : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (k + 3)), ordered k hd ψ σ n) / (Nat.factorial (k + 3) : ℝ)

private def orderedConverse : Prop :=
  ∀ (k : ℕ) (d : Fin (k + 3) → ℕ) (hd : ∀ i, 0 < d i) (ψ : Tensor d),
    (∑ x : Coordinate d, Complex.normSq (ψ x)) = 1 → ¬ ReducibleTensor ψ →
      ∀ n : ℕ, 2 ≤ n → ∀ σ, 0 < ordered k hd ψ σ n

private def averagedConverse : Prop :=
  ∀ (k : ℕ) (d : Fin (k + 3) → ℕ) (hd : ∀ i, 0 < d i) (ψ : Tensor d),
    (∑ x : Coordinate d, Complex.normSq (ψ x)) = 1 → ¬ ReducibleTensor ψ →
      ∀ n : ℕ, 2 ≤ n → 0 < averaged k hd ψ n

def claim : Prop := orderedConverse ∨ averagedConverse

/-! ## Evaluation of the four-party graph -/

private noncomputable def pairedVertices (ψ : Bits → ℂ) (a b : Fin 4)
    (p q : BitPair) (z : Bits) : ℂ :=
  if z a = 0 ∧ z b = 0 then
    ψ (setPair a b p.1 q.1 z) * star (ψ (setPair a b p.2 q.2 z))
  else 0

/-- The two-color marginal for four qubits. -/
private noncomputable def pairEntryCRaw (ψ : Bits → ℂ) (a b : Fin 4) (p q : BitPair) : ℂ :=
  ∑ z : Bits, pairedVertices ψ a b p q z

private theorem fill_four (a b : Fin 4) (x y : Fin 2) (z : Bits) :
    fill (d := qubits) a b x y z = setPair a b x y z := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [fill, setPair]
  · by_cases hb : i = b
    · subst i
      simp [fill, setPair, ha]
    · simp [fill, setPair, ha, hb]

private theorem marginalEntry_four (ψ : Bits → ℂ) (a b : Fin 4) (p q : BitPair) :
    marginalEntry positiveQubits ψ a b p q = pairEntryCRaw ψ a b p q := by
  unfold marginalEntry pairEntryCRaw pairedVertices
  simp only [fill_four]
  rfl

/-- Eq. (24) for four qubits. The three spectator assignments label the parallel internal
edges within the three vertex pairs. The two bit pairs label the edges across adjacent
pairs. The middle white vertex is on the other strand. The input is ket–dual and
the output is dual–ket. Each summand contains all six vertex amplitudes. -/
private noncomputable def graphEntry (ψ : Bits → ℂ) (a b c d : Fin 4) (out input : BitPair) : ℂ :=
  ∑ x : BitPair, ∑ y : BitPair, ∑ w : Bits, ∑ u : Bits, ∑ v : Bits,
    pairedVertices ψ a b input x u *
      pairedVertices ψ b c x.swap y.swap v * pairedVertices ψ c d y out.swap w

private theorem graphEntry_eq_marginal_chain (ψ : Bits → ℂ) (a b c d : Fin 4) (out input : BitPair) :
    graphEntry ψ a b c d out input =
      ∑ x : BitPair, ∑ y : BitPair,
        pairEntryCRaw ψ a b input x * pairEntryCRaw ψ b c x.swap y.swap *
          pairEntryCRaw ψ c d y out.swap := by
  simp only [graphEntry, pairEntryCRaw]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]

private def pairEntry (a b : Fin 4) (p q : BitPair) : ℚ :=
  ∑ z : Bits, if z a = 0 ∧ z b = 0 then
    cluster (setPair a b p.1 q.1 z) * cluster (setPair a b p.2 q.2 z)
  else 0

private def pairEntryC (a b : Fin 4) (p q : BitPair) : ℂ := (pairEntry a b p q : ℂ)

private def pairTable (a b : Fin 4) (p q : BitPair) : ℚ :=
  if a.val / 2 = b.val / 2 then
    if p = q ∧ p.1 = p.2 then 1 / 2 else 0
  else if p.1 = p.2 ∧ q.1 = q.2 then 1 / 4 else 0

private def rationalContraction (a b c d : Fin 4) (out input : BitPair) : ℚ :=
  ∑ x : BitPair, ∑ y : BitPair,
    pairEntry a b input x * pairEntry b c x.swap y.swap * pairEntry c d y out.swap

private def complexContraction (a b c d : Fin 4) (out input : BitPair) : ℂ :=
  ∑ x : BitPair, ∑ y : BitPair,
    pairEntryC a b input x * pairEntryC b c x.swap y.swap * pairEntryC c d y out.swap

private def corners (scale : ℚ) (out input : BitPair) : ℚ :=
  if out.1 = out.2 ∧ input.1 = input.2 then scale else 0

private def Distinct (a b c d : Fin 4) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

private instance distinctDecidable (a b c d : Fin 4) : Decidable (Distinct a b c d) := by
  unfold Distinct
  infer_instance

private theorem pairEntryC_cast (a b : Fin 4) (p q : BitPair) :
    pairEntryCRaw clusterState a b p q = (pairEntry a b p q : ℂ) := by
  simp only [pairEntryCRaw, pairedVertices, pairEntry, clusterState, star_ratCast]
  change _ = (Rat.castHom ℂ) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs
  · exact (map_mul (Rat.castHom ℂ) _ _).symm
  · simp

private theorem pair_check :
    ∀ (a b : Fin 4) (p q : BitPair), a ≠ b →
      pairEntry a b p q = pairTable a b p q := by
  decide +kernel

private theorem path_check :
    ∀ (a b c d : Fin 4) (out input : BitPair), Distinct a b c d →
      (∑ x : BitPair, ∑ y : BitPair,
        pairTable a b input x * pairTable b c x.swap y.swap *
          pairTable c d y out.swap) =
        corners (1 / 16) out input := by
  decide +kernel

private theorem rationalContraction_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    rationalContraction a b c d out input = corners (1 / 16) out input := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  simpa only [rationalContraction, pair_check _ _ _ _ hab, pair_check _ _ _ _ hbc,
    pair_check _ _ _ _ hcd] using
      path_check a b c d out input ⟨hab, hac, had, hbc, hbd, hcd⟩

private theorem complexContraction_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    complexContraction a b c d out input =
      (corners (1 / 16) out input : ℂ) := by
  calc
    complexContraction a b c d out input =
        (Rat.castHom ℂ) (rationalContraction a b c d out input) := by
      simp only [complexContraction, rationalContraction, pairEntryC,
        map_sum, map_mul, Rat.coe_castHom]
    _ = _ := congrArg (Rat.castHom ℂ) (rationalContraction_eq a b c d out input h)

private theorem cluster_graph_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    graphEntry clusterState a b c d out input = (corners (1 / 16) out input : ℂ) := by
  rw [graphEntry_eq_marginal_chain]
  simp_rw [pairEntryC_cast]
  exact complexContraction_eq a b c d out input h

private theorem cluster_normalization : (∑ s : Bits, cluster s * cluster s) = 1 := by
  decide +kernel

private theorem complex_gram : ∀ out input : BitPair,
    (∑ k : BitPair, (corners (1 / 16) out k : ℂ) *
      star (corners (1 / 16) input k : ℂ)) =
      (corners (1 / 128) out input : ℂ) := by
  intro out input
  fin_cases out <;> fin_cases input <;>
    norm_num [corners, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_product]

private theorem complex_square : ∀ out input : BitPair,
    (∑ k : BitPair, (corners (1 / 128) out k : ℂ) *
      (corners (1 / 128) k input : ℂ)) =
      (1 / 64 : ℂ) * (corners (1 / 128) out input : ℂ) := by
  intro out input
  fin_cases out <;> fin_cases input <;>
    norm_num [corners, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_product]

private theorem power_succ_of_square {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (t : ℂ) (hsq : X * X = t • X) (k : ℕ) :
    X ^ (k + 1) = t ^ k • X := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ X (k + 1), ih, Matrix.smul_mul, hsq, smul_smul, pow_succ t k]

private theorem logRatio_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (t : ℝ) (ht : t ≠ 0)
    (htrace : X.trace = (t : ℂ)) (hsq : X * X = (t : ℂ) • X) (k : ℕ) :
    -Real.log ((X ^ (k + 1)).trace.re / X.trace.re ^ (k + 1)) = 0 := by
  rw [power_succ_of_square X _ hsq, Matrix.trace_smul, smul_eq_mul, htrace,
    ← pow_succ, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re,
    div_self (pow_ne_zero _ ht), Real.log_one, neg_zero]

private def wireEquiv : (BitPair × BitPair × BitPair × BitPair) ≃ (Fin 4 → BitPair) where
  toFun w := ![w.1, w.2.1, w.2.2.1, w.2.2.2]
  invFun w := (w 0, w 1, w 2, w 3)
  left_inv w := by rcases w with ⟨a,b,c,d⟩; rfl
  right_inv w := by funext i; fin_cases i <;> rfl

private theorem sum_internal_wires (P Q R : BitPair → BitPair → ℂ) (input out : BitPair) :
    (∑ w : Fin 4 → BitPair, if w 0 = input ∧ w 3 = out then
      P (w 0) (w 1) * Q (w 1) (w 2) * R (w 2) (w 3) else 0) =
      ∑ x : BitPair, ∑ y : BitPair, P input x * Q x y * R y out := by
  let f (w : Fin 4 → BitPair) :=
    if w 0 = input ∧ w 3 = out then P (w 0) (w 1) * Q (w 1) (w 2) * R (w 2) (w 3)
    else 0
  change (∑ w, f w) = _
  calc
    _ = ∑ w : BitPair × BitPair × BitPair × BitPair, f (wireEquiv w) :=
      (Equiv.sum_comp wireEquiv f).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type (α₁ := BitPair)]
      change (∑ a : BitPair, ∑ b : BitPair, ∑ c : BitPair, ∑ d : BitPair,
        if a = input ∧ d = out then P a b * Q b c * R c d else 0) = _
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const_zero]

private theorem contraction_four_product (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4))
    (w : Fin 4 → BitPair) :
    (∏ i : Fin 3,
      if i.val % 2 = 0 then marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ)
        (w i.castSucc) (w i.succ)
      else marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ)
        (w i.castSucc).swap (w i.succ).swap) =
      marginalEntry positiveQubits ψ (σ 0) (σ 1) (w 0) (w 1) *
        marginalEntry positiveQubits ψ (σ 1) (σ 2) (w 1).swap (w 2).swap *
        marginalEntry positiveQubits ψ (σ 2) (σ 3) (w 2) (w 3) := by
  let step (i : Fin 3) :=
    if i.val % 2 = 0 then marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ)
      (w i.castSucc) (w i.succ)
    else marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ)
      (w i.castSucc).swap (w i.succ).swap
  change (∏ i, step i) = _
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
  rw [← mul_assoc]
  rfl

private theorem contraction_four (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4)) :
    contraction 1 positiveQubits ψ σ =
      (fun out input => graphEntry ψ (σ 0) (σ 1) (σ 2) (σ 3) out input) := by
  apply Matrix.ext
  intro out input
  let P := marginalEntry positiveQubits ψ (σ 0) (σ 1)
  let Q (a b : BitPair) := marginalEntry positiveQubits ψ (σ 1) (σ 2) a.swap b.swap
  let R := marginalEntry positiveQubits ψ (σ 2) (σ 3)
  change _ = graphEntry ψ (σ 0) (σ 1) (σ 2) (σ 3) out input
  calc
    (contraction 1 positiveQubits ψ σ) out input =
      (∑ w : Fin 4 → BitPair, if w 0 = input ∧ w 3 = out.swap then
        P (w 0) (w 1) * Q (w 1) (w 2) * R (w 2) (w 3) else 0) := by
      change (∑ w : Fin 4 → BitPair, if w 0 = input ∧ w 3 = out.swap then
        (∏ i : Fin 3, if i.val % 2 = 0 then
          marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ) (w i.castSucc) (w i.succ)
        else marginalEntry positiveQubits ψ (σ i.castSucc) (σ i.succ)
          (w i.castSucc).swap (w i.succ).swap) else 0) = _
      exact Finset.sum_congr rfl fun w _ => by
        rw [contraction_four_product ψ σ w]
    _ = ∑ x : BitPair, ∑ y : BitPair, P input x * Q x y * R y out.swap :=
      sum_internal_wires P Q R input out.swap
    _ = _ := by rw [graphEntry_eq_marginal_chain]; simp only [P, Q, R, marginalEntry_four]

private theorem cluster_state_normalized : (∑ s : Bits, Complex.normSq (clusterState s)) = 1 := by
  have h := congrArg (Rat.castHom ℝ) cluster_normalization
  simpa only [clusterState, Complex.normSq_ratCast, map_sum, map_mul, map_one,
    Rat.coe_castHom] using h

private theorem cluster_ordered_zero (σ : Equiv.Perm (Fin 4)) (n : ℕ) (hn : 2 ≤ n) :
    ordered 1 positiveQubits clusterState σ n = 0 := by
  have hd : Distinct (σ 0) (σ 1) (σ 2) (σ 3) := by
    unfold Distinct
    simpa only [Ne, σ.injective.eq_iff] using
      (show (0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧
        (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3 from by decide)
  let X : Matrix BitPair BitPair ℂ := fun i j => (corners (1 / 128) i j : ℂ)
  have hgram : contraction 1 positiveQubits clusterState σ * (contraction 1 positiveQubits clusterState σ)ᴴ = X := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, contraction_four, cluster_graph_eq _ _ _ _ _ _ hd]
    exact complex_gram i j
  have ht : X.trace = ((1 / 64 : ℝ) : ℂ) := by
    norm_num [X, Matrix.trace, Matrix.diag, corners, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hs : X * X = ((1 / 64 : ℝ) : ℂ) • X := by
    ext i j
    change (∑ k, (corners (1 / 128) i k : ℂ) * (corners (1 / 128) k j : ℂ)) = _
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact complex_square i j
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa only [ordered, hgram] using logRatio_eq_zero X _ (by norm_num) ht hs k

private theorem cluster_averaged_zero (n : ℕ) (hn : 2 ≤ n) : averaged 1 positiveQubits clusterState n = 0 := by
  simp [averaged, cluster_ordered_zero _ n hn]

/-! ## Cut ranks and irreducibility -/

private theorem rank_kronecker {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  rw [rank_eq_finrank_range_toLin _
    ((Pi.basisFun ℂ m).tensorProduct (Pi.basisFun ℂ p))
    ((Pi.basisFun ℂ n).tensorProduct (Pi.basisFun ℂ q)), Matrix.toLin_kronecker]
  change finrank ℂ (LinearMap.range (TensorProduct.map A.mulVecLin B.mulVecLin)) = _
  rw [TensorProduct.range_map]
  exact rectangle_finrank _ _

/-- Matrix rank multiplies over a finite product of rectangular matrices. -/
private theorem rank_productMap (k : ℕ)
    (m n : Fin k → Type) [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]
    (A : ∀ i, Matrix (m i) (n i) ℂ) :
    (productMap n A).rank = ∏ i, (A i).rank := by
  classical
  induction k with
  | zero =>
    let trivial (t : Fin 0 → Type) : Unit ≃ (∀ i, t i) :=
      ⟨fun _ i => Fin.elim0 i, fun _ => (), fun _ => rfl, fun _ => Subsingleton.elim _ _⟩
    have h : (productMap n A).submatrix (trivial m) (trivial n) =
        (1 : Matrix Unit Unit ℂ) := by
      ext u v
      simp [productMap, Matrix.one_apply, Subsingleton.elim u v]
    rw [← Matrix.rank_submatrix _ (trivial m) (trivial n), h, Matrix.rank_one]
    simp
  | succ k ih =>
    let m' := fun i : Fin k => m i.succ
    let n' := fun i : Fin k => n i.succ
    let A' : ∀ i, Matrix (m' i) (n' i) ℂ := fun i => A i.succ
    have h : (productMap n A).submatrix (Fin.consEquiv m) (Fin.consEquiv n) =
        A 0 ⊗ₖ productMap n' A' := by
      ext ⟨u, us⟩ ⟨v, vs⟩
      simp [productMap, Fin.prod_univ_succ, A']
    rw [← Matrix.rank_submatrix _ (Fin.consEquiv m) (Fin.consEquiv n), h,
      rank_kronecker, ih m' n' A', Fin.prod_univ_succ]

/-- Grouping local coordinate labels on the two sides of a cut. -/
private def flatten {I : Type*} (s : I → Prop) [DecidablePred s] {d : I → Type*}
    (ψ : (∀ i, d i) → ℂ) :
    Matrix (∀ i : {i // s i}, d i) (∀ i : {i // ¬s i}, d i) ℂ :=
  fun u v => ψ ((Equiv.piEquivPiSubtypeProd s d).symm (u, v))

private theorem productMap_gram {I : Type*} [Fintype I] [DecidableEq I]
    {d e : I → Type*} [∀ i, Fintype (e i)] [∀ i, DecidableEq (d i)]
    (U : ∀ i, Matrix (e i) (d i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (productMap d U)ᴴ * productMap d U = 1 := by
  ext x y
  calc
    _ = ∏ i, ((U i)ᴴ * U i) (x i) (y i) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, productMap, star_prod,
        ← Finset.prod_mul_distrib, Fintype.prod_sum]
    _ = _ := by
      simp only [hU, Matrix.one_apply]
      by_cases hxy : x = y
      · subst y
        simp
      · rw [if_neg hxy]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          by_contra! hn
          exact hxy (funext hn)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A left inverse and a right inverse recover the original flattening. -/
private theorem rank_mul_transpose_of_isometries {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (L : Matrix p m ℂ) (R : Matrix q n ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) :
    (L * A * Rᵀ).rank = A.rank := by
  let B := L * A * Rᵀ
  have hRight : Rᵀ * (Rᴴ)ᵀ = 1 := by
    rw [← transpose_mul, hR, transpose_one]
  have hA : Lᴴ * B * (Rᴴ)ᵀ = A := by
    calc
      _ = (Lᴴ * L) * A * (Rᵀ * (Rᴴ)ᵀ) := by dsimp [B]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hL, hRight, Matrix.one_mul, Matrix.mul_one]
  exact le_antisymm
    ((rank_mul_le_left (L * A) Rᵀ).trans (rank_mul_le_right L A))
    ((congrArg Matrix.rank hA).ge.trans
      ((rank_mul_le_left (Lᴴ * B) (Rᴴ)ᵀ).trans (rank_mul_le_right Lᴴ B)))

/-- Applying a matrix at each party acts on a cut by its two grouped matrices. -/
private theorem flatten_localImage {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → Prop) [DecidablePred s]
    {d e : I → Type*} [∀ i, Fintype (d i)]
    (ψ : (∀ i, d i) → ℂ) (U : ∀ i, Matrix (e i) (d i) ℂ) :
    flatten s (productMap d U *ᵥ ψ) =
      productMap (fun i : {i // s i} => d i) (fun i => U i) * flatten s ψ *
        (productMap (fun i : {i // ¬s i} => d i) (fun i => U i))ᵀ := by
  classical
  let E := Equiv.piEquivPiSubtypeProd s d
  apply Matrix.ext
  intro z w
  let v := (Equiv.piEquivPiSubtypeProd s e).symm (z, w)
  let L (x : ∀ i : {i // s i}, d i) := ∏ i : {i // s i}, U i (z i) (x i)
  let R (y : ∀ i : {i // ¬s i}, d i) := ∏ i : {i // ¬s i}, U i (w i) (y i)
  change (∑ x, (∏ i, U i (v i) (x i)) * ψ x) = _
  calc
    _ = ∑ x : (∀ i : {i // s i}, d i) × (∀ i : {i // ¬s i}, d i),
        L x.1 * ψ (E.symm x) * R x.2 := by
      refine (Fintype.sum_equiv E.symm _ _ ?_).symm
      rintro ⟨x, y⟩
      change L x * ψ (E.symm (x, y)) * R y =
        (∏ i, U i (v i) (E.symm (x, y) i)) * ψ (E.symm (x, y))
      rw [← Fintype.prod_subtype_mul_prod_subtype s
        (fun i => U i (v i) (E.symm (x, y) i))]
      have hl : (∏ i : {i // s i}, U i (v i) (E.symm (x, y) i)) = L x := by
        apply Finset.prod_congr rfl
        intro i _
        simp [v, E, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      have hr : (∏ i : {i // ¬s i}, U i (v i) (E.symm (x, y) i)) = R y := by
        apply Finset.prod_congr rfl
        intro i _
        simp [v, E, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      rw [hl, hr]
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type, Matrix.mul_apply, Finset.sum_mul,
        Matrix.transpose_apply, productMap, flatten, L, R, E]
      exact Finset.sum_comm

private theorem flatten_rank_local_isometries {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → Prop) [DecidablePred s]
    {d e : I → Type*} [∀ i, Fintype (d i)] [∀ i, Fintype (e i)]
    [∀ i, DecidableEq (d i)]
    (ψ : (∀ i, d i) → ℂ) (U : ∀ i, Matrix (e i) (d i) ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (flatten s (productMap d U *ᵥ ψ)).rank = (flatten s ψ).rank := by
  classical
  rw [flatten_localImage]
  exact rank_mul_transpose_of_isometries _ _ _
    (productMap_gram _ fun i => hU i) (productMap_gram _ fun i => hU i)

/-- Across a party cut, regrouping product factors just transposes the two index arrays. -/
private theorem flatten_rank_grouped {I : Type} [Fintype I] [DecidableEq I] (s : I → Prop) [DecidablePred s]
    (k : ℕ) (d : Fin k → I → Type) [∀ j i, Fintype (d j i)]
    (ψ : ∀ j, (∀ i, d j i) → ℂ) :
    (flatten (d := fun i => ∀ j, d j i) s (fun x => ∏ j, ψ j (fun i => x i j))).rank =
      ∏ j, (flatten s (ψ j)).rank := by
  classical
  let row := Equiv.piComm (fun (j : Fin k) (i : {i // s i}) => d j i)
  let col := Equiv.piComm (fun (j : Fin k) (i : {i // ¬s i}) => d j i)
  let A := flatten (d := fun i => ∀ j, d j i) s (fun x => ∏ j, ψ j (fun i => x i j))
  have h : A.submatrix row col =
      productMap (fun j => ∀ i : {i // ¬s i}, d j i) (fun j => flatten s (ψ j)) := by
    ext u v
    simp only [A, Matrix.submatrix_apply, flatten, productMap]
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg (ψ j)
    funext i
    by_cases hi : s i <;>
      simp [row, col, Equiv.piComm, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  change A.rank = _
  rw [← Matrix.rank_submatrix A row col, h, rank_productMap]

private theorem rectangular_outer {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (hA : A.rank ≤ 1) :
    ∃ u : m → ℂ, ∃ v : n → ℂ, A = vecMulVec u v := by
  classical
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := ℂ)
    (V := LinearMap.range A.mulVecLin)).mp hA
  have hcol (j : n) : A.col j ∈ LinearMap.range A.mulVecLin :=
    ⟨Pi.single j 1, A.mulVec_single_one j⟩
  choose v hv using fun j => hu ⟨A.col j, hcol j⟩
  refine ⟨u.val, v, ?_⟩
  ext i j
  have h := congrArg (fun z : LinearMap.range A.mulVecLin => z.val i) (hv j)
  simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    vecMulVec_apply, mul_comm] using h.symm

section Stripping

variable {I : Type} [Fintype I] [DecidableEq I]
variable {d : I → Type} [∀ i, Fintype (d i)]
variable (ψ : (∀ i, d i) → ℂ)

private theorem strip_one (base : ∀ i, d i) (hb : ψ base ≠ 0) (i : I)
    (hi : (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) (z : ∀ i, d i) :
    ψ z = (ψ (Function.update base i (z i)) / ψ base) *
      ψ (Function.update z i (base i)) := by
  obtain ⟨u, v, hv⟩ := rectangular_outer _ hi
  have he (x : ∀ j, d j) :
      ψ x = u (fun j : {j // j ∈ ({i} : Finset I)} => x j) * v (fun j : {j // j ∉ ({i} : Finset I)} => x j) := by
    let E := Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset I)) d
    have h := congrFun (congrFun hv (E x).1) (E x).2
    change ψ (E.symm (E x)) = u (E x).1 * v (E x).2 at h
    rw [E.symm_apply_apply] at h
    exact h
  simp only [div_mul_eq_mul_div]
  apply (eq_div_iff hb).mpr
  rw [he z, he base, he (Function.update base i (z i)), he (Function.update z i (base i))]
  have left (x y : ∀ j, d j) :
      (fun j : {j // j ∈ ({i} : Finset I)} => Function.update x i (y i) j) = (fun j : {j // j ∈ ({i} : Finset I)} => y j) := by
    funext j
    obtain ⟨j, hj⟩ := j
    obtain rfl := Finset.mem_singleton.mp hj
    simp
  have right (x y : ∀ j, d j) :
      (fun j : {j // j ∉ ({i} : Finset I)} => Function.update x i (y i) j) = (fun j : {j // j ∉ ({i} : Finset I)} => x j) := by
    funext j
    exact Function.update_of_ne (by simpa using j.property) _ _
  rw [left, left, right, right]
  ring

private def reset (base : ∀ i, d i) (s : Finset I) (z : ∀ i, d i) : ∀ i, d i :=
  fun i => if i ∈ s then base i else z i

private theorem strip_many (base : ∀ i, d i) (hb : ψ base ≠ 0)
    (s : Finset I) (hs : ∀ i ∈ s, (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) (z : ∀ i, d i) :
    ψ z = (∏ i ∈ s, ψ (Function.update base i (z i)) / ψ base) *
      ψ (reset base s z) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : reset base ∅ z = z := by funext i; simp [reset]
    simp [h]
  | @insert i s hi ih =>
    have hrest : ∀ j ∈ s, (flatten (· ∈ ({j} : Finset I)) ψ).rank ≤ 1 :=
      fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hreset : Function.update (reset base s z) i (base i) = reset base (insert i s) z := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [reset]
      · simp [reset, Function.update_of_ne hj, Finset.mem_insert, hj]
    calc
      ψ z = (∏ j ∈ s, ψ (Function.update base j (z j)) / ψ base) *
          ψ (reset base s z) := ih hrest
      _ = _ := by
        rw [strip_one ψ base hb i (hs i (Finset.mem_insert_self i s)) (reset base s z), hreset,
          Finset.prod_insert hi]
        simp only [reset, if_neg hi]
        ring

private theorem rank_cut_le_one_of_singletons (s : Finset I) (base : ∀ i, d i) (hb : ψ base ≠ 0)
    (hs : ∀ i ∈ s, (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) :
    (flatten (· ∈ s) ψ).rank ≤ 1 := by
  let u (x : ∀ i : { i // i ∈ s }, d i) :=
    ∏ i : { i // i ∈ s }, ψ (Function.update base i (x i)) / ψ base
  let v (y : ∀ i : { i // i ∉ s }, d i) :=
    ψ ((Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm ((fun i => base i), y))
  have he : flatten (· ∈ s) ψ = vecMulVec u v := by
    ext x y
    let z := (Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm (x, y)
    have hreset : reset base s z =
        (Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm ((fun i => base i), y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [z, reset, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
    change ψ z = u x * v y
    rw [strip_many ψ base hb s hs z, hreset]
    unfold u v
    congr 1
    rw [Finset.prod_subtype s (fun _ => Iff.rfl)
      (fun i => ψ (Function.update base i (z i)) / ψ base)]
    apply Finset.prod_congr rfl
    intro i _
    simp [z, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

/-- Opposite cuts have transposed flattenings. -/
private theorem rank_cut_complement (s : Finset I) :
    (flatten (· ∈ sᶜ) ψ).rank = (flatten (· ∈ s) ψ).rank := by
  let l : (∀ i : {i // i ∉ s}, d i) ≃ (∀ i : {i // i ∈ sᶜ}, d i) :=
    ⟨fun x i => x ⟨i, Finset.mem_compl.mp i.property⟩,
      fun x i => x ⟨i, Finset.mem_compl.mpr i.property⟩, fun _ => rfl, fun _ => rfl⟩
  let r : (∀ i : {i // i ∈ s}, d i) ≃ (∀ i : {i // i ∉ sᶜ}, d i) :=
    ⟨fun x i => x ⟨i, by simpa using i.property⟩,
      fun x i => x ⟨i, by simpa using i.property⟩, fun _ => rfl, fun _ => rfl⟩
  have h : (flatten (· ∈ sᶜ) ψ).submatrix l r = (flatten (· ∈ s) ψ)ᵀ := by
    apply Matrix.ext
    intro x y
    apply congrArg ψ
    funext i
    by_cases hi : i ∈ s <;>
      simp [flatten, Equiv.piEquivPiSubtypeProd_symm_apply, hi, l, r]
  rw [← Matrix.rank_submatrix _ l r, h, Matrix.rank_transpose]

end Stripping

private theorem cluster_half_or_zero {z : Bits} (hz : ∃ i, z i = 0) :
    clusterState z = 0 ∨ clusterState z = 1 / 2 := by
  have hneg (hp : z 0 = z 1 ∧ z 2 = z 3) : ¬(z 0 = 1 ∧ z 2 = 1) := by
    rintro ⟨h0, h2⟩
    obtain ⟨i, hi⟩ := hz
    have h1 : z 1 = 1 := hp.1.symm.trans h0
    have h3 : z 3 = 1 := hp.2.symm.trans h2
    have hall : ∀ i : Fin 4, z i = 1 := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    exact (by decide : (0 : Fin 2) ≠ 1) (hi.symm.trans (hall i))
  by_cases hp : z 0 = z 1 ∧ z 2 = z 3
  · right
    simp only [clusterState, cluster, if_pos hp, if_neg (hneg hp)]
    norm_num
  · left
    simp only [clusterState, cluster, if_neg hp, Rat.cast_zero]

private theorem cluster_cut_rank_ge_two (s : Finset (Fin 4)) (hs : s.Nonempty)
    (ht : ∃ i, i ∉ s) : 2 ≤ (flatten (· ∈ s) clusterState).rank := by
  let F := flatten (· ∈ s) clusterState
  let row (b : Fin 2) : ∀ i : {i // i ∈ s}, Fin 2 := fun _ => b
  let col (b : Fin 2) : ∀ i : {i // i ∉ s}, Fin 2 := fun _ => b
  let M := F.submatrix row col
  let E := Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ : Fin 4 => Fin 2)
  have hd (b : Fin 2) : E.symm (row b, col b) = fun _ => b := by
    funext i
    by_cases hi : i ∈ s <;> simp [E, row, col, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have h00 : M 0 0 = 1 / 2 := by
    change clusterState (E.symm (row 0, col 0)) = _
    rw [hd]
    norm_num [clusterState, cluster]
  have h11 : M 1 1 = -(1 / 2) := by
    change clusterState (E.symm (row 1, col 1)) = _
    rw [hd]
    norm_num [clusterState, cluster]
  have h01 : M 0 1 = 0 ∨ M 0 1 = 1 / 2 := by
    change clusterState (E.symm (row 0, col 1)) = _ ∨ _
    apply cluster_half_or_zero
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, by simp [E, row, Equiv.piEquivPiSubtypeProd_symm_apply, hi]⟩
  have h10 : M 1 0 = 0 ∨ M 1 0 = 1 / 2 := by
    change clusterState (E.symm (row 1, col 0)) = _ ∨ _
    apply cluster_half_or_zero
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simp [E, col, Equiv.piEquivPiSubtypeProd_symm_apply, hi]⟩
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_two, h00, h11]
    rcases h01 with h | h <;> rcases h10 with g | g <;> norm_num [h, g]
  have hm : M.rank = 2 := by simpa using Matrix.rank_of_det_ne_zero hdet
  calc 2 = M.rank := hm.symm
    _ ≤ F.rank := Matrix.rank_submatrix_le F row col

private theorem cluster_singleton_rank (i : Fin 4) : (flatten (· ∈ ({i} : Finset _)) clusterState).rank = 2 := by
  apply le_antisymm
  · refine (Matrix.rank_le_card_height _).trans ?_
    simp [Fintype.card_pi, Fintype.card_coe]
  · apply cluster_cut_rank_ge_two
    · exact Finset.singleton_nonempty _
    · fin_cases i <;> decide

private theorem prime_singleton_stripping {r : ℕ} (hprime : Nat.Prime r)
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (hprod : ∏ i, f i = r) :
    ∃ i, f i = r ∧ ∀ j, j ≠ i → f j = 1 := by
  classical
  have hdiv (i : ι) : f i ∣ r := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcases (i : ι) : f i = 1 ∨ f i = r :=
    hprime.eq_one_or_self_of_dvd _ (hdiv i)
  obtain ⟨i, hi⟩ : ∃ i, f i = r := by
    by_contra hnone
    have hall : ∀ i, f i = 1 := by
      intro i
      rcases hcases i with h | h
      · exact h
      · exact False.elim (hnone ⟨i, h⟩)
    have : (1 : ℕ) = r := by simpa [hall] using hprod
    exact hprime.ne_one this.symm
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hrest : (Finset.univ.erase i).prod f = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hprime.pos
    calc
      r * (Finset.univ.erase i).prod f =
          f i * (Finset.univ.erase i).prod f := by rw [hi]
      _ = ∏ k, f k := Finset.mul_prod_erase _ f (Finset.mem_univ i)
      _ = r * 1 := by simp [hprod]
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
  have hone := (Finset.prod_eq_one_iff.mp hrest)
  exact hone j hjmem

/-- The rank-two singleton cuts force effective factor supports to partition the parties.
Any effective support is a rank-one cut of the grouped product. -/
private theorem cluster_irreducible : ¬ ReducibleTensor (d := qubits) clusterState := by
  classical
  rintro ⟨k, S, dims, η, common, U, V, hp, hs, hn, hU, hV, he⟩
  have hcut (p : Fin 4 → Prop) [DecidablePred p] :
      (flatten p clusterState).rank = ∏ j, (flatten p (η j)).rank := by
    rw [← flatten_rank_local_isometries p clusterState U hU, he,
      flatten_rank_local_isometries p _ V hV]
    exact flatten_rank_grouped p k (fun j i => Fin (dims j i)) η
  let r (j : Fin k) (i : Fin 4) := (flatten (· ∈ ({i} : Finset _)) (η j)).rank
  have hr (i : Fin 4) : ∏ j, r j i = 2 := by
    rw [show (∏ j, r j i) = ∏ j, (flatten (· ∈ ({i} : Finset (Fin 4))) (η j)).rank from rfl,
      ← hcut (· ∈ ({i} : Finset (Fin 4))), cluster_singleton_rank]
  choose active ha using fun i => prime_singleton_stripping Nat.prime_two (r · i) (hr i)
  let j₀ := active 0
  let T : Finset (Fin 4) := Finset.univ.filter fun i => active i = j₀
  have hmem (i : Fin 4) : i ∈ T ↔ active i = j₀ := by simp [T]
  have hT : T.Nonempty := ⟨0, (hmem _).mpr rfl⟩
  have hsub : T ⊆ S j₀ := by
    intro i hi
    by_contra h
    have hdim : dims j₀ i = 1 := hs j₀ i h
    have hrow : Subsingleton (∀ a : {a : Fin 4 // a ∈ ({i} : Finset (Fin 4))}, Fin (dims j₀ a)) :=
      ⟨by
        intro x y
        funext a
        obtain ⟨a, ha⟩ := a
        obtain rfl := Finset.mem_singleton.mp ha
        have hd (v : Fin (dims j₀ a)) : v.val = 0 := by have := v.isLt; omega
        exact Fin.ext ((hd _).trans (hd _).symm)⟩
    have hle : r j₀ i ≤ 1 := (Matrix.rank_le_card_height _).trans
      (Fintype.card_le_one_iff_subsingleton.mpr hrow)
    have htwo := (ha i).1
    rw [(hmem i).mp hi] at htwo
    omega
  have hproper : ∃ i, i ∉ T := by
    by_contra! h
    exact hp j₀ (Finset.eq_univ_of_forall fun i => hsub (h i))
  have hfactor (j : Fin k) : (flatten (· ∈ T) (η j)).rank ≤ 1 := by
    obtain ⟨base, hb⟩ : ∃ base, η j base ≠ 0 := by
      by_contra! h
      simpa [h] using hn j
    by_cases hj : j = j₀
    · rw [← rank_cut_complement (η j) T]
      apply rank_cut_le_one_of_singletons (η j) _ base hb
      intro i hi
      have hne : j ≠ active i := fun h => (Finset.mem_compl.mp hi)
        ((hmem i).mpr (h.symm.trans hj))
      exact ((ha i).2 j hne).le
    · apply rank_cut_le_one_of_singletons (η j) _ base hb
      intro i hi
      exact ((ha i).2 j (by rwa [(hmem i).mp hi])).le
  have hle : (flatten (· ∈ T) clusterState).rank ≤ 1 := by
    rw [hcut]
    simpa using Finset.prod_le_prod fun j (_ : j ∈ Finset.univ) => hfactor j
  have htwo := cluster_cut_rank_ge_two T hT hproper
  omega

end

theorem result : ¬ claim := by
  rintro (h | h)
  · have ht := h 1 qubits positiveQubits clusterState cluster_state_normalized
      cluster_irreducible 2 (by decide) (Equiv.refl _)
    rw [cluster_ordered_zero _ 2 (by decide)] at ht
    exact (lt_irrefl 0) ht
  · have ht := h 1 qubits positiveQubits clusterState cluster_state_normalized
      cluster_irreducible 2 (by decide)
    rw [cluster_averaged_zero 2 (by decide)] at ht
    exact (lt_irrefl 0) ht

end D5.S3.Quantum.Entanglement.MultipartiteMonotones.CarrozzaChevrierLionniConverseRefutation
