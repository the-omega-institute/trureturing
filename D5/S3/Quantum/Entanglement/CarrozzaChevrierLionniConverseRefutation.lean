/- GID: D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation.claim; result=D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation.result; claim=D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation.claim
   digest: A four-qubit cluster state refutes both converses of Corollary 7. -/

import D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniIrreducibilityWIP
import Mathlib.Data.Fin.VecNotation

/-! The two Corollary 7 converses for arbitrary finite positive local dimensions. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniConverseRefutation

open Matrix
open CarrozzaChevrierLionniIrreducibilityWIP (ReducibleTensor)
open CarrozzaChevrierLionniConverseWIP
  (Bits BitPair Coordinate Tensor Wire qubits positiveQubits clusterState marginalEntry
    marginalEntry_four graphEntry_eq_marginal_chain)

/-- Eq. (24) for D = k+3. Each column pair traces all colors other than the
two strand colors incident to it. Internal strands carry top–bottom pairs. -/
def contraction (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
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

def ordered (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (σ : Equiv.Perm (Fin (k + 3))) (n : ℕ) : ℝ :=
  let A := contraction k hd ψ σ
  let X := A * Aᴴ
  (-Real.log ((X ^ n).trace.re / X.trace.re ^ n))

def averaged (k : ℕ) {d : Fin (k + 3) → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (n : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (k + 3)), ordered k hd ψ σ n) / (Nat.factorial (k + 3) : ℝ)

def orderedConverse : Prop :=
  ∀ (k : ℕ) (d : Fin (k + 3) → ℕ) (hd : ∀ i, 0 < d i) (ψ : Tensor d),
    (∑ x : Coordinate d, Complex.normSq (ψ x)) = 1 → ¬ ReducibleTensor ψ →
      ∀ n : ℕ, 2 ≤ n → ∀ σ, 0 < ordered k hd ψ σ n

def averagedConverse : Prop :=
  ∀ (k : ℕ) (d : Fin (k + 3) → ℕ) (hd : ∀ i, 0 < d i) (ψ : Tensor d),
    (∑ x : Coordinate d, Complex.normSq (ψ x)) = 1 → ¬ ReducibleTensor ψ →
      ∀ n : ℕ, 2 ≤ n → 0 < averaged k hd ψ n

def claim : Prop := orderedConverse ∨ averagedConverse

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

theorem contraction_four (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4)) :
    contraction 1 positiveQubits ψ σ = CarrozzaChevrierLionniConverseWIP.contraction ψ σ := by
  apply Matrix.ext
  intro out input
  let P := marginalEntry positiveQubits ψ (σ 0) (σ 1)
  let Q (a b : BitPair) := marginalEntry positiveQubits ψ (σ 1) (σ 2) a.swap b.swap
  let R := marginalEntry positiveQubits ψ (σ 2) (σ 3)
  change _ = CarrozzaChevrierLionniConverseWIP.graphEntry ψ (σ 0) (σ 1) (σ 2) (σ 3) out input
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

theorem ordered_four (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4)) (n : ℕ) :
    ordered 1 positiveQubits ψ σ n = CarrozzaChevrierLionniConverseWIP.ordered ψ σ n := by
  simp only [ordered, CarrozzaChevrierLionniConverseWIP.ordered, contraction_four]

theorem averaged_four (ψ : Bits → ℂ) (n : ℕ) :
    averaged 1 positiveQubits ψ n = CarrozzaChevrierLionniConverseWIP.averaged ψ n := by
  simp only [averaged, CarrozzaChevrierLionniConverseWIP.averaged, ordered_four]

/-- For the same witness, both general-model readouts vanish at every n ≥ 2. -/
theorem cluster_readouts_zero (n : ℕ) (hn : 2 ≤ n) :
    (∀ σ, ordered 1 positiveQubits clusterState σ n = 0) ∧
      averaged 1 positiveQubits clusterState n = 0 := by
  exact ⟨fun σ => (ordered_four _ σ n).trans
    (CarrozzaChevrierLionniConverseWIP.cluster_ordered_zero σ n hn),
    (averaged_four _ n).trans
      (CarrozzaChevrierLionniConverseWIP.cluster_averaged_zero n hn)⟩

theorem result : ¬ claim := by
  obtain ⟨hnorm, hirr, _⟩ := CarrozzaChevrierLionniIrreducibilityWIP.cluster_counterexample
  have hIrr : ¬ ReducibleTensor (d := qubits) clusterState := hirr
  rcases cluster_readouts_zero 2 (by decide) with ⟨ho, ha⟩
  rintro (h | h)
  · have ht := h 1 qubits positiveQubits clusterState hnorm hIrr 2 (by decide) (Equiv.refl _)
    rw [ho] at ht
    exact (lt_irrefl 0) ht
  · have ht := h 1 qubits positiveQubits clusterState hnorm hIrr 2 (by decide)
    rw [ha] at ht
    exact (lt_irrefl 0) ht

end D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniConverseRefutation

end
