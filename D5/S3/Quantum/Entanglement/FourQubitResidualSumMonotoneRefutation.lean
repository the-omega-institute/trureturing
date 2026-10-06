/- GID: D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.claim; result=D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result; claim=D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.claim
   digest: A one-qubit measurement raises the residual-correlation sum of four qubits on average. -/

/-
proof_shape: linearEntropy, concurrence, residualSum: definition (the paper's linear entropy,
  Wootters' concurrence and Eq. (7))
proof_shape: claim: definition (published conjecture, arXiv:quant-ph/0703098, read for every
  normalized four-qubit vector and every local instrument on qubit A)
proof_shape: psi, instrument: definition (the counterexample state and measurement)
proof_shape: pairEquiv, outEquiv, singleEquiv, out3Equiv, fourEquiv: definition (coordinate
  equivalences of the qubit configurations)
proof_shape: phi0, phi1, xmat, rmat: private definition (the two normalized outcomes and real X
  matrices)
proof_shape: result: bind-only (as local steps: the reindexing of the frozen reduced states and of
  sigmaYTensor to Fin 2 × Fin 2, invariance of the characteristic polynomial under reindexing,
  the factorization of the characteristic polynomial of an X matrix and the sorting of its
  roots, the coordinate form of the frozen localOp on qubit A, and entrywise rational
  computations of the reduced states, linear entropies, concurrences and outcome probabilities)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12466; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.Outside
    sha256:22a66bd1cf70aa0215d327bcab393d44fd715d36c5b7924a2279d5500f074f1a
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.join
    sha256:b4d70d024cb174f7d6ec1491438cded1a4c04640dacc0715b561e92baf6f0409
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.reducedState
    sha256:e65dc7b2f0f3b5addc7d668c466eff01c28a16d0b5d73337e0f7016866bfd137
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.sigmaYTensor
    sha256:288ee9132d194157051954f10426fc5977682fb38401f8faee7f42fca3cd86eb
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.timeReversed
    sha256:9c0316e5a7bce75fffa602c752a613e0e25ff1e3c8cce0c5795192654d42362c
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/FiniteDimensional.qubitX
    sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  D5/S3/Quantum/FiniteDimensional.qubitZ
    sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.tensorOp
    sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.localOp
    sha256:a8376a57b9d3e52109fea12f73db0ab84164e4cb061792f870b54843e0dedb67
-/

import D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation

/-!
Y.-K. Bai, D. Yang and Z. D. Wang, *Multipartite quantum correlation and entanglement in four-qubit
pure states*, arXiv:quant-ph/0703098 (Phys. Rev. A 76 (2007) 022336), conjecture that the sum of the
residual correlations `M = Σ_k τ_k - 2 Σ_{p>q} C_pq²` of a four-qubit pure state (Eq. (7)), with
the one-qubit linear entropies `τ_k = 2 (1 - Tr ρ_k²)` and Wootters' concurrences `C_pq` of the
two-qubit reduced states, is an entanglement monotone. It is not. For
`ψ = (20|0001⟩ + 2|1000⟩ + 6|1011⟩ + |1110⟩)/21` and the measurement `K₀ = diag(21/29, 0)`,
`K₁ = diag(20/29, 1)` on the qubit `A`, the outcome `K₀` has probability `400/841` and leaves the
product state `|0001⟩`, and the outcome `K₁` has probability `441/841` and leaves
`φ₁ = (400|0001⟩ + 58|1000⟩ + 174|1011⟩ + 29|1110⟩)/441`. Every two-qubit reduced state is a real X
matrix, whose spin-flip product has eigenvalues `(√(us) ± |w|)²` and `(√(vr) ± |z|)²`, so
`M(ψ) = 7552/194481` and `M(φ₁) = 2967747712/37822859361`, and the average of `M` after the
measurement is `3528832/85766121 > M(ψ)`.
-/

open Matrix Polynomial D5.S3.Quantum.FiniteDimensional
  D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
  (Outside join reducedState sigmaYTensor timeReversed)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (localOp tensorOp)

/-- The linear entropy `τ_k = 2 (1 - Tr ρ_k²)` of the qubit `k`, with `ρ_k` the reduced state of
the qubit `k`. -/
noncomputable def linearEntropy (k : Fin 4) (ψ : (Fin 4 → Fin 2) → ℂ) : ℝ :=
  2 * (1 - (trace (reducedState {k} ψ * reducedState {k} ψ)).re)

/-- Wootters' concurrence `C_pq = max (√λ₁ - √λ₂ - √λ₃ - √λ₄) 0` of the pair `{p, q}`, where
`λ₁ ≥ λ₂ ≥ λ₃ ≥ λ₄` are the real parts of the roots, with multiplicity, of the characteristic
polynomial of `ρ_pq (σ_y ⊗ σ_y) ρ_pq^* (σ_y ⊗ σ_y)`, sorted decreasingly. -/
noncomputable def concurrence (p q : Fin 4) (ψ : (Fin 4 → Fin 2) → ℂ) : ℝ :=
  let l := ((reducedState {p, q} ψ * timeReversed {p, q} (reducedState {p, q} ψ)).charpoly.roots.map
    Complex.re).sort (· ≥ ·)
  max (Real.sqrt (l.getD 0 0) - Real.sqrt (l.getD 1 0) - Real.sqrt (l.getD 2 0) -
    Real.sqrt (l.getD 3 0)) 0

/-- The sum of the residual correlations, Eq. (7): `M = Σ_k τ_k - 2 Σ_{p<q} C_pq²`. -/
noncomputable def residualSum (ψ : (Fin 4 → Fin 2) → ℂ) : ℝ :=
  ∑ k, linearEntropy k ψ - 2 * ∑ p, ∑ q, if p < q then concurrence p q ψ ^ 2 else 0

/-- The sum of the residual correlations does not increase on average under any complete
instrument on the qubit `A`, a one-step LOCC protocol; outcomes of probability zero are omitted. -/
def claim : Prop :=
  ∀ ψ : (Fin 4 → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 →
    ∀ (n : ℕ) (K : Fin n → Matrix (Fin 2) (Fin 2) ℂ), ∑ j, (K j)ᴴ * K j = 1 →
      ∑ j, (if ∑ w, ‖(localOp (0 : Fin 4) (K j) *ᵥ ψ) w‖ ^ 2 = 0 then 0 else
        (∑ w, ‖(localOp (0 : Fin 4) (K j) *ᵥ ψ) w‖ ^ 2) *
          residualSum (((Real.sqrt (∑ w, ‖(localOp (0 : Fin 4) (K j) *ᵥ ψ) w‖ ^ 2))⁻¹ : ℂ) •
            (localOp (0 : Fin 4) (K j) *ᵥ ψ))) ≤
        residualSum ψ

/-- The configurations of the pair `{p, q}` as `Fin 2 × Fin 2`, the qubit `p` first. -/
def pairEquiv (p q : Fin 4) (h : p ≠ q) :
    (↥({p, q} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 × Fin 2 where
  toFun x := (x ⟨p, by simp⟩, x ⟨q, by simp⟩)
  invFun ab i := if i.1 = p then ab.1 else ab.2
  left_inv x := by
    funext ⟨i, hi⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp
    · simp [Ne.symm h]
  right_inv ab := by simp [Ne.symm h]

/-- The configurations of the two qubits `r, s` outside `{p, q}` as `Fin 2 × Fin 2`. -/
def outEquiv (p q r s : Fin 4) (hr : r ∉ ({p, q} : Finset (Fin 4)))
    (hs : s ∉ ({p, q} : Finset (Fin 4))) (hrs : r ≠ s)
    (hcov : ∀ i : Fin 4, i ∉ ({p, q} : Finset (Fin 4)) → i = r ∨ i = s) :
    (Outside ({p, q} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 × Fin 2 where
  toFun z := (z ⟨r, hr⟩, z ⟨s, hs⟩)
  invFun cd i := if i.1 = r then cd.1 else cd.2
  left_inv z := by
    funext ⟨i, hi⟩
    rcases hcov i hi with rfl | rfl
    · simp
    · simp [Ne.symm hrs]
  right_inv cd := by simp [Ne.symm hrs]

/-- The configurations of the single qubit `k` as `Fin 2`. -/
def singleEquiv (k : Fin 4) : (↥({k} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 where
  toFun x := x ⟨k, by simp⟩
  invFun a _ := a
  left_inv x := by
    funext ⟨i, hi⟩
    simp only [Finset.mem_singleton] at hi
    subst hi
    rfl
  right_inv _ := rfl

/-- The configurations of the three qubits `r, s, t` outside `k` as `Fin 2 × Fin 2 × Fin 2`. -/
def out3Equiv (k r s t : Fin 4) (hr : r ∉ ({k} : Finset (Fin 4)))
    (hs : s ∉ ({k} : Finset (Fin 4))) (ht : t ∉ ({k} : Finset (Fin 4))) (hrs : r ≠ s)
    (hrt : r ≠ t) (hst : s ≠ t)
    (hcov : ∀ i : Fin 4, i ∉ ({k} : Finset (Fin 4)) → i = r ∨ i = s ∨ i = t) :
    (Outside ({k} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun z := (z ⟨r, hr⟩, z ⟨s, hs⟩, z ⟨t, ht⟩)
  invFun x i := if i.1 = r then x.1 else if i.1 = s then x.2.1 else x.2.2
  left_inv z := by
    funext ⟨i, hi⟩
    rcases hcov i hi with rfl | rfl | rfl
    · simp
    · simp [Ne.symm hrs]
    · simp [Ne.symm hrt, Ne.symm hst]
  right_inv x := by simp [Ne.symm hrs, Ne.symm hrt, Ne.symm hst]

/-- The configurations of the four qubits as `Fin 2 × Fin 2 × Fin 2 × Fin 2`. -/
def fourEquiv : (Fin 4 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 where
  toFun w := (w 0, w 1, w 2, w 3)
  invFun x := ![x.1, x.2.1, x.2.2.1, x.2.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- The real X matrix with diagonal `u, v, r, s` in the basis `00, 01, 10, 11`, the entry `w`
between `00` and `11` and the entry `z` between `01` and `10`. -/
private def xmat (u v r s w z : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun x y =>
  if x = y then
    (if x = (0, 0) then (u : ℂ) else if x = (0, 1) then v else if x = (1, 0) then r else s)
  else if (x = (0, 0) ∧ y = (1, 1)) ∨ (x = (1, 1) ∧ y = (0, 0)) then (w : ℂ)
  else if (x = (0, 1) ∧ y = (1, 0)) ∨ (x = (1, 0) ∧ y = (0, 1)) then (z : ℂ) else 0

/-- The product of an X matrix with its spin flip, written entrywise. -/
private def rmat (u v r s w z : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun x y =>
  if x = y then
    (if x = (0, 0) ∨ x = (1, 1) then ((u * s + w ^ 2 : ℝ) : ℂ) else ((v * r + z ^ 2 : ℝ) : ℂ))
  else if x = (0, 0) ∧ y = (1, 1) then ((2 * u * w : ℝ) : ℂ)
  else if x = (1, 1) ∧ y = (0, 0) then ((2 * s * w : ℝ) : ℂ)
  else if x = (0, 1) ∧ y = (1, 0) then ((2 * v * z : ℝ) : ℂ)
  else if x = (1, 0) ∧ y = (0, 1) then ((2 * r * z : ℝ) : ℂ) else 0

/-- The counterexample state `(20|0001⟩ + 2|1000⟩ + 6|1011⟩ + |1110⟩)/21`. -/
noncomputable def psi : (Fin 4 → Fin 2) → ℂ := fun w =>
  if (w 0, w 1, w 2, w 3) = (0, 0, 0, 1) then 20 / 21
  else if (w 0, w 1, w 2, w 3) = (1, 0, 0, 0) then 2 / 21
  else if (w 0, w 1, w 2, w 3) = (1, 0, 1, 1) then 6 / 21
  else if (w 0, w 1, w 2, w 3) = (1, 1, 1, 0) then 1 / 21 else 0

/-- The measurement `K₀ = diag(21/29, 0)`, `K₁ = diag(20/29, 1)` on the qubit `A`. -/
noncomputable def instrument : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![21 / 29, 0; 0, 0], !![20 / 29, 0; 0, 1]]

/-- The normalized outcome `|0001⟩` of `K₀`. -/
private def phi0 : (Fin 4 → Fin 2) → ℂ := fun w =>
  if (w 0, w 1, w 2, w 3) = (0, 0, 0, 1) then 1 else 0

/-- The normalized outcome `(400|0001⟩ + 58|1000⟩ + 174|1011⟩ + 29|1110⟩)/441` of `K₁`. -/
private noncomputable def phi1 : (Fin 4 → Fin 2) → ℂ := fun w =>
  if (w 0, w 1, w 2, w 3) = (0, 0, 0, 1) then 400 / 441
  else if (w 0, w 1, w 2, w 3) = (1, 0, 0, 0) then 58 / 441
  else if (w 0, w 1, w 2, w 3) = (1, 0, 1, 1) then 174 / 441
  else if (w 0, w 1, w 2, w 3) = (1, 1, 1, 0) then 29 / 441 else 0

set_option maxHeartbeats 8000000 in -- three states' explicit computations share this declaration
/-- The conjecture fails for `psi` and `instrument`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      S = Matrix.of fun x y => (Complex.I • (qubitX * qubitZ)) x.1 y.1 *
        (Complex.I • (qubitX * qubitZ)) x.2 y.2 := ⟨_, rfl⟩
  have hsig : ∀ (p q : Fin 4) (h : p ≠ q),
      reindex (pairEquiv p q h) (pairEquiv p q h) (sigmaYTensor ({p, q} : Finset (Fin 4))) = S := by
    intro p q h
    rw [hS]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [reindex_apply, submatrix_apply, sigmaYTensor, Matrix.of_apply, pairEquiv,
      Equiv.coe_fn_symm_mk]
    rw [Finset.prod_coe_sort ({p, q} : Finset (Fin 4)) (fun i => (Complex.I • (qubitX * qubitZ))
      (if i = p then a else b) (if i = p then c else d)), Finset.prod_pair h]
    simp [Ne.symm h]
  have hCP : ∀ (p q : Fin 4) (h : p ≠ q)
      (ρ : Matrix (↥({p, q} : Finset (Fin 4)) → Fin 2) (↥({p, q} : Finset (Fin 4)) → Fin 2) ℂ),
      (ρ * timeReversed {p, q} ρ).charpoly =
        (reindex (pairEquiv p q h) (pairEquiv p q h) ρ *
          (S * (reindex (pairEquiv p q h) (pairEquiv p q h) ρ).map star * S)).charpoly := by
    intro p q h ρ
    rw [← hsig p q h, ← Matrix.charpoly_reindex (pairEquiv p q h) (ρ * timeReversed {p, q} ρ)]
    congr 1
    simp only [timeReversed, reindex_apply, ← submatrix_map, submatrix_mul_equiv, Matrix.mul_assoc]
  have hpe : ∀ (p q r s : Fin 4) (h : p ≠ q) (hr : r ∉ ({p, q} : Finset (Fin 4)))
      (hs : s ∉ ({p, q} : Finset (Fin 4))) (hrs : r ≠ s)
      (hcov : ∀ i : Fin 4, i ∉ ({p, q} : Finset (Fin 4)) → i = r ∨ i = s)
      (ψ : (Fin 4 → Fin 2) → ℂ) (a b a' b' : Fin 2),
      reindex (pairEquiv p q h) (pairEquiv p q h) (reducedState ({p, q} : Finset (Fin 4)) ψ) (a, b)
          (a', b') =
        ∑ c, ∑ d, ψ (fun i => if i = p then a else if i = q then b else if i = r then c else d) *
          star (ψ (fun i =>
            if i = p then a' else if i = q then b' else if i = r then c else d)) := by
    intro p q r s h hr hs hrs hcov ψ a b a' b'
    simp only [reindex_apply, submatrix_apply, reducedState, partialTraceRight, Matrix.of_apply]
    rw [← Equiv.sum_comp (outEquiv p q r s hr hs hrs hcov).symm, Fintype.sum_prod_type]
    have hp : p ∈ ({p, q} : Finset (Fin 4)) := by simp
    have hq : q ∈ ({p, q} : Finset (Fin 4)) := by simp
    have key : ∀ x y c d : Fin 2,
        join ({p, q} : Finset (Fin 4)) ((pairEquiv p q h).symm (x, y))
            ((outEquiv p q r s hr hs hrs hcov).symm (c, d)) =
          fun i => if i = p then x else if i = q then y else if i = r then c else d := by
      intro x y c d
      funext i
      simp only [join, Equiv.piEquivPiSubtypeProd_symm_apply, pairEquiv, outEquiv,
        Equiv.coe_fn_symm_mk]
      by_cases hi : i ∈ ({p, q} : Finset (Fin 4))
      · rw [dif_pos hi]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simp
        · simp [Ne.symm h]
      · rw [dif_neg hi]
        have hip : i ≠ p := fun e => hi (e ▸ hp)
        have hiq : i ≠ q := fun e => hi (e ▸ hq)
        rcases hcov i hi with rfl | rfl
        · simp [hip, hiq]
        · simp [hip, hiq, Ne.symm hrs]
    simp only [key]
  have hse : ∀ (k r s t : Fin 4) (hr : r ∉ ({k} : Finset (Fin 4)))
      (hs : s ∉ ({k} : Finset (Fin 4))) (ht : t ∉ ({k} : Finset (Fin 4))) (hrs : r ≠ s)
      (hrt : r ≠ t) (hst : s ≠ t)
      (hcov : ∀ i : Fin 4, i ∉ ({k} : Finset (Fin 4)) → i = r ∨ i = s ∨ i = t)
      (ψ : (Fin 4 → Fin 2) → ℂ) (a a' : Fin 2),
      reducedState ({k} : Finset (Fin 4)) ψ ((singleEquiv k).symm a) ((singleEquiv k).symm a') =
        ∑ b, ∑ c, ∑ d,
          ψ (fun i => if i = k then a else if i = r then b else if i = s then c else d) *
            star (ψ (fun i =>
              if i = k then a' else if i = r then b else if i = s then c else d)) := by
    intro k r s t hr hs ht hrs hrt hst hcov ψ a a'
    simp only [reducedState, partialTraceRight, Matrix.of_apply]
    rw [← Equiv.sum_comp (out3Equiv k r s t hr hs ht hrs hrt hst hcov).symm, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have hk : k ∈ ({k} : Finset (Fin 4)) := by simp
    have key : ∀ x b c d : Fin 2,
        join ({k} : Finset (Fin 4)) ((singleEquiv k).symm x)
            ((out3Equiv k r s t hr hs ht hrs hrt hst hcov).symm (b, c, d)) =
          fun i => if i = k then x else if i = r then b else if i = s then c else d := by
      intro x b c d
      funext i
      simp only [join, Equiv.piEquivPiSubtypeProd_symm_apply, singleEquiv, out3Equiv,
        Equiv.coe_fn_symm_mk]
      by_cases hi : i ∈ ({k} : Finset (Fin 4))
      · rw [dif_pos hi]
        simp only [Finset.mem_singleton] at hi
        subst hi
        simp
      · rw [dif_neg hi]
        have hik : i ≠ k := fun e => hi (e ▸ hk)
        rcases hcov i hi with rfl | rfl | rfl
        · simp [hik]
        · simp [hik, Ne.symm hrs]
        · simp [hik, Ne.symm hrt, Ne.symm hst]
    simp only [key]
  have htr : ∀ (k : Fin 4)
      (ρ : Matrix (↥({k} : Finset (Fin 4)) → Fin 2) (↥({k} : Finset (Fin 4)) → Fin 2) ℂ),
      trace (ρ * ρ) = ∑ a, ∑ a', ρ ((singleEquiv k).symm a) ((singleEquiv k).symm a') *
        ρ ((singleEquiv k).symm a') ((singleEquiv k).symm a) := by
    intro k ρ
    simp only [trace, diag, mul_apply]
    rw [← Equiv.sum_comp (singleEquiv k).symm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp (singleEquiv k).symm]
  have hsum : ∀ f : (Fin 4 → Fin 2) → ℝ, ∑ w, f w = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
    intro f
    rw [← Equiv.sum_comp fourEquiv.symm]
    simp only [Fintype.sum_prod_type]
    rfl
  have hsumC : ∀ f : (Fin 4 → Fin 2) → ℂ, ∑ w, f w = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
    intro f
    rw [← Equiv.sum_comp fourEquiv.symm]
    simp only [Fintype.sum_prod_type]
    rfl
  have hupd : ∀ x0 x1 x2 x3 a : Fin 2,
      Function.update ![x0, x1, x2, x3] 0 a = ![a, x1, x2, x3] := by
    intro x0 x1 x2 x3 a
    funext i
    fin_cases i <;> rfl
  have hloc : ∀ (K : Matrix (Fin 2) (Fin 2) ℂ) (ψ : (Fin 4 → Fin 2) → ℂ) (w : Fin 4 → Fin 2),
      (localOp (0 : Fin 4) K *ᵥ ψ) w = ∑ a, K (w 0) a * ψ (Function.update w 0 a) := by
    intro K ψ w
    obtain ⟨⟨x0, x1, x2, x3⟩, rfl⟩ : ∃ x : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ![x.1, x.2.1, x.2.2.1, x.2.2.2] = w :=
      ⟨(w 0, w 1, w 2, w 3), by funext i; fin_cases i <;> rfl⟩
    simp only [Matrix.mulVec, dotProduct, localOp, tensorOp, Matrix.of_apply, hupd]
    rw [hsumC]
    fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
      simp [Fin.prod_univ_four, Fin.sum_univ_two, Function.update_apply, Matrix.one_apply]
  have roots_xmat : ∀ u v r s w z : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ r → 0 ≤ s →
      ((xmat u v r s w z * (S * (xmat u v r s w z).map star * S)).charpoly.roots.map
        Complex.re) =
        {(Real.sqrt (u * s) + |w|) ^ 2, (Real.sqrt (u * s) - |w|) ^ 2,
          (Real.sqrt (v * r) + |z|) ^ 2, (Real.sqrt (v * r) - |z|) ^ 2} := by
    intro u v r s w z hu hv hr hs
    have hR : xmat u v r s w z * (S * (xmat u v r s w z).map star * S) =
        rmat u v r s w z := by
      rw [hS]
      ext ⟨a, b⟩ ⟨c, d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [xmat, rmat, qubitX, qubitZ, Matrix.mul_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two] <;> ring
    have hCP : (rmat u v r s w z).charpoly =
        (X ^ 2 - C ((2 * (u * s + w ^ 2) : ℝ) : ℂ) * X + C (((u * s - w ^ 2) ^ 2 : ℝ) : ℂ)) *
        (X ^ 2 - C ((2 * (v * r + z ^ 2) : ℝ) : ℂ) * X + C (((v * r - z ^ 2) ^ 2 : ℝ) : ℂ)) := by
      rw [← Matrix.charpoly_reindex finProdFinEquiv]
      rw [Matrix.charpoly, Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
      simp [Matrix.charmatrix, Matrix.submatrix, Matrix.reindex_apply, finProdFinEquiv, rmat,
        Fin.succAbove, Fin.divNat, Fin.modNat]
      simp only [map_ofNat]
      ring
    have hq : ∀ p q t : ℝ, 0 ≤ p → 0 ≤ q →
        (X ^ 2 - C ((2 * (p * q + t ^ 2) : ℝ) : ℂ) * X + C (((p * q - t ^ 2) ^ 2 : ℝ) : ℂ)) =
          (X - C (((Real.sqrt (p * q) + |t|) ^ 2 : ℝ) : ℂ)) *
            (X - C (((Real.sqrt (p * q) - |t|) ^ 2 : ℝ) : ℂ)) := by
      intro p q t hp hq
      have h1 : (Real.sqrt (p * q)) ^ 2 = p * q := Real.sq_sqrt (mul_nonneg hp hq)
      have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
      have r1 : (2 * (p * q + t ^ 2) : ℝ) =
          (Real.sqrt (p * q) + |t|) ^ 2 + (Real.sqrt (p * q) - |t|) ^ 2 := by
        linear_combination (-2 : ℝ) * h1 - 2 * h2
      have r2 : ((p * q - t ^ 2) ^ 2 : ℝ) =
          (Real.sqrt (p * q) + |t|) ^ 2 * (Real.sqrt (p * q) - |t|) ^ 2 := by
        have : (Real.sqrt (p * q) + |t|) ^ 2 * (Real.sqrt (p * q) - |t|) ^ 2 =
            (Real.sqrt (p * q) ^ 2 - |t| ^ 2) ^ 2 := by ring
        rw [this, h1, h2]
      have e1 : ((2 * (p * q + t ^ 2) : ℝ) : ℂ) =
          (((Real.sqrt (p * q) + |t|) ^ 2 : ℝ) : ℂ) +
            (((Real.sqrt (p * q) - |t|) ^ 2 : ℝ) : ℂ) := by
        rw [r1]; push_cast; ring
      have e2 : (((p * q - t ^ 2) ^ 2 : ℝ) : ℂ) =
          (((Real.sqrt (p * q) + |t|) ^ 2 : ℝ) : ℂ) *
            (((Real.sqrt (p * q) - |t|) ^ 2 : ℝ) : ℂ) := by
        rw [r2]; push_cast; ring
      rw [e1, e2, map_add, map_mul]; ring
    rw [hR, hCP, hq u s w hu hs, hq v r z hv hr]
    have : (X - C (((Real.sqrt (u * s) + |w|) ^ 2 : ℝ) : ℂ)) *
          (X - C (((Real.sqrt (u * s) - |w|) ^ 2 : ℝ) : ℂ)) *
        ((X - C (((Real.sqrt (v * r) + |z|) ^ 2 : ℝ) : ℂ)) *
          (X - C (((Real.sqrt (v * r) - |z|) ^ 2 : ℝ) : ℂ))) =
        (({(((Real.sqrt (u * s) + |w|) ^ 2 : ℝ) : ℂ), (((Real.sqrt (u * s) - |w|) ^ 2 : ℝ) : ℂ),
          (((Real.sqrt (v * r) + |z|) ^ 2 : ℝ) : ℂ), (((Real.sqrt (v * r) - |z|) ^ 2 : ℝ) : ℂ)} :
          Multiset ℂ).map fun x => X - C x).prod := by
      simp [Multiset.insert_eq_cons]; ring
    rw [this, Polynomial.roots_multiset_prod_X_sub_C]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Complex.ofReal_re]
  have sort4 : ∀ a b c d : ℝ, b ≤ a → c ≤ b → d ≤ c →
      (({a, b, c, d} : Multiset ℝ).sort (· ≥ ·)) = [a, b, c, d] := by
    intro a b c d h1 h2 h3
    rw [Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.insert_eq_cons, Multiset.sort_cons,
      Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.sort_singleton]
    · intro x hx; rw [Multiset.mem_singleton] at hx; linarith
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> linarith
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> linarith
  have hW : ∀ (p q : Fin 4) (h : p ≠ q) (ψ : (Fin 4 → Fin 2) → ℂ) (u v r s w : ℝ),
      reindex (pairEquiv p q h) (pairEquiv p q h) (reducedState ({p, q} : Finset (Fin 4)) ψ) =
        xmat u v r s w 0 → 0 ≤ u → 0 ≤ v → 0 ≤ r → 0 ≤ s → v * r = 0 →
        |w| ≤ Real.sqrt (u * s) → concurrence p q ψ = 2 * |w| := by
    intro p q h ψ u v r s w hR hu hv hr hs hvr hw
    simp only [concurrence]
    rw [hCP p q h, hR, roots_xmat u v r s w 0 hu hv hr hs, hvr, Real.sqrt_zero, abs_zero, add_zero,
      sub_zero]
    have hA : 0 ≤ Real.sqrt (u * s) - |w| := by linarith
    rw [sort4 _ _ _ _ (by nlinarith [abs_nonneg w, Real.sqrt_nonneg (u * s)])
      (by nlinarith [sq_nonneg (Real.sqrt (u * s) - |w|)]) le_rfl]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq hA]
    have e : Real.sqrt (u * s) + |w| - (Real.sqrt (u * s) - |w|) - Real.sqrt (0 ^ 2) -
        Real.sqrt (0 ^ 2) = 2 * |w| := by simp; ring
    rw [e, max_eq_left (by positivity)]
  have hZ : ∀ (p q : Fin 4) (h : p ≠ q) (ψ : (Fin 4 → Fin 2) → ℂ) (u v r s z : ℝ),
      reindex (pairEquiv p q h) (pairEquiv p q h) (reducedState ({p, q} : Finset (Fin 4)) ψ) =
        xmat u v r s 0 z → 0 ≤ u → 0 ≤ v → 0 ≤ r → 0 ≤ s → u * s = 0 →
        |z| ≤ Real.sqrt (v * r) → concurrence p q ψ = 2 * |z| := by
    intro p q h ψ u v r s z hR hu hv hr hs hus hz
    simp only [concurrence]
    rw [hCP p q h, hR, roots_xmat u v r s 0 z hu hv hr hs, hus, Real.sqrt_zero, abs_zero, add_zero,
      sub_zero]
    have hA : 0 ≤ Real.sqrt (v * r) - |z| := by linarith
    have hperm : ({(0 : ℝ) ^ 2, (0 : ℝ) ^ 2, (Real.sqrt (v * r) + |z|) ^ 2,
        (Real.sqrt (v * r) - |z|) ^ 2} : Multiset ℝ) =
        {(Real.sqrt (v * r) + |z|) ^ 2, (Real.sqrt (v * r) - |z|) ^ 2, (0 : ℝ) ^ 2,
          (0 : ℝ) ^ 2} := by
      simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
      rw [Multiset.cons_swap ((0 : ℝ) ^ 2) ((Real.sqrt (v * r) + |z|) ^ 2),
        Multiset.cons_swap ((0 : ℝ) ^ 2) ((Real.sqrt (v * r) + |z|) ^ 2),
        Multiset.cons_swap ((0 : ℝ) ^ 2) ((Real.sqrt (v * r) - |z|) ^ 2),
        Multiset.cons_swap ((0 : ℝ) ^ 2) ((Real.sqrt (v * r) - |z|) ^ 2)]
    rw [hperm, sort4 _ _ _ _ (by nlinarith [abs_nonneg z, Real.sqrt_nonneg (v * r)])
      (by nlinarith [sq_nonneg (Real.sqrt (v * r) - |z|)]) le_rfl]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq hA]
    have e : Real.sqrt (v * r) + |z| - (Real.sqrt (v * r) - |z|) - Real.sqrt (0 ^ 2) -
        Real.sqrt (0 ^ 2) = 2 * |z| := by simp; ring
    rw [e, max_eq_left (by positivity)]
  have hCD : ∀ (p q : Fin 4) (h : p ≠ q) (ψ : (Fin 4 → Fin 2) → ℂ) (u v r s w : ℝ),
      reindex (pairEquiv p q h) (pairEquiv p q h) (reducedState ({p, q} : Finset (Fin 4)) ψ) =
        xmat u v r s w 0 → 0 ≤ u → 0 ≤ v → 0 ≤ r → 0 ≤ s → |w| = Real.sqrt (u * s) →
        Real.sqrt (v * r) ≤ 2 * |w| → |w| ≤ Real.sqrt (v * r) → concurrence p q ψ = 0 := by
    intro p q h ψ u v r s w hR hu hv hr hs hw h1 h2
    simp only [concurrence]
    rw [hCP p q h, hR, roots_xmat u v r s w 0 hu hv hr hs, ← hw, abs_zero, add_zero, sub_zero,
      sub_self]
    have hperm : ({(|w| + |w|) ^ 2, (0 : ℝ) ^ 2, Real.sqrt (v * r) ^ 2, Real.sqrt (v * r) ^ 2} :
        Multiset ℝ) = {(|w| + |w|) ^ 2, Real.sqrt (v * r) ^ 2, Real.sqrt (v * r) ^ 2,
          (0 : ℝ) ^ 2} := by
      simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
      rw [Multiset.cons_swap ((0 : ℝ) ^ 2) (Real.sqrt (v * r) ^ 2),
        Multiset.cons_swap ((0 : ℝ) ^ 2) (Real.sqrt (v * r) ^ 2)]
    rw [hperm, sort4 _ _ _ _ (by nlinarith [Real.sqrt_nonneg (v * r)]) le_rfl
      (by nlinarith [sq_nonneg (Real.sqrt (v * r))])]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (Real.sqrt_nonneg _)]
    rw [max_eq_right (by simp; linarith)]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hpe01 := hpe 0 1 2 3 h01 (by decide) (by decide) (by decide) (by decide)
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have hpe02 := hpe 0 2 1 3 h02 (by decide) (by decide) (by decide) (by decide)
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have hpe03 := hpe 0 3 1 2 h03 (by decide) (by decide) (by decide) (by decide)
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have hpe12 := hpe 1 2 0 3 h12 (by decide) (by decide) (by decide) (by decide)
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have hpe13 := hpe 1 3 0 2 h13 (by decide) (by decide) (by decide) (by decide)
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hpe23 := hpe 2 3 0 1 h23 (by decide) (by decide) (by decide) (by decide)
  have hse0 := hse 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hse1 := hse 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hse2 := hse 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hse3 := hse 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hM : residualSum psi = 7552 / 194481 := by
    have hcdpsi : |(4 / 147 : ℝ)| = Real.sqrt ((4 / 441) * (4 / 49)) ∧
        Real.sqrt ((400 / 441) * (1 / 441)) ≤ 2 * |(4 / 147 : ℝ)| ∧
        |(4 / 147 : ℝ)| ≤ Real.sqrt ((400 / 441) * (1 / 441)) := by
      have e1 : Real.sqrt ((4 / 441) * (4 / 49)) = 4 / 147 := by
        rw [show (4 / 441 : ℝ) * (4 / 49) = (4 / 147) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have e2 : Real.sqrt ((400 / 441) * (1 / 441)) = 20 / 441 := by
        rw [show (400 / 441 : ℝ) * (1 / 441) = (20 / 441) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [e1, e2]; norm_num
    have rpsiAB : reindex (pairEquiv 0 1 h01) (pairEquiv 0 1 h01)
        (reducedState ({0, 1} : Finset (Fin 4)) psi) =
          xmat (400 / 441) 0 (40 / 441) (1 / 441) 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe01]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiAB : concurrence 0 1 psi = 0 := by
      rw [hW 0 1 h01 psi _ _ _ _ _ rpsiAB]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rpsiAC : reindex (pairEquiv 0 2 h02) (pairEquiv 0 2 h02)
        (reducedState ({0, 2} : Finset (Fin 4)) psi) =
          xmat (400 / 441) 0 (4 / 441) (37 / 441) (40 / 147) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe02]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiAC : concurrence 0 2 psi = (80 / 147) := by
      rw [hW 0 2 h02 psi _ _ _ _ _ rpsiAC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rpsiAD : reindex (pairEquiv 0 3 h03) (pairEquiv 0 3 h03)
        (reducedState ({0, 3} : Finset (Fin 4)) psi) =
          xmat 0 (400 / 441) (5 / 441) (4 / 49) 0 (40 / 441) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe03]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiAD : concurrence 0 3 psi = (80 / 441) := by
      rw [hZ 0 3 h03 psi _ _ _ _ _ rpsiAD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rpsiBC : reindex (pairEquiv 1 2 h12) (pairEquiv 1 2 h12)
        (reducedState ({1, 2} : Finset (Fin 4)) psi) =
          xmat (404 / 441) (4 / 49) 0 (1 / 441) (2 / 441) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe12]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiBC : concurrence 1 2 psi = (4 / 441) := by
      rw [hW 1 2 h12 psi _ _ _ _ _ rpsiBC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rpsiBD : reindex (pairEquiv 1 3 h13) (pairEquiv 1 3 h13)
        (reducedState ({1, 3} : Finset (Fin 4)) psi) =
          xmat (4 / 441) (436 / 441) (1 / 441) 0 0 (2 / 147) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe13]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiBD : concurrence 1 3 psi = (4 / 147) := by
      rw [hZ 1 3 h13 psi _ _ _ _ _ rpsiBD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rpsiCD : reindex (pairEquiv 2 3 h23) (pairEquiv 2 3 h23)
        (reducedState ({2, 3} : Finset (Fin 4)) psi) =
          xmat (4 / 441) (400 / 441) (1 / 441) (4 / 49) (4 / 147) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe23]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [psi, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cpsiCD : concurrence 2 3 psi = 0 := by
      refine hCD 2 3 h23 psi _ _ _ _ _ rpsiCD ?_ ?_ ?_ ?_ hcdpsi.1 hcdpsi.2.1 hcdpsi.2.2 <;>
        norm_num
    have tpsiA : linearEntropy 0 psi = (65600 / 194481) := by
      rw [linearEntropy, htr]
      simp only [hse0 psi]
      simp [psi, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tpsiB : linearEntropy 1 psi = (1760 / 194481) := by
      rw [linearEntropy, htr]
      simp only [hse1 psi]
      simp [psi, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tpsiC : linearEntropy 2 psi = (59792 / 194481) := by
      rw [linearEntropy, htr]
      simp only [hse2 psi]
      simp [psi, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tpsiD : linearEntropy 3 psi = (8720 / 194481) := by
      rw [linearEntropy, htr]
      simp only [hse3 psi]
      simp [psi, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    simp only [residualSum, Fin.sum_univ_four, Fin.reduceLT, ↓reduceIte, tpsiA, tpsiB, tpsiC, tpsiD,
      cpsiAB, cpsiAC, cpsiAD, cpsiBC, cpsiBD, cpsiCD]
    norm_num
  have hM1 : residualSum phi1 = 2967747712 / 37822859361 := by
    have hcdphi1 : |(3364 / 64827 : ℝ)| = Real.sqrt ((3364 / 194481) * (3364 / 21609)) ∧
        Real.sqrt ((160000 / 194481) * (841 / 194481)) ≤ 2 * |(3364 / 64827 : ℝ)| ∧
        |(3364 / 64827 : ℝ)| ≤ Real.sqrt ((160000 / 194481) * (841 / 194481)) := by
      have e1 : Real.sqrt ((3364 / 194481) * (3364 / 21609)) = 3364 / 64827 := by
        rw [show (3364 / 194481 : ℝ) * (3364 / 21609) = (3364 / 64827) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      have e2 : Real.sqrt ((160000 / 194481) * (841 / 194481)) = 11600 / 194481 := by
        rw [show (160000 / 194481 : ℝ) * (841 / 194481) = (11600 / 194481) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [e1, e2]; norm_num
    have rphi1AB : reindex (pairEquiv 0 1 h01) (pairEquiv 0 1 h01)
        (reducedState ({0, 1} : Finset (Fin 4)) phi1) =
          xmat (160000 / 194481) 0 (33640 / 194481) (841 / 194481) 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe01]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1AB : concurrence 0 1 phi1 = 0 := by
      rw [hW 0 1 h01 phi1 _ _ _ _ _ rphi1AB]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi1AC : reindex (pairEquiv 0 2 h02) (pairEquiv 0 2 h02)
        (reducedState ({0, 2} : Finset (Fin 4)) phi1) =
          xmat (160000 / 194481) 0 (3364 / 194481) (31117 / 194481) (23200 / 64827) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe02]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1AC : concurrence 0 2 phi1 = (46400 / 64827) := by
      rw [hW 0 2 h02 phi1 _ _ _ _ _ rphi1AC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi1AD : reindex (pairEquiv 0 3 h03) (pairEquiv 0 3 h03)
        (reducedState ({0, 3} : Finset (Fin 4)) phi1) =
          xmat 0 (160000 / 194481) (4205 / 194481) (3364 / 21609) 0 (23200 / 194481) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe03]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1AD : concurrence 0 3 phi1 = (46400 / 194481) := by
      rw [hZ 0 3 h03 phi1 _ _ _ _ _ rphi1AD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi1BC : reindex (pairEquiv 1 2 h12) (pairEquiv 1 2 h12)
        (reducedState ({1, 2} : Finset (Fin 4)) phi1) =
          xmat (163364 / 194481) (3364 / 21609) 0 (841 / 194481) (1682 / 194481) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe12]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1BC : concurrence 1 2 phi1 = (3364 / 194481) := by
      rw [hW 1 2 h12 phi1 _ _ _ _ _ rphi1BC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi1BD : reindex (pairEquiv 1 3 h13) (pairEquiv 1 3 h13)
        (reducedState ({1, 3} : Finset (Fin 4)) phi1) =
          xmat (3364 / 194481) (190276 / 194481) (841 / 194481) 0 0 (1682 / 64827) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe13]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1BD : concurrence 1 3 phi1 = (3364 / 64827) := by
      rw [hZ 1 3 h13 phi1 _ _ _ _ _ rphi1BD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi1CD : reindex (pairEquiv 2 3 h23) (pairEquiv 2 3 h23)
        (reducedState ({2, 3} : Finset (Fin 4)) phi1) =
          xmat (3364 / 194481) (160000 / 194481) (841 / 194481) (3364 / 21609)
            (3364 / 64827) 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe23]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi1, xmat, Fin.sum_univ_two, map_ofNat, map_div₀] <;> norm_num
    have cphi1CD : concurrence 2 3 phi1 = 0 := by
      refine hCD 2 3 h23 phi1 _ _ _ _ _ rphi1CD ?_ ?_ ?_ ?_ hcdphi1.1 hcdphi1.2.1 hcdphi1.2.2 <;>
        norm_num
    have tphi1A : linearEntropy 0 phi1 = (22067840000 / 37822859361) := by
      rw [linearEntropy, htr]
      simp only [hse0 phi1]
      simp [phi1, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tphi1B : linearEntropy 1 phi1 = (651404960 / 37822859361) := by
      rw [linearEntropy, htr]
      simp only [hse1 phi1]
      simp [phi1, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tphi1C : linearEntropy 2 phi1 = (20333590352 / 37822859361) := by
      rw [linearEntropy, htr]
      simp only [hse2 phi1]
      simp [phi1, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    have tphi1D : linearEntropy 3 phi1 = (3200442320 / 37822859361) := by
      rw [linearEntropy, htr]
      simp only [hse3 phi1]
      simp [phi1, Fin.sum_univ_two, map_ofNat, map_div₀]
      norm_num
    simp only [residualSum, Fin.sum_univ_four, Fin.reduceLT, ↓reduceIte, tphi1A, tphi1B, tphi1C,
      tphi1D, cphi1AB, cphi1AC, cphi1AD, cphi1BC, cphi1BD, cphi1CD]
    norm_num
  have hM0 : residualSum phi0 = 0 := by
    have rphi0AB : reindex (pairEquiv 0 1 h01) (pairEquiv 0 1 h01)
        (reducedState ({0, 1} : Finset (Fin 4)) phi0) =
          xmat 1 0 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe01]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0AB : concurrence 0 1 phi0 = 0 := by
      rw [hW 0 1 h01 phi0 _ _ _ _ _ rphi0AB]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi0AC : reindex (pairEquiv 0 2 h02) (pairEquiv 0 2 h02)
        (reducedState ({0, 2} : Finset (Fin 4)) phi0) =
          xmat 1 0 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe02]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0AC : concurrence 0 2 phi0 = 0 := by
      rw [hW 0 2 h02 phi0 _ _ _ _ _ rphi0AC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi0AD : reindex (pairEquiv 0 3 h03) (pairEquiv 0 3 h03)
        (reducedState ({0, 3} : Finset (Fin 4)) phi0) =
          xmat 0 1 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe03]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0AD : concurrence 0 3 phi0 = 0 := by
      rw [hW 0 3 h03 phi0 _ _ _ _ _ rphi0AD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi0BC : reindex (pairEquiv 1 2 h12) (pairEquiv 1 2 h12)
        (reducedState ({1, 2} : Finset (Fin 4)) phi0) =
          xmat 1 0 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe12]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0BC : concurrence 1 2 phi0 = 0 := by
      rw [hW 1 2 h12 phi0 _ _ _ _ _ rphi0BC]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi0BD : reindex (pairEquiv 1 3 h13) (pairEquiv 1 3 h13)
        (reducedState ({1, 3} : Finset (Fin 4)) phi0) =
          xmat 0 1 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe13]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0BD : concurrence 1 3 phi0 = 0 := by
      rw [hW 1 3 h13 phi0 _ _ _ _ _ rphi0BD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have rphi0CD : reindex (pairEquiv 2 3 h23) (pairEquiv 2 3 h23)
        (reducedState ({2, 3} : Finset (Fin 4)) phi0) =
          xmat 0 1 0 0 0 0 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      rw [hpe23]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [phi0, xmat, Fin.sum_univ_two]
    have cphi0CD : concurrence 2 3 phi0 = 0 := by
      rw [hW 2 3 h23 phi0 _ _ _ _ _ rphi0CD]
      · norm_num
      all_goals first | (apply Real.le_sqrt_of_sq_le; norm_num) | norm_num
    have tphi0A : linearEntropy 0 phi0 = 0 := by
      rw [linearEntropy, htr]
      simp only [hse0 phi0]
      simp [phi0, Fin.sum_univ_two]
    have tphi0B : linearEntropy 1 phi0 = 0 := by
      rw [linearEntropy, htr]
      simp only [hse1 phi0]
      simp [phi0, Fin.sum_univ_two]
    have tphi0C : linearEntropy 2 phi0 = 0 := by
      rw [linearEntropy, htr]
      simp only [hse2 phi0]
      simp [phi0, Fin.sum_univ_two]
    have tphi0D : linearEntropy 3 phi0 = 0 := by
      rw [linearEntropy, htr]
      simp only [hse3 phi0]
      simp [phi0, Fin.sum_univ_two]
    simp only [residualSum, Fin.sum_univ_four, Fin.reduceLT, ↓reduceIte, tphi0A, tphi0B, tphi0C,
      tphi0D, cphi0AB, cphi0AC, cphi0AD, cphi0BC, cphi0BD, cphi0CD]
    norm_num
  have hnorm : ∑ w, ‖psi w‖ ^ 2 = 1 := by
    rw [hsum]
    simp [psi, Fin.sum_univ_two]
    norm_num
  have hK : ∑ j, (instrument j)ᴴ * instrument j = 1 := by
    simp only [Fin.sum_univ_two, instrument]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat, map_div₀]
  have hp0 : ∑ w, ‖(localOp (0 : Fin 4) (instrument 0) *ᵥ psi) w‖ ^ 2 = 400 / 841 := by
    rw [hsum]
    simp [hloc, instrument, psi, Fin.sum_univ_two]
    norm_num
  have hp1 : ∑ w, ‖(localOp (0 : Fin 4) (instrument 1) *ᵥ psi) w‖ ^ 2 = 441 / 841 := by
    rw [hsum]
    simp [hloc, instrument, psi, Fin.sum_univ_two]
    norm_num
  have hs0 : Real.sqrt (400 / 841) = 20 / 29 := by
    rw [show (400 / 841 : ℝ) = (20 / 29) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs1 : Real.sqrt (441 / 841) = 21 / 29 := by
    rw [show (441 / 841 : ℝ) = (21 / 29) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hphi0 :
      (((Real.sqrt (400 / 841))⁻¹ : ℝ) : ℂ) • (localOp (0 : Fin 4) (instrument 0) *ᵥ psi) =
        phi0 := by
    rw [hs0]
    funext w
    obtain ⟨⟨a, b, c, d⟩, rfl⟩ : ∃ x : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ![x.1, x.2.1, x.2.2.1, x.2.2.2] = w :=
      ⟨(w 0, w 1, w 2, w 3), by funext i; fin_cases i <;> rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [hloc, instrument, psi, phi0]
  have hphi1 :
      (((Real.sqrt (441 / 841))⁻¹ : ℝ) : ℂ) • (localOp (0 : Fin 4) (instrument 1) *ᵥ psi) =
        phi1 := by
    rw [hs1]
    funext w
    obtain ⟨⟨a, b, c, d⟩, rfl⟩ : ∃ x : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        ![x.1, x.2.1, x.2.2.1, x.2.2.2] = w :=
      ⟨(w 0, w 1, w 2, w 3), by funext i; fin_cases i <;> rfl⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [hloc, instrument, psi, phi1] <;> norm_num
  have key := h psi hnorm 2 instrument hK
  rw [Fin.sum_univ_two, hp0, hp1, if_neg (by norm_num), if_neg (by norm_num)] at key
  have e0 : ((Real.sqrt (400 / 841))⁻¹ : ℂ) = (((Real.sqrt (400 / 841))⁻¹ : ℝ) : ℂ) := by
    push_cast; rfl
  have e1 : ((Real.sqrt (441 / 841))⁻¹ : ℂ) = (((Real.sqrt (441 / 841))⁻¹ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e0, e1, hphi0, hphi1, hM0, hM1, hM] at key
  norm_num at key

end D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation
