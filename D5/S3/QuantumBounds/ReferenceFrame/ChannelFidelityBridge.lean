/- GID: D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the reference-frame fidelity from a finite excitation-exchange channel. -/

/-
Library-search audit trail (mathlib v4.31.0, offline, 2026-08-17):

* Searches for `Kraus`, `entanglement fidelity`, and `quantum channel` found no packaged
  finite-dimensional Kraus or entanglement-fidelity interface. The broader search for
  `completely positive` found `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap`, which is more
  general than the finite matrix family required here and is therefore not imported directly.
* Matrix searches found and this module applies `Equiv.Perm.permMatrix`,
  `Matrix.conjTranspose_permMatrix`, and `Matrix.permMatrix_mulVec` for the exchange unitary.
  `Matrix.trace`, `Matrix.mul_apply`, and `Matrix.conjTranspose_apply` provide the finite trace form.
* Kronecker-product searches found `Matrix.conjTranspose_kronecker` and
  `Matrix.mul_kronecker_mul`. The exchange acts directly on the product basis, so the permutation
  matrix is the exact representation and no Kronecker expansion is needed.

Repository search audit trail (working tree, 2026-08-17):

* Searches under `D5/` for Kraus families and entanglement fidelity found no prior definition.
* `D5.S3.QuantumBounds.ReferenceFrameTax.nearestNeighborQuadratic` is the frozen target and is
  imported below; it is not redefined.
-/

import D5.S3.QuantumBounds.ReferenceFrameTax
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite excitation-exchange channel bridge

The joint permutation exchanges `|0,m+1>` with `|1,m>` and fixes the two unmatched boundary
vectors. Thus it preserves total excitation and implements a bit flip whenever the reference can
supply or absorb one excitation. Contracting this unitary with a real reference amplitude vector
gives a finite Kraus family. The usual maximally-mixed entanglement-fidelity trace form against the
ideal bit flip then reduces exactly to the frozen zero-boundary nearest-neighbour quadratic form.
-/

namespace D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge

open Matrix
open scoped BigOperators
open scoped Matrix

open D5.S3.QuantumBounds.ReferenceFrameTax

/-- A system basis bit and an `N`-level reference basis label. -/
abbrev JointBasis (N : ℕ) := Fin 2 × Fin N

/-- Exchange one excitation between the system and the reference, fixing unmatched boundaries. -/
def exchangeBasis {N : ℕ} (x : JointBasis N) : JointBasis N :=
  if hs : x.1 = 0 then
    if hm : 0 < x.2.val then
      (⟨1, by omega⟩, ⟨x.2.val - 1, lt_of_le_of_lt (Nat.sub_le ..) x.2.isLt⟩)
    else x
  else if hm : x.2.val + 1 < N then
    (⟨0, by omega⟩, ⟨x.2.val + 1, hm⟩)
  else x

/-- The exchange is its own inverse. -/
theorem exchange_basis_involutive {N : ℕ} : Function.Involutive (@exchangeBasis N) := by
  rintro ⟨s, m⟩
  fin_cases s <;> simp only [exchangeBasis, Fin.zero_eta, Fin.isValue, ↓reduceDIte]
  · by_cases hm : 0 < m.val
    · simp only [hm, ↓reduceDIte]
      have hback : m.val - 1 + 1 = m.val := by omega
      simp [hback]
    · simp [hm]
  · by_cases hm : m.val + 1 < N
    · simp only [hm, ↓reduceDIte]
      have hpos : 0 < m.val + 1 := by omega
      simp [hpos]
    · simp [hm]

/-- The exchange permutation of the joint computational basis. -/
def exchangePermutation (N : ℕ) : Equiv.Perm (JointBasis N) :=
  exchange_basis_involutive.toPerm exchangeBasis

/-- The finite-dimensional excitation-exchange unitary in the joint computational basis. -/
noncomputable def exchangeUnitary (N : ℕ) :
    Matrix (JointBasis N) (JointBasis N) ℂ :=
  fun i j ↦ if j = exchangeBasis i then 1 else 0

/-- The coordinate definition is the permutation matrix supplied by mathlib. -/
theorem exchange_unitary_eq_perm_matrix (N : ℕ) :
    exchangeUnitary N = (exchangePermutation N).permMatrix ℂ := by
  ext i j
  simp [exchangeUnitary, exchangePermutation, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Option.mem_def, eq_comm]

/-- The permutation matrix is unitary. -/
theorem exchange_unitary_is_unitary (N : ℕ) :
    (exchangeUnitary N)ᴴ * exchangeUnitary N = 1 := by
  rw [exchange_unitary_eq_perm_matrix, Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

/-- Total excitation of a joint computational-basis label. -/
def totalExcitation {N : ℕ} (x : JointBasis N) : ℕ := x.1.val + x.2.val

/-- The exchange unitary is covariant for the conserved total-excitation grading. -/
theorem exchange_basis_preserves_total_excitation {N : ℕ} (x : JointBasis N) :
    totalExcitation (exchangeBasis x) = totalExcitation x := by
  rcases x with ⟨s, m⟩
  fin_cases s <;> simp only [exchangeBasis, totalExcitation, Fin.zero_eta, Fin.isValue,
    ↓reduceDIte]
  · by_cases hm : 0 < m.val
    · simp [hm]
      omega
    · simp [hm]
  · by_cases hm : m.val + 1 < N
    · simp [hm, Nat.add_comm]
    · simp [hm]

/-- Away from the lower boundary, system input `0` is flipped to `1`. -/
theorem exchange_basis_flips_zero {N : ℕ} (m : Fin N) (hm : 0 < m.val) :
    exchangeBasis ((0 : Fin 2), m) =
      ((1 : Fin 2), ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩) := by
  simp [exchangeBasis, hm]

/-- Away from the upper boundary, system input `1` is flipped to `0`. -/
theorem exchange_basis_flips_one {N : ℕ} (m : Fin N) (hm : m.val + 1 < N) :
    exchangeBasis ((1 : Fin 2), m) = ((0 : Fin 2), ⟨m.val + 1, hm⟩) := by
  simp [exchangeBasis, hm]

/-- The ideal system bit-flip matrix. -/
def bitFlip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Kraus operator obtained by projecting the exchanged reference onto output level `r`. -/
noncomputable def exchangeKraus {N : ℕ} (c : Fin N → ℝ) (r : Fin N) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun sOut sIn ↦ ∑ m : Fin N,
    exchangeUnitary N (sOut, r) (sIn, m) * (c m : ℂ)

/-- The reduced system channel induced by the finite exchange unitary and reference amplitudes. -/
noncomputable def exchangeChannel {N : ℕ} (c : Fin N → ℝ)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ r : Fin N, exchangeKraus c r * rho * (exchangeKraus c r)ᴴ

/-- The channel is, definitionally, represented by the displayed finite Kraus family. -/
theorem exchange_channel_kraus_form {N : ℕ} (c : Fin N → ℝ)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    exchangeChannel c rho =
      ∑ r : Fin N, exchangeKraus c r * rho * (exchangeKraus c r)ᴴ := rfl

/-- Maximally-mixed entanglement fidelity of the exchange channel relative to the ideal bit flip,
written in its finite Kraus trace form. -/
noncomputable def entanglementFidelity {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ r : Fin N,
    Complex.normSq (Matrix.trace (bitFlipᴴ * exchangeKraus c r))

private theorem exchange_kraus_one_zero {N : ℕ} (c : Fin N → ℝ) (r : Fin N) :
    exchangeKraus c r 1 0 =
      (if _h : r.val + 1 < N then (c ⟨r.val + 1, _h⟩ : ℂ) else 0) := by
  classical
  by_cases hr : r.val + 1 < N
  · simp only [hr, ↓reduceDIte, exchangeKraus]
    rw [Finset.sum_eq_single ⟨r.val + 1, hr⟩]
    · simp [exchangeUnitary, exchangeBasis, hr]
    · intro b _ hb
      simp [exchangeUnitary, exchangeBasis, hr]
      intro h
      exact (hb (Fin.ext (congrArg Fin.val h))).elim
    · simp
  · simp only [hr, ↓reduceDIte, exchangeKraus]
    apply Finset.sum_eq_zero
    intro b _hb
    simp [exchangeUnitary, exchangeBasis, hr]

private theorem exchange_kraus_zero_one {N : ℕ} (c : Fin N → ℝ) (r : Fin N) :
    exchangeKraus c r 0 1 =
      (if _h : 0 < r.val then
        (c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ : ℂ) else 0) := by
  classical
  by_cases hl : 0 < r.val
  · simp only [hl, ↓reduceDIte, exchangeKraus]
    rw [Finset.sum_eq_single
      ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩]
    · simp [exchangeUnitary, exchangeBasis, hl]
    · intro b _ hb
      simp [exchangeUnitary, exchangeBasis, hl]
      intro h
      exact (hb (Fin.ext (congrArg Fin.val h))).elim
    · simp
  · simp only [hl, ↓reduceDIte, exchangeKraus]
    apply Finset.sum_eq_zero
    intro b _hb
    simp [exchangeUnitary, exchangeBasis, hl]

private theorem exchange_kraus_trace {N : ℕ} (c : Fin N → ℝ) (r : Fin N) :
    Matrix.trace (bitFlipᴴ * exchangeKraus c r) =
      ((if _h : 0 < r.val then
          c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ else 0) +
        (if _h : r.val + 1 < N then c ⟨r.val + 1, _h⟩ else 0) : ℝ) := by
  simp only [bitFlip, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]
  rw [exchange_kraus_one_zero, exchange_kraus_zero_one]
  by_cases hl : 0 < r.val <;> by_cases hr : r.val + 1 < N <;>
    (simp [hl, hr]; try ring_nf)

/-- The physical channel trace form is exactly the frozen nearest-neighbour quadratic. -/
theorem entanglement_fidelity_eq_nearest_neighbor_quadratic {N : ℕ} (c : Fin N → ℝ) :
    entanglementFidelity c = nearestNeighborQuadratic c := by
  rw [entanglementFidelity]
  unfold nearestNeighborQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [exchange_kraus_trace]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The bridge in norm notation: fidelity is the squared Euclidean norm of zero-boundary
nearest-neighbour averaging. -/
theorem entanglement_fidelity_eq_average_norm_sq {N : ℕ} (c : Fin N → ℝ) :
    entanglementFidelity c =
      ∑ r : Fin N,
        (((if _h : 0 < r.val then
            c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ else 0) +
          (if _h : r.val + 1 < N then c ⟨r.val + 1, _h⟩ else 0)) / 2) ^ 2 := by
  exact entanglement_fidelity_eq_nearest_neighbor_quadratic c

#print axioms exchange_basis_involutive
#print axioms exchange_unitary_is_unitary
#print axioms exchange_basis_preserves_total_excitation
#print axioms exchange_basis_flips_zero
#print axioms exchange_basis_flips_one
#print axioms exchange_channel_kraus_form
#print axioms entanglement_fidelity_eq_nearest_neighbor_quadratic
#print axioms entanglement_fidelity_eq_average_norm_sq

end D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
