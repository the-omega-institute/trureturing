/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical symmetric Werner–Holevo channel has Choi rank n(n+1)/2 and a full symmetric unitary basis attains it. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Symmetric Werner–Holevo channel and its mixed-unitary rank

The implication from a full Hilbert–Schmidt orthogonal family of symmetric
unitaries to an optimal decomposition is Theorem 19(1) of Girard, Leung,
Levick, Li, Paulsen, Poon, and Watrous, "On the mixed-unitary rank of
quantum channels", arXiv:2003.14405, DOI 10.1007/s00220-022-04412-y.

In output-first Choi coordinates, the symmetric Werner–Holevo Choi matrix is
the identity plus the tensor flip, divided by the dimension plus one. Its
range is identified with functions on unordered pairs. The same range is
spanned by the vectorized symmetric unitary family, so the two Gram matrices
agree after rescaling.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace AffineNineRank

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The symmetric Werner–Holevo map on all complex matrices. -/
def symmetricWernerHolevo (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MatrixMap ι ι ℂ :=
  ((Fintype.card ι : ℂ) + 1)⁻¹ •
    ((Matrix.traceLinearMap ι ℂ ℂ).smulRight 1 +
      (Matrix.transposeLinearEquiv ι ι ℂ ℂ).toLinearMap)

@[simp] theorem symmetricWernerHolevo_apply (X : Matrix ι ι ℂ) :
    symmetricWernerHolevo ι X =
      ((Fintype.card ι : ℂ) + 1)⁻¹ • (X.trace • 1 + Xᵀ) := rfl

/-- A weighted sum of unitary conjugations, with arbitrary complex coefficients. -/
def conjugationSum (p : κ → ℂ) (U : κ → Matrix ι ι ℂ) : MatrixMap ι ι ℂ :=
  ∑ k, p k • MatrixMap.conj (U k)

omit [DecidableEq ι] in
@[simp] theorem conjugationSum_apply (p : κ → ℂ) (U : κ → Matrix ι ι ℂ)
    (X : Matrix ι ι ℂ) :
    conjugationSum p U X = ∑ k, p k • (U k * X * (U k)ᴴ) := by
  simp [conjugationSum, MatrixMap.conj]

private def columns (U : κ → Matrix ι ι ℂ) : Matrix (ι × ι) κ ℂ :=
  fun p k => U k p.1 p.2

private theorem conj_single_apply (U : Matrix ι ι ℂ) (a b i j : ι) :
    (U * Matrix.single a b (1 : ℂ) * Uᴴ) i j = U i a * star (U j b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp [Matrix.mul_single_apply_same]
  · intro k _ hkb
    simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hkb]
  · simp

private theorem choi_conjugationSum [DecidableEq κ] (p : κ → ℂ) (U : κ → Matrix ι ι ℂ) :
    (conjugationSum p U).choi_matrix =
      (columns U * Matrix.diagonal p) * (columns U)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change conjugationSum p U (Matrix.single a b 1) i j = _
  simp only [conjugationSum_apply, Matrix.sum_apply, Matrix.smul_apply, conj_single_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, columns, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Twice the symmetric projection, in output-first Choi coordinates. -/
private def symmetrizer (ι : Type*) [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  fun p q => (if p = q then 1 else 0) + (if p.swap = q then 1 else 0)

private theorem choi_symmetricWernerHolevo :
    (symmetricWernerHolevo ι).choi_matrix =
      ((Fintype.card ι : ℂ) + 1)⁻¹ • symmetrizer ι := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change symmetricWernerHolevo ι (Matrix.single a b 1) i j = _
  have ht : (Matrix.single a b (1 : ℂ)).trace = if a = b then 1 else 0 := by
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  simp only [symmetricWernerHolevo_apply, Matrix.smul_apply, Matrix.add_apply, ht,
    Matrix.one_apply, Matrix.transpose_apply, symmetrizer, Prod.mk.injEq,
    Prod.swap_prod_mk, smul_eq_mul]
  simp only [Matrix.single, Matrix.of_apply]
  have hswap : (a = j ∧ b = i) ↔ (a = j ∧ i = b) := by tauto
  simp only [hswap]
  by_cases hab : a = b <;> simp [hab]

private theorem symmetrizer_mulVec (v : ι × ι → ℂ) (p : ι × ι) :
    (symmetrizer ι *ᵥ v) p = v p + v p.swap := by
  classical
  simp [symmetrizer, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

omit [Fintype ι] in
private theorem symmetrizer_adjoint : (symmetrizer ι)ᴴ = symmetrizer ι := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change star ((if (j, b) = (i, a) then (1 : ℂ) else 0) +
    (if (b, j) = (i, a) then 1 else 0)) = _
  have h₁ : (j, b) = (i, a) ↔ (i, a) = (j, b) := eq_comm
  have h₂ : (b, j) = (i, a) ↔ (a, i) = (j, b) := by
    simp only [Prod.mk.injEq]
    tauto
  by_cases h₃ : (i, a) = (j, b) <;> by_cases h₄ : (a, i) = (j, b) <;>
    simp [symmetrizer, h₁, h₂, h₃, h₄]

omit [Fintype κ] in
private theorem symmetrizer_mul_of_symmetric_columns (A : Matrix (ι × ι) κ ℂ)
    (hA : ∀ p k, A p.swap k = A p k) :
    symmetrizer ι * A = (2 : ℂ) • A := by
  ext p k
  change (symmetrizer ι *ᵥ fun q => A q k) p = _
  rw [symmetrizer_mulVec, hA, Matrix.smul_apply, smul_eq_mul, two_mul]

omit [Fintype ι] in
private theorem symmetrizer_col_swap (p q : ι × ι) :
    symmetrizer ι p.swap q = symmetrizer ι p q := by
  simp [symmetrizer, add_comm]

private theorem symmetrizer_psd : (symmetrizer ι).PosSemidef := by
  have hs : (symmetrizer ι)ᴴ * symmetrizer ι = (2 : ℂ) • symmetrizer ι := by
    rw [symmetrizer_adjoint]
    exact symmetrizer_mul_of_symmetric_columns _ symmetrizer_col_swap
  have h := (Matrix.posSemidef_conjTranspose_mul_self (symmetrizer ι)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [hs, ← Complex.coe_smul, smul_smul] at h
  norm_num at h
  exact h

private def unorderedCoordinates : (Sym2 ι → ℂ) →ₗ[ℂ] (ι × ι → ℂ) where
  toFun f p := f (Sym2.mk p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem mem_range_symmetrizer_iff (v : ι × ι → ℂ) :
    v ∈ LinearMap.range (symmetrizer ι).mulVecLin ↔ ∀ p, v p.swap = v p := by
  constructor
  · rintro ⟨w, rfl⟩ p
    simp only [Matrix.mulVecLin_apply, symmetrizer_mulVec, Prod.swap_swap, add_comm]
  · intro h
    refine ⟨(2 : ℂ)⁻¹ • v, ?_⟩
    funext p
    simp only [Matrix.mulVecLin_apply, symmetrizer_mulVec, Pi.smul_apply, h,
      smul_eq_mul]
    ring

private theorem range_symmetrizer :
    LinearMap.range (symmetrizer ι).mulVecLin = LinearMap.range
      (unorderedCoordinates : (Sym2 ι → ℂ) →ₗ[ℂ] (ι × ι → ℂ)) := by
  ext v
  rw [mem_range_symmetrizer_iff]
  constructor
  · intro h
    exact ⟨Sym2.lift ⟨fun a b => v (a, b), fun a b => (h (a, b)).symm⟩, rfl⟩
  · rintro ⟨f, rfl⟩ ⟨a, b⟩
    exact congrArg f Sym2.eq_swap

private theorem symmetrizer_rank :
    (symmetrizer ι).rank = (Fintype.card ι + 1).choose 2 := by
  classical
  rw [Matrix.rank, range_symmetrizer, LinearMap.finrank_range_of_inj,
    Module.finrank_fintype_fun_eq_card, Sym2.card]
  intro f g h
  funext e
  induction e using Sym2.inductionOn with
  | _ a b => exact congrFun h (a, b)

/-- The Choi rank is the dimension of the complex symmetric subspace. -/
theorem choiRank_symmetricWernerHolevo :
    (symmetricWernerHolevo ι).choi_matrix.rank = (Fintype.card ι + 1).choose 2 := by
  rw [choi_symmetricWernerHolevo, Matrix.rank_smul_of_mem_nonZeroDivisors, symmetrizer_rank]
  exact mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (by exact_mod_cast
    (Nat.succ_ne_zero (Fintype.card ι))))

/-- The symmetric Werner–Holevo map is a canonical finite quantum channel. -/
theorem exists_symmetricWernerHolevo_channel (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ channel : QuantumChannel ι ι,
      ∀ X : Matrix ι ι ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = symmetricWernerHolevo ι X := by
  have hpos : (symmetricWernerHolevo ι).choi_matrix.PosSemidef := by
    rw [choi_symmetricWernerHolevo]
    have h := (symmetrizer_psd (ι := ι)).smul
      (inv_nonneg.mpr (show 0 ≤ (Fintype.card ι : ℝ) + 1 by positivity))
    simpa only [← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one] using h
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_PSD _ hpos
  have hmap := MatrixMap.choi_matrix_inj hK
  have haction (X : Matrix ι ι ℂ) :
      symmetricWernerHolevo ι X = ∑ k, K k * X * (K k)ᴴ := by
    rw [hmap]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  have htrace (X : Matrix ι ι ℂ) : (symmetricWernerHolevo ι X).trace = X.trace := by
    have hn : (Fintype.card ι : ℂ) + 1 ≠ 0 := by exact_mod_cast
      (Nat.succ_ne_zero (Fintype.card ι))
    simp only [symmetricWernerHolevo_apply, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_one, Matrix.trace_transpose, smul_eq_mul]
    field_simp
  have hcomplete : ∑ k, (K k)ᴴ * K k = 1 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    rw [Matrix.mul_one, ← htrace X, haction, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun k _ =>
      (Matrix.trace_mul_comm X ((K k)ᴴ * K k)).trans
        (Matrix.trace_mul_cycle (K k) X (K k)ᴴ).symm
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel K hcomplete
  exact ⟨channel, fun X => (hchannel X).trans (haction X).symm⟩

/-- A Choi-rank lower bound for every finite conjugation-sum representation.
In particular it applies to any probability weights and any unitary family. -/
theorem card_le_of_conjugationSum (p : κ → ℂ) (U : κ → Matrix ι ι ℂ)
    (h : ∀ X, symmetricWernerHolevo ι X = ∑ k, p k • (U k * X * (U k)ᴴ)) :
    (Fintype.card ι + 1).choose 2 ≤ Fintype.card κ := by
  classical
  have hmap : symmetricWernerHolevo ι = conjugationSum p U :=
    LinearMap.ext fun X => (h X).trans (conjugationSum_apply p U X).symm
  rw [← choiRank_symmetricWernerHolevo (ι := ι), hmap, choi_conjugationSum]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Any mixed-unitary decomposition of the canonical channel needs at least
`n(n+1)/2` terms, with no symmetry assumptions on its unitary operators. -/
theorem mixedUnitary_length_lower_bound
    (channel : QuantumChannel ι ι)
    (hchannel : ∀ X : Matrix ι ι ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = symmetricWernerHolevo ι X)
    (m : ℕ) (p : Fin m → ℝ) (U : Fin m → Matrix.unitaryGroup ι ℂ)
    (_hp : ∀ k, 0 ≤ p k) (_hpsum : ∑ k, p k = 1)
    (h : ∀ X : Matrix ι ι ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ k, (p k : ℂ) • ((U k : Matrix ι ι ℂ) * X * (U k : Matrix ι ι ℂ)ᴴ)) :
    Fintype.card ι * (Fintype.card ι + 1) / 2 ≤ m := by
  simpa [Nat.choose_two_right, Nat.mul_comm] using
    card_le_of_conjugationSum (fun k => (p k : ℂ)) (fun k => (U k : Matrix ι ι ℂ))
      (fun X => (hchannel X).symm.trans (h X))

/-- The Hilbert–Schmidt inner product, conjugate-linear in its first argument. -/
def hsInner (A B : Matrix ι ι ℂ) : ℂ := (Aᴴ * B).trace

omit [DecidableEq ι] in
theorem hsInner_eq_sum (A B : Matrix ι ι ℂ) :
    hsInner A B = ∑ i, ∑ j, star (A i j) * B i j := by
  change (∑ i, ∑ j, star (A j i) * B j i) = _
  exact Finset.sum_comm

omit [Fintype κ] in
private theorem family_gram [DecidableEq κ]
    (U : κ → Matrix ι ι ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ)
    (horth : ∀ i j, i ≠ j → hsInner (U i) (U j) = 0) :
    (columns U)ᴴ * columns U = (Fintype.card ι : ℂ) • 1 := by
  have hentry (i j : κ) : ((columns U)ᴴ * columns U) i j = hsInner (U i) (U j) := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      columns, hsInner_eq_sum]
  ext i j
  rw [hentry, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, smul_eq_mul, mul_one, hsInner, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp (hU i), Matrix.trace_one]
  · rw [ite_eq_right hij, smul_zero, horth i j hij]

private theorem columns_mul_adjoint [Nonempty ι] [DecidableEq κ]
    (U : κ → Matrix ι ι ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ)
    (hsym : ∀ k, (U k).IsSymm) (horth : ∀ i j, i ≠ j → hsInner (U i) (U j) = 0)
    (hcard : Fintype.card κ = (Fintype.card ι + 1).choose 2) :
    columns U * (columns U)ᴴ = ((Fintype.card ι : ℂ) / 2) • symmetrizer ι := by
  let A := columns U
  let S := symmetrizer ι
  let n : ℂ := Fintype.card ι
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hgram : Aᴴ * A = n • 1 := family_gram U hU horth
  have hsymA : ∀ p k, A p.swap k = A p k := fun p k => (hsym k).apply p.1 p.2
  have hrank : A.rank = S.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self A, hgram, Matrix.rank_smul_of_mem_nonZeroDivisors,
      Matrix.rank_one, hcard, symmetrizer_rank]
    exact mem_nonZeroDivisors_of_ne_zero hn
  have hrange : LinearMap.range A.mulVecLin = LinearMap.range S.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le _ (le_of_eq hrank.symm)
    rintro _ ⟨v, rfl⟩
    rw [mem_range_symmetrizer_iff]
    intro p
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hsymA]
  have hcolS : ∀ q : ι × ι, S.col q ∈ LinearMap.range A.mulVecLin := by
    intro q
    rw [hrange]
    exact ⟨Pi.single q 1, Matrix.mulVec_single_one S q⟩
  choose v hv using hcolS
  let B : Matrix κ (ι × ι) ℂ := fun k q => v q k
  have hAB : A * B = S := by
    ext p q
    exact congrFun (hv q) p
  have hSA : S * A = (2 : ℂ) • A := symmetrizer_mul_of_symmetric_columns A hsymA
  have hAS : Aᴴ * S = (2 : ℂ) • Aᴴ := by
    simpa [S, Matrix.conjTranspose_mul, symmetrizer_adjoint, Matrix.conjTranspose_smul]
      using congrArg Matrix.conjTranspose hSA
  have hscaled : (2 : ℂ) • (A * Aᴴ) = n • S := calc
    _ = A * (Aᴴ * S) := by rw [hAS, Matrix.mul_smul]
    _ = A * ((Aᴴ * A) * B) := by rw [← hAB, Matrix.mul_assoc]
    _ = n • S := by rw [hgram, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hAB]
  calc
    A * Aᴴ = (2 : ℂ)⁻¹ • ((2 : ℂ) • (A * Aᴴ)) := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
    _ = (n / 2) • S := by rw [hscaled, smul_smul, div_eq_mul_inv, mul_comm]

/-- The equal-weight average of a full Hilbert–Schmidt orthogonal family of
symmetric unitary conjugations agrees with the symmetric Werner–Holevo map
on every complex matrix. -/
theorem equal_weight_average [Nonempty ι]
    (U : κ → Matrix ι ι ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ)
    (hsym : ∀ k, (U k).IsSymm) (horth : ∀ i j, i ≠ j → hsInner (U i) (U j) = 0)
    (hcard : Fintype.card κ = (Fintype.card ι + 1).choose 2) (X : Matrix ι ι ℂ) :
    (Fintype.card κ : ℂ)⁻¹ • (∑ k, U k * X * (U k)ᴴ) =
      ((Fintype.card ι : ℂ) + 1)⁻¹ • (X.trace • 1 + Xᵀ) := by
  classical
  have hmap : conjugationSum (fun _ : κ => (Fintype.card κ : ℂ)⁻¹) U =
      symmetricWernerHolevo ι := by
    apply MatrixMap.choi_matrix_inj
    rw [choi_conjugationSum, choi_symmetricWernerHolevo,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      columns_mul_adjoint U hU hsym horth hcard, smul_smul]
    congr 1
    rw [hcard, Nat.cast_choose_two]
    have hn : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hn' : (Fintype.card ι : ℂ) + 1 ≠ 0 := by exact_mod_cast
      (Nat.succ_ne_zero (Fintype.card ι))
    push_cast
    field_simp
    ring
  simpa [Finset.smul_sum] using LinearMap.congr_fun hmap X

/-- A decomposition of a canonical channel into exactly `m` unitary
conjugations with nonnegative real weights summing to one. -/
def HasMixedUnitaryDecomposition (channel : QuantumChannel ι ι) (m : ℕ) : Prop :=
  ∃ (p : Fin m → ℝ) (U : Fin m → Matrix.unitaryGroup ι ℂ),
    (∀ k, 0 ≤ p k) ∧ (∑ k, p k = 1) ∧
    ∀ X : Matrix ι ι ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ k, (p k : ℂ) • ((U k : Matrix ι ι ℂ) * X * (U k : Matrix ι ι ℂ)ᴴ)

/-- A full symmetric unitary family establishes the exact mixed-unitary rank
of the canonical symmetric Werner–Holevo channel. -/
theorem mixedUnitary_rank_exact [Nonempty ι]
    (U : κ → Matrix ι ι ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ)
    (hsym : ∀ k, (U k).IsSymm) (horth : ∀ i j, i ≠ j → hsInner (U i) (U j) = 0)
    (hcard : Fintype.card κ = (Fintype.card ι + 1).choose 2) :
    ∃ channel : QuantumChannel ι ι,
      (∀ X : Matrix ι ι ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = symmetricWernerHolevo ι X) ∧
      IsLeast {m : ℕ | HasMixedUnitaryDecomposition channel m}
        (Fintype.card ι * (Fintype.card ι + 1) / 2) := by
  classical
  obtain ⟨channel, hchannel⟩ := exists_symmetricWernerHolevo_channel ι
  refine ⟨channel, hchannel, ?_⟩
  have hlength : Fintype.card κ = Fintype.card ι * (Fintype.card ι + 1) / 2 := by
    simpa [Nat.choose_two_right, Nat.mul_comm] using hcard
  constructor
  · change HasMixedUnitaryDecomposition channel _
    rw [← hlength]
    let e := (Fintype.equivFin κ).symm
    have hκ : Fintype.card κ ≠ 0 := by
      rw [hcard]
      exact Nat.ne_of_gt (Nat.choose_pos (by have := Fintype.card_pos (α := ι); omega))
    refine ⟨fun _ => (Fintype.card κ : ℝ)⁻¹, fun k => ⟨U (e k), hU (e k)⟩,
      fun _ => by positivity, ?_, ?_⟩
    · simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_ne_zero.mpr hκ]
    · intro X
      rw [hchannel, symmetricWernerHolevo_apply, ← equal_weight_average U hU hsym horth hcard,
        Finset.smul_sum]
      simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
        (Equiv.sum_comp e (fun k => (Fintype.card κ : ℂ)⁻¹ • (U k * X * (U k)ᴴ))).symm
  · intro m hm
    obtain ⟨p, V, hp, hpsum, h⟩ := hm
    exact mixedUnitary_length_lower_bound channel hchannel m p V hp hpsum h

#print axioms exists_symmetricWernerHolevo_channel
#print axioms choiRank_symmetricWernerHolevo
#print axioms card_le_of_conjugationSum
#print axioms mixedUnitary_length_lower_bound
#print axioms hsInner_eq_sum
#print axioms equal_weight_average
#print axioms mixedUnitary_rank_exact

end AffineNineRank
