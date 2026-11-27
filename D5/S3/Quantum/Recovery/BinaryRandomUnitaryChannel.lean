/- GID: D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BinaryRandomUnitaryChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical overlap and actual CPTP realization of binary random-unitary channels. -/

import D5.S3.Quantum.Recovery.BinaryUnitaryOptimization
import D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore
import D5.S3.QuantumBounds.PeritoTsirelson
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel

/-! Binary random-unitary recovery for the canonical finite quantum channel.
The system is the first tensor factor in the canonical overlap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Matrix
open Matrix Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open D5.S3.QuantumBounds.PeritoTsirelson
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)

noncomputable section

open D5.S3.Quantum.Recovery.BinaryUnitaryOptimization

namespace D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel

open scoped CStarAlgebra ComplexOrder MatrixOrder in
/-- Matrix action of the canonical completely positive map. -/
def matrixAction {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)) :
    PhyslibLeaf.MatrixMap a b ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (f.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)

/-- Canonical purification overlap at the maximally mixed input, with the system first.
This is the same definition as in the pinned Li–Jiang recovery calculation. -/
def entanglementFidelity (d : ℕ) (f : PhyslibLeaf.MatrixMap (Fin d) (Fin d) ℂ) : ℝ :=
  let psi := maxEntangledVector (Fin d)
  (dotProduct (star psi)
    ((PhyslibLeaf.MatrixMap.kron f LinearMap.id
      (maxEntangled (Fin d))).mulVec psi)).re

/-- Kraus trace identity for the normalized canonical purification overlap.
The reference action in the canonical overlap is the identity. -/
theorem canonical_overlap_kraus (d : ℕ) (hd : 0 < d) {k : Type*} [Fintype k]
    (L : k → Matrix (Fin d) (Fin d) ℂ) :
    entanglementFidelity d (MatrixMap.of_kraus L L) =
      (d : ℝ)⁻¹ ^ 2 * ∑ a, Complex.normSq (trace (L a)) := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let e := (Fintype.equivFin k).symm
  let Lf := fun j => L (e j)
  have hindex : PhyslibLeaf.MatrixMap.of_kraus L L =
      PhyslibLeaf.MatrixMap.of_kraus Lf Lf := by
    ext X a b
    simpa only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, Lf] using
      (e.sum_comp (fun j => (L j * X * (L j).conjTranspose) a b)).symm
  have htensor (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      PhyslibLeaf.MatrixMap.kron (PhyslibLeaf.MatrixMap.of_kraus Lf Lf) LinearMap.id X =
        PhyslibLeaf.MatrixMap.of_kraus
          (fun j => Matrix.kronecker (Lf j) (1 : Matrix (Fin d) (Fin d) ℂ))
          (fun j => Matrix.kronecker (Lf j) (1 : Matrix (Fin d) (Fin d) ℂ)) X := by
    ext ⟨a,b⟩ ⟨c,f⟩
    rw [PhyslibLeaf.MatrixMap.kron_def]
    simp only [PhyslibLeaf.MatrixMap.of_kraus, mul_assoc, Matrix.single, ite_and,
      LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero,
      apply_ite, mul_comm, LinearMap.id_coe, id_eq, Finset.mul_sum,
      Finset.sum_ite_eq', Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
      star_zero, mul_zero, Fintype.sum_prod_type, Finset.sum_mul, mul_left_comm]
    simp only [starRingEnd_apply]
    calc
      _ = ∑ x : Fin d, ∑ i : Fin (Fintype.card k), ∑ y : Fin d,
          X (x,b) (y,f) * (Lf i a x * star (Lf i c y)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  have hamplitude (j : Fin (Fintype.card k)) :
      dotProduct (star (maxEntangledVector (Fin d)))
        ((Matrix.kronecker (Lf j) (1 : Matrix (Fin d) (Fin d) ℂ)).mulVec
          (maxEntangledVector (Fin d))) = Matrix.trace (Lf j) / (d : ℂ) := by
    calc
      _ = Matrix.trace (maxEntangled (Fin d) *
          Matrix.kronecker (Lf j) (1 : Matrix (Fin d) (Fin d) ℂ)) := by
        rw [D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled.eq_1,
          Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
          Matrix.dotProduct_mulVec, dotProduct_comm]
      _ = _ := by
        rw [Matrix.kronecker, max_entangled_trace, Matrix.mul_one, Matrix.trace_transpose,
          Fintype.card_fin]
  rw [hindex]
  change (dotProduct (star (maxEntangledVector (Fin d)))
    ((PhyslibLeaf.MatrixMap.kron (PhyslibLeaf.MatrixMap.of_kraus Lf Lf) LinearMap.id
      (maxEntangled (Fin d))).mulVec (maxEntangledVector (Fin d)))).re = _
  rw [htensor]
  change (dotProduct (star (maxEntangledVector (Fin d)))
    ((PhyslibLeaf.MatrixMap.of_kraus _ _
      (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
        (maxEntangledVector (Fin d)))).mulVec (maxEntangledVector (Fin d)))).re = _
  rw [D5.S3.Quantum.QuantumChannels.MayerKnillInfidelityScalingCore.kraus_survival]
  calc
    _ = ∑ j, ‖Matrix.trace (Lf j) / (d : ℂ)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hamplitude j]
    _ = _ := by
      simp only [norm_div, Complex.norm_natCast, div_pow, ← Complex.normSq_eq_norm_sq]
      dsimp only [Lf]
      rw [← Finset.sum_div, e.sum_comp (fun j => Complex.normSq (Matrix.trace (L j)))]
      simp [div_eq_mul_inv, inv_pow, mul_comm]

abbrev CodeMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev CodeChannel (d : ℕ) := QuantumChannel (Fin d) (Fin d)

/-- The canonical purification is normalized and its reference marginal is
    exactly the maximally mixed code state. -/
theorem canonical_reference (d : ℕ) (hd : 0 < d) :
    trace (maxEntangled (Fin d)) = 1 ∧
    partialTraceLeft (maxEntangled (Fin d)) = (d : ℂ)⁻¹ • (1 : CodeMatrix d) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  refine ⟨(max_entangled_density (Fin d)).2, ?_⟩
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceLeft, maxEntangled, maxEntangledVector, vecMulVec_apply]
    rw [← pow_two, inv_pow, hs]
  · simp [partialTraceLeft, maxEntangled, maxEntangledVector, hij, vecMulVec_apply]

def channelAction {d : ℕ} (D : CodeChannel d) : MatrixMap (Fin d) (Fin d) ℂ :=
  matrixAction D.toCompletelyPositiveMap

/-- Entanglement fidelity at the maximally mixed code input. -/
def recoveryScore {d : ℕ} (N D : CodeChannel d) : ℝ :=
  entanglementFidelity d (channelAction (D.comp N))

private theorem channelOfKraus_action {d : ℕ} {k : Type*} [Fintype k]
    (K : k → CodeMatrix d) (hK : ∑ a, (K a)ᴴ * K a = 1) :
    ∃ D : CodeChannel d, ∀ X, channelAction D X = ∑ a, K a * X * (K a)ᴴ :=
  finite_kraus_quantum_channel K hK

/-- The canonical single-Kraus channel associated to a unitary. -/
def unitaryChannel {d : ℕ} (U : unitaryGroup (Fin d) ℂ) : CodeChannel d :=
  (channelOfKraus_action (fun _ : Unit => (U : CodeMatrix d)) (by
    simpa only [Fintype.sum_unique, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U)).choose

theorem unitaryChannel_action {d : ℕ} (U : unitaryGroup (Fin d) ℂ) (X : CodeMatrix d) :
    channelAction (unitaryChannel U) X = (U : CodeMatrix d) * X * (U : CodeMatrix d)ᴴ := by
  unfold unitaryChannel
  simpa only [Fintype.sum_unique] using
    (channelOfKraus_action (fun _ : Unit => (U : CodeMatrix d)) (by
      simpa only [Fintype.sum_unique, Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self U)).choose_spec X

private def branches {d : ℕ} (r s : ℝ) (U V : unitaryGroup (Fin d) ℂ) :
    Bool → CodeMatrix d
  | false => (r : ℂ) • (U : CodeMatrix d)
  | true => (s : ℂ) • (V : CodeMatrix d)

private theorem weighted_unitary_complete {d : ℕ} (r : ℝ)
    (U : unitaryGroup (Fin d) ℂ) :
    (((r : ℂ) • (U : CodeMatrix d))ᴴ * ((r : ℂ) • (U : CodeMatrix d))) =
      ((r ^ 2 : ℝ) : ℂ) • (1 : CodeMatrix d) := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← pow_two, Complex.ofReal_pow]
  congr 1
  exact Unitary.coe_star_mul_self U

private theorem branches_complete {d : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) (U V : unitaryGroup (Fin d) ℂ) :
    (∑ a, (branches (Real.sqrt p) (Real.sqrt q) U V a)ᴴ *
      branches (Real.sqrt p) (Real.sqrt q) U V a) = 1 := by
  rw [Fintype.sum_bool]
  simp only [branches, weighted_unitary_complete, Real.sq_sqrt hp, Real.sq_sqrt hq]
  rw [← add_smul, ← Complex.ofReal_add, add_comm q p, hpq, Complex.ofReal_one, one_smul]

/-- The CPTP channel with branch probabilities `p` and `q`, including zero weights. -/
def binaryChannel {d : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (U V : unitaryGroup (Fin d) ℂ) : CodeChannel d :=
  (channelOfKraus_action _ (branches_complete hp hq hpq U V)).choose

private theorem binary_kraus_action {d : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) (U V : unitaryGroup (Fin d) ℂ) (X : CodeMatrix d) :
    channelAction (binaryChannel hp hq hpq U V) X =
      ∑ a, branches (Real.sqrt p) (Real.sqrt q) U V a * X *
        (branches (Real.sqrt p) (Real.sqrt q) U V a)ᴴ :=
  (channelOfKraus_action _ (branches_complete hp hq hpq U V)).choose_spec X

/-- The branch implementation acts as the stated convex combination of unitary
    conjugations on every code matrix. -/
theorem binaryChannel_action {d : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) (U V : unitaryGroup (Fin d) ℂ) (X : CodeMatrix d) :
    channelAction (binaryChannel hp hq hpq U V) X =
      (p : ℂ) • channelAction (unitaryChannel U) X +
      (q : ℂ) • channelAction (unitaryChannel V) X := by
  rw [binary_kraus_action, Fintype.sum_bool]
  simp only [branches, unitaryChannel_action, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact add_comm _ _

private theorem comp_kraus_trace {d : ℕ} (hd : 0 < d)
    {k l : Type*} [Fintype k] [Fintype l]
    (D N : CodeChannel d) (K : k → CodeMatrix d) (L : l → CodeMatrix d)
    (hK : ∀ X, channelAction D X = ∑ a, K a * X * (K a)ᴴ)
    (hL : ∀ X, channelAction N X = ∑ b, L b * X * (L b)ᴴ) :
    recoveryScore N D =
      (d : ℝ)⁻¹ ^ 2 * ∑ a, ∑ b, Complex.normSq (trace (K a * L b)) := by
  have hcomp : channelAction (D.comp N) =
      MatrixMap.of_kraus (fun t : k × l => K t.1 * L t.2) (fun t : k × l => K t.1 * L t.2) := by
    apply LinearMap.ext
    intro X
    change channelAction D (channelAction N X) = _
    rw [hK, hL]
    simp only [Matrix.mul_sum, Matrix.sum_mul, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  unfold recoveryScore
  rw [hcomp, canonical_overlap_kraus _ hd, Fintype.sum_prod_type]

/-- Score of any decoder in terms of any of its valid Kraus families. -/
theorem binary_score_kraus {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (U V : unitaryGroup (Fin d) ℂ) (D : CodeChannel d)
    {k : Type*} [Fintype k] (K : k → CodeMatrix d)
    (hK : ∀ X, channelAction D X = ∑ a, K a * X * (K a)ᴴ) :
    recoveryScore (binaryChannel hp hq hpq U V) D = (d : ℝ)⁻¹ ^ 2 *
      (p * ∑ a, Complex.normSq (trace (K a * (U : CodeMatrix d))) +
       q * ∑ a, Complex.normSq (trace (K a * (V : CodeMatrix d)))) := by
  rw [comp_kraus_trace hd D _ K _ hK (binary_kraus_action hp hq hpq U V)]
  congr 1
  simp only [Fintype.sum_bool, branches, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.normSq_mul, ← Complex.sq_norm (↑(Real.sqrt p) : ℂ),
    ← Complex.sq_norm (↑(Real.sqrt q) : ℂ), Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hp, Real.sq_sqrt hq, Finset.sum_add_distrib, Finset.mul_sum]
  exact add_comm _ _

/-- The diagonal matrix with the given unit-modulus entries, as a unitary. -/
def diagonalUnitary {d : ℕ} (z : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    unitaryGroup (Fin d) ℂ :=
  ⟨diagonal z, Unitary.mem_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    constructor <;> congr 1 <;> funext j
    · change conj (z j) * z j = 1
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz j]
      norm_num
    · change z j * conj (z j) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz j]
      norm_num)⟩

private def diagonalVectors {d : ℕ} {k : Type*} [Fintype k]
    (K : k → CodeMatrix d) (j : Fin d) : EuclideanSpace ℂ k :=
  WithLp.toLp 2 (fun a => K a j j)

private theorem diagonalVectors_le {d : ℕ} {k : Type*} [Fintype k]
    (K : k → CodeMatrix d) (hK : ∑ a, (K a)ᴴ * K a = 1) (j : Fin d) :
    ‖diagonalVectors K j‖ ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) zero_le_one
  rw [one_pow, EuclideanSpace.norm_sq_eq]
  have h := congrArg (fun M : CodeMatrix d => (M j j).re) hK
  simp only [Matrix.sum_apply, Complex.re_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re] at h
  rw [← h]
  exact sum_le_sum fun a _ => by
    change ‖K a j j‖ ^ 2 ≤ _
    rw [Complex.sq_norm]
    exact single_le_sum (fun i _ => Complex.normSq_nonneg (K a i j)) (mem_univ j)

theorem diagonal_objective {d : ℕ} {k : Type*} [Fintype k]
    (K : k → CodeMatrix d) (z : Fin d → ℂ) (r s : ℝ) :
    columnLength r s z (diagonalVectors K) ^ 2 =
      r ^ 2 * ∑ a, Complex.normSq (trace (K a)) +
      s ^ 2 * ∑ a, Complex.normSq (trace (K a * diagonal z)) := by
  rw [columnLength_sq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, diagonalVectors,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.sq_norm,
    Matrix.trace, Matrix.diag, Matrix.mul_diagonal, mul_comm]

theorem diagonal_unitary_objective {d : ℕ} (u z : Fin d → ℂ) (r s : ℝ) :
    columnLength r s z u ^ 2 =
      r ^ 2 * Complex.normSq (trace (diagonal u)) +
      s ^ 2 * Complex.normSq (trace (diagonal u * diagonal z)) := by
  simp only [columnLength_sq, Complex.sq_norm, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, smul_eq_mul, mul_comm]

/-- For diagonal noise, every actual CPTP decoder has a feasible Euclidean
    family whose squared two-column length is its unnormalized score. -/
theorem diagonal_score_vectors {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (z : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) (D : CodeChannel d) :
    ∃ v : Fin d → EuclideanSpace ℂ (Fin d × Fin d),
      (∀ j, ‖v j‖ ≤ 1) ∧
      recoveryScore (binaryChannel hp hq hpq 1 (diagonalUnitary z hz)) D =
        (d : ℝ)⁻¹ ^ 2 * columnLength (Real.sqrt p) (Real.sqrt q) z v ^ 2 := by
  let K := actual_kraus_representation D
  let hcard := finCongr (Fintype.card_fin d)
  -- Use the canonical Kraus index, reindexed along the cardinality equality.
  let f : Fin d × Fin d ≃ Fin (Fintype.card (Fin d)) × Fin (Fintype.card (Fin d)) :=
    Equiv.prodCongr hcard.symm hcard.symm
  let L := K.kraus ∘ f
  have hL : ∑ a, (L a)ᴴ * L a = 1 := by
    rw [show (∑ a, (L a)ᴴ * L a) = ∑ a, (K.kraus a)ᴴ * K.kraus a from
      f.sum_comp (fun b => (K.kraus b)ᴴ * K.kraus b), K.hkraus]
  have hAction (X : CodeMatrix d) : channelAction D X = ∑ a, L a * X * (L a)ᴴ := by
    rw [show (∑ a, L a * X * (L a)ᴴ) = ∑ a, K.kraus a * X * (K.kraus a)ᴴ from
      f.sum_comp (fun b => K.kraus b * X * (K.kraus b)ᴴ)]
    exact K.haction X
  refine ⟨diagonalVectors L, diagonalVectors_le L hL, ?_⟩
  rw [binary_score_kraus hd hp hq hpq _ _ _ L hAction, diagonal_objective,
    Real.sq_sqrt hp, Real.sq_sqrt hq]
  simp [diagonalUnitary]

theorem diagonal_phase_score {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (z u : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) (hu : ∀ j, ‖u j‖ = 1) :
    recoveryScore (binaryChannel hp hq hpq 1 (diagonalUnitary z hz))
      (unitaryChannel (diagonalUnitary u hu)) =
      (d : ℝ)⁻¹ ^ 2 * columnLength (Real.sqrt p) (Real.sqrt q) z u ^ 2 := by
  rw [binary_score_kraus hd hp hq hpq _ _ _
    (fun _ : Unit => (diagonalUnitary u hu : CodeMatrix d))
    (fun X => by simp only [unitaryChannel_action, Fintype.sum_unique])]
  rw [diagonal_unitary_objective, Real.sq_sqrt hp, Real.sq_sqrt hq]
  simp [diagonalUnitary]

/-- A single diagonal unitary maximizes the actual CPTP recovery score for diagonal noise. -/
theorem diagonal_binary_unitary_optimal {d : ℕ} (hd : 0 < d) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (z : Fin d → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    ∃ u : Fin d → ℂ, ∃ hu : ∀ j, ‖u j‖ = 1, ∀ D : CodeChannel d,
      recoveryScore (binaryChannel hp hq hpq 1 (diagonalUnitary z hz)) D ≤
      recoveryScore (binaryChannel hp hq hpq 1 (diagonalUnitary z hz))
        (unitaryChannel (diagonalUnitary u hu)) := by
  obtain ⟨u, hu, hmax⟩ := optimal_phases (Real.sqrt p) (Real.sqrt q) z hz
  refine ⟨u, hu, fun D => ?_⟩
  obtain ⟨v, hv, hD⟩ := diagonal_score_vectors hd hp hq hpq z hz D
  rw [hD, diagonal_phase_score hd hp hq hpq z u hz hu]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hmax v hv) 2) (sq_nonneg _)

#print axioms canonical_reference
#print axioms binaryChannel_action
#print axioms canonical_overlap_kraus
#print axioms binary_score_kraus
#print axioms diagonal_binary_unitary_optimal

end D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
