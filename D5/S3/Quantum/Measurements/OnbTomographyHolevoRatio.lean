/- GID: D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/OnbTomographyHolevoRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Full orthonormal qudit tomography has NHCRB at most d+1 times HCRB. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
import D5.S3.Resource.LogDet.PathSpectralClassical

/-!
For a full Hilbert–Schmidt orthonormal basis of traceless Hermitian matrices,
the locally unbiased family is unique. The covariance's imaginary part obeys
`traceNorm (imPart z) ≥ d * tr(ρ²) - 1`: its Hermitian multiple `i imPart z`
is bounded between `-1/2` and `1/2`, and its squared Frobenius norm is
`(d * tr(ρ²) - 1) / 2`. This gives the required Holevo lower bound.

The Nagaoka–Hayashi upper bound uses the feasible point of Das et al.,
"Holevo Cramér-Rao bound: How close can we get without entangling measurements?",
arXiv:2405.09622v2, equation `upperboundNHCRB` and Lemma `primalsolutionNHCRB`.
Its positivity follows from a Hermitian block involution and the ONB contraction identity.
Both bounds use the source's uncentered LUB operators, identity weight, and parameter-square
subtraction. The semidefinite block constraint uses a parameter–quantum pair as its index.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
noncomputable section

/-- Hilbert–Schmidt orthonormal traceless Hermitian matrices, with source normalization. -/
def IsTracelessONB (d : ℕ)
    (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ j, (b j).IsHermitian) ∧ (∀ j, (b j).trace = 0) ∧
  ∀ j k, (b j * b k).trace = if j = k then 1 else 0

/-- The full linear tomography model. Positivity is imposed in the claim. -/
def model (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / (d : ℂ)) • 1 + ∑ j, (θ j : ℂ) • b j

/-- The source's uncentered locally unbiased operators. -/
def IsLUB (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ)
    (x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ k, (x k).IsHermitian) ∧ (∀ k, (model d b θ * x k).trace = (θ k : ℂ)) ∧
  ∀ j k, (b j * x k).trace = if j = k then 1 else 0

/-- The complex covariance matrix before subtracting the parameter square. -/
def zMatrix {d n : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => (ρ * x j * x k).trace

/-- Entrywise imaginary part, embedded into the complex matrices for the trace norm. -/
def imPart {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ((a j k).im : ℂ)

/-- Symmetric Hermitian blocks and the source's semidefinite constraint.
The block matrix is indexed by pairs consisting of a parameter and a quantum index. -/
def IsAdmissible {d n : ℕ} (x : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (l : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ j k, (l j k).IsHermitian) ∧ (∀ j k, l j k = l k j) ∧
  (show Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ from
    fun a b => (l a.1 b.1 - x a.1 * x b.1) a.2 b.2).PosSemidef

/-- Holevo Cramér–Rao bound with identity weight, as the source infimum. -/
def hcrb (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x, IsLUB d b θ x ∧
    c = (zMatrix (model d b θ) x).trace.re +
      traceNorm (imPart (zMatrix (model d b θ) x))} - ∑ j, θ j ^ 2

/-- Nagaoka–Hayashi Cramér–Rao bound with identity weight, as the source infimum. -/
def nhcrb (d : ℕ) (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (θ : Fin (d ^ 2 - 1) → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
    c = (∑ j, (model d b θ * l j j).trace).re} - ∑ j, θ j ^ 2

/-- The full-ONB form of the conjecture of Das et al., arXiv:2405.09622v2. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ, IsTracelessONB d b →
    ∀ θ : Fin (d ^ 2 - 1) → ℝ, (model d b θ).PosSemidef →
      nhcrb d b θ ≤ ((d : ℝ) + 1) * hcrb d b θ

private def primal (d : ℕ)
    (b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (j k : Fin (d ^ 2 - 1)) : Matrix (Fin d) (Fin d) ℂ :=
  (((d : ℂ) + 1) / ((d : ℂ) + 2)) •
    (b j * b k + b k * b j + if j = k then 1 else 0)

private lemma model_trace {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) : (model d b θ).trace = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [model]
  simp [trace_add, trace_smul, trace_sum, hb.2.1, hd0]

private lemma basis_is_lub {d : ℕ}
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) : IsLUB d b θ b := by
  classical
  refine ⟨hb.1, ?_, hb.2.2⟩
  intro k
  simp [model, add_mul, Finset.sum_mul, trace_add, trace_sum,
    trace_smul, hb.2.1, hb.2.2]

private lemma matrix_expansion {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (a : Matrix (Fin d) (Fin d) ℂ) :
    a = (a.trace / (d : ℂ)) • 1 + ∑ j, (b j * a).trace • b j := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  let f : Option (Fin (d ^ 2 - 1)) → Matrix (Fin d) (Fin d) ℂ :=
    fun i => i.elim 1 b
  have hli : LinearIndependent ℂ f := by
    let g : Option (Fin (d ^ 2 - 1)) → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ) :=
      fun i => i.elim ((1 / (d : ℂ)) • Matrix.traceLinearMap (Fin d) ℂ ℂ)
        (fun j => (Matrix.traceLinearMap (Fin d) ℂ ℂ).comp (LinearMap.mulLeft ℂ (b j)))
    apply LinearIndependent.of_pairwise_dual_eq_zero_one f g
    · intro i j hij
      cases i <;> cases j <;> simp_all [g, f, hb.2.1, hb.2.2]
    · intro i
      cases i <;> simp [g, f, hd0, hb.2.2]
  have hdim : Fintype.card (Option (Fin (d ^ 2 - 1))) =
      Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) := by
    simp only [Fintype.card_option, Fintype.card_fin, Module.finrank_matrix,
      Module.finrank_self, mul_one]
    have hsq : 1 ≤ d ^ 2 := by nlinarith
    simpa only [pow_two] using Nat.sub_add_cancel hsq
  let v := basisOfLinearIndependentOfCardEqFinrank hli hdim
  have hv (i) : v i = f i := coe_basisOfLinearIndependentOfCardEqFinrank hli hdim ▸ rfl
  have he := v.sum_repr a
  simp only [hv, Fintype.sum_option] at he
  change v.repr a none • 1 + ∑ j, v.repr a (some j) • b j = a at he
  have ht := congrArg Matrix.trace he
  simp only [trace_add, trace_smul, trace_one, Fintype.card_fin, trace_sum,
    hb.2.1, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero] at ht
  have hn : v.repr a none = a.trace / (d : ℂ) := (eq_div_iff hd0).mpr ht
  have hs (j : Fin (d ^ 2 - 1)) : v.repr a (some j) = (b j * a).trace := by
    have hk := congrArg (fun m => (b j * m).trace) he
    simpa [mul_add, Matrix.mul_smul, Matrix.mul_sum, trace_add, trace_smul,
      trace_sum, hb.2.1, hb.2.2] using hk
  rw [hn] at he
  simp_rw [hs] at he
  exact he.symm

private lemma basis_tensor {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (i j k l : Fin d) :
    ∑ q, b q i j * b q k l =
      (if i = l then if j = k then 1 else 0 else 0) -
        (1 / (d : ℂ)) * (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
  classical
  have he := congrArg (fun a : Matrix (Fin d) (Fin d) ℂ => a k l)
    (matrix_expansion hd hb (Matrix.single j i 1))
  have ht : (Matrix.single j i (1 : ℂ)).trace = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.trace_single_eq_of_ne, Ne.symm hij, hij]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.trace_mul_single,
    MulOpposite.op_one, one_smul, smul_eq_mul, ht] at he
  have heq : (Matrix.single j i (1 : ℂ)) k l =
      if i = l then if j = k then 1 else 0 else 0 := by
    simp only [Matrix.single_apply, ← ite_and, and_comm]
  rw [heq, Matrix.one_apply] at he
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    simp only [hij, hkl, ↓reduceIte, zero_div, zero_mul] at he ⊢ <;>
    linear_combination -he

private lemma fierz {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (a : Matrix (Fin d) (Fin d) ℂ) :
    ∑ q, b q * a * b q = a.trace • 1 - (1 / (d : ℂ)) • a := by
  classical
  ext i l
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul]
  change (∑ q, ∑ m, (∑ k, b q i k * a k m) * b q m l) =
    a.trace * (1 : Matrix (Fin d) (Fin d) ℂ) i l - (1 / (d : ℂ)) * a i l
  calc
    _ = ∑ k, ∑ m, a k m * ∑ q, b q i k * b q m l := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      simp_rw [basis_tensor hd hb]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Matrix.one_apply]
      split_ifs <;> simp_all [Matrix.trace, Matrix.diag_apply, mul_comm]

private lemma unique_lub {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    {θ : Fin (d ^ 2 - 1) → ℝ}
    {x : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hx : IsLUB d b θ x) : x = b := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  funext k
  have he := matrix_expansion hd hb (x k)
  have ht := hx.2.1 k
  have ht0 : (x k).trace = 0 := by
    have heq : (model d b θ * x k).trace =
        (1 / (d : ℂ)) * (x k).trace + (θ k : ℂ) := by
      simp [model, add_mul, Matrix.sum_mul, trace_add,
        trace_smul, trace_sum, hx.2.2]
    rw [heq] at ht
    have hz : (1 / (d : ℂ)) * (x k).trace = 0 := by linear_combination ht
    exact (mul_eq_zero.mp hz).resolve_left (one_div_ne_zero hd0)
  simpa [ht0, hx.2.2] using he

private lemma casimir {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b) :
    ∑ j, b j * b j = (((d : ℂ) ^ 2 - 1) / (d : ℂ)) • 1 := by
  have he := fierz hd hb (1 : Matrix (Fin d) (Fin d) ℂ)
  simp only [mul_one, trace_one, Fintype.card_fin] at he
  rw [he, ← sub_smul]
  congr 1
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  apply (eq_div_iff hd0).mpr
  rw [sub_mul, one_div_mul_cancel hd0]
  ring

private lemma purity_expansion {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (model d b θ * model d b θ).trace.re = 1 / (d : ℝ) + ∑ j, θ j ^ 2 := by
  have ht := model_trace hd hb θ
  have he := (basis_is_lub hb θ).2.1
  have hp : (model d b θ * model d b θ).trace =
      1 / (d : ℂ) + ∑ j, (θ j : ℂ) ^ 2 := by
    calc
      _ = (model d b θ * ((1 / (d : ℂ)) • 1 + ∑ j, (θ j : ℂ) • b j)).trace := rfl
      _ = _ := by
        simp only [mul_add, Matrix.mul_smul, mul_one, Finset.mul_sum, trace_add,
          trace_smul, trace_sum, ht, he, mul_one, smul_eq_mul, pow_two]
  have heq : (model d b θ * model d b θ).trace =
      ((1 / (d : ℝ) + ∑ j, θ j ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_pow] using hp
  simpa only [Complex.ofReal_re] using congrArg Complex.re heq

private lemma real_cost {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (zMatrix (model d b θ) b).trace.re = ((d : ℝ) ^ 2 - 1) / d := by
  have ht := model_trace hd hb θ
  have hc := casimir hd hb
  have he : (zMatrix (model d b θ) b).trace =
      ((d : ℂ) ^ 2 - 1) / (d : ℂ) := by
    change (∑ j, (model d b θ * b j * b j).trace) = _
    simp_rw [mul_assoc]
    rw [← trace_sum, ← Finset.mul_sum, hc, Matrix.mul_smul, mul_one, trace_smul, ht]
    simp
  rw [he]
  have hh : ((d : ℂ) ^ 2 - 1) / (d : ℂ) =
      ((((d : ℝ) ^ 2 - 1) / d : ℝ) : ℂ) := by push_cast; rfl
  rw [hh, Complex.ofReal_re]

private lemma trace_pairing {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (a c : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j, (a * b j).trace * (b j * c).trace =
      (a * c).trace - a.trace * c.trace / (d : ℂ) := by
  have he := congrArg (fun m => (a * m).trace) (matrix_expansion hd hb c)
  simp only [mul_add, Matrix.mul_smul, Matrix.mul_sum, trace_add, trace_smul,
    trace_sum, mul_one, smul_eq_mul] at he
  simp_rw [mul_comm (a * b _).trace] at ⊢
  linear_combination -he

private lemma covariance_hermitian {d n : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) {b : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hb : ∀ j, (b j).IsHermitian) : (zMatrix ρ b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro j k
  change star (ρ * b k * b j).trace = _
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul,
    (hb j).eq, (hb k).eq, hρ.eq, trace_mul_comm]
  rw [mul_assoc, trace_mul_comm (b k) (ρ * b j)]
  rw [zMatrix]

private lemma covariance_psd {d n : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) {b : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hb : ∀ j, (b j).IsHermitian) : (zMatrix ρ b).PosSemidef := by
  letI := ρ.toMatrixSeminormedAddCommGroup hρ
  letI := ρ.toMatrixInnerProductSpace hρ
  convert Matrix.posSemidef_gram ℂ b using 1
  ext j k
  change (ρ * b j * b k).trace = (b k * ρ * (b j)ᴴ).trace
  rw [(hb j).eq, trace_mul_cycle]

private lemma norm_contraction {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ)
    (ha : a.IsHermitian) (hp : (1 + (2 : ℂ) • a).PosSemidef)
    (hm : (1 - (2 : ℂ) • a).PosSemidef) :
    2 * (a * a).trace.re ≤ traceNorm a := by
  classical
  have hbound (j : Fin n) : |ha.eigenvalues j| ≤ 1 / 2 := by
    have hv : star ⇑(ha.eigenvectorBasis j) ⬝ᵥ ⇑(ha.eigenvectorBasis j) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      simpa only [ite_true] using
        (orthonormal_iff_ite.mp ha.eigenvectorBasis.orthonormal j j)
    have hplus := hp.re_dotProduct_nonneg ⇑(ha.eigenvectorBasis j)
    have hminus := hm.re_dotProduct_nonneg ⇑(ha.eigenvectorBasis j)
    simp [add_mulVec, sub_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_sub,
      dotProduct_smul, ha.mulVec_eigenvectorBasis, hv, RCLike.real_smul_eq_coe_mul] at hplus hminus
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : traceNorm a = ∑ j, |ha.eigenvalues j| := by
    change (CFC.abs a).trace.re = _
    rw [CFC.abs_eq_cfc_norm a ha.isSelfAdjoint]
    simpa only [Real.norm_eq_abs] using
      D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum a ha (fun t : ℝ => ‖t‖)
  have hs : (a * a).trace.re = ∑ j, (ha.eigenvalues j) ^ 2 := by
    have h := RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues ha
    rw [RHLinalg.frobSq, ha.eq] at h
    exact h
  rw [hn, hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := hbound j
  have hh : |ha.eigenvalues j| ^ 2 = (ha.eigenvalues j) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (ha.eigenvalues j)]

private lemma commutator_square_sum {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (ht : ρ.trace = 1) :
    (∑ j, ((ρ * b j - b j * ρ) * (ρ * b j - b j * ρ)).trace) =
      2 - 2 * (d : ℂ) * (ρ * ρ).trace := by
  have hex (j) : ((ρ * b j - b j * ρ) * (ρ * b j - b j * ρ)).trace =
      2 * (ρ * b j * ρ * b j).trace - 2 * (ρ * ρ * b j * b j).trace := by
    have h1 := trace_mul_comm (b j) (ρ * b j * ρ)
    have h2 := trace_mul_cycle (ρ * b j) (b j) ρ
    have h3 := trace_mul_comm (b j) (ρ * ρ * b j)
    simp only [mul_assoc] at h1 h2 h3
    simp only [sub_mul, mul_sub, trace_sub, mul_assoc]
    linear_combination h1 - h2 - h3
  have h1 : (∑ j, (ρ * b j * ρ * b j).trace) = 1 - (ρ * ρ).trace / (d : ℂ) := by
    calc
      _ = (ρ * ∑ j, b j * ρ * b j).trace := by
        simp only [Matrix.mul_sum, trace_sum, mul_assoc]
      _ = _ := by
        rw [fierz hd hb]
        simp only [mul_sub, Matrix.mul_smul, trace_sub, trace_smul, mul_one, ht,
          smul_eq_mul]
        ring
  have h2 : (∑ j, (ρ * ρ * b j * b j).trace) =
      (((d : ℂ) ^ 2 - 1) / d) * (ρ * ρ).trace := by
    calc
      _ = ((ρ * ρ) * ∑ j, b j * b j).trace := by
        simp only [Matrix.mul_sum, trace_sum, mul_assoc]
      _ = _ := by rw [casimir hd hb, Matrix.mul_smul, mul_one, trace_smul]; rfl
  simp_rw [hex]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp
  ring

private lemma imaginary_bound {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    (d : ℝ) * (model d b θ * model d b θ).trace.re - 1 ≤
      traceNorm (imPart (zMatrix (model d b θ) b)) := by
  classical
  let ρ := model d b θ
  let z := zMatrix ρ b
  let a := Complex.I • imPart z
  have ht : ρ.trace = 1 := model_trace hd hb θ
  have hzh : z.IsHermitian := covariance_hermitian hρ.1 hb.1
  have hzp : z.PosSemidef := covariance_psd hρ hb.1
  have haz : a = (1 / (2 : ℂ)) • (z - zᵀ) := by
    ext j k
    have hjk : z k j = star (z j k) := (hzh.apply k j).symm
    change Complex.I * ((z j k).im : ℂ) = (1 / (2 : ℂ)) * (z j k - z k j)
    rw [hjk, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hah : a.IsHermitian := by
    rw [haz]
    exact (hzh.sub hzh.transpose).smul (by simp)
  have hcomp : (1 - z).PosSemidef := by
    have hρc : (1 - ρ).PosSemidef := by
      simpa only [ht, Complex.one_re, Complex.ofReal_one, one_smul] using
        D5.S3.Quantum.Matrix.LinGProperty.trace_identity_sub_posSemidef ρ hρ
    have h := covariance_psd hρc hb.1
    have he : zMatrix (1 - ρ) b = 1 - z := by
      ext j k
      simp only [zMatrix, sub_mul, one_mul, trace_sub, hb.2.2, Matrix.sub_apply,
        Matrix.one_apply, z]
    rwa [he] at h
  have htwo : (2 : ℂ) • a = z - zᵀ := by rw [haz, smul_smul]; norm_num
  have hp : (1 + (2 : ℂ) • a).PosSemidef := by
    rw [htwo]
    convert hzp.add hcomp.transpose using 1
    simp only [transpose_sub, transpose_one]
    abel
  have hm : (1 - (2 : ℂ) • a).PosSemidef := by
    rw [htwo]
    convert hcomp.add hzp.transpose using 1
    abel
  let c := fun j => ρ * b j - b j * ρ
  have hc (j) : (c j).trace = 0 := by
    change (ρ * b j - b j * ρ).trace = 0
    exact LieAlgebra.matrix_trace_commutator_zero (Fin d) ℂ ρ (b j)
  have hae (j k) : a j k = (1 / (2 : ℂ)) * (c j * b k).trace := by
    rw [haz]
    change (1 / (2 : ℂ)) * ((ρ * b j * b k).trace - (ρ * b k * b j).trace) = _
    simp only [c, sub_mul, trace_sub, mul_assoc]
    rw [trace_mul_comm (b j) (ρ * b k)]
    simp only [mul_assoc]
  have has (j k) : a k j = -a j k := by
    rw [haz]
    change (1 / (2 : ℂ)) * (z k j - z j k) = -((1 / (2 : ℂ)) * (z j k - z k j))
    ring
  have hparse (j) : (∑ k, (c j * b k).trace ^ 2) = (c j * c j).trace := by
    calc
      _ = ∑ k, (c j * b k).trace * (b k * c j).trace := by
        apply Finset.sum_congr rfl
        intro k _
        rw [trace_mul_comm (b k) (c j)]
        ring
      _ = _ := by rw [trace_pairing hd hb, hc]; simp
  have hsq : (a * a).trace = ((d : ℂ) * (ρ * ρ).trace - 1) / 2 := by
    calc
      _ = ∑ j, -(1 / (4 : ℂ)) * (c j * c j).trace := by
        change (∑ j, ∑ k, a j k * a k j) =
          ∑ j, -(1 / (4 : ℂ)) * (c j * c j).trace
        apply Finset.sum_congr rfl
        intro j _
        rw [← hparse j, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [has j k, hae j k]
        ring
      _ = -(1 / (4 : ℂ)) * ∑ j, (c j * c j).trace := by rw [Finset.mul_sum]
      _ = _ := by rw [show (∑ j, (c j * c j).trace) =
          2 - 2 * (d : ℂ) * (ρ * ρ).trace from commutator_square_sum hd hb ρ ht]; ring
  have hn : traceNorm a = traceNorm (imPart z) := by
    change (CFC.abs (Complex.I • imPart z)).trace.re = (CFC.abs (imPart z)).trace.re
    rw [CFC.abs_smul, Complex.norm_I, one_smul]
  have h := norm_contraction a hah hp hm
  rw [hsq, hn] at h
  have he : (((d : ℂ) * (ρ * ρ).trace - 1) / 2).re =
      ((d : ℝ) * (ρ * ρ).trace.re - 1) / 2 := by
    simp [Complex.mul_re]
  rw [he] at h
  change (d : ℝ) * (ρ * ρ).trace.re - 1 ≤ traceNorm (imPart z)
  linarith

private lemma holevo_exact {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    hcrb d b θ = (zMatrix (model d b θ) b).trace.re +
      traceNorm (imPart (zMatrix (model d b θ) b)) - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hb θ
  have hu := @unique_lub d hd b hb θ
  have he : {c : ℝ | ∃ x, IsLUB d b θ x ∧
      c = (zMatrix (model d b θ) x).trace.re +
        traceNorm (imPart (zMatrix (model d b θ) x))} =
      {(zMatrix (model d b θ) b).trace.re +
        traceNorm (imPart (zMatrix (model d b θ) b))} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hu hx]
      exact Set.mem_singleton _
    · intro hc
      exact ⟨b, hl, Set.mem_singleton_iff.mp hc⟩
  rw [hcrb, he, csInf_singleton]

private lemma holevo_lower {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    ((d : ℝ) ^ 2 - 1) / d ≤ hcrb d b θ := by
  have he := holevo_exact hd hb θ
  have hr := real_cost hd hb θ
  have hi := imaginary_bound hd hb θ hρ
  have hp := purity_expansion hd hb θ
  have hs : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hdiv : (d : ℝ) * (1 / (d : ℝ)) = 1 := mul_one_div_cancel hd0
  rw [he, hr]
  nlinarith

private lemma primal_admissible {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b) :
    IsAdmissible b (primal d b) := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℂ) + 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < d + 1)
  have hd2 : (d : ℂ) + 2 ≠ 0 := by
    exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < d + 2)
  let r : ℂ := 1 / ((d : ℂ) + 1)
  let t : Matrix (Fin (d ^ 2 - 1)) (Fin (d ^ 2 - 1))
      (Matrix (Fin d) (Fin d) ℂ) := fun j k => b k * b j - r • (b j * b k)
  have ht : t.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro j k
    change (b j * b k - r • (b k * b j))ᴴ = _
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_smul,
      (hb.1 j).eq, (hb.1 k).eq]
    simp [r, t]
  have ht2 : t * t = 1 := by
    apply Matrix.ext
    intro j l
    change (∑ k, t j k * t k l) = (1 : Matrix _ _ (Matrix (Fin d) (Fin d) ℂ)) j l
    have he : (∑ k, t j k * t k l) =
        (∑ k, b k * (b j * b l) * b k) -
        r • ((∑ k, b k * b j * b k) * b l) -
        r • (b j * (∑ k, b k * b l * b k)) +
        (r * r) • (b j * (∑ k, b k * b k) * b l) := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [t, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_assoc]
      module
    rw [he, fierz hd hb, fierz hd hb, fierz hd hb, casimir hd hb, hb.2.1,
      hb.2.1, hb.2.2]
    simp only [zero_smul, zero_sub, neg_mul, mul_neg, Matrix.smul_mul, Matrix.mul_smul,
      mul_one, smul_neg, smul_smul, sub_neg_eq_add]
    rw [Matrix.one_apply]
    split_ifs <;> simp only [zero_smul, one_smul] <;> match_scalars <;>
      dsimp [r] <;> field_simp <;> ring
  let s : Matrix (Fin (d ^ 2 - 1) × Fin d) (Fin (d ^ 2 - 1) × Fin d) ℂ :=
    Matrix.comp _ _ _ _ ℂ t
  have hs : s.IsHermitian := Matrix.isHermitian_comp_iff.mpr ht
  have hs2 : s * s = 1 := by
    change Matrix.compRingEquiv _ _ ℂ t * Matrix.compRingEquiv _ _ ℂ t = 1
    rw [← map_mul, ht2, map_one]
  have hps : (1 + s).PosSemidef :=
    (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper.involution_binary s hs
      (by simpa only [pow_two] using hs2)).2
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    rw [IsHermitian, primal]
    simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
      (hb.1 j).eq, (hb.1 k).eq, star_div₀, star_add, star_natCast, star_one,
      star_ofNat, apply_ite, conjTranspose_one, conjTranspose_zero]
    rw [add_comm (b k * b j) (b j * b k)]
    split_ifs <;> rfl
  · intro j k
    simp only [primal]
    rw [add_comm (b j * b k) (b k * b j)]
    congr 2
    simp only [eq_comm]
  · have hscale : (0 : ℂ) ≤ ((d : ℂ) + 1) / ((d : ℂ) + 2) := by
      have he : ((d : ℂ) + 1) / ((d : ℂ) + 2) =
          ((((d : ℝ) + 1) / ((d : ℝ) + 2) : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.zero_le_real]
      positivity
    have hcoef : (((d : ℂ) + 1) / ((d : ℂ) + 2)) * r =
        1 - ((d : ℂ) + 1) / ((d : ℂ) + 2) := by
      dsimp [r]
      field_simp
      ring
    have hblock (j k) : primal d b j k - b j * b k =
        (((d : ℂ) + 1) / ((d : ℂ) + 2)) •
          ((if j = k then 1 else 0) + (b k * b j - r • (b j * b k))) := by
      simp only [primal, smul_add, smul_sub, smul_smul, hcoef]
      module
    convert hps.smul hscale using 1
    ext a c
    have hi : (1 : Matrix (Fin (d ^ 2 - 1) × Fin d) _ ℂ) a c =
        (if a.1 = c.1 then (1 : Matrix (Fin d) (Fin d) ℂ) else 0) a.2 c.2 := by
      exact (congrArg (fun m : Matrix (Fin (d ^ 2 - 1) × Fin d) _ ℂ => m a c)
        (Matrix.compRingEquiv (Fin (d ^ 2 - 1)) (Fin d) ℂ |>.map_one)).symm
    change (primal d b a.1 c.1 - b a.1 * b c.1) a.2 c.2 =
      (((d : ℂ) + 1) / ((d : ℂ) + 2)) * ((1 : Matrix _ _ ℂ) a c + s a c)
    rw [hblock, hi]
    rfl

private lemma primal_cost {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) :
    (∑ j, (model d b θ * primal d b j j).trace).re =
      (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by
  have hc := casimir hd hb
  have ht := model_trace hd hb θ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd2 : (d : ℂ) + 2 ≠ 0 := by
    have hn : (0 : ℝ) < d + 2 := by positivity
    exact_mod_cast ne_of_gt hn
  have hn : ((d ^ 2 - 1 : ℕ) : ℂ) = (d : ℂ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ d ^ 2)]
    simp
  have hs : ∑ j, primal d b j j =
      ((((d : ℂ) ^ 2 - 1) * ((d : ℂ) + 1)) / d) • 1 := by
    simp only [primal, ↓reduceIte, ← Finset.smul_sum, Finset.sum_add_distrib, hc,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← add_smul, ← Nat.cast_smul_eq_nsmul ℂ,
      hn, ← add_smul, smul_smul]
    congr 1
    apply (eq_div_iff hd0).mpr
    rw [mul_assoc]
    simp only [add_mul, div_mul_cancel₀ _ hd0]
    have hf : ((d : ℂ) ^ 2 - 1) + ((d : ℂ) ^ 2 - 1) +
        ((d : ℂ) ^ 2 - 1) * d = ((d : ℂ) + 2) * ((d : ℂ) ^ 2 - 1) := by ring
    rw [hf, ← mul_assoc, div_mul_cancel₀ _ hd2]
    ring
  have he : (∑ j, (model d b θ * primal d b j j).trace) =
      (((d : ℂ) ^ 2 - 1) * ((d : ℂ) + 1)) / d := by
    rw [← trace_sum, ← Matrix.mul_sum, hs, Matrix.mul_smul, mul_one, trace_smul, ht]
    simp
  rw [he]
  have hh : (((d : ℂ) ^ 2 - 1) * ((d : ℂ) + 1)) / d =
      (((((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d : ℝ) : ℂ) := by push_cast; rfl
  rw [hh, Complex.ofReal_re]

private lemma admissible_cost_nonneg {d n : ℕ}
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    {x : Fin n → Matrix (Fin d) (Fin d) ℂ} (hx : ∀ j, (x j).IsHermitian)
    {l : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ} (hl : IsAdmissible x l) :
    0 ≤ (∑ j, (ρ * l j j).trace).re := by
  classical
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  have hd : (l j j - x j * x j).PosSemidef := hl.2.2.submatrix (fun i => (j, i))
  have hs : (x j * x j).PosSemidef := by
    simpa only [(hx j).eq] using posSemidef_conjTranspose_mul_self (x j)
  have hp : (l j j).PosSemidef := by
    simpa only [sub_add_cancel] using hd.add hs
  exact RHLinalg.trace_mul_nonneg_of_posSemidef hρ hp

private lemma nagaoka_upper {d : ℕ} (hd : 2 ≤ d)
    {b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ} (hb : IsTracelessONB d b)
    (θ : Fin (d ^ 2 - 1) → ℝ) (hρ : (model d b θ).PosSemidef) :
    nhcrb d b θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d - ∑ j, θ j ^ 2 := by
  have hl := basis_is_lub hb θ
  have ha := primal_admissible hd hb
  have hc := primal_cost hd hb θ
  have hn := @admissible_cost_nonneg d (d ^ 2 - 1) (model d b θ) hρ
  have hbd : BddBelow {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
      c = (∑ j, (model d b θ * l j j).trace).re} := by
    refine ⟨0, ?_⟩
    rintro c ⟨x, l, hx, ha, rfl⟩
    exact hn hx.1 ha
  have hf : (∑ j, (model d b θ * primal d b j j).trace).re ∈
      {c : ℝ | ∃ x l, IsLUB d b θ x ∧ IsAdmissible x l ∧
        c = (∑ j, (model d b θ * l j j).trace).re} :=
    ⟨b, primal d b, hl, ha, rfl⟩
  have hi := csInf_le hbd hf
  rw [nhcrb]
  rw [hc] at hi
  exact sub_le_sub_right hi _

theorem result : claim := by
  intro d hd b hb θ hρ
  have hh := holevo_lower hd hb θ hρ
  have hn := nagaoka_upper hd hb θ hρ
  have hs : 0 ≤ ∑ j, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hdpos : 0 ≤ (d : ℝ) + 1 := by positivity
  calc
    nhcrb d b θ ≤ (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 1)) / d := by linarith
    _ = ((d : ℝ) + 1) * (((d : ℝ) ^ 2 - 1) / d) := by ring
    _ ≤ ((d : ℝ) + 1) * hcrb d b θ := mul_le_mul_of_nonneg_left hh hdpos

end
end D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
