/- GID: D5/S3/Analytic/Hunter/NCHunterPositivity
   generality: G
   mirror-B: D5/B/S3/Analytic/Hunter/NCHunterPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp noncommutative Hunter operator bound. -/
/-
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/Entanglement/OccupancyWordSectors; statement_id: sha256:4c2e6fd9d41a26d9ddd554f91b64b4ed76e6b80ed308ee656970febafbbe55e1.
Information-escape registration is paused under CLAUDE.md section 3.9.
sharp_from_representers: proof_shape: bind-only; escape_witness: none; consumer: sharp_posSemidef_of_representers | complete_variance_posSemidef: proof_shape: bind-only; escape_witness: none; consumer: constant_block_even_bound
all_ones_posSemidef: proof_shape: bind-only; escape_witness: none; consumer: constant_block_odd_bound | constant_block_even_bound: proof_shape: bind-only; escape_witness: none; consumer: pure_block_bound
constant_block_odd_bound: proof_shape: bind-only; escape_witness: none; consumer: pure_block_bound | count_constant_all: proof_shape: bind-only; escape_witness: none; consumer: representer_certificate
word_constant_of_full_count: proof_shape: bind-only; escape_witness: none; consumer: representer_certificate | binomial_normalization: proof_shape: bind-only; escape_witness: none; consumer: normalized_pure_value
normalized_pure_value: proof_shape: bind-only; escape_witness: none; consumer: representer_certificate | count_constant: proof_shape: bind-only; escape_witness: none; consumer: degree_fiber_constant
generalized_vandermonde_range: proof_shape: bind-only; escape_witness: none; consumer: binomial_weighted_convolution | binomial_weighted_convolution: proof_shape: bind-only; escape_witness: none; consumer: inverse_convolution_identity
choose_add_rectangular: proof_shape: bind-only; escape_witness: none; consumer: inverse_convolution_identity | inverse_convolution_identity: proof_shape: bind-only; escape_witness: none; consumer: inverse_convolution_real
inverse_convolution_real: proof_shape: bind-only; escape_witness: none; consumer: inverse_word_sum | negative_binomial: proof_shape: bind-only; escape_witness: none; consumer: inverse_urn_term
inverse_urn_term: proof_shape: bind-only; escape_witness: none; consumer: inverse_word_sum | binomial_urn_step: proof_shape: bind-only; escape_witness: none; consumer: urn_closed_form
other_mass_add: proof_shape: bind-only; escape_witness: none; consumer: urn_closed_form | count_cons: proof_shape: bind-only; escape_witness: none; consumer: moment_coefficient_cons
factorial_word_cons: proof_shape: bind-only; escape_witness: none; consumer: urn_step | sum_count: proof_shape: bind-only; escape_witness: none; consumer: urn_step
sum_word_succ: proof_shape: bind-only; escape_witness: none; consumer: moment_words_succ_inner | urn_step: proof_shape: bind-only; escape_witness: none; consumer: urn_closed_form
urn_closed_form: proof_shape: content; escape_witness: urn_closed_form | inverse_word_sum: proof_shape: content; escape_witness: urn_closed_form
representer_certificate: proof_shape: content; escape_witness: urn_closed_form | matrix_action_mul: proof_shape: bind-only; escape_witness: none; consumer: positive_definite_form_zero_vectors
hilbert_gram_action: proof_shape: bind-only; escape_witness: none; consumer: positive_form_zero_rows | hilbert_gram_identity: proof_shape: bind-only; escape_witness: none; consumer: positive_form_zero_rows
positive_form_zero_rows: proof_shape: bind-only; escape_witness: none; consumer: kernel_to_mixed_rows | positive_definite_form_zero_vectors: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_zero_coefficients
degree_feature_diagonal: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_complex_posDef | factorial_feature_self_pos: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_complex_posDef
shifted_factorial_gram: proof_shape: bind-only; escape_witness: none; consumer: shifted_factorial_gram_bound | shifted_factorial_gram_bound: proof_shape: bind-only; escape_witness: none; consumer: factorial_moment_gram
factorial_moment_gram: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_complex_posDef | factorial_weight_pos: proof_shape: bind-only; escape_witness: none; consumer: shifted_moment_complex_posDef
count_append: proof_shape: bind-only; escape_witness: none; consumer: word_moment_even_identity | reverse_word_list: proof_shape: bind-only; escape_witness: none; consumer: count_reverse
count_reverse: proof_shape: bind-only; escape_witness: none; consumer: word_moment_even_identity | word_eval_append: proof_shape: bind-only; escape_witness: none; consumer: word_moment_even_identity
word_eval_reverse: proof_shape: bind-only; escape_witness: none; consumer: word_moment_even_identity | factorial_moment_posDef: proof_shape: bind-only; escape_witness: none; consumer: real_gram_posSemidef
real_gram_posSemidef: proof_shape: bind-only; escape_witness: none; consumer: sharp_posSemidef_of_representers | real_to_complex_psd: proof_shape: bind-only; escape_witness: none; consumer: sharp_posSemidef_of_representers
constant_word_injective: proof_shape: bind-only; escape_witness: none; consumer: embedding_product | embedding_product: proof_shape: bind-only; escape_witness: none; consumer: sharp_posSemidef_of_representers
sharp_posSemidef_of_representers: proof_shape: bind-only; escape_witness: none; consumer: sharp_gram_posSemidef | word_gram_identity: proof_shape: bind-only; escape_witness: none; consumer: nchs_inner_gram
nchs_inner_gram: proof_shape: bind-only; escape_witness: none; consumer: residual_inner_gram | sum_pure: proof_shape: bind-only; escape_witness: none; consumer: pure_form
pure_form: proof_shape: bind-only; escape_witness: none; consumer: residual_inner_gram | form_sub_smul: proof_shape: bind-only; escape_witness: none; consumer: residual_inner_gram
residual_inner_gram: proof_shape: bind-only; escape_witness: none; consumer: kernel_to_mixed_rows | transpose_embedding_action: proof_shape: bind-only; escape_witness: none; consumer: inverse_pure_block
inverse_pure_block: proof_shape: bind-only; escape_witness: none; consumer: pure_block_bound | degree_count_pos: proof_shape: bind-only; escape_witness: none; consumer: pure_block_bound
double_degree_count_pos: proof_shape: bind-only; escape_witness: none; consumer: pure_block_bound | pure_block_bound: proof_shape: bind-only; escape_witness: none; consumer: sharp_gram_posSemidef
mu_nonnegative: proof_shape: bind-only; escape_witness: none; consumer: sharp_gram_posSemidef | sharp_gram_posSemidef: proof_shape: content; escape_witness: urn_closed_form
matrix_form_nonnegative: proof_shape: bind-only; escape_witness: none; consumer: sharp_positivity | sharp_positivity: proof_shape: content; escape_witness: urn_closed_form
-/
import D5.S3.Quantum.Entanglement.OccupancyWordSectors
open scoped BigOperators Matrix MatrixOrder ComplexOrder InnerProductSpace Matrix.Module
set_option backward.isDefEq.respectTransparency false
namespace GVHunter
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (occupation)
attribute [local instance] Classical.propDecidable Classical.decEq
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} [Fintype I]
variable {A : Type*} [Ring A] [Algebra ℂ A]
private theorem sharp_from_representers {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m ℝ) (R E : Matrix m n ℝ) (c : ℝ) (hA : A.PosSemidef) (hAR : A * R = E) (hc : 0 ≤ c) (hB : (1 - c • (Eᵀ * R)).PosSemidef) : (A - c • (E * Eᵀ)).PosSemidef := by
  let P : Matrix m m ℝ := 1 - c • (R * Eᵀ)
  have htA : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hRA : Rᵀ * A = Eᵀ := by
    have ht := congrArg Matrix.transpose hAR
    simpa only [Matrix.transpose_mul, htA] using ht
  have heq : A - c • (E * Eᵀ) =
      Pᵀ * A * P + c • (E * (1 - c • (Eᵀ * R)) * Eᵀ) := by
    dsimp [P]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hAR]
    simp only [Matrix.mul_assoc, hAR]
    rw [hRA]
    have hRE : Rᵀ * E = Eᵀ * R := by
      calc
        Rᵀ * E = Rᵀ * (A * R) := by rw [hAR]
        _ = (Rᵀ * A) * R := by rw [Matrix.mul_assoc]
        _ = Eᵀ * R := by rw [hRA]
    simp only [← Matrix.mul_assoc, hRE]
    simp only [Matrix.mul_assoc, smul_sub, smul_smul]
    module
  rw [heq]
  have hp := hA.conjTranspose_mul_mul_same P
  have hb := hB.mul_mul_conjTranspose_same E
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp.add (hb.smul hc)
private theorem complete_variance_posSemidef (n : ℕ) : ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of (fun _ _ : Fin n => (1 : ℝ)))).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply, eq_comm]
  · intro x
    have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1:ℝ)) x
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    have heq : star x ⬝ᵥ (((n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of (fun _ _ : Fin n => (1 : ℝ)))) *ᵥ x) =
        (n:ℝ) * ∑ i : Fin n, x i ^ 2 - (∑ i : Fin n, x i)^2 := by
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_trivial]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, one_mul]
      simp_rw [← sq]
      rw [← Finset.sum_mul]
      ring
    rw [heq]
    exact sub_nonneg.mpr hs
private theorem all_ones_posSemidef (n : ℕ) : ((Matrix.of (fun _ _ : Fin n => (1 : ℝ)))).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin n => (1:ℝ)) using 1
  ext i j
  simp [Matrix.vecMulVec, Matrix.of_apply]
private theorem constant_block_even_bound (n : ℕ) (a b c : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b) (he : c * (a + (n:ℝ)*b) = 1) : (1 - c • (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))))).PosSemidef := by
  have hid : 1 - c • (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • (Matrix.of (fun _ _ : Fin n => (1 : ℝ)))) =
      (c*b) • ((n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of (fun _ _ : Fin n => (1 : ℝ)))) := by
    have ha : 1-c*a=c*b*(n:ℝ) := by nlinarith [he]
    calc
      _ = (1-c*a) • (1 : Matrix (Fin n) (Fin n) ℝ) + (-c*b) • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))) := by module
      _ = (c*b*(n:ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ) + (-c*b) • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))) := by rw [ha]
      _ = _ := by module
  rw [hid]
  exact (complete_variance_posSemidef n).smul (mul_nonneg hc hb)
private theorem constant_block_odd_bound (n : ℕ) (a b c : ℝ) (hc : 0 ≤ c) (hb : b ≤ 0) (he : c*a=1) : (1 - c • (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))))).PosSemidef := by
  have hid : 1 - c • (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • (Matrix.of (fun _ _ : Fin n => (1 : ℝ)))) =
      (-c*b) • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))) := by
    have hz : 1-c*a=0 := by linarith [he]
    calc
      _ = (1-c*a) • (1 : Matrix (Fin n) (Fin n) ℝ) + (-c*b) • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))) := by module
      _ = _ := by rw [hz]; simp
  rw [hid]
  exact (all_ones_posSemidef n).smul (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hc) hb)
private lemma count_constant_all {n d : ℕ} (i j : Fin n) : (occupation (fun _ : Fin d => i)).count j = if j=i then d else 0 := by
  classical
  by_cases h : j=i
  · subst j
    simp [occupation, List.ofFn_const]
  · simp [occupation, List.ofFn_const, h]
private lemma word_constant_of_full_count {n d : ℕ} (w : (Fin d → Fin n)) (i : Fin n) (hc : (occupation w).count i = d) : w=(fun _=>i) := by
  have hcard : (occupation w).count i = (occupation w).card := by
    simpa only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation_card] using hc
  have hm := Multiset.count_eq_card.mp hcard
  funext j
  exact (hm (w j) (by simp [occupation, List.mem_ofFn])).symm
private lemma binomial_normalization (m d : ℕ) (hd : d ≤ m) : Nat.choose m d * Nat.choose (m+d) d * (Nat.factorial d)^2 = Nat.choose (m+d) (2*d) * Nat.factorial (2*d) := by
  apply Nat.mul_right_cancel (Nat.factorial_pos (m-d))
  have h1 := Nat.choose_mul_factorial_mul_factorial (n:=m) (k:=d) hd
  have h2 := Nat.choose_mul_factorial_mul_factorial (n:=m+d) (k:=d) (by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (n:=m+d) (k:=2*d) (by omega)
  rw [show m+d-d=m by omega] at h2
  rw [show m+d-2*d=m-d by omega] at h3
  calc
    _ = Nat.choose (m+d) d * Nat.factorial d *
      (Nat.choose m d * Nat.factorial d * Nat.factorial (m-d)) := by ring
    _ = _ := by rw [h1, h2, h3]
private lemma normalized_pure_value (n d : ℕ) : (Nat.choose (n-1+d) d : ℝ) / (Nat.choose (n-1+2*d) (2*d) : ℝ) / (Nat.factorial (2*d) : ℝ) * (Nat.factorial d : ℝ)^2 * (Nat.choose (n-1+d+d) d : ℝ) = 1 := by
  have h1 : (Nat.choose (n-1+2*d) (2*d) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2*d ≤ n-1+2*d)).ne'
  have h2 : (Nat.factorial (2*d) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*d)
  have hh : (Nat.choose (n-1+d) d : ℝ) * (Nat.choose (n-1+d+d) d : ℝ) *
      (Nat.factorial d : ℝ)^2 =
      (Nat.choose (n-1+2*d) (2*d) : ℝ) * (Nat.factorial (2*d) : ℝ) := by
    have h := binomial_normalization (n-1+d) d (by omega)
    rw [show n-1+d+d=n-1+2*d by omega] at h
    rw [show n-1+d+d=n-1+2*d by omega]
    exact_mod_cast h
  field_simp
  nlinarith [hh]
lemma count_constant {n m : ℕ} (i : Fin n) : (occupation (fun _ : Fin m => i)).count i = m := by
  simp [occupation, List.ofFn_const]
private noncomputable def factorialWord {n k : ℕ} (l : Fin n → ℕ) (w : (Fin k → Fin n)) : ℝ :=
  ∏ j : Fin n, (Nat.factorial (l j + (occupation w).count j) : ℝ)
private noncomputable def binomialUrn (a b d : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d+1),
    (Nat.choose d k : ℝ) * (Nat.ascFactorial a k : ℝ) *
      (Nat.ascFactorial b (d-k) : ℝ) * f k
private noncomputable def inverseConvolution (m l d : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (d+1), (Nat.choose m k : ℚ) *
    Ring.choose ((l : ℚ) - m) (d-k) * (Nat.choose (l+k) k : ℚ)
private theorem generalized_vandermonde_range (r s : ℚ) (d : ℕ) : Ring.choose (r+s) d = ∑ k ∈ Finset.range (d+1), Ring.choose r k * Ring.choose s (d-k) := by
  rw [Ring.add_choose_eq d (Commute.all r s),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
private theorem binomial_weighted_convolution (m d j : ℕ) (r : ℚ) (hj : j ≤ d) (hm : d ≤ m) : (∑ k ∈ Finset.range (d+1), (Nat.choose m k : ℚ) * (Nat.choose k j : ℚ) * Ring.choose r (d-k)) = (Nat.choose m j : ℚ) * Ring.choose (r+(m-j : ℕ)) (d-j) := by
  have hsplit : d+1 = j + (d-j+1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range j, (Nat.choose m k : ℚ) *
      (Nat.choose k j : ℚ) * Ring.choose r (d-k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    simp [Nat.choose_eq_zero_of_lt hkj]
  rw [hz, zero_add]
  rw [add_comm r, generalized_vandermonde_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : j+k ≤ m := by have := Finset.mem_range.mp hk; omega
  have h := Nat.choose_mul (n:=m) (k:=j+k) (s:=j) (by omega)
  have ht : j+k-j=k := by omega
  rw [ht] at h
  have hcast : (Nat.choose m (j+k) : ℚ) * (Nat.choose (j+k) j : ℚ) =
      (Nat.choose m j : ℚ) * (Nat.choose (m-j) k : ℚ) := by exact_mod_cast h
  rw [hcast]
  have hs : d-(j+k)=d-j-k := by omega
  rw [hs]
  rw [Ring.choose_natCast]
  ring
private theorem choose_add_rectangular (l k d : ℕ) (hk : k ≤ d) : (Nat.choose (l+k) k : ℚ) = ∑ j ∈ Finset.range (d+1), (Nat.choose l j : ℚ) * (Nat.choose k j : ℚ) := by
  have h := Nat.add_choose_eq l k k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hs : (Nat.choose (l+k) k : ℚ) =
      ∑ j ∈ Finset.range (k+1), (Nat.choose l j : ℚ) * (Nat.choose k j : ℚ) := by
    rw [h]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.choose_symm (by simpa using hj)]
  rw [hs]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))
  intro j hj hjk
  have hlt : k < j := by simp only [Finset.mem_range] at hjk; omega
  simp [Nat.choose_eq_zero_of_lt hlt]
private theorem inverse_convolution_identity (m l d : ℕ) (hm : d ≤ m) : inverseConvolution m l d = (Nat.choose l d : ℚ) * (Nat.choose (m+d) d : ℚ) := by
  unfold inverseConvolution
  have hexpand : (∑ k ∈ Finset.range (d+1), (Nat.choose m k : ℚ) *
      Ring.choose ((l : ℚ)-m) (d-k) * (Nat.choose (l+k) k : ℚ)) =
      ∑ k ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
        (Nat.choose l j : ℚ) * ((Nat.choose m k : ℚ) * (Nat.choose k j : ℚ) *
          Ring.choose ((l : ℚ)-m) (d-k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [choose_add_rectangular l k d (by simpa using hk), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand, Finset.sum_comm]
  calc
    (∑ j ∈ Finset.range (d+1), ∑ k ∈ Finset.range (d+1),
        (Nat.choose l j : ℚ) * ((Nat.choose m k : ℚ) * (Nat.choose k j : ℚ) *
          Ring.choose ((l : ℚ)-m) (d-k))) =
      ∑ j ∈ Finset.range (d+1), (Nat.choose l j : ℚ) * (Nat.choose m j : ℚ) *
        Ring.choose ((l : ℚ)-j) (d-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j ≤ d := by simpa using hj
      rw [← Finset.mul_sum, binomial_weighted_convolution m d j _ hjd hm]
      have hcast : ((l : ℚ)-m) + (m-j : ℕ) = (l : ℚ)-j := by
        rw [Nat.cast_sub (hjd.trans hm)]
        ring
      rw [hcast]
      ring
    _ = ∑ j ∈ Finset.range (d+1), (Nat.choose l d : ℚ) *
        (Nat.choose m j : ℚ) * (Nat.choose d j : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j ≤ d := by simpa using hj
      have h := Ring.choose_smul_choose (l : ℚ) hjd
      simp only [nsmul_eq_mul, Ring.choose_natCast] at h
      calc
        (Nat.choose l j : ℚ) * (Nat.choose m j : ℚ) * Ring.choose ((l : ℚ)-j) (d-j) =
          (Nat.choose m j : ℚ) * ((Nat.choose l j : ℚ) * Ring.choose ((l : ℚ)-j) (d-j)) := by ring
        _ = _ := by rw [← h]; ring
    _ = _ := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← choose_add_rectangular m d d (le_refl d)]
private lemma inverse_convolution_real (m l d : ℕ) (hm : d ≤ m) : (∑ k ∈ Finset.range (d+1), (Nat.choose m k : ℝ) * Ring.choose ((l:ℝ)-m) (d-k) * (Nat.choose (l+k) k : ℝ)) = (Nat.choose l d : ℝ) * (Nat.choose (m+d) d : ℝ) := by
  have h := congrArg (algebraMap ℚ ℝ) (inverse_convolution_identity m l d hm)
  simpa only [inverseConvolution, map_sum, map_mul, Ring.map_choose, map_sub, map_natCast] using h
private lemma negative_binomial (b r : ℕ) (hb : 0 < b) : Ring.choose (-(b:ℝ)) r = (-1:ℝ)^r * (Nat.choose (b+r-1) r : ℝ) := by
  rw [Ring.choose_neg]
  have he : (b:ℝ)+(r:ℝ)-1=(b+r-1 : ℕ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [he, Ring.choose_natCast]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
private lemma inverse_urn_term (m l d k : ℕ) (hl : l < m) (hk : k ≤ d) : (Nat.choose d k : ℝ) * (Nat.ascFactorial (l+1) k : ℝ) * (Nat.ascFactorial (m-l) (d-k) : ℝ) * ((-1:ℝ)^(d-k) * (Nat.choose m k : ℝ)) = (Nat.factorial d : ℝ) * ((Nat.choose m k : ℝ) * Ring.choose ((l:ℝ)-m) (d-k) * (Nat.choose (l+k) k : ℝ)) := by
  have hs : (l:ℝ)-m = -((m-l:ℕ):ℝ) := by rw [Nat.cast_sub (by omega)]; ring
  rw [hs, negative_binomial _ _ (by omega), Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.ascFactorial_eq_factorial_mul_choose']
  push_cast
  have hf : (Nat.choose d k : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial (d-k) : ℝ) =
      (Nat.factorial d : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  calc
    _ = ((Nat.choose d k : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial (d-k) : ℝ)) *
      ((Nat.choose m k : ℝ) * ((-1:ℝ)^(d-k) * (Nat.choose (m-l+(d-k)-1) (d-k) : ℝ)) *
        (Nat.choose (l+k) k : ℝ)) := by ring
    _ = _ := by rw [hf]
private noncomputable def otherMass {n : ℕ} (l : Fin n → ℕ) (i : Fin n) : ℕ :=
  (∑ j : Fin n, l j) + n - (l i+1)
private noncomputable def urnSum {n : ℕ} (l : Fin n → ℕ) (i : Fin n) (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w : (Fin k → Fin n), factorialWord l w * f ((occupation w).count i)
private lemma binomial_urn_step (a b d : ℕ) (f : ℕ → ℝ) : binomialUrn a b (d+1) f = binomialUrn a b d (fun k => ((a+k : ℕ):ℝ) * f (k+1) + ((b+d-k : ℕ):ℝ) * f k) := by
  unfold binomialUrn
  have hs := Finset.sum_choose_succ_mul
    (fun k r => (Nat.ascFactorial a k : ℝ) * (Nat.ascFactorial b r : ℝ) * f k) d
  simp only [mul_assoc] at hs ⊢
  rw [hs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by simpa using hk
  have he : b+d-k=b+(d-k) := by omega
  have hsub : d+1-k=(d-k)+1 := by omega
  rw [hsub]
  simp only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add, he]
  ring
private lemma other_mass_add {n : ℕ} (l : Fin n → ℕ) (i : Fin n) : otherMass l i + l i + 1 = (∑ j : Fin n, l j) + n := by
  have hle : l i ≤ ∑ j : Fin n, l j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hn : 0 < n := by have := i.isLt; omega
  unfold otherMass
  omega
lemma count_cons {n k : ℕ} (i j : Fin n) (w : (Fin k → Fin n)) : (occupation (Fin.cons i w)).count j = (if j=i then 1 else 0) + (occupation w).count j := by
  classical
  by_cases hij : i=j
  · subst j
    simp [occupation, List.ofFn_succ, Nat.add_comm]
  · simp [occupation, List.ofFn_succ, hij, Ne.symm hij]
private lemma factorial_word_cons {n k : ℕ} (l : Fin n → ℕ) (i : Fin n) (w : (Fin k → Fin n)) : factorialWord l (Fin.cons i w) = ((l i + (occupation w).count i + 1 : ℕ) : ℝ) * factorialWord l w := by
  classical
  have ht (j : Fin n) :
      (Nat.factorial (l j + (occupation (Fin.cons i w)).count j) : ℝ) =
        (if j=i then ((l i+(occupation w).count i+1 : ℕ):ℝ) else 1) *
          (Nat.factorial (l j + (occupation w).count j) : ℝ) := by
    by_cases hj : j=i
    · subst j
      simp only [count_cons, if_true]
      rw [show l i + (1+(occupation w).count i) = (l i+(occupation w).count i)+1 by omega, Nat.factorial_succ]
      push_cast
      rfl
    · simp only [count_cons, hj, if_false, zero_add, one_mul]
  unfold factorialWord
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
noncomputable def wordDegree {n m : ℕ} (w : (Fin m → Fin n)) : {a : Fin n → Fin (m+1) // ∑ i, (a i : ℕ) = m} := by
  refine ⟨fun i => ⟨(occupation w).count i, ?_⟩, ?_⟩
  · have h := Multiset.count_le_card i
      (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation w)
    rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation_card] at h
    exact Nat.lt_succ_of_le h
  · simpa [occupation] using Multiset.sum_count_eq_card
      (m := D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation w)
      (fun _ _ => Finset.mem_univ _)
private lemma sum_count {n k : ℕ} (w : (Fin k → Fin n)) : ∑ j : Fin n, (occupation w).count j = k := by
  simpa only [wordDegree] using (wordDegree w).property
theorem sum_word_succ {A : Type*} [AddCommMonoid A] {n k : ℕ} (f : (Fin (k+1) → Fin n) → A) : (∑ w, f w) = ∑ i : Fin n, ∑ w : (Fin k → Fin n), f (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Fin n)).sum_comp f,
    Fintype.sum_prod_type]
  rfl
private lemma urn_step {n d : ℕ} (l : Fin n → ℕ) (i : Fin n) (f : ℕ → ℝ) : urnSum l i (d+1) f = urnSum l i d (fun k => ((l i + k + 1 : ℕ) : ℝ) * f (k+1) + ((∑ j : Fin n, l j : ℕ) + d + n - (l i+k+1) : ℝ) * f k) := by
  classical
  unfold urnSum
  rw [sum_word_succ, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [factorial_word_cons, count_cons]
  have hs : ∑ j : Fin n, ((l j + (occupation w).count j + 1 : ℕ) : ℝ) =
      ((∑ j : Fin n, l j : ℕ) + d + n : ℝ) := by
    push_cast
    simp only [Finset.sum_add_distrib, ← Nat.cast_sum, sum_count, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have ht (j : Fin n) :
      ((l j+(occupation w).count j+1:ℕ):ℝ) * factorialWord l w * f ((if j=i then 1 else 0)+(occupation w).count i) =
      factorialWord l w * (((l j+(occupation w).count j+1:ℕ):ℝ) * f ((occupation w).count i) +
        if j=i then ((l i+(occupation w).count i+1:ℕ):ℝ) * (f ((occupation w).count i+1)-f ((occupation w).count i)) else 0) := by
    by_cases hj : j=i
    · subst j
      simp only [if_true]
      rw [Nat.add_comm 1 ((occupation w).count i)]
      ring
    · simp only [hj, if_false, zero_add, add_zero]
      ring
  simp only [eq_comm (a:=i)]
  simp_rw [ht]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hs]
  push_cast
  ring
private lemma urn_closed_form {n : ℕ} (l : Fin n → ℕ) (i : Fin n) (d : ℕ) (f : ℕ → ℝ) : urnSum l i d f = (∏ j : Fin n, (Nat.factorial (l j) : ℝ)) * binomialUrn (l i+1) (otherMass l i) d f := by
  induction d generalizing f with
  | zero =>
    simp [urnSum, factorialWord, occupation, binomialUrn]
  | succ d ih =>
    rw [urn_step, ih, binomial_urn_step]
    congr 1
    unfold binomialUrn
    apply Finset.sum_congr rfl
    intro k hk
    have hkd : k ≤ d := by simpa using hk
    have hm := other_mass_add l i
    have hmc : (otherMass l i : ℝ) + (l i : ℝ) + 1 = (∑ j : Fin n, l j : ℕ) + (n:ℝ) := by
      exact_mod_cast hm
    push_cast at hmc
    dsimp only
    have hc : ((otherMass l i+d-k : ℕ):ℝ) =
        (∑ j : Fin n, l j : ℕ) + (d:ℝ) + (n:ℝ) - ((l i+k+1:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith [hmc]
    simp only [Nat.cast_add, Nat.cast_one] at hc
    rw [hc]
    simp only [show l i+1+k=l i+k+1 by omega]
private lemma inverse_word_sum {n d : ℕ} (hn : 2 ≤ n) (l : Fin n → ℕ) (hl : ∑ j : Fin n, l j = d) (i : Fin n) : urnSum l i d (fun k => (-1:ℝ)^(d-k) * (Nat.choose (n-1+d) k : ℝ)) = (∏ j : Fin n, (Nat.factorial (l j) : ℝ)) * (Nat.factorial d : ℝ) * ((Nat.choose (l i) d : ℝ) * (Nat.choose (n-1+d+d) d : ℝ)) := by
  have hli : l i ≤ d := by
    rw [← hl]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hother : otherMass l i = n-1+d-l i := by
    unfold otherMass
    rw [hl]
    omega
  rw [urn_closed_form, hother]
  have hb : binomialUrn (l i+1) (n-1+d-l i) d
      (fun k => (-1:ℝ)^(d-k) * (Nat.choose (n-1+d) k : ℝ)) =
      (Nat.factorial d : ℝ) * ((Nat.choose (l i) d : ℝ) * (Nat.choose (n-1+d+d) d : ℝ)) := by
    unfold binomialUrn
    calc
      _ = ∑ k ∈ Finset.range (d+1), (Nat.factorial d : ℝ) * ((Nat.choose (n-1+d) k : ℝ) *
          Ring.choose ((l i:ℝ)-(n-1+d:ℕ)) (d-k) * (Nat.choose (l i+k) k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact inverse_urn_term (n-1+d) (l i) d k (by omega) (by simpa using hk)
      _ = _ := by rw [← Finset.mul_sum, inverse_convolution_real _ _ _ (by omega)]
  rw [hb]
  ring
private noncomputable def pureEmbedding (n d : ℕ) : Matrix ((Fin d → Fin n)) (Fin n) ℝ :=
  fun w i => if w=(fun _ => i) then 1 else 0
private noncomputable def realGram (n d : ℕ) : Matrix ((Fin d → Fin n)) ((Fin d → Fin n)) ℝ :=
  fun u v => (∏ i : Fin n, (Nat.factorial ((occupation u).count i + (occupation v).count i) : ℝ)) /
    (Nat.factorial (2*d) : ℝ)
private noncomputable def representers (n d : ℕ) : Matrix ((Fin d → Fin n)) (Fin n) ℝ :=
  fun w i =>
    (Nat.choose (n-1+d) d : ℝ) / (Nat.choose (n-1+2*d) (2*d) : ℝ) *
      (-1 : ℝ)^(d-(occupation w).count i) * (Nat.choose (n-1+d) ((occupation w).count i) : ℝ)
private theorem representer_certificate {n d : ℕ} (hn : 2 ≤ n) : realGram n d * representers n d = pureEmbedding n d := by
  classical
  ext u i
  have hsum := inverse_word_sum hn ((occupation u).count) (sum_count u) i
  have hfactor : (realGram n d * representers n d) u i =
      ((Nat.choose (n-1+d) d : ℝ)/(Nat.choose (n-1+2*d) (2*d) : ℝ)/(Nat.factorial (2*d) : ℝ)) *
        urnSum ((occupation u).count) i d (fun k => (-1:ℝ)^(d-k) * (Nat.choose (n-1+d) k : ℝ)) := by
    simp only [Matrix.mul_apply, realGram, representers, urnSum, factorialWord,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  rw [hfactor, hsum]
  by_cases hc : (occupation u).count i=d
  · have hu := word_constant_of_full_count u i hc
    subst u
    simp only [count_constant_all, if_true, Nat.choose_self, Nat.cast_one, one_mul,
      pureEmbedding, if_true]
    have hp : (∏ j : Fin n, (Nat.factorial (if j=i then d else 0) : ℝ)) =
        (Nat.factorial d : ℝ) := by
      simp only [apply_ite, Nat.factorial_zero, Nat.cast_one]
      simp
    rw [hp]
    have hnrm := normalized_pure_value n d
    nlinarith [hnrm]
  · have hli : (occupation u).count i ≤ d := by
      have ht := Finset.single_le_sum (f:=(occupation u).count) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa only [sum_count] using ht
    have hlt : (occupation u).count i < d := by omega
    have hu : u ≠ (fun _ => i) := by
      intro he
      apply hc
      rw [he, count_constant]
    simp [Nat.choose_eq_zero_of_lt hlt, pureEmbedding, hu]
noncomputable def wordEval {n k : ℕ} {A : Type*} [Monoid A] (X : Fin n → A) (w : (Fin k → Fin n)) : A := (List.ofFn (fun j => X (w j))).prod
noncomputable def matrixForm (D : Matrix I I ℂ) (v : I → H) : ℂ :=
  ∑ i : I, inner ℂ (v i) ((D • v) i)
noncomputable def factorialMoment {n B : ℕ} (g : Fin n → ℕ) (a b : Fin n → Fin (B+1)) : ℝ :=
  ∏ i : Fin n, (Nat.factorial (a i + b i + g i) : ℝ)
omit [CompleteSpace H] in
private theorem matrix_action_mul (D E : Matrix I I ℂ) (v : I → H) (i : I) : ((D * E) • v) i = (D • (fun j => (E • v) j)) i := by
  simp only [Matrix.Module.smul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]
omit [CompleteSpace H] in
private theorem hilbert_gram_action (B : Matrix I I ℂ) (v : I → H) (i : I) : ((Bᴴ * B) • v) i = ∑ k : I, star (B k i) • ((B • v) k) := by
  simp only [Matrix.Module.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]
omit [CompleteSpace H] in
private theorem hilbert_gram_identity (B : Matrix I I ℂ) (v : I → H) : matrixForm (Bᴴ * B) v = ∑ k : I, inner ℂ (((B • v) k)) (((B • v) k)) := by
  simp only [matrixForm, Matrix.Module.smul_apply, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, mul_assoc]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext k
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [starRingEnd_apply]
  ring
omit [CompleteSpace H] in
theorem positive_form_zero_rows (D : Matrix I I ℂ) (hD : D.PosSemidef) (v : I → H) (hh : matrixForm D v = 0) : ∀ i, (D • v) i = 0 := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  rw [hB, hilbert_gram_identity] at hh
  have hr : ∑ k : I, ‖((B • v) k)‖ ^ 2 = 0 := by
    have h := congrArg Complex.re hh
    simpa [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using h
  have hz : ∀ k, ((B • v) k) = 0 := by
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset I)) (f := fun k => ‖((B • v) k)‖^2)
      (fun k _ => sq_nonneg _)).mp hr
    intro k
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hsum k (Finset.mem_univ k)))
  intro i
  rw [hB, hilbert_gram_action]
  simp [hz]
omit [CompleteSpace H] in
theorem positive_definite_form_zero_vectors (D : Matrix I I ℂ) (hD : D.PosDef) (v : I → H) (hh : matrixForm D v = 0) : ∀ i, v i = 0 := by
  classical
  have hrows := positive_form_zero_rows D hD.posSemidef v hh
  have hinv : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)
  intro i
  have ha := matrix_action_mul D⁻¹ D v i
  rw [hinv] at ha
  simp only [hrows] at ha
  simpa [Matrix.Module.smul_apply, Matrix.one_apply] using ha
noncomputable def factorialFeature {n B : ℕ} (g : Fin n → ℕ) (a k : Fin n → Fin (B+1)) : ℝ :=
  ∏ i : Fin n, (Nat.factorial (a i + g i) : ℝ) * (Nat.choose (a i) (k i) : ℝ)
theorem degree_feature_diagonal {n B d : ℕ} (g : Fin n → ℕ) (a b : {a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d}) (hne : a ≠ b) : factorialFeature g b.val a.val = 0 := by
  classical
  have hsome : ∃ i, (b.val i : ℕ) < a.val i := by
    by_contra hx
    push Not at hx
    have hle : ∀ i, (a.val i : ℕ) ≤ b.val i := fun i => hx i
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)), (a.val i : ℕ) < b.val i := by
      by_contra hn
      push Not at hn
      apply hne
      apply Subtype.ext
      funext i
      apply Fin.ext
      apply le_antisymm (hle i)
      exact hn i (Finset.mem_univ i)
    have hs := Finset.sum_lt_sum (fun i _ => hle i) hlt
    rw [a.property, b.property] at hs
    exact lt_irrefl d hs
  obtain ⟨i, hi⟩ := hsome
  unfold factorialFeature
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Nat.choose_eq_zero_of_lt hi]
noncomputable def factorialWeight {n B : ℕ} (g : Fin n → ℕ) (k : Fin n → Fin (B+1)) : ℝ :=
  ∏ i : Fin n, (Nat.factorial (k i) : ℝ) / (Nat.factorial (g i + k i) : ℝ)
theorem factorial_feature_self_pos {n B : ℕ} (g : Fin n → ℕ) (a : Fin n → Fin (B+1)) : 0 < factorialFeature g a a := by
  unfold factorialFeature
  apply Finset.prod_pos
  intro i hi
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  positivity
private theorem shifted_factorial_gram (a b g : ℕ) : (Nat.factorial (a+b+g) : ℝ) = ∑ k ∈ Finset.range (a+1), (Nat.factorial (a+g) : ℝ) * (Nat.factorial (b+g) : ℝ) * (Nat.choose a k : ℝ) * (Nat.choose b k : ℝ) * (Nat.factorial k : ℝ) / (Nat.factorial (g+k) : ℝ) := by
  have hv := Nat.add_choose_eq b (a+g) a
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hc : (Nat.choose (b+(a+g)) a : ℝ) * (Nat.factorial a : ℝ) *
      (Nat.factorial (b+g) : ℝ) = (Nat.factorial (a+b+g) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := b+(a+g)) (k := a) (by omega)
    have he : b+(a+g)-a=b+g := by omega
    rw [he] at h
    have ht : b+(a+g)=a+b+g := by omega
    rw [ht] at h
    norm_cast
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  rw [← hc, hv]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hka : k ≤ a := by simpa using hk
  have hfac := Nat.choose_mul_factorial_mul_factorial hka
  have hfac2 := Nat.choose_mul_factorial_mul_factorial (n:=a+g) (k:=a-k) (by omega)
  have he : a+g-(a-k)=g+k := by omega
  rw [he] at hfac2
  have h1 : (Nat.choose a k : ℝ) * (Nat.factorial k : ℝ) *
      (Nat.factorial (a-k) : ℝ) = (Nat.factorial a : ℝ) := by exact_mod_cast hfac
  have h2 : (Nat.choose (a+g) (a-k) : ℝ) * (Nat.factorial (a-k) : ℝ) *
      (Nat.factorial (g+k) : ℝ) = (Nat.factorial (a+g) : ℝ) := by exact_mod_cast hfac2
  have hn : (Nat.factorial (g+k) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (g+k)
  apply (eq_div_iff hn).mpr
  rw [← h1, ← h2]
  ring
private theorem shifted_factorial_gram_bound (a b g B : ℕ) (ha : a ≤ B) : (Nat.factorial (a+b+g) : ℝ) = ∑ k ∈ Finset.range (B+1), (Nat.factorial (a+g) : ℝ) * (Nat.factorial (b+g) : ℝ) * (Nat.choose a k : ℝ) * (Nat.choose b k : ℝ) * (Nat.factorial k : ℝ) / (Nat.factorial (g+k) : ℝ) := by
  rw [shifted_factorial_gram]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ ha))
  intro k hk hka
  have hlt : a < k := by simp only [Finset.mem_range] at hka; omega
  simp [Nat.choose_eq_zero_of_lt hlt]
theorem factorial_moment_gram {n B : ℕ} (g : Fin n → ℕ) (a b : Fin n → Fin (B+1)) : factorialMoment g a b = ∑ k : Fin n → Fin (B+1), factorialWeight g k * factorialFeature g a k * factorialFeature g b k := by
  unfold factorialMoment factorialWeight factorialFeature
  calc
    (∏ i : Fin n, (Nat.factorial (a i + b i + g i) : ℝ)) =
        ∏ i : Fin n, ∑ k : Fin (B+1),
          (Nat.factorial (a i+g i) : ℝ) * (Nat.factorial (b i+g i) : ℝ) *
            (Nat.choose (a i) k : ℝ) * (Nat.choose (b i) k : ℝ) *
              (Nat.factorial k : ℝ) / (Nat.factorial (g i+k) : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa only [← Fin.sum_univ_eq_sum_range] using
        shifted_factorial_gram_bound (a i) (b i) (g i) B (Nat.le_of_lt_succ (a i).isLt)
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      ring
theorem factorial_weight_pos {n B : ℕ} (g : Fin n → ℕ) (k : Fin n → Fin (B+1)) : 0 < factorialWeight g k := by
  unfold factorialWeight
  apply Finset.prod_pos
  intro i hi
  positivity
theorem count_append {n a b : ℕ} (u : (Fin a → Fin n)) (v : (Fin b → Fin n)) (i : Fin n) : (occupation (Fin.append u v)).count i = (occupation u).count i + (occupation v).count i := by
  simp only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation_append,
    Multiset.count_add]
private theorem reverse_word_list {n k : ℕ} (w : (Fin k → Fin n)) : List.ofFn ((Equiv.piCongrLeft' (fun _ : Fin k => Fin n) Fin.revPerm) w) = (List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn, Equiv.piCongrLeft'_apply, Fin.revPerm_symm,
      Fin.revPerm_apply, List.getElem_reverse]
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega
theorem count_reverse {n k : ℕ} (w : (Fin k → Fin n)) (i : Fin n) : (occupation ((Equiv.piCongrLeft' (fun _ : Fin k => Fin n) Fin.revPerm) w)).count i = (occupation w).count i := by
  simp only [occupation, reverse_word_list, Multiset.coe_count]
  simp
def gramWordEquiv (n d : ℕ) : ((Fin d → Fin n) × (Fin d → Fin n)) ≃ (Fin (d+d) → Fin n) :=
  (Equiv.prodCongr ((Equiv.piCongrLeft' (fun _ : Fin d => Fin n) Fin.revPerm)) (Equiv.refl ((Fin d → Fin n)))).trans (Fin.appendEquiv d d)
theorem word_eval_append {n a b : ℕ} {A : Type*} [Monoid A] (X : Fin n → A) (u : (Fin a → Fin n)) (v : (Fin b → Fin n)) : wordEval X (Fin.append u v) = wordEval X u * wordEval X v := by
  unfold wordEval
  have hl : (fun j => X ((Fin.append u v) j)) = Fin.append (fun j => X (u j)) (fun j => X (v j)) := by
    funext j; exact (Fin.addCases (fun i => by simp) (fun i => by simp) j)
  rw [hl, List.ofFn_fin_append, List.prod_append]
theorem word_eval_reverse {n k : ℕ} {A : Type*} [Monoid A] [StarMul A] (X : Fin n → A) (hs : ∀ i, IsSelfAdjoint (X i)) (w : (Fin k → Fin n)) : wordEval X ((Equiv.piCongrLeft' (fun _ : Fin k => Fin n) Fin.revPerm) w) = star (wordEval X w) := by
  have hlist (l : List (Fin n)) : (l.reverse.map X).prod = star ((l.map X).prod) := by
    have hh := unop_map_list_prod (starMulEquiv : A ≃* Aᵐᵒᵖ) (l.map X)
    change star ((l.map X).prod) = _ at hh
    rw [List.map_map] at hh
    have he : (MulOpposite.unop ∘ ⇑(starMulEquiv : A ≃* Aᵐᵒᵖ)) ∘ X = X := by
      funext a
      exact (hs a).star_eq
    rw [he] at hh
    simpa only [List.map_reverse] using hh.symm
  have he : (List.ofFn (fun j => X (((Equiv.piCongrLeft' (fun _ : Fin k => Fin n) Fin.revPerm) w) j))) = (List.ofFn ((Equiv.piCongrLeft' (fun _ : Fin k => Fin n) Fin.revPerm) w)).map X := by
    simp only [List.map_ofFn]
    rfl
  unfold wordEval
  rw [he, reverse_word_list, hlist]
  congr 1
  simp only [List.map_ofFn]
  rfl
private theorem factorial_moment_posDef {n B d : ℕ} (g : Fin n → ℕ) : Matrix.PosDef (fun a b : {a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d} => factorialMoment g a.val b.val) := by
  classical
  let F : Matrix (Fin n → Fin (B+1)) ({a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d}) ℝ :=
    fun k a => factorialFeature g a.val k
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    funext a
    have hh := congrFun hxy a.val
    have ha : factorialFeature g a.val a.val ≠ 0 := (factorial_feature_self_pos g a.val).ne'
    have hrow (z : {a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d} → ℝ) :
        F.mulVec z a.val = factorialFeature g a.val a.val * z a := by
      change (∑ b : {a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d}, factorialFeature g b.val a.val * z b) = _
      apply Finset.sum_eq_single a
      · intro b hb hba
        rw [degree_feature_diagonal g a b (Ne.symm hba), zero_mul]
      · intro hn
        exact (hn (Finset.mem_univ a)).elim
    rw [hrow x, hrow y] at hh
    exact mul_left_cancel₀ ha hh
  have hdiag : (Matrix.diagonal (fun k : Fin n → Fin (B+1) => factorialWeight g k)).PosDef :=
    Matrix.PosDef.diagonal (fun k => factorial_weight_pos g k)
  have hp := hdiag.conjTranspose_mul_mul_same hinj
  have hm : (fun a b : {a : Fin n → Fin (B+1) // ∑ i, (a i : ℕ) = d} => factorialMoment g a.val b.val) =
      Fᴴ * (Matrix.diagonal (fun k : Fin n → Fin (B+1) => factorialWeight g k)) * F := by
    ext a b
    rw [factorial_moment_gram]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    star_trivial]
    dsimp only [F]
    simp only [mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hm]
  exact hp
private lemma real_gram_posSemidef (n d : ℕ) : (realGram n d).PosSemidef := by
  have hp := (factorial_moment_posDef (B:=d) (d:=d) (fun _ : Fin n => 0)).posSemidef.submatrix
    (fun w : (Fin d → Fin n) => wordDegree w)
  have hc : 0 ≤ (1/(Nat.factorial (2*d) : ℝ)) := by positivity
  convert hp.smul hc using 1
  ext u v
  simp only [realGram, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
    factorialMoment, wordDegree, Nat.add_zero]
  ring
private lemma real_to_complex_psd {I : Type*} [Fintype I] (A : Matrix I I ℝ) (hA : A.PosSemidef) : (A.map (algebraMap ℝ ℂ)).PosSemidef := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hc := Matrix.posSemidef_conjTranspose_mul_self (B.map (algebraMap ℝ ℂ))
  convert hc using 1
  rw [hB]
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]
private lemma constant_word_injective {n d : ℕ} (hd : 0 < d) : Function.Injective (fun i : Fin n => (fun _ : Fin d => i)) := by
  intro i j hij
  exact congrFun hij ⟨0,hd⟩
def pure {n d : ℕ} (w : (Fin d → Fin n)) : Prop := ∃ i : Fin n, ∀ j, w j = i
private lemma embedding_product {n d : ℕ} (hd : 0 < d) : pureEmbedding n d * (pureEmbedding n d)ᵀ = Matrix.diagonal (fun w : (Fin d → Fin n) => if pure w then (1:ℝ) else 0) := by
  classical
  ext u v
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pureEmbedding, Matrix.diagonal_apply]
  by_cases hu : pure u
  · obtain ⟨i,hi⟩ := hu
    have hui : u=(fun _ => i) := funext hi
    subst u
    have he (j : Fin n) : ((fun _ : Fin d => i)=(fun _ => j)) ↔ i=j :=
      ⟨fun h => constant_word_injective hd h,fun h => by rw [h]⟩
    simp only [he, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hp : pure (fun _ : Fin d => i) := ⟨i,fun _ => rfl⟩
    simp only [hp, if_true]
    simp only [eq_comm]
  · have hn (i : Fin n) : u≠(fun _=>i) := by
      intro he
      apply hu
      rw [he]
      exact ⟨i,fun _=>rfl⟩
    simp only [hn, if_false, zero_mul, Finset.sum_const_zero, hu]
    by_cases huv : u=v <;> simp [huv]
noncomputable def gram (n d : ℕ) : Matrix ((Fin d → Fin n)) ((Fin d → Fin n)) ℂ :=
  fun u v => (∏ i : Fin n, (Nat.factorial ((occupation u).count i + (occupation v).count i) : ℂ)) /
    (Nat.factorial (2*d) : ℂ)
noncomputable def mu (n d : ℕ) : ℝ :=
  if n = 1 then 1 else
  if Odd d then
    (Nat.choose (n - 1 + 2 * d) (2 * d) : ℝ) /
      ((Nat.choose (n - 1 + d) d : ℝ) * ((Nat.choose (n - 1 + d) d : ℝ) + 1))
  else
    (Nat.choose (n - 1 + 2 * d) (2 * d) : ℝ) /
      ((Nat.choose (n - 1 + d) d : ℝ) * ((Nat.choose (n - 1 + d) d : ℝ) + n - 1))
noncomputable def pureProjection (n d : ℕ) : Matrix ((Fin d → Fin n)) ((Fin d → Fin n)) ℂ :=
  by
    classical
    exact Matrix.diagonal (fun w => if pure w then 1 else 0)
noncomputable def sharpGram (n d : ℕ) : Matrix ((Fin d → Fin n)) ((Fin d → Fin n)) ℂ :=
  gram n d - (mu n d : ℂ) • pureProjection n d
private lemma sharp_posSemidef_of_representers {n d : ℕ} (hd : 0 < d) (hQR : realGram n d * representers n d = pureEmbedding n d) (hc : 0 ≤ mu n d) (hB : (1 - mu n d • ((pureEmbedding n d)ᵀ * representers n d)).PosSemidef) : (sharpGram n d).PosSemidef := by
  have hr := sharp_from_representers (realGram n d) (representers n d) (pureEmbedding n d)
    (mu n d) (real_gram_posSemidef n d) hQR hc hB
  rw [embedding_product hd] at hr
  have h := real_to_complex_psd _ hr
  convert h using 1
  ext u v
  simp only [sharpGram, gram, realGram, pureProjection, Matrix.map_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  push_cast
  split_ifs <;> simp
noncomputable def coefficient {n k : ℕ} (w : (Fin k → Fin n)) : ℂ :=
  (∏ i : Fin n, (Nat.factorial ((occupation w).count i) : ℂ)) / (Nat.factorial k : ℂ)
noncomputable def nchs {A : Type*} [Ring A] [Algebra ℂ A] (n k : ℕ) (X : Fin n → A) : A :=
  ∑ w : (Fin k → Fin n), coefficient w • wordEval X w
noncomputable def residual {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n d : ℕ) (X : Fin n → H →L[ℂ] H) : H →L[ℂ] H :=
  nchs n (2 * d) X - (mu n d : ℂ) • ∑ i : Fin n, X i ^ (2 * d)
private theorem word_gram_identity {n d : ℕ} {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] (X : Fin n → A) (hs : ∀ i, IsSelfAdjoint (X i)) : nchs n (d+d) X = ∑ u : (Fin d → Fin n), ∑ v : (Fin d → Fin n), gram n d u v • (star (wordEval X u) * wordEval X v) := by
  classical
  unfold nchs
  rw [← (gramWordEquiv n d).sum_comp (fun w => coefficient w • wordEval X w),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change coefficient (Fin.append ((Equiv.piCongrLeft' (fun _ : Fin d => Fin n) Fin.revPerm) u) v) •
    wordEval X (Fin.append ((Equiv.piCongrLeft' (fun _ : Fin d => Fin n) Fin.revPerm) u) v) = _
  rw [word_eval_append, word_eval_reverse X hs]
  congr 1
  simp only [coefficient, count_append, count_reverse, gram, show d+d=2*d by omega]
private lemma nchs_inner_gram {n d : ℕ} (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) : inner ℂ h (nchs n (2*d) X h) = matrixForm (gram n d) (fun w : (Fin d → Fin n) => wordEval X w h) := by
  rw [show 2*d=d+d by omega, word_gram_identity X hs]
  simp only [sum_apply, smul_apply,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    inner_sum, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    matrixForm, Matrix.Module.smul_apply]
private lemma sum_pure {n d : ℕ} (hd : 0 < d) {A : Type*} [AddCommMonoid A] (f : (Fin d → Fin n) → A) : (∑ w : (Fin d → Fin n) with pure w, f w) = ∑ i : Fin n, f (fun _ => i) := by
  classical
  have hinj : Function.Injective (fun i : Fin n => (fun _ : Fin d => i)) := by
    intro i j hij
    exact congrFun hij ⟨0,hd⟩
  have heq : (Finset.univ.filter (pure (n:=n) (d:=d))) =
      Finset.univ.image (fun i : Fin n => (fun _ : Fin d => i)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i, (funext hi).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i, fun _ => rfl⟩
  rw [heq, Finset.sum_image]
  intro i hi j hj he
  exact hinj he
omit [CompleteSpace H] in
private lemma pure_form {n d : ℕ} (hd : 0 < d) (X : Fin n → H →L[ℂ] H) (h : H) : matrixForm (pureProjection n d) (fun w : (Fin d → Fin n) => wordEval X w h) = ∑ i : Fin n, inner ℂ ((X i ^ d) h) ((X i ^ d) h) := by
  classical
  have ha (w : (Fin d → Fin n)) :
      ((pureProjection n d) • (fun v : (Fin d → Fin n) => wordEval X v h)) w =
        (if pure w then (1:ℂ) else 0) • wordEval X w h := by
    simp only [Matrix.Module.smul_apply]
    rw [Finset.sum_eq_single w]
    · simp [pureProjection, Matrix.diagonal_apply]
    · intro v hv hvw
      simp [pureProjection, Matrix.diagonal_apply, Ne.symm hvw]
    · intro hn
      exact (hn (Finset.mem_univ w)).elim
  unfold matrixForm
  simp only [ha, inner_smul_right, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rw [sum_pure hd]
  simp [wordEval, List.ofFn_const]
omit [CompleteSpace H] in
private lemma form_sub_smul {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (c : ℂ) (v : I → H) : matrixForm (A - c • B) v = matrixForm A v - c * matrixForm B v := by
  simp only [matrixForm, Matrix.Module.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum,
    inner_sub_right, inner_sum, inner_smul_right, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
lemma residual_inner_gram {n d : ℕ} (hd : 0 < d) (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) (h : H) : inner ℂ h (residual n d X h) = matrixForm (sharpGram n d) (fun w : (Fin d → Fin n) => wordEval X w h) := by
  rw [sharpGram, form_sub_smul, ← nchs_inner_gram X hs h, pure_form hd X h]
  unfold residual
  simp only [ContinuousLinearMap.sub_apply, sum_apply,
    smul_apply, inner_sub_right, inner_smul_right, inner_sum,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hstar : star (X i ^ d) = X i ^ d := (hs i).pow d |>.star_eq
  calc
    _ = (mu n d : ℂ) * inner ℂ h ((star (X i ^ d) * X i ^ d) h) := by
      rw [hstar, ← pow_add, show d+d=2*d by omega]
    _ = _ := by simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
private noncomputable def degreeCount (n d : ℕ) : ℝ := Nat.choose (n-1+d) d
private noncomputable def doubleDegreeCount (n d : ℕ) : ℝ := Nat.choose (n-1+2*d) (2*d)
private noncomputable def pureDiagonal (n d : ℕ) : ℝ := (degreeCount n d)^2 / doubleDegreeCount n d
private noncomputable def pureOffDiagonal (n d : ℕ) : ℝ := (-1:ℝ)^d * degreeCount n d / doubleDegreeCount n d
private lemma transpose_embedding_action {n d : ℕ} (R : Matrix ((Fin d → Fin n)) (Fin n) ℝ) (i j : Fin n) : ((pureEmbedding n d)ᵀ * R) i j = R (fun _=>i) j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, pureEmbedding, ite_mul]
private lemma inverse_pure_block (n d : ℕ) : (pureEmbedding n d)ᵀ * representers n d = (pureDiagonal n d-pureOffDiagonal n d) • (1 : Matrix (Fin n) (Fin n) ℝ) + pureOffDiagonal n d • (Matrix.of (fun _ _ : Fin n => (1 : ℝ))) := by
  ext i j
  rw [transpose_embedding_action]
  simp only [representers, count_constant_all, pureDiagonal, pureOffDiagonal,
    degreeCount, doubleDegreeCount, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.of_apply]
  by_cases h : j=i
  · subst j
    simp only [if_true, Nat.sub_self, pow_zero, mul_one]
    ring
  · simp only [h, Ne.symm h, if_false, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
      mul_one, mul_zero, zero_add]
    ring
private lemma degree_count_pos (n d : ℕ) : 0 < degreeCount n d := by
  unfold degreeCount
  exact_mod_cast Nat.choose_pos (by omega : d ≤ n-1+d)
private lemma double_degree_count_pos (n d : ℕ) : 0 < doubleDegreeCount n d := by
  unfold doubleDegreeCount
  exact_mod_cast Nat.choose_pos (by omega : 2*d ≤ n-1+2*d)
private lemma pure_block_bound {n d : ℕ} (hn : 2 ≤ n) : (1 - mu n d • ((pureEmbedding n d)ᵀ * representers n d)).PosSemidef := by
  rw [inverse_pure_block]
  have hN := degree_count_pos n d
  have hT := double_degree_count_pos n d
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : n ≠ 1 := by omega
  rcases Nat.even_or_odd d with he | ho
  · have hno : ¬ Odd d := by simpa using he
    have hm : mu n d = doubleDegreeCount n d /
        (degreeCount n d * (degreeCount n d + (n:ℝ)-1)) := by
      simp [mu, hn1, hno, degreeCount, doubleDegreeCount]
    have hoff : pureOffDiagonal n d = degreeCount n d / doubleDegreeCount n d := by
      rw [pureOffDiagonal, he.neg_one_pow, one_mul]
    apply constant_block_even_bound
    · rw [hm]
      exact div_nonneg hT.le (mul_nonneg hN.le (by linarith))
    · rw [hoff]
      positivity
    · rw [hm, pureDiagonal, hoff]
      have hden : 0 < degreeCount n d + (n:ℝ)-1 := by linarith
      field_simp [hN.ne', hT.ne', hden.ne']
      ring
  · have hm : mu n d = doubleDegreeCount n d /
        (degreeCount n d * (degreeCount n d + 1)) := by
      simp [mu, hn1, ho, degreeCount, doubleDegreeCount]
    have hoff : pureOffDiagonal n d = -degreeCount n d / doubleDegreeCount n d := by
      rw [pureOffDiagonal, ho.neg_one_pow, neg_one_mul]
    apply constant_block_odd_bound
    · rw [hm]
      positivity
    · rw [hoff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hN.le) hT.le
    · rw [hm, pureDiagonal, hoff]
      field_simp [hN.ne', hT.ne', (by linarith : degreeCount n d + 1 ≠ 0)]
      ring
private lemma mu_nonnegative {n d : ℕ} (hn : 2 ≤ n) : 0 ≤ mu n d := by
  have hn1 : n ≠ 1 := by omega
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hN := degree_count_pos n d
  have hT := double_degree_count_pos n d
  unfold degreeCount at hN
  unfold doubleDegreeCount at hT
  simp only [mu, hn1, if_false]
  split_ifs
  · exact div_nonneg hT.le (mul_nonneg hN.le (by linarith))
  · exact div_nonneg hT.le (mul_nonneg hN.le (by linarith))
theorem sharp_gram_posSemidef {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) : (sharpGram n d).PosSemidef :=
  sharp_posSemidef_of_representers hd (representer_certificate hn)
    (mu_nonnegative hn) (pure_block_bound hn)

omit [CompleteSpace H] in
private theorem matrix_form_nonnegative (D : Matrix I I ℂ) (hD : D.PosSemidef) (v : I → H) : 0 ≤ matrixForm D v := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  rw [hB, hilbert_gram_identity]
  exact Finset.sum_nonneg (fun _ _ => by simp only [inner_self_eq_norm_sq_to_K]; positivity)

/-- Garcia--Volčič, Theorem 1.1(ii): the literal sharp operator inequality. -/
theorem sharp_positivity {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (X : Fin n → H →L[ℂ] H) (hs : ∀ i, IsSelfAdjoint (X i)) :
    (mu n d : ℂ) • (∑ i : Fin n, X i ^ (2*d)) ≤ nchs n (2*d) X := by
  by_cases hn1 : n = 1
  · subst n
    have he : nchs 1 (2*d) X = X 0 ^ (2*d) := by
      have hc (w : Fin (2*d) → Fin 1) : w = fun _ => 0 := Subsingleton.elim _ _
      simp only [nchs]
      simp_rw [hc]
      have hf : (Nat.factorial (2*d) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*d)
      simp [coefficient, occupation, wordEval, List.ofFn_const, Fin.prod_univ_one,
        Fintype.card_pi, Fintype.card_fin, hf]
    rw [he]
    simp [mu, Fin.sum_univ_one]
  · change (residual n d X).IsPositive
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro h
    have hp : 0 ≤ inner ℂ h (residual n d X h) := by
      rw [residual_inner_gram hd X hs h]
      exact matrix_form_nonnegative _ (sharp_gram_posSemidef (by omega) hd) _
    constructor
    · apply Complex.ext
      · rfl
      · change 0 = RCLike.im (inner ℂ ((residual n d X) h) h)
        rw [inner_im_symm]
        change 0 = -(inner ℂ h ((residual n d X) h)).im
        rw [← (Complex.nonneg_iff.mp hp).2]
        simp
    · rw [inner_re_symm]
      exact (Complex.nonneg_iff.mp hp).1

end GVHunter
