/- GID: D5/S3/Quantum/Information/DickeClifford/DickeCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DickeClifford/DickeCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dicke Pauli expectations have binomial denominators and at most four unit entries. -/

/-
proof_shape: dicke_certificate: content
escape_witness: weight-layer exchange forces constant flip and sign masks;
  only I and Z words survive, plus X and Y words on the balanced layer.
admission_basis: escape-witness
Direct frozen dependencies (GID and statement_id):
  D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation
    pauliGroup: sha256:828566194dd41346a7611fcace6be573297934e11b7a2293c899532d9519d650
    State: sha256:98e97720240c871fb1020533a3055605618ebdb0cc173efcdc0d9b7982f7240a
    Operator: sha256:e502425b163288070c85af8662b9a67de5c1f1bedcf73ac8ed3002d9b0ff16a3
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
    pauliMatrix: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
    instFintypePauli: sha256:86b778dc124feee0fe09eb37727ded0ed70c523451613e21523f2ee58963ccfd
    instDecidableEqPauli: sha256:33c12f5e37295acca8f6d08be0dd7c7dff2c7a3f0389f74e6c56155c84d61cc8
    Pauli: sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc
    wordOp: sha256:716021b4dbe91f63db8a8ce009e9f85de30e6cc741033f164343fc5ce30653ed
    tensorOp: sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
  D5/S3/Quantum/Information/SignedPauliSumNormRefutation
    pauliZ: sha256:61ea0b0971de26d2479eb5faaefb162074ffdfe2562ca9621d05f53503521f36
  D5/S3/Quantum/FiniteDimensional
    QubitMatrix: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
    qubitX: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
    qubitZ: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

noncomputable section
namespace D5.S3.Quantum.Information.DickeClifford.DickeCertificate
open Matrix Complex
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation (State Operator)
open D5.S3.Quantum.Information.SignedPauliSumNormRefutation (pauliZ sigmaOfDigit)
open scoped BigOperators ComplexOrder

/-- The existing Pauli subgroup represented as matrices. -/
def pauliMatrices (n : ℕ) : Set (Operator n) :=
  Units.val '' (D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauliGroup n : Set (Operator n)ˣ)

/-- Definition A.1: the special-unitary normalizer of the n-qubit Pauli group. -/
def Clifford (n : ℕ) : Set (Operator n) :=
  {U | U ∈ Matrix.specialUnitaryGroup (Fin n → Fin 2) ℂ ∧
    ∀ P ∈ pauliMatrices n, U * P * Uᴴ ∈ pauliMatrices n}

def dicke (n k : ℕ) : State n :=
  fun x => if hammingNorm x = k then ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) else 0

def productVector {n : ℕ} (φ : Fin n → Fin 2 → ℂ) : State n :=
  fun x => ∏ j, φ j (x j)

def LocalNormalized (φ : Fin 2 → ℂ) : Prop := ∑ b, Complex.normSq (φ b) = 1

def expectation {n : ℕ} (ψ : State n) (P : Operator n) : ℂ :=
  star ψ ⬝ᵥ (P *ᵥ ψ)

def pauliUnitCount {n : ℕ} (ψ : State n) : ℕ :=
  (Finset.univ.filter (fun p : Fin n → Pauli => ‖expectation ψ (wordOp p)‖ = 1)).card

def HasIntegerPauliDenominator {n : ℕ} (B : ℕ) (ψ : State n) : Prop :=
  ∀ p : Fin n → Pauli, ∃ a : ℤ, (B : ℂ) * expectation ψ (wordOp p) = (a : ℂ)


/-- Integral binomial-scaled expectations and the two/four-word unit-count bound. -/
theorem dicke_certificate (n k : ℕ) (hn : 2 < n) (hk : 0 < k) (hkn : k < n) :
    HasIntegerPauliDenominator (n.choose k) (dicke n k) ∧
      pauliUnitCount (dicke n k) ≤ if n = 2 * k then 4 else 2 := by
  classical
  have tensor_mul {n : ℕ}
      (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      tensorOp M * tensorOp N = tensorOp (fun j => M j * N j) := by
    ext x z
    simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
    simp_rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have tensor_star {n : ℕ}
      (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      (tensorOp M)ᴴ = tensorOp (fun j => (M j)ᴴ) := by
    ext x y
    simp [tensorOp, Matrix.conjTranspose_apply, map_prod]
  have tensor_one (n : ℕ) :
      tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    ext x y
    simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        contrapose! h
        exact funext h
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  have local_pauli_star (p : Pauli) : (pauliMatrix p)ᴴ = pauliMatrix p := by
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  have local_pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  have word_star {n : ℕ} (p : Fin n → Pauli) : (wordOp p)ᴴ = wordOp p := by
    simp only [wordOp, tensor_star, local_pauli_star]
  have word_sq {n : ℕ} (p : Fin n → Pauli) : wordOp p * wordOp p = 1 := by
    rw [wordOp, tensor_mul]
    simp only [local_pauli_sq, tensor_one]
  have expectation_star {n : ℕ} (ψ : State n) (P : Operator n) :
      star (expectation ψ P) = expectation ψ Pᴴ := by
    calc
      star (expectation ψ P) = star (P *ᵥ ψ) ⬝ᵥ ψ :=
        (star_dotProduct (P *ᵥ ψ) ψ).symm
      _ = expectation ψ Pᴴ := by
        rw [Matrix.star_mulVec, ← dotProduct_mulVec]
        rfl
  have word_expectation_real {n : ℕ} (ψ : State n) (p : Fin n → Pauli) :
      (expectation ψ (wordOp p)).im = 0 := by
    have h := expectation_star ψ (wordOp p)
    rw [word_star] at h
    have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  have layer_swap_base {α : Type} [Fintype α] [DecidableEq α]
      (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card α) (i j : α) (hij : i ≠ j) :
      ∃ T : Finset α, i ∉ T ∧ j ∉ T ∧ T.card = k - 1 := by
    let S : Finset α := Finset.univ \ {i, j}
    have hcard : S.card = Fintype.card α - 2 := by
      dsimp [S]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [hij]
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq
      (show k - 1 ≤ S.card by rw [hcard]; omega)
    refine ⟨T, ?_, ?_, hTc⟩
    · intro hi
      have := (Finset.mem_sdiff.mp (hT hi)).2
      exact this (by simp)
    · intro hj
      have := (Finset.mem_sdiff.mp (hT hj)).2
      exact this (by simp)
  have layer_sum_rigidity {α : Type} [Fintype α] [DecidableEq α]
      (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card α)
      (a : α → ℤ) (t : ℤ) (h : ∀ S : Finset α, S.card = k → ∑ i ∈ S, a i = t) :
      ∀ i j, a i = a j := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    obtain ⟨T, hi, hj, hT⟩ := layer_swap_base k hk hkn i j hij
    have hci : (insert i T).card = k := by rw [Finset.card_insert_of_notMem hi, hT]; omega
    have hcj : (insert j T).card = k := by rw [Finset.card_insert_of_notMem hj, hT]; omega
    have hei := h (insert i T) hci
    have hej := h (insert j T) hcj
    rw [Finset.sum_insert hi] at hei
    rw [Finset.sum_insert hj] at hej
    omega
  have layer_parity_rigidity {α : Type} [Fintype α] [DecidableEq α]
      (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card α)
      (a : α → ℤ) (t : ℤ) (h : ∀ S : Finset α, S.card = k → (∑ i ∈ S, a i) % 2 = t) :
      ∀ i j, a i % 2 = a j % 2 := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    obtain ⟨T, hi, hj, hT⟩ := layer_swap_base k hk hkn i j hij
    have hci : (insert i T).card = k := by rw [Finset.card_insert_of_notMem hi, hT]; omega
    have hcj : (insert j T).card = k := by rw [Finset.card_insert_of_notMem hj, hT]; omega
    have hei := h (insert i T) hci
    have hej := h (insert j T) hcj
    rw [Finset.sum_insert hi] at hei
    rw [Finset.sum_insert hj] at hej
    omega
  let bitSupport {n : ℕ} (x : (Fin n → Fin 2)) : Finset (Fin n) :=
    Finset.univ.filter (fun j => x j = 1)
  let bitsOfSet {n : ℕ} (S : Finset (Fin n)) : (Fin n → Fin 2) := fun j => if j ∈ S then 1 else 0
  have support_inverse {n : ℕ} (S : Finset (Fin n)) :
      bitSupport (bitsOfSet S) = S := by
    ext j
    simp [bitSupport, bitsOfSet]
  have bits_inverse {n : ℕ} (x : (Fin n → Fin 2)) : bitsOfSet (bitSupport x) = x := by
    funext j
    generalize hx : x j = b
    fin_cases b <;> simp [bitsOfSet, bitSupport, hx]
  have hammingNorm_sum {n : ℕ} (x : Fin n → Fin 2) :
      hammingNorm x = ∑ j, (x j).val := by
    rw [hammingNorm, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    generalize hx : x j = b
    fin_cases b <;> norm_num
  have support_card {n : ℕ} (x : (Fin n → Fin 2)) : (bitSupport x).card = hammingNorm x := by
    dsimp only [bitSupport]
    rw [hammingNorm_sum, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    generalize hx : x j = b
    fin_cases b <;> norm_num
  have layer_card (n k : ℕ) :
      (Finset.univ.filter (fun x : (Fin n → Fin 2) => hammingNorm x = k)).card = n.choose k := by
    let e : {x : (Fin n → Fin 2) // hammingNorm x = k} ≃
        {S : Finset (Fin n) // S ∈ Finset.powersetCard k Finset.univ} :=
      { toFun := fun x => ⟨bitSupport x.val, by
          simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
          rw [support_card, x.property]⟩
        invFun := fun S => ⟨bitsOfSet S.val, by
          rw [← support_card, support_inverse]
          exact (Finset.mem_powersetCard.mp S.property).2⟩
        left_inv := fun x => by apply Subtype.ext; exact bits_inverse x.val
        right_inv := fun S => by apply Subtype.ext; exact support_inverse S.val }
    have he := Fintype.card_congr e
    simpa [Fintype.card_subtype, Finset.card_powersetCard] using he
  let rawDicke (n k : ℕ) : State n := fun x => if hammingNorm x = k then 1 else 0
  have dicke_scale (n k : ℕ) :
      dicke n k = ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) • rawDicke n k := by
    funext x
    simp only [dicke, rawDicke, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have rawDicke_norm (n k : ℕ) :
      star (rawDicke n k) ⬝ᵥ rawDicke n k = (n.choose k : ℂ) := by
    have ht (x : (Fin n → Fin 2)) : star (rawDicke n k x) * rawDicke n k x =
        if hammingNorm x = k then 1 else 0 := by
      by_cases hx : hammingNorm x = k <;> simp [rawDicke, hx]
    change (∑ x : (Fin n → Fin 2), star (rawDicke n k x) * rawDicke n k x) = _
    simp_rw [ht]
    rw [Finset.sum_boole, layer_card]
  have dicke_scale_square (n k : ℕ) (hk : k ≤ n) :
      (n.choose k : ℂ) * ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) ^ 2 = 1 := by
    have hB : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
    have h : (n.choose k : ℝ) * (Real.sqrt (n.choose k : ℝ))⁻¹ ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt hB.le, mul_inv_cancel₀ (ne_of_gt hB)]
    exact_mod_cast h
  have expectation_state_smul {n : ℕ} (ψ : State n) (P : Operator n) (s : ℂ) :
      expectation (s • ψ) P = (star s * s) * expectation ψ P := by
    simp [expectation, Matrix.mulVec_smul, star_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have dicke_normalized (n k : ℕ) (hk : k ≤ n) :
      star (dicke n k) ⬝ᵥ dicke n k = 1 := by
    rw [dicke_scale]
    simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, rawDicke_norm,
      Complex.star_def, map_inv₀, Complex.conj_ofReal]
    convert dicke_scale_square n k hk using 1; ring
  have pauliZ_cast (p : Pauli) (a b : Fin 2) :
      ((pauliZ p a b : GaussianInt) : ℂ) = pauliMatrix p a b := by
    cases p <;> fin_cases a <;> fin_cases b <;>
      simp [pauliZ, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, GaussianInt.toComplex_def,
        Matrix.mul_apply, Fin.sum_univ_two]
  let gaussianWord {n : ℕ} (p : Fin n → Pauli) (x y : (Fin n → Fin 2)) : GaussianInt :=
    ∏ j, pauliZ (p j) (x j) (y j)
  have gaussianWord_cast {n : ℕ} (p : Fin n → Pauli) (x y : (Fin n → Fin 2)) :
      (gaussianWord p x y : ℂ) = wordOp p x y := by
    change GaussianInt.toComplex (∏ j, pauliZ (p j) (x j) (y j)) =
      ∏ j, pauliMatrix (p j) (x j) (y j)
    rw [map_prod]
    exact Finset.prod_congr rfl (fun j _ => pauliZ_cast (p j) (x j) (y j))
  let gaussianDickeExpectation {n : ℕ} (k : ℕ) (p : Fin n → Pauli) : GaussianInt :=
    ∑ x : (Fin n → Fin 2), ∑ y : (Fin n → Fin 2),
      (if hammingNorm x = k then 1 else 0) * gaussianWord p x y * (if hammingNorm y = k then 1 else 0)
  have gaussianDickeExpectation_cast {n : ℕ} (k : ℕ) (p : Fin n → Pauli) :
      (gaussianDickeExpectation k p : ℂ) = expectation (rawDicke n k) (wordOp p) := by
    simp only [gaussianDickeExpectation, map_sum, map_mul, apply_ite, map_one, map_zero]
    simp only [expectation, rawDicke, Matrix.mulVec, dotProduct, Pi.star_apply,
      apply_ite, star_one, star_zero, Finset.mul_sum]
    congr 1
    ext x
    congr 1
    ext y
    rw [gaussianWord_cast]
    split_ifs <;> simp
  have dicke_denominator (n k : ℕ) (hk : k ≤ n) :
      HasIntegerPauliDenominator (n.choose k) (dicke n k) := by
    intro p
    let z : GaussianInt := gaussianDickeExpectation k p
    have hz : (n.choose k : ℂ) * expectation (dicke n k) (wordOp p) = (z : ℂ) := by
      rw [dicke_scale, expectation_state_smul]
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [← pow_two, ← mul_assoc, dicke_scale_square n k hk, one_mul]
      exact (gaussianDickeExpectation_cast k p).symm
    have hzIm : z.im = 0 := by
      have hi := congrArg Complex.im hz
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        word_expectation_real, mul_zero, zero_mul, add_zero, GaussianInt.toComplex_def,
        Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.I_im, Complex.I_re, mul_one, zero_add] at hi
      exact_mod_cast hi.symm
    refine ⟨z.re, ?_⟩
    simpa [GaussianInt.toComplex_def, hzIm] using hz
  let flipBit : Pauli → Fin 2
    | .I => 0
    | .X => 1
    | .Y => 1
    | .Z => 0
  let signBit : Pauli → ℕ
    | .I => 0
    | .X => 0
    | .Y => 1
    | .Z => 1
  let phaseConstant : Pauli → ℂ
    | .I => 1
    | .X => 1
    | .Y => -Complex.I
    | .Z => 1
  let pauliPhase (p : Pauli) (b : Fin 2) : ℂ :=
    phaseConstant p * (-1 : ℂ) ^ (signBit p * b.val)
  let flipBits {n : ℕ} (p : Fin n → Pauli) (x : (Fin n → Fin 2)) : (Fin n → Fin 2) :=
    fun j => x j + flipBit (p j)
  let wordPhase {n : ℕ} (p : Fin n → Pauli) (x : (Fin n → Fin 2)) : ℂ :=
    ∏ j, pauliPhase (p j) (x j)
  have local_monomial (p : Pauli) (a b : Fin 2) :
      pauliMatrix p a b = if b = a + flipBit p then pauliPhase p a else 0 := by
    cases p <;> fin_cases a <;> fin_cases b <;>
      norm_num [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two,
        pauliPhase, phaseConstant, signBit, flipBit, Fin.add_def]
  have word_monomial {n : ℕ} (p : Fin n → Pauli) (x y : (Fin n → Fin 2)) :
      wordOp p x y = if y = flipBits p x then wordPhase p x else 0 := by
    change (∏ j, pauliMatrix (p j) (x j) (y j)) = _
    simp_rw [local_monomial]
    by_cases h : y = flipBits p x
    · subst y
      simp [flipBits, wordPhase]
    · rw [if_neg h]
      obtain ⟨j, hj⟩ : ∃ j, y j ≠ x j + flipBit (p j) := by
        contrapose! h
        exact funext h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  have word_action {n : ℕ} (p : Fin n → Pauli) (ψ : State n) (x : (Fin n → Fin 2)) :
      (wordOp p *ᵥ ψ) x = wordPhase p x * ψ (flipBits p x) := by
    change (∑ y : (Fin n → Fin 2), wordOp p x y * ψ y) = _
    simp_rw [word_monomial, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (flipBits p x)]
    simp
  have flip_weight_identity {n : ℕ} (p : Fin n → Pauli) (x : (Fin n → Fin 2)) :
      (hammingNorm (flipBits p x) : ℤ) =
        (hammingNorm x : ℤ) + (hammingNorm (fun j => flipBit (p j)) : ℤ) -
          2 * ∑ j, ((x j).val : ℤ) * ((flipBit (p j)).val : ℤ) := by
    simp only [hammingNorm_sum, Nat.cast_sum, flipBits]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    generalize hx : x j = a
    generalize hf : flipBit (p j) = b
    fin_cases a <;> fin_cases b <;> norm_num [Fin.add_def]
  have bit_is_constant {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k < n)
      (f : (Fin n → Fin 2)) (h : ∀ S : Finset (Fin n), S.card = k →
        2 * ∑ j ∈ S, ((f j).val : ℤ) = (hammingNorm f : ℤ)) :
      ∀ i j, f i = f j := by
    have hc := layer_sum_rigidity k hk (by simpa using hkn)
      (fun j => ((f j).val : ℤ)) ((hammingNorm f : ℤ) / 2) (by
        intro S hS
        have he := h S hS
        omega)
    intro i j
    apply Fin.ext
    exact_mod_cast hc i j
  have layer_flip_rigidity {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k < n)
      (p : Fin n → Pauli) (h : ∀ x : (Fin n → Fin 2), hammingNorm x = k → hammingNorm (flipBits p x) = k) :
      (∀ j, flipBit (p j) = 0) ∨ ((∀ j, flipBit (p j) = 1) ∧ n = 2 * k) := by
    have hf (S : Finset (Fin n)) (hS : S.card = k) :
        2 * ∑ j ∈ S, ((flipBit (p j)).val : ℤ) =
          (hammingNorm (fun j => flipBit (p j)) : ℤ) := by
      have hx : hammingNorm (bitsOfSet S) = k := by rw [← support_card, support_inverse, hS]
      have he := flip_weight_identity p (bitsOfSet S)
      rw [h _ hx, hx] at he
      have hsum : ∑ j : Fin n, ((bitsOfSet S j).val : ℤ) * ((flipBit (p j)).val : ℤ) =
          ∑ j ∈ S, ((flipBit (p j)).val : ℤ) := by
        have hid (j : Fin n) : ((bitsOfSet S j).val : ℤ) = if j ∈ S then 1 else 0 := by
          by_cases hj : j ∈ S <;> simp [bitsOfSet, hj]
        simp_rw [hid, ite_mul, one_mul, zero_mul]
        simp [← Finset.sum_filter]
      rw [hsum] at he
      omega
    have hc := bit_is_constant k hk hkn (fun j => flipBit (p j)) hf
    let j0 : Fin n := ⟨0, by omega⟩
    have hsame (j : Fin n) : flipBit (p j) = flipBit (p j0) := hc j j0
    generalize h0 : flipBit (p j0) = b at hsame
    fin_cases b
    · exact Or.inl hsame
    · refine Or.inr ⟨hsame, ?_⟩
      obtain ⟨S, hSsub, hSc⟩ := Finset.exists_subset_card_eq
        (show k ≤ (Finset.univ : Finset (Fin n)).card by simpa using hkn.le)
      have he := hf S hSc
      simp only [hsame, Fin.val_one, Nat.cast_one, Finset.sum_const, nsmul_eq_mul,
        mul_one, hammingNorm_sum, Finset.card_univ, Fintype.card_fin, hSc] at he
      exact_mod_cast he.symm
  have word_expectation_unit_iff {n : ℕ} (ψ : State n)
      (hψ : star ψ ⬝ᵥ ψ = 1) (p : Fin n → Pauli) :
      ‖expectation ψ (wordOp p)‖ = 1 ↔
        wordOp p *ᵥ ψ = ψ ∨ wordOp p *ᵥ ψ = -ψ := by
    let P := wordOp p
    have hPstar : Pᴴ = P := word_star p
    have hPsq : P * P = 1 := word_sq p
    have hnorm : star (P *ᵥ ψ) ⬝ᵥ (P *ᵥ ψ) = 1 := by
      rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul, hPstar,
        hPsq, vecMul_one]
      exact hψ
    have hcross : star (P *ᵥ ψ) ⬝ᵥ ψ = expectation ψ P := by
      rw [Matrix.star_mulVec, ← dotProduct_mulVec, hPstar]
      rfl
    constructor
    · intro he
      have him : (expectation ψ P).im = 0 := word_expectation_real ψ p
      have hre : (expectation ψ P : ℂ) = ((expectation ψ P).re : ℂ) := by
        apply Complex.ext <;> simp [him]
      have he' : |(expectation ψ P).re| = 1 := by
        rw [hre, Complex.norm_real, Real.norm_eq_abs] at he
        exact he
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he' with hplus | hminus
      · have hE : expectation ψ P = 1 := by rw [hre, hplus]; norm_num
        have hzero : star (P *ᵥ ψ - ψ) ⬝ᵥ (P *ᵥ ψ - ψ) = 0 := by
          rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
            hnorm, hcross, show star ψ ⬝ᵥ (P *ᵥ ψ) = expectation ψ P from rfl,
            hψ, hE]
          norm_num
        exact Or.inl (sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hzero))
      · have hE : expectation ψ P = -1 := by rw [hre, hminus]; norm_num
        have hzero : star (P *ᵥ ψ + ψ) ⬝ᵥ (P *ᵥ ψ + ψ) = 0 := by
          rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add,
            hnorm, hcross, show star ψ ⬝ᵥ (P *ᵥ ψ) = expectation ψ P from rfl,
            hψ, hE]
          norm_num
        exact Or.inr (eq_neg_of_add_eq_zero_left (dotProduct_star_self_eq_zero.mp hzero))
    · rintro (h | h) <;> simp [expectation, h, hψ]
  have dicke_eigen_support {n : ℕ} (k : ℕ) (hk : k ≤ n)
      (p : Fin n → Pauli) (s : ℂ) (hs : s ≠ 0)
      (he : wordOp p *ᵥ dicke n k = s • dicke n k) :
      ∀ x : (Fin n → Fin 2), hammingNorm x = k →
        hammingNorm (flipBits p x) = k ∧ wordPhase p x = s := by
    have hB : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
    have hr : ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hB))
    intro x hx
    have he' := congrFun he x
    rw [word_action] at he'
    simp only [Pi.smul_apply, smul_eq_mul, dicke, if_pos hx] at he'
    have hf : hammingNorm (flipBits p x) = k := by
      by_contra h
      rw [if_neg h, mul_zero] at he'
      exact (mul_ne_zero hs hr) he'.symm
    rw [if_pos hf] at he'
    exact ⟨hf, mul_right_cancel₀ hr he'⟩
  have wordPhase_factor {n : ℕ} (p : Fin n → Pauli) (x : (Fin n → Fin 2)) :
      wordPhase p x = (∏ j, phaseConstant (p j)) *
        (-1 : ℂ) ^ (∑ j, signBit (p j) * (x j).val) := by
    simp only [wordPhase, pauliPhase, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have phaseConstant_product_nonzero {n : ℕ} (p : Fin n → Pauli) :
      (∏ j, phaseConstant (p j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    cases p j <;> norm_num [phaseConstant]
  have sign_sum_set {n : ℕ} (p : Fin n → Pauli) (S : Finset (Fin n)) :
      (∑ j, signBit (p j) * (bitsOfSet S j).val) = ∑ j ∈ S, signBit (p j) := by
    have hid (j : Fin n) : (bitsOfSet S j).val = if j ∈ S then 1 else 0 := by
      by_cases hj : j ∈ S <;> simp [bitsOfSet, hj]
    simp_rw [hid, mul_ite, mul_one, mul_zero]
    simp [← Finset.sum_filter]
  have neg_one_pow_parity (a b : ℕ)
      (h : (-1 : ℂ)^a = (-1 : ℂ)^b) : a % 2 = b % 2 := by
    replace h : (-1 : ℂ) ^ (a % 2) = (-1 : ℂ) ^ (b % 2) :=
      (neg_one_pow_eq_pow_mod_two a).symm.trans (h.trans (neg_one_pow_eq_pow_mod_two b))
    have ha := Nat.mod_lt a (by norm_num : 0 < 2)
    have hb := Nat.mod_lt b (by norm_num : 0 < 2)
    by_cases ha0 : a % 2 = 0 <;> by_cases hb0 : b % 2 = 0
    · omega
    · have hb1 : b % 2 = 1 := by omega
      rw [ha0, hb1] at h
      have hi := congrArg Complex.re h
      norm_num at hi
    · have ha1 : a % 2 = 1 := by omega
      rw [ha1, hb0] at h
      have hi := congrArg Complex.re h
      norm_num at hi
    · omega
  have layer_sign_rigidity {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k < n)
      (p : Fin n → Pauli) (s : ℂ)
      (h : ∀ x : (Fin n → Fin 2), hammingNorm x = k → wordPhase p x = s) :
      ∀ i j, signBit (p i) = signBit (p j) := by
    obtain ⟨S0, hS0sub, hS0card⟩ := Finset.exists_subset_card_eq
      (show k ≤ (Finset.univ : Finset (Fin n)).card by simpa using hkn.le)
    let t : ℤ := (∑ j ∈ S0, (signBit (p j) : ℤ)) % 2
    have hmod (S : Finset (Fin n)) (hScard : S.card = k) :
        (∑ j ∈ S, (signBit (p j) : ℤ)) % 2 = t := by
      have hx : hammingNorm (bitsOfSet S) = k := by rw [← support_card, support_inverse, hScard]
      have hx0 : hammingNorm (bitsOfSet S0) = k := by rw [← support_card, support_inverse, hS0card]
      have he : wordPhase p (bitsOfSet S) = wordPhase p (bitsOfSet S0) :=
        (h _ hx).trans (h _ hx0).symm
      rw [wordPhase_factor, wordPhase_factor, sign_sum_set, sign_sum_set] at he
      have hpow := mul_left_cancel₀ (phaseConstant_product_nonzero p) he
      have hp := neg_one_pow_parity _ _ hpow
      dsimp [t]
      exact_mod_cast hp
    have hc := layer_parity_rigidity k hk (by simpa using hkn)
      (fun j => (signBit (p j) : ℤ)) t hmod
    intro i j
    have he := hc i j
    generalize hpi : p i = u at he ⊢
    generalize hpj : p j = v at he ⊢
    cases u <;> cases v <;> norm_num [signBit] at he <;> norm_num [signBit]
  have pauli_mask_unique (p q : Pauli)
      (hf : flipBit p = flipBit q) (hz : signBit p = signBit q) : p = q := by
    cases p <;> cases q <;> solve
    | rfl
    | norm_num [flipBit] at hf
    | norm_num [signBit] at hz
  have dicke_eigen_classification (n k : ℕ) (hn : 2 < n)
      (hk : 0 < k) (hkn : k < n) (p : Fin n → Pauli)
      (hp : ‖expectation (dicke n k) (wordOp p)‖ = 1) :
      p = (fun _ => Pauli.I) ∨ p = (fun _ => Pauli.Z) ∨
        (n = 2 * k ∧ (p = (fun _ => Pauli.X) ∨ p = (fun _ => Pauli.Y))) := by
    have hnorm := dicke_normalized n k hkn.le
    have he := (word_expectation_unit_iff (dicke n k) hnorm p).mp hp
    have hex : ∃ s : ℂ, s ≠ 0 ∧ wordOp p *ᵥ dicke n k = s • dicke n k := by
      rcases he with he | he
      · exact ⟨1, by norm_num, by simpa using he⟩
      · exact ⟨-1, by norm_num, by simpa using he⟩
    obtain ⟨s, hs, hEigen⟩ := hex
    have hsupport := dicke_eigen_support k hkn.le p s hs hEigen
    have hflip := layer_flip_rigidity k hk hkn p (fun x hx => (hsupport x hx).1)
    have hsign := layer_sign_rigidity k hk hkn p s (fun x hx => (hsupport x hx).2)
    let j0 : Fin n := ⟨0, by omega⟩
    have hconst : ∀ j, p j = p j0 := by
      intro j
      apply pauli_mask_unique
      · rcases hflip with hf | ⟨hf, hn⟩ <;> rw [hf j, hf j0]
      · exact hsign j j0
    have hpconst : p = fun _ => p j0 := funext hconst
    cases h0 : p j0
    · exact Or.inl (by simpa [h0] using hpconst)
    · refine Or.inr (Or.inr ⟨?_, Or.inl (by simpa [h0] using hpconst)⟩)
      rcases hflip with hf | ⟨hf, hn⟩
      · have h := hf j0
        norm_num [h0, flipBit] at h
      · exact hn
    · refine Or.inr (Or.inr ⟨?_, Or.inr (by simpa [h0] using hpconst)⟩)
      rcases hflip with hf | ⟨hf, hn⟩
      · have h := hf j0
        norm_num [h0, flipBit] at h
      · exact hn
    · exact Or.inr (Or.inl (by simpa [h0] using hpconst))
  have dicke_count_upper (n k : ℕ) (hn : 2 < n)
      (hk : 0 < k) (hkn : k < n) :
      pauliUnitCount (dicke n k) ≤ if n = 2 * k then 4 else 2 := by
    unfold pauliUnitCount
    let i : Fin n → Pauli := fun _ => .I
    let z : Fin n → Pauli := fun _ => .Z
    let x : Fin n → Pauli := fun _ => .X
    let y : Fin n → Pauli := fun _ => .Y
    by_cases hbal : n = 2 * k
    · rw [if_pos hbal]
      have hsub : (Finset.univ.filter (fun p : Fin n → Pauli =>
          ‖expectation (dicke n k) (wordOp p)‖ = 1)) ⊆ {i, z, x, y} := by
        intro p hp
        have he := dicke_eigen_classification n k hn hk hkn p (Finset.mem_filter.mp hp).2
        rcases he with he | he | ⟨_, he | he⟩ <;> simp [i, z, x, y, he]
      have hc := Finset.card_le_card hsub
      have hc' : ({i, z, x, y} : Finset (Fin n → Pauli)).card ≤ 4 := by
        exact le_trans (Finset.card_insert_le _ _) (by
          apply Nat.succ_le_succ
          exact le_trans (Finset.card_insert_le _ _) (by
            apply Nat.succ_le_succ
            exact le_trans (Finset.card_insert_le _ _) (by simp)))
      omega
    · rw [if_neg hbal]
      have hsub : (Finset.univ.filter (fun p : Fin n → Pauli =>
          ‖expectation (dicke n k) (wordOp p)‖ = 1)) ⊆ {i, z} := by
        intro p hp
        have he := dicke_eigen_classification n k hn hk hkn p (Finset.mem_filter.mp hp).2
        rcases he with he | he | ⟨he, _⟩
        · simp [i, z, he]
        · simp [i, z, he]
        · exact False.elim (hbal he)
      have hc := Finset.card_le_card hsub
      have hc' : ({i, z} : Finset (Fin n → Pauli)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
  exact ⟨dicke_denominator n k hkn.le, dicke_count_upper n k hn hk hkn⟩

end D5.S3.Quantum.Information.DickeClifford.DickeCertificate
