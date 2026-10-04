/- GID: D5/S3/Quantum/Information/DickeCliffordProductObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DickeCliffordProductObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No Clifford maps a nontrivial Dicke state to a normalized total product state. -/

/-
proof_shape: result: content
escape_witness: primitive pure-qubit denominators exclude two, and the tensor
  Bezout certificate forces their product to divide the binomial coefficient;
  the unit-count bound and the inductive binomial estimate give a contradiction.
admission_basis: open-problem-resolution (#12575; Proved)
Direct frozen dependencies (GID and statement_id):
  D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation
    pauliGroup: sha256:828566194dd41346a7611fcace6be573297934e11b7a2293c899532d9519d650
    Phase: sha256:308f5a5daaa999d7f59dbd38667e28247b8c9d191f982bc56437f68f3c77d3ff
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
    sigmaOfDigit: sha256:c4252857368aa7e8f59c9f5bcc5c20278f6d2068602b6b8a5ae01bcca46e9fe7
  D5/S3/Quantum/FiniteDimensional
    QubitMatrix: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
    qubitX: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
    qubitZ: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
Local chain prerequisite: DickeClifford/DickeCertificate.dicke_certificate.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Information.DickeClifford.DickeCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

noncomputable section
namespace D5.S3.Quantum.Information.DickeCliffordProductObstruction
open Matrix Complex
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation (State Operator)
open D5.S3.Quantum.Information.SignedPauliSumNormRefutation (pauliZ sigmaOfDigit)
open scoped BigOperators ComplexOrder

open D5.S3.Quantum.Information.DickeClifford.DickeCertificate

def claim : Prop :=
  ∀ n k : ℕ, 2 < n → 0 < k → k < n →
    ∀ U ∈ Clifford n, ∀ φ : Fin n → Fin 2 → ℂ,
      (∀ j, LocalNormalized (φ j)) → U *ᵥ dicke n k ≠ productVector φ

/-- Remark F.1 of arXiv:2607.18400v1. -/
theorem result : claim := by
  classical
  let pauliGroup (n : ℕ) : Set (Operator n) :=
    {P | ∃ (c : Fin 4) (p : Fin n → Pauli), P = Complex.I ^ c.val • wordOp p}
  let Primitive {ι : Type} [Fintype ι] (v : ι → ℤ) : Prop :=
    ∃ c : ι → ℤ, ∑ i, c i * v i = 1
  have choose_lt_three_pow (n k : ℕ) (hn : 4 ≤ n) :
      n.choose k < 3 ^ (n - 2) := by
    induction n, hn using Nat.le_induction generalizing k with
    | base =>
      have h := Nat.choose_le_middle k 4
      norm_num [Nat.choose] at h ⊢
      omega
    | succ n hn ih =>
      have hp : 0 < 3 ^ (n - 2) := by positivity
      have he : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [he, pow_succ]
      cases k with
      | zero => simp; nlinarith
      | succ k =>
        rw [Nat.choose_succ_succ]
        have h₁ := ih k
        have h₂ := ih (k + 1)
        nlinarith
  have primitive_pi {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
      (a : ι → κ → ℤ) (ha : ∀ i, Primitive (a i)) :
      Primitive (fun x : ι → κ => ∏ i, a i (x i)) := by
    classical
    choose c hc using ha
    refine ⟨fun x => ∏ i, c i (x i), ?_⟩
    simp only [← Finset.prod_mul_distrib]
    rw [← Fintype.piFinset_univ]
    simpa [hc] using (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset κ))
      (fun i x => c i x * a i x)).symm
  have purity_denominator_ne_two (d a b c : ℤ)
      (hp : a ^ 2 + b ^ 2 + c ^ 2 = d ^ 2)
      (hprimitive : Primitive (![d, a, b, c] : Fin 4 → ℤ)) : d ≠ 2 := by
    intro hd
    subst d
    obtain ⟨q, hq⟩ := hprimitive
    have ha : -2 ≤ a ∧ a ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg b, sq_nonneg c]
    have hb : -2 ≤ b ∧ b ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg a, sq_nonneg c]
    have hc : -2 ≤ c ∧ c ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
    rcases ha with ⟨hal, hau⟩
    rcases hb with ⟨hbl, hbu⟩
    rcases hc with ⟨hcl, hcu⟩
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      norm_num at hp <;>
      simp [Fin.sum_univ_succ] at hq <;> omega
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
  have tensor_trace {n : ℕ}
      (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.trace (tensorOp M) = ∏ j, Matrix.trace (M j) := by
    change (∑ x : (Fin n → Fin 2), ∏ j, M j (x j) (x j)) =
      ∏ j, ∑ b : Fin 2, M j b b
    simpa [Fintype.piFinset_univ] using
      (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
        (fun j b => M j b b)).symm
  have local_pauli_star (p : Pauli) : (pauliMatrix p)ᴴ = pauliMatrix p := by
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  have local_pauli_sq (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  have local_trace_pair (p q : Pauli) :
      Matrix.trace (pauliMatrix p * pauliMatrix q) = if p = q then 2 else 0 := by
    cases p <;> cases q <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.trace,
        Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have word_star {n : ℕ} (p : Fin n → Pauli) : (wordOp p)ᴴ = wordOp p := by
    simp only [wordOp, tensor_star, local_pauli_star]
  have word_sq {n : ℕ} (p : Fin n → Pauli) : wordOp p * wordOp p = 1 := by
    rw [wordOp, tensor_mul]
    simp only [local_pauli_sq, tensor_one]
  have word_trace_pair {n : ℕ} (p q : Fin n → Pauli) :
      Matrix.trace (wordOp p * wordOp q) = if p = q then (2 : ℂ) ^ n else 0 := by
    rw [wordOp, wordOp, tensor_mul, tensor_trace]
    simp_rw [local_trace_pair]
    by_cases h : p = q
    · subst q; simp
    · rw [if_neg h]
      obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
        contrapose! h
        exact funext h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  have word_signed_unique {n : ℕ} (p q : Fin n → Pauli) (s t : ℂ)
      (hs : s ≠ 0) (h : s • wordOp p = t • wordOp q) :
      p = q ∧ s = t := by
    have he := congrArg (fun M : Operator n => Matrix.trace (M * wordOp p)) h
    simp only [Matrix.smul_mul, Matrix.trace_smul, word_trace_pair, smul_eq_mul] at he
    have hp : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpq : p = q := by
      by_contra hne
      simp [hne, Ne.symm hne] at he
      exact hs he
    subst q
    simp only [ite_true] at he
    exact ⟨rfl, (mul_right_cancel₀ hp) he⟩
  have tensor_expectation {n : ℕ}
      (φ : Fin n → Fin 2 → ℂ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
      expectation (productVector φ) (tensorOp M) =
        ∏ j, star (φ j) ⬝ᵥ ((M j) *ᵥ φ j) := by
    change (∑ x : (Fin n → Fin 2), star (∏ j, φ j (x j)) *
      (∑ y : (Fin n → Fin 2), (∏ j, M j (x j) (y j)) * ∏ j, φ j (y j))) =
      ∏ j, ∑ a : Fin 2, star (φ j a) * (∑ b : Fin 2, M j a b * φ j b)
    simp only [star_prod, Finset.mul_sum]
    simp_rw [← Finset.prod_mul_distrib]
    have hf (x : (Fin n → Fin 2)) :
        (∑ y : (Fin n → Fin 2), ∏ j, star (φ j (x j)) * (M j (x j) (y j) * φ j (y j))) =
        ∏ j, ∑ b : Fin 2, star (φ j (x j)) * (M j (x j) b * φ j b) := by
      simpa [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
          (fun j b => star (φ j (x j)) * (M j (x j) b * φ j b))).symm
    simp_rw [hf]
    simpa [Fintype.piFinset_univ] using
      (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
        (fun j a => ∑ b : Fin 2, star (φ j a) * (M j a b * φ j b))).symm
  let bloch (φ : Fin 2 → ℂ) : Pauli → ℝ
    | .I => Complex.normSq (φ 0) + Complex.normSq (φ 1)
    | .X => 2 * (star (φ 0) * φ 1).re
    | .Y => 2 * (star (φ 0) * φ 1).im
    | .Z => Complex.normSq (φ 0) - Complex.normSq (φ 1)
  have local_expectation (φ : Fin 2 → ℂ) (p : Pauli) :
      star φ ⬝ᵥ (pauliMatrix p *ᵥ φ) = (bloch φ p : ℂ) := by
    cases p <;> apply Complex.ext <;>
      simp [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mulVec, dotProduct,
        Matrix.mul_apply, Fin.sum_univ_two, bloch, Complex.normSq,
        Complex.mul_re, Complex.mul_im] <;> ring
  have bloch_purity (φ : Fin 2 → ℂ) (h : LocalNormalized φ) :
      (bloch φ .X) ^ 2 + (bloch φ .Y) ^ 2 + (bloch φ .Z) ^ 2 = 1 := by
    have hid : (bloch φ .X) ^ 2 + (bloch φ .Y) ^ 2 + (bloch φ .Z) ^ 2 =
        (bloch φ .I) ^ 2 := by
      simp [bloch, Complex.normSq, Complex.mul_re, Complex.mul_im]
      ring
    rw [hid]
    have hI : bloch φ .I = 1 := by simpa [LocalNormalized, Fin.sum_univ_two, bloch] using h
    rw [hI]
    norm_num
  have primitive_of_gcd_one {ι : Type} [Fintype ι] (a : ι → ℤ)
      (h : Finset.univ.gcd a = 1) : Primitive a := by
    obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ a
    refine ⟨c, ?_⟩
    simpa [mul_comm, h] using hc.symm
  have primitive_divisor {ι : Type} [Fintype ι] (a : ι → ℤ)
      (ha : Primitive a) (D B : ℤ) (h : ∀ i, D ∣ B * a i) : D ∣ B := by
    obtain ⟨c, hc⟩ := ha
    have hsum : D ∣ ∑ i, c i * (B * a i) :=
      Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (h i) (c i))
    have he : ∑ i, c i * (B * a i) = B := by
      calc
        _ = B * ∑ i, c i * a i := by
          rw [Finset.mul_sum]
          congr 1
          ext i
          ring
        _ = B := by rw [hc, mul_one]
    rwa [he] at hsum
  have primitive_product_denominator {ι κ : Type}
      [Fintype ι] [Fintype κ] [DecidableEq ι]
      (a : ι → κ → ℤ) (ha : ∀ i, Primitive (a i)) (d : ι → ℤ) (B : ℤ)
      (h : ∀ x : ι → κ, (∏ i, d i) ∣ B * ∏ i, a i (x i)) :
      (∏ i, d i) ∣ B :=
    primitive_divisor _ (primitive_pi a ha) _ _ h
  have primitive_coordinates (B : ℕ) (hB : 0 < B) (r : Fin 4 → ℝ)
      (h0 : r 0 = 1) (hr : ∀ i, ∃ a : ℤ, (B : ℝ) * r i = a) :
      ∃ (d : ℤ) (a : Fin 4 → ℤ), 0 < d ∧ Primitive a ∧ a 0 = d ∧
        ∀ i, r i = (a i : ℝ) / (d : ℝ) := by
    choose A hA using hr
    have hA0 : A 0 = (B : ℤ) := by
      have := hA 0
      rw [h0, mul_one] at this
      exact_mod_cast this.symm
    let g : ℤ := Finset.univ.gcd A
    have hg_nonneg : 0 ≤ g :=
      Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := A))
    have hg_ne : g ≠ 0 := by
      intro hg
      have hzero := (Finset.gcd_eq_zero_iff (s := Finset.univ) (f := A)).mp hg
      have h := hzero 0 (Finset.mem_univ 0)
      rw [hA0] at h
      exact_mod_cast (Nat.ne_of_gt hB) (by exact_mod_cast h)
    have hg : 0 < g := lt_of_le_of_ne hg_nonneg (Ne.symm hg_ne)
    obtain ⟨a, ha, hprim⟩ := Finset.extract_gcd A (by exact Finset.univ_nonempty)
    have hfactor (i : Fin 4) : A i = g * a i := ha i (Finset.mem_univ i)
    have hBfactor : (B : ℤ) = g * a 0 := hA0.symm.trans (hfactor 0)
    have ha0 : 0 < a 0 := by
      have hBi : (0 : ℤ) < B := by exact_mod_cast hB
      nlinarith
    refine ⟨a 0, a, ha0, primitive_of_gcd_one a hprim, rfl, ?_⟩
    intro i
    have hBr : (B : ℝ) = (g : ℝ) * (a 0 : ℝ) := by exact_mod_cast hBfactor
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg_ne
    have hdR : (a 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ha0
    have hi : (B : ℝ) * r i = (g : ℝ) * (a i : ℝ) := by
      rw [hA i, hfactor i]
      push_cast
      rfl
    apply (eq_div_iff hdR).mpr
    rw [hBr] at hi
    apply (mul_left_cancel₀ hgR)
    nlinarith [hi]
  have primitive_purity (d : ℤ) (a : Fin 4 → ℤ) (hd : 0 < d)
      (r : Fin 4 → ℝ) (hr : ∀ i, r i = (a i : ℝ) / (d : ℝ))
      (hp : (r 1)^2 + (r 2)^2 + (r 3)^2 = 1) :
      (a 1)^2 + (a 2)^2 + (a 3)^2 = d^2 := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    simp only [hr] at hp
    have he : (a 1 : ℝ)^2 + (a 2 : ℝ)^2 + (a 3 : ℝ)^2 = (d : ℝ)^2 := by
      field_simp [hdR] at hp
      nlinarith [hp]
    exact_mod_cast he
  have primitive_denominator_at_least_three (d a b c : ℤ) (hd : 0 < d)
      (hp : a^2 + b^2 + c^2 = d^2)
      (hprimitive : Primitive (![d, a, b, c] : Fin 4 → ℤ)) (h1 : d ≠ 1) : 3 ≤ d := by
    have h2 := purity_denominator_ne_two d a b c hp hprimitive
    omega
  have pauliGroup_finite (n : ℕ) : (pauliGroup n).Finite := by
    have h :
        pauliGroup n = Set.range (fun x : Fin 4 × (Fin n → Pauli) =>
          Complex.I ^ x.1.val • wordOp x.2) := by
      ext P
      simp [pauliGroup, Set.mem_range, Prod.exists, eq_comm]
    rw [h]
    exact Set.finite_range _
  have conjugation_injective {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ) :
      Function.Injective (fun P : Operator n => U * P * Uᴴ) := by
    have hleft : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    intro P Q h
    have he := congrArg (fun R : Operator n => Uᴴ * R * U) h
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hleft, one_mul,
      ← Matrix.mul_assoc _ Uᴴ U, hleft, mul_one] using he
  have normalizer_inverse {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ)
      (hN : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n) :
      ∀ P ∈ pauliGroup n, Uᴴ * P * U ∈ pauliGroup n := by
    let : Fintype {P : Operator n // P ∈ pauliGroup n} := (pauliGroup_finite n).fintype
    let f : {P : Operator n // P ∈ pauliGroup n} →
        {P : Operator n // P ∈ pauliGroup n} :=
      fun P => ⟨U * P.val * Uᴴ, hN P.val P.property⟩
    have hf : Function.Injective f := by
      intro P Q h
      apply Subtype.ext
      exact conjugation_injective U hU (congrArg Subtype.val h)
    have hs := Finite.surjective_of_injective hf
    intro P hP
    obtain ⟨Q, hQ⟩ := hs ⟨P, hP⟩
    have he : U * Q.val * Uᴴ = P := congrArg Subtype.val hQ
    have hleft : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    rw [← he]
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hleft, one_mul,
      ← Matrix.mul_assoc _ Uᴴ U, hleft, mul_one] using Q.property
  have expectation_conjugation {n : ℕ} (U P : Operator n) (ψ : State n) :
      expectation (U *ᵥ ψ) P = expectation ψ (Uᴴ * P * U) := by
    simp only [expectation, Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have conjugated_word_signed {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ)
      (hN : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n)
      (p : Fin n → Pauli) :
      ∃ (q : Fin n → Pauli) (s : ℂ), (s = 1 ∨ s = -1) ∧
        Uᴴ * wordOp p * U = s • wordOp q := by
    have hmem : wordOp p ∈ pauliGroup n := ⟨0, p, by simp⟩
    obtain ⟨c, q, hq⟩ := normalizer_inverse U hU hN (wordOp p) hmem
    have hherm : (Uᴴ * wordOp p * U)ᴴ = Uᴴ * wordOp p * U := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, word_star]
    rw [hq] at hherm
    have hstar : star (Complex.I ^ c.val) • wordOp q = Complex.I ^ c.val • wordOp q := by
      simpa [Matrix.conjTranspose_smul, word_star] using hherm
    have hnz : star (Complex.I ^ c.val) ≠ 0 := by
      simp only [map_pow, Complex.star_def]
      exact pow_ne_zero _ (by simp)
    have he := (word_signed_unique q q _ _ hnz hstar).2
    refine ⟨q, Complex.I ^ c.val, ?_, hq⟩
    fin_cases c <;> norm_num at he ⊢ <;>
      have hi := congrArg Complex.im he <;> norm_num at hi
  have normalizer_word_permutation {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ)
      (hN : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n) :
      ∃ e : Equiv.Perm (Fin n → Pauli), ∀ p,
        ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ Uᴴ * wordOp p * U = s • wordOp (e p) := by
    choose q s hs hq using (conjugated_word_signed U hU hN)
    have hright : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hsne (p : Fin n → Pauli) : s p ≠ 0 := by rcases hs p with h | h <;> rw [h] <;> norm_num
    have hqinj : Function.Injective q := by
      intro p r h
      have he : s r • (Uᴴ * wordOp p * U) = s p • (Uᴴ * wordOp r * U) := by
        rw [hq p, hq r, h, smul_smul, smul_smul, mul_comm]
      have he' := congrArg (fun A : Operator n => U * A * Uᴴ) he
      have hp : U * (s r • (Uᴴ * wordOp p * U)) * Uᴴ = s r • wordOp p := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc U Uᴴ, hright, one_mul, ← Matrix.mul_assoc _ U Uᴴ,
          hright, mul_one]
      have hr : U * (s p • (Uᴴ * wordOp r * U)) * Uᴴ = s p • wordOp r := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc U Uᴴ, hright, one_mul, ← Matrix.mul_assoc _ U Uᴴ,
          hright, mul_one]
      rw [hp, hr] at he'
      exact (word_signed_unique p r _ _ (hsne r) he').1
    let e := Equiv.ofBijective q ⟨hqinj, Finite.surjective_of_injective hqinj⟩
    exact ⟨e, fun p => ⟨s p, hs p, hq p⟩⟩
  have expectation_smul {n : ℕ} (ψ : State n) (P : Operator n) (s : ℂ) :
      expectation ψ (s • P) = s * expectation ψ P := by
    simp [expectation, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have normalizer_count {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ)
      (hN : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n)
      (ψ : State n) : pauliUnitCount (U *ᵥ ψ) = pauliUnitCount ψ := by
    obtain ⟨e, he⟩ := normalizer_word_permutation U hU hN
    have hn (p : Fin n → Pauli) :
        ‖expectation (U *ᵥ ψ) (wordOp p)‖ = ‖expectation ψ (wordOp (e p))‖ := by
      obtain ⟨s, hs, hp⟩ := he p
      rw [expectation_conjugation, hp, expectation_smul, norm_mul]
      rcases hs with rfl | rfl <;> simp
    unfold pauliUnitCount
    simp_rw [hn]
    apply Finset.card_bij (fun p _ => e p)
    · intro p hp
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
    · intro p hp q hq heq
      exact e.injective heq
    · intro q hq
      refine ⟨e.symm q, ?_, by simp⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, e.apply_symm_apply] using hq
  have normalizer_denominator {n : ℕ} (U : Operator n)
      (hU : U ∈ Matrix.unitaryGroup ((Fin n → Fin 2)) ℂ)
      (hN : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n)
      (B : ℕ) (ψ : State n) (h : HasIntegerPauliDenominator B ψ) :
      HasIntegerPauliDenominator B (U *ᵥ ψ) := by
    obtain ⟨e, he⟩ := normalizer_word_permutation U hU hN
    intro p
    obtain ⟨s, hs, hp⟩ := he p
    obtain ⟨a, ha⟩ := h (e p)
    rw [expectation_conjugation, hp, expectation_smul]
    rcases hs with rfl | rfl
    · exact ⟨a, by simpa using ha⟩
    · refine ⟨-a, ?_⟩
      simpa [mul_neg, neg_mul] using congrArg Neg.neg ha
  have primitive_purity_unit (d a b c : ℤ) (hd : 0 < d)
      (hp : a^2 + b^2 + c^2 = d^2)
      (hprimitive : Primitive (![d, a, b, c] : Fin 4 → ℤ)) :
      d = 1 ↔ |a| = d ∨ |b| = d ∨ |c| = d := by
    constructor
    · intro hd1
      subst d
      have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b, sq_nonneg c]
      have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg c]
      have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
      rcases ha with ⟨hal, hau⟩
      rcases hb with ⟨hbl, hbu⟩
      rcases hc with ⟨hcl, hcu⟩
      interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at hp <;> norm_num
    · intro hu
      have hdiv (u v w : ℤ) (he : u^2 + v^2 + w^2 = d^2) (hh : |u| = d) :
          d ∣ u ∧ v = 0 ∧ w = 0 := by
        have husq : u^2 = d^2 := by rw [← hh, sq_abs]
        have hv : v = 0 := by nlinarith [sq_nonneg w]
        have hw : w = 0 := by nlinarith [sq_nonneg v]
        refine ⟨?_, hv, hw⟩
        rcases le_total 0 u with h | h
        · rw [abs_of_nonneg h] at hh
          rw [hh]
        · rw [abs_of_nonpos h] at hh
          have he' : u = -d := by omega
          rw [he']
          exact dvd_neg.mpr dvd_rfl
      have hda : d ∣ a ∧ d ∣ b ∧ d ∣ c := by
        rcases hu with hu | hu | hu
        · obtain ⟨hdu, rfl, rfl⟩ := hdiv a b c hp hu
          simp [hdu]
        · obtain ⟨hdu, ha, hc⟩ := hdiv b a c (by nlinarith [hp]) hu
          simp [ha, hc, hdu]
        · obtain ⟨hdu, ha, hb⟩ := hdiv c a b (by nlinarith [hp]) hu
          simp [ha, hb, hdu]
      have hd1 : d ∣ (1 : ℤ) := by
        apply primitive_divisor (![d, a, b, c] : Fin 4 → ℤ) hprimitive d 1
        intro i
        fin_cases i
        · simp
        · simpa using hda.1
        · simpa using hda.2.1
        · simpa using hda.2.2
      have hle := Int.natAbs_le_of_dvd_ne_zero hd1 (by norm_num)
      have hle' : d ≤ 1 := by
        have h : (d.natAbs : ℤ) ≤ 1 := by exact_mod_cast (show d.natAbs ≤ 1 by simpa using hle)
        simpa [Int.natCast_natAbs, abs_of_pos hd] using h
      omega
  have denominator_product_lower_bound {n : ℕ} (d : Fin n → ℕ)
      (hd : ∀ j, d j = 1 ∨ 3 ≤ d j) :
      3 ^ (n - (Finset.univ.filter (fun j => d j = 1)).card) ≤ ∏ j, d j := by
    let S := Finset.univ.filter (fun j => d j = 1)
    let T := Finset.univ.filter (fun j => d j ≠ 1)
    have hsum : S.card + T.card = n := by
      simpa [S, T] using (Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun j : Fin n => d j = 1))
    have hS : ∏ j ∈ S, d j = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hT : 3 ^ T.card ≤ ∏ j ∈ T, d j := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun j hj => by norm_num)
      intro j hj
      rcases hd j with h | h
      · exact False.elim ((Finset.mem_filter.mp hj).2 h)
      · exact h
    have hprod : (∏ j ∈ S, d j) * ∏ j ∈ T, d j = ∏ j, d j := by
      exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => d j = 1) d
    rw [hS, one_mul] at hprod
    have hcard : T.card = n - S.card := by omega
    simpa only [hcard, hprod] using hT
  have arithmetic_obstruction (n k s D : ℕ)
      (hn : 2 < n) (hk : 0 < k) (hkn : k < n)
      (hN : 2 ^ s ≤ if n = 2 * k then 4 else 2)
      (hD : 3 ^ (n - s) ≤ D) (hDB : D ≤ n.choose k) : False := by
    have hs2 : s ≤ 2 := by
      have hpow : 2 ^ s ≤ 2 ^ 2 := by
        split_ifs at hN <;> norm_num at hN ⊢ <;> omega
      exact (pow_le_pow_iff_right₀ (by omega : (1 : ℕ) < 2)).mp hpow
    by_cases hn3 : n = 3
    · subst n
      have hnot : 3 ≠ 2 * k := by omega
      rw [if_neg hnot] at hN
      have hs1 : s ≤ 1 := by
        have hpow : 2 ^ s ≤ 2 ^ 1 := by simpa using hN
        exact (pow_le_pow_iff_right₀ (by omega : (1 : ℕ) < 2)).mp hpow
      have h9 : 9 ≤ 3 ^ (3 - s) := by
        have := pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 3) (show 2 ≤ 3 - s by omega)
        norm_num at this
        exact this
      have hB : Nat.choose 3 k ≤ 3 := by
        have h := Nat.choose_le_middle k 3
        norm_num [Nat.choose] at h
        exact h
      omega
    · have hn4 : 4 ≤ n := by omega
      have hpow := pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 3)
        (show n - 2 ≤ n - s by omega)
      have hlt := choose_lt_three_pow n k hn4
      omega
  have product_expectation {n : ℕ} (φ : Fin n → Fin 2 → ℂ)
      (p : Fin n → Pauli) :
      expectation (productVector φ) (wordOp p) = ∏ j, (bloch (φ j) (p j) : ℂ) := by
    rw [wordOp, tensor_expectation]
    apply Finset.prod_congr rfl
    intro j _
    exact local_expectation (φ j) (p j)
  have local_global_expectation {n : ℕ} (φ : Fin n → Fin 2 → ℂ)
      (hφ : ∀ j, LocalNormalized (φ j)) (j : Fin n) (p : Pauli) :
      expectation (productVector φ) (wordOp (Function.update (fun _ => Pauli.I) j p)) =
        (bloch (φ j) p : ℂ) := by
    rw [product_expectation]
    rw [Finset.prod_eq_single j]
    · simp
    · intro l hl hlj
      rw [Function.update_of_ne hlj]
      have he : bloch (φ l) .I = 1 := by
        simpa [LocalNormalized, Fin.sum_univ_two, bloch] using hφ l
      simp [he]
    · simp
  have product_local_rational {n : ℕ} (B : ℕ)
      (φ : Fin n → Fin 2 → ℂ) (hφ : ∀ j, LocalNormalized (φ j))
      (hB : HasIntegerPauliDenominator B (productVector φ)) (j : Fin n) (p : Pauli) :
      ∃ a : ℤ, (B : ℝ) * bloch (φ j) p = (a : ℝ) := by
    obtain ⟨a, ha⟩ := hB (Function.update (fun _ => Pauli.I) j p)
    rw [local_global_expectation φ hφ j p] at ha
    refine ⟨a, ?_⟩
    have he := congrArg Complex.re ha
    simpa using he
  have product_primitive_data {n : ℕ} (B : ℕ) (hBpos : 0 < B)
      (φ : Fin n → Fin 2 → ℂ) (hφ : ∀ j, LocalNormalized (φ j))
      (hB : HasIntegerPauliDenominator B (productVector φ)) :
      ∃ (d : Fin n → ℤ) (a : Fin n → Fin 4 → ℤ),
        (∀ j, 0 < d j) ∧ (∀ j, Primitive (a j)) ∧ (∀ j, a j 0 = d j) ∧
        (∀ j i, bloch (φ j) (sigmaOfDigit i.val) = (a j i : ℝ) / (d j : ℝ)) ∧
        (∀ j, (a j 1)^2 + (a j 2)^2 + (a j 3)^2 = (d j)^2) := by
    have hx (j : Fin n) :
        ∃ (d : ℤ) (a : Fin 4 → ℤ), 0 < d ∧ Primitive a ∧ a 0 = d ∧
          ∀ i, bloch (φ j) (sigmaOfDigit i.val) = (a i : ℝ) / (d : ℝ) := by
      apply primitive_coordinates B hBpos (fun i => bloch (φ j) (sigmaOfDigit i.val))
      · simpa [sigmaOfDigit, LocalNormalized, Fin.sum_univ_two, bloch] using hφ j
      · intro i
        exact product_local_rational B φ hφ hB j (sigmaOfDigit i.val)
    choose d a hd hprim hzero hr using hx
    refine ⟨d, a, hd, hprim, hzero, hr, ?_⟩
    intro j
    apply primitive_purity (d j) (a j) (hd j) (fun i => bloch (φ j) (sigmaOfDigit i.val)) (hr j)
    simpa [sigmaOfDigit] using bloch_purity (φ j) (hφ j)
  have product_denominator_divides {n : ℕ} (B : ℕ)
      (φ : Fin n → Fin 2 → ℂ) (hB : HasIntegerPauliDenominator B (productVector φ))
      (d : Fin n → ℤ) (a : Fin n → Fin 4 → ℤ)
      (hd : ∀ j, 0 < d j) (ha : ∀ j, Primitive (a j))
      (hr : ∀ j i, bloch (φ j) (sigmaOfDigit i.val) = (a j i : ℝ) / (d j : ℝ)) :
      (∏ j, d j) ∣ (B : ℤ) := by
    apply primitive_product_denominator a ha d (B : ℤ)
    intro x
    obtain ⟨z, hz⟩ := hB (fun j => sigmaOfDigit (x j).val)
    rw [product_expectation] at hz
    have he := congrArg Complex.re hz
    have hrprod : (∏ j, (bloch (φ j) (sigmaOfDigit (x j).val) : ℂ)) =
        ((∏ j, bloch (φ j) (sigmaOfDigit (x j).val) : ℝ) : ℂ) := by
      exact (map_prod Complex.ofRealHom _ _).symm
    rw [hrprod] at he
    have heR : (B : ℝ) * (∏ j, bloch (φ j) (sigmaOfDigit (x j).val)) = (z : ℝ) := by
      simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, zero_mul,
        mul_zero, add_zero, sub_zero] using he
    simp_rw [hr, Finset.prod_div_distrib] at heR
    have hD : (∏ j, (d j : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact_mod_cast ne_of_gt (hd j)
    have heR' : (B : ℝ) * (∏ j, (a j (x j) : ℝ)) =
        (∏ j, (d j : ℝ)) * (z : ℝ) := by
      field_simp [hD] at heR
      nlinarith [heR]
    refine ⟨z, ?_⟩
    exact_mod_cast heR'
  have local_unit_from_denominator_one (φ : Fin 2 → ℂ) (d : ℤ)
      (a : Fin 4 → ℤ) (hd : 0 < d) (hprim : Primitive a) (hzero : a 0 = d)
      (hr : ∀ i, bloch φ (sigmaOfDigit i.val) = (a i : ℝ) / (d : ℝ))
      (hp : (a 1)^2 + (a 2)^2 + (a 3)^2 = d^2) (hd1 : d = 1) :
      ∃ p : Pauli, p ≠ .I ∧ |bloch φ p| = 1 := by
    have ha : a = (![d, a 1, a 2, a 3] : Fin 4 → ℤ) := by
      ext i
      fin_cases i <;> simp [hzero]
    have hu := (primitive_purity_unit d (a 1) (a 2) (a 3) hd hp (by rwa [← ha])).mp hd1
    have hunit (i : Fin 4) (hi : |a i| = d) :
        |bloch φ (sigmaOfDigit i.val)| = 1 := by
      rw [hr, hd1, Int.cast_one, div_one]
      have h : |(a i : ℝ)| = 1 := by exact_mod_cast (hi.trans hd1)
      exact h
    rcases hu with hu | hu | hu
    · exact ⟨.X, by decide, by simpa [sigmaOfDigit] using hunit 1 hu⟩
    · exact ⟨.Y, by decide, by simpa [sigmaOfDigit] using hunit 2 hu⟩
    · exact ⟨.Z, by decide, by simpa [sigmaOfDigit] using hunit 3 hu⟩
  have product_count_lower {n : ℕ} (φ : Fin n → Fin 2 → ℂ)
      (hφ : ∀ j, LocalNormalized (φ j)) (d : Fin n → ℤ)
      (hu : ∀ j, d j = 1 → ∃ p : Pauli, p ≠ .I ∧ |bloch (φ j) p| = 1) :
      2 ^ (Finset.univ.filter (fun j => d j = 1)).card ≤ pauliUnitCount (productVector φ) := by
    classical
    have hx (j : Fin n) : ∃ p : Pauli, d j = 1 → p ≠ .I ∧ |bloch (φ j) p| = 1 := by
      by_cases h : d j = 1
      · obtain ⟨p, hp, hb⟩ := hu j h
        exact ⟨p, fun _ => ⟨hp, hb⟩⟩
      · exact ⟨.I, fun h' => False.elim (h h')⟩
    choose p hp using hx
    let A (j : Fin n) : Finset Pauli := if d j = 1 then {.I, p j} else {.I}
    have hcard (j : Fin n) : (A j).card = if d j = 1 then 2 else 1 := by
      by_cases hj : d j = 1
      · simp [A, hj, Ne.symm (hp j hj).1]
      · simp [A, hj]
    have hsize : (Fintype.piFinset A).card =
        2 ^ (Finset.univ.filter (fun j => d j = 1)).card := by
      rw [Fintype.card_piFinset]
      simp_rw [hcard]
      rw [← Finset.prod_filter]
      simp
    have hsub : Fintype.piFinset A ⊆
        Finset.univ.filter (fun q : Fin n → Pauli =>
          ‖expectation (productVector φ) (wordOp q)‖ = 1) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [product_expectation, norm_prod]
      apply Finset.prod_eq_one
      intro j _
      have hj := Fintype.mem_piFinset.mp hq j
      have hI : bloch (φ j) .I = 1 := by
        simpa [LocalNormalized, Fin.sum_univ_two, bloch] using hφ j
      by_cases hdj : d j = 1
      · simp only [A, if_pos hdj, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj
        · rw [hj, hI]; simp
        · rw [hj, Complex.norm_real, Real.norm_eq_abs]
          exact (hp j hdj).2
      · have hqj : q j = .I := by simpa [A, hdj] using hj
        rw [hqj, hI]; simp
    rw [← hsize]
    exact Finset.card_le_card hsub
  have product_certificate {n : ℕ} (B : ℕ) (hBpos : 0 < B)
      (φ : Fin n → Fin 2 → ℂ) (hφ : ∀ j, LocalNormalized (φ j))
      (hB : HasIntegerPauliDenominator B (productVector φ)) :
      ∃ d : Fin n → ℕ,
        (∀ j, d j = 1 ∨ 3 ≤ d j) ∧
        (∏ j, d j) ∣ B ∧
        2 ^ (Finset.univ.filter (fun j => d j = 1)).card ≤ pauliUnitCount (productVector φ) := by
    obtain ⟨d, a, hd, ha, hzero, hr, hp⟩ := product_primitive_data B hBpos φ hφ hB
    have havec (j : Fin n) : a j = (![d j, a j 1, a j 2, a j 3] : Fin 4 → ℤ) := by
      ext i
      fin_cases i <;> simp [hzero]
    have hp4 (j : Fin n) : Primitive (![d j, a j 1, a j 2, a j 3] : Fin 4 → ℤ) := by
      rw [← havec j]
      exact ha j
    have hsize (j : Fin n) : d j = 1 ∨ 3 ≤ d j := by
      by_cases h : d j = 1
      · exact Or.inl h
      · exact Or.inr (primitive_denominator_at_least_three _ _ _ _ (hd j) (hp j) (hp4 j) h)
    have hdiv := product_denominator_divides B φ hB d a hd ha hr
    let dN : Fin n → ℕ := fun j => (d j).toNat
    have hdN (j : Fin n) : (dN j : ℤ) = d j := Int.toNat_of_nonneg (hd j).le
    have heq1 (j : Fin n) : dN j = 1 ↔ d j = 1 := by
      constructor
      · intro h
        have he : (dN j : ℤ) = 1 := by exact_mod_cast h
        rwa [hdN j] at he
      · intro h
        have he : (dN j : ℤ) = 1 := by rw [hdN j, h]
        exact_mod_cast he
    refine ⟨dN, ?_, ?_, ?_⟩
    · intro j
      rcases hsize j with h | h
      · exact Or.inl ((heq1 j).mpr h)
      · exact Or.inr (by exact_mod_cast (show (3 : ℤ) ≤ (dN j : ℤ) by rw [hdN j]; exact h))
    · have hprod : ((∏ j, dN j : ℕ) : ℤ) = ∏ j, d j := by
        push_cast
        apply Finset.prod_congr rfl
        intro j _
        exact hdN j
      rw [← hprod] at hdiv
      exact_mod_cast hdiv
    · have hunit (j : Fin n) (hj : d j = 1) :
          ∃ p : Pauli, p ≠ .I ∧ |bloch (φ j) p| = 1 :=
        local_unit_from_denominator_one (φ j) (d j) (a j) (hd j) (ha j)
          (hzero j) (hr j) (hp j) hj
      have hcount := product_count_lower φ hφ d hunit
      have hfilter : Finset.univ.filter (fun j => dN j = 1) =
          Finset.univ.filter (fun j => d j = 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq1]
      rw [hfilter]
      exact hcount
  intro n k hn hk hkn U hU φ hφ hproduct
  rcases hU with ⟨hSU, hnormalizer⟩
  have hunit := (Matrix.mem_specialUnitaryGroup_iff.mp hSU).1
  have group_model (m : ℕ) : pauliGroup m = pauliMatrices m := by
    ext P
    constructor
    · rintro ⟨c, p, rfl⟩
      have hs := word_sq p
      let w : (Operator m)ˣ := ⟨wordOp p, wordOp p, hs, hs⟩
      have hc : Complex.I ^ c.val ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
      let u : (Operator m)ˣ :=
        Units.map (algebraMap ℂ (Operator m)).toMonoidHom (Units.mk0 _ hc) * w
      have hu : (u : Operator m) = Complex.I ^ c.val • wordOp p := by
        simp [u, w, Algebra.algebraMap_eq_smul_one]
      refine ⟨u, ?_, hu⟩
      refine ⟨Complex.I ^ c.val, ?_, p, hu⟩
      fin_cases c <;> norm_num [D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.Phase]
    · rintro ⟨u, ⟨c, hc, p, hu⟩, rfl⟩
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0, p, by simpa using hu⟩
      · exact ⟨2, p, by norm_num; simpa only [neg_one_smul] using hu⟩
      · exact ⟨1, p, by simpa using hu⟩
      · exact ⟨3, p, by norm_num; simpa only [neg_smul] using hu⟩
  have hnormalizer' : ∀ P ∈ pauliGroup n, U * P * Uᴴ ∈ pauliGroup n := by
    simpa only [group_model n] using hnormalizer
  obtain ⟨dicke_denominator, dicke_count_upper⟩ := dicke_certificate n k hn hk hkn
  have hBpos := Nat.choose_pos hkn.le
  have hden := normalizer_denominator U hunit hnormalizer' (n.choose k) (dicke n k)
    dicke_denominator
  rw [hproduct] at hden
  obtain ⟨d, hd, hdiv, hcount⟩ := product_certificate (n.choose k) hBpos φ hφ hden
  have hN := normalizer_count U hunit hnormalizer' (dicke n k)
  rw [hproduct] at hN
  have hNbound := dicke_count_upper
  rw [← hN] at hNbound
  have hD : 3 ^ (n - (Finset.univ.filter (fun j => d j = 1)).card) ≤ ∏ j, d j :=
    denominator_product_lower_bound d hd
  have hDB : (∏ j, d j) ≤ n.choose k := Nat.le_of_dvd hBpos hdiv
  exact arithmetic_obstruction n k _ _ hn hk hkn (hcount.trans hNbound) hD hDB

end D5.S3.Quantum.Information.DickeCliffordProductObstruction
