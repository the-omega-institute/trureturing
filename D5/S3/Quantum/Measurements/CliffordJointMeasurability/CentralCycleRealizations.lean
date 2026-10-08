/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The central loop involution normalizes arbitrary even-cycle realizations. -/
/-
proof_shape: cycle_majorana_extension: content
escape_witness: cycle_majorana_extension
admission_basis: escape-witness
Direct frozen dependencies: none on the baseline; supporting lane modules are first-freeze dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: pathWord_step: bind-only; consumer: pathWord_generator_relation
proof_shape: wordSign_step: bind-only; consumer: pathWord_generator_relation
proof_shape: pathWord_generator_relation: content; consumer: pathWord_square
proof_shape: pathWord_square: content; consumer: full_cycle_loop_square
proof_shape: pathMajorana_word: bind-only; consumer: antiperiodic_closing_bond
proof_shape: pathWord_star: content; consumer: full_cycle_loop_star
proof_shape: closingPrefixSign_step: bind-only; consumer: pathWord_closing_relation
proof_shape: pathWord_closing_relation: content; consumer: full_cycle_loop_central
proof_shape: full_cycle_loop_central: content; consumer: loop_normalization
proof_shape: full_cycle_loop_square: content; consumer: loop_normalization
proof_shape: full_cycle_loop_star: content; consumer: normalizedLoop_star
proof_shape: loopSign_square: bind-only; consumer: loop_normalization
proof_shape: loop_normalization: content; consumer: realization_cycle_loop
proof_shape: normalizedLoop_star: bind-only; consumer: realization_cycle_loop
proof_shape: pathWord_seed_relation: content; consumer: antiperiodic_closing_bond
proof_shape: antiperiodic_closing_bond: content; consumer: cycle_majorana_extension
proof_shape: sectorProjector_hermitian: bind-only; consumer: central_relabel_parent
proof_shape: sectorProjector_square: bind-only; consumer: central_relabel_parent
proof_shape: sectorProjector_sum: bind-only; consumer: central_relabel_parent
proof_shape: sector_compression_sum: bind-only; consumer: central_relabel_parent
proof_shape: sector_compression_signed: bind-only; consumer: central_relabel_parent
proof_shape: sectorLabel_sign: bind-only; consumer: central_relabel_parent
proof_shape: central_relabel_parent: bind-only; consumer: cycle_JM_threshold
proof_shape: natural_cycle_adj: bind-only; consumer: cycle_prefix_relations
proof_shape: cycle_prefix_relations: bind-only; consumer: realization_cycle_loop
proof_shape: realization_cycle_loop: content; consumer: cycle_majorana_extension
proof_shape: pathWord_liftPath: bind-only; consumer: cycle_majorana_extension
-/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.CentralCycleRealizations
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
def pathWord (A : ℕ → R) (k : ℕ) : R := ((List.range k).map A).prod
private lemma pathWord_step (A : ℕ → R) (k : ℕ) : pathWord A (k+1)=pathWord A k*A k := by
  simp [List.range_succ, pathWord, List.range_succ]
private def wordSign (k j : ℕ) : ℂ :=
  if j = 0 then (if k ≤ 1 then 1 else -1) else prefixSign k j
private lemma wordSign_step (k j : ℕ) :
    wordSign (k + 1) j = wordSign k j * generatorSign k j := by
  unfold wordSign prefixSign generatorSign
  split_ifs <;> norm_num <;> omega
private lemma pathWord_generator_relation (m : ℕ) (A : ℕ → R)
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k)) :
    ∀ k, k ≤ m → ∀ j, j < m →
      pathWord A k * A j = wordSign k j • (A j * pathWord A k) := by
  intro k
  induction k with
  | zero => intro hk j hj; by_cases hj0 : j = 0 <;> simp [List.range_succ, pathWord, wordSign, prefixSign, hj0]
  | succ k ih =>
    intro hk j hj
    rw [pathWord_step, wordSign_step]
    exact signed_product _ _ _ _ _ (ih (by omega) j hj) (hA k j (by omega) hj)
private lemma pathWord_square (m : ℕ) (A : ℕ → R)
    (hsq : ∀ k, k < m → A k * A k = 1)
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k)) :
    ∀ k, k ≤ m → pathWord A k * pathWord A k = ((-1 : ℂ) ^ (k - 1)) • (1 : R) := by
  have hrel := pathWord_generator_relation m A hA
  intro k
  induction k with
  | zero => intro _; simp [List.range_succ, pathWord]
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k; simp [List.range_succ, pathWord, hsq 0 (by omega)]
    · have hanti : pathWord A k * A k = -(A k * pathWord A k) := by
        simpa [wordSign, prefixSign, hk0] using hrel k (by omega) k (by omega)
      have hp : (pathWord A k * A k) * (pathWord A k * A k) =
          -(pathWord A k * pathWord A k) := by
        calc
          (pathWord A k * A k) * (pathWord A k * A k) =
              -(A k * (pathWord A k * pathWord A k) * A k) := by
            calc
              _ = (pathWord A k * A k) * pathWord A k * A k := by noncomm_ring
              _ = _ := by rw [hanti]; noncomm_ring
          _ = -(pathWord A k * pathWord A k) := by rw [ih (by omega)]; simp [hsq k (by omega)]
      rw [pathWord_step, hp, ih (by omega)]
      have hpow : (-1 : ℂ) ^ k = -((-1 : ℂ) ^ (k - 1)) := by
        calc
          (-1 : ℂ) ^ k = (-1 : ℂ) ^ ((k - 1) + 1) := by congr 1; omega
          _ = _ := by rw [pow_succ]; ring
      simp only [Nat.add_sub_cancel, hpow, neg_smul]
private lemma pathMajorana_word (A : ℕ → R) (q : R) (k : ℕ) :
    pathMajorana A q k = (-Complex.I) ^ k • (q * pathWord A k) := by
  induction k with
  | zero => simp [pathMajorana, pathWord]
  | succ k ih =>
    rw [pathMajorana, ih, smul_mul_assoc, smul_smul, pow_succ, pathWord_step, mul_assoc]
    rw [mul_comm ((-Complex.I)^k) (-Complex.I)]
section Star
variable [StarRing R] [StarModule ℂ R]
private lemma pathWord_star (m : ℕ) (A : ℕ → R)
    (hstar : ∀ k, k < m → star (A k) = A k)
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k)) :
    ∀ k, k ≤ m → star (pathWord A k) = ((-1 : ℂ) ^ (k - 1)) • pathWord A k := by
  have hrel := pathWord_generator_relation m A hA
  intro k
  induction k with
  | zero => intro _; simp [List.range_succ, pathWord]
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k; simp [List.range_succ, pathWord, hstar 0 (by omega)]
    · have hanti : A k * pathWord A k = -(pathWord A k * A k) := by
        have h := hrel k (by omega) k (by omega)
        simpa [wordSign, prefixSign, hk0] using congrArg Neg.neg h.symm
      have hpow : (-1 : ℂ) ^ k = -((-1 : ℂ) ^ (k - 1)) := by
        calc
          (-1 : ℂ) ^ k = (-1 : ℂ) ^ ((k - 1) + 1) := by congr 1; omega
          _ = _ := by rw [pow_succ]; ring
      rw [pathWord_step, star_mul, hstar k (by omega), ih (by omega), mul_smul_comm,
        hanti, smul_neg, ← neg_smul, Nat.add_sub_cancel, hpow]
end Star
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
private def closingSign (m k : ℕ) : ℂ := if k = 0 ∨ k + 1 = m then -1 else 1
private def closingPrefixSign (m k : ℕ) : ℂ := if k = 0 ∨ k = m then 1 else -1
private lemma closingPrefixSign_step (m k : ℕ) (hm : 2 ≤ m) (hk : k < m) :
    closingPrefixSign m (k+1) = closingPrefixSign m k * closingSign m k := by
  unfold closingPrefixSign closingSign
  by_cases h0 : k = 0
  · subst k
    simp [show m ≠ 0 by omega, show 1 ≠ m by omega]
  · have hkm : k ≠ m := by omega
    by_cases hl : k+1 = m
    · simp [h0, hkm, hl]
    · simp [h0, hkm, hl]
private lemma pathWord_closing_relation (m : ℕ) (hm : 2 ≤ m) (A : ℕ → R) (B : R)
    (hB : ∀ k, k < m → A k * B = closingSign m k • (B * A k)) :
    ∀ k, k ≤ m → pathWord A k * B = closingPrefixSign m k • (B * pathWord A k) := by
  intro k
  induction k with
  | zero => intro _; simp [List.range_succ, pathWord, closingPrefixSign]
  | succ k ih =>
    intro hk
    rw [pathWord_step, closingPrefixSign_step m k hm (by omega)]
    exact signed_product _ _ _ _ _ (ih (by omega)) (hB k (by omega))
private lemma full_cycle_loop_central (m : ℕ) (hm : 3 ≤ m) (A : ℕ → R) (B : R)
    (hA : ∀ k j, k < m → j < m → A k * A j = generatorSign k j • (A j * A k))
    (hB : ∀ k, k < m → A k * B = closingSign m k • (B * A k)) :
    (pathWord A m * B) * B = B * (pathWord A m * B) ∧
    ∀ j, j < m → (pathWord A m * B) * A j = A j * (pathWord A m * B) := by
  have hQ := pathWord_generator_relation m A hA
  have hQB : pathWord A m * B = B * pathWord A m := by
    simpa [closingPrefixSign] using pathWord_closing_relation m (by omega) A B hB m le_rfl
  constructor
  · rw [← mul_assoc, hQB]
  · intro j hj
    have hsign : wordSign m j = closingSign m j := by
      unfold wordSign prefixSign closingSign
      split_ifs <;> norm_num <;> omega
    have hBj : B * A j = closingSign m j • (A j * B) := by
      have h := hB j hj
      unfold closingSign at *
      split_ifs at *
      · simpa using congrArg Neg.neg h.symm
      · simpa using h.symm
    have hsign2 : closingSign m j * closingSign m j = 1 := by
      unfold closingSign
      split_ifs <;> norm_num
    rw [mul_assoc, hBj, mul_smul_comm, ← mul_assoc, hQ m le_rfl j hj,
      smul_mul_assoc, smul_smul, hsign, hsign2, one_smul, mul_assoc]
private lemma full_cycle_loop_square (n : ℕ) (A : ℕ → R) (B : R)
    (hsq : ∀ k, k < 2*n+1 → A k * A k = 1) (hBsq : B * B = 1)
    (hA : ∀ k j, k < 2*n+1 → j < 2*n+1 → A k * A j = generatorSign k j • (A j * A k))
    (hB : ∀ k, k < 2*n+1 → A k * B = closingSign (2*n+1) k • (B * A k))
    (hn : 1 ≤ n) : (pathWord A (2*n+1) * B) * (pathWord A (2*n+1) * B) = 1 := by
  have hQB : pathWord A (2*n+1) * B = B * pathWord A (2*n+1) := by
    simpa [closingPrefixSign] using pathWord_closing_relation (2*n+1) (by omega) A B hB (2*n+1) le_rfl
  have hQsq : pathWord A (2*n+1) * pathWord A (2*n+1) = 1 := by
    have h := pathWord_square (2*n+1) A hsq hA (2*n+1) le_rfl
    simpa [pow_mul] using h
  calc
    (pathWord A (2*n+1) * B) * (pathWord A (2*n+1) * B) =
        pathWord A (2*n+1) * (B * pathWord A (2*n+1)) * B := by noncomm_ring
    _ = (pathWord A (2*n+1) * pathWord A (2*n+1)) * (B * B) := by rw [← hQB]; noncomm_ring
    _ = 1 := by rw [hQsq, hBsq, mul_one]
section Star
variable [StarRing R] [StarModule ℂ R]
private lemma full_cycle_loop_star (n : ℕ) (A : ℕ → R) (B : R)
    (hstar : ∀ k, k < 2*n+1 → star (A k) = A k) (hBs : star B = B)
    (hA : ∀ k j, k < 2*n+1 → j < 2*n+1 → A k * A j = generatorSign k j • (A j * A k))
    (hB : ∀ k, k < 2*n+1 → A k * B = closingSign (2*n+1) k • (B * A k))
    (hn : 1 ≤ n) : star (pathWord A (2*n+1) * B) = pathWord A (2*n+1) * B := by
  have hQB : pathWord A (2*n+1) * B = B * pathWord A (2*n+1) := by
    simpa [closingPrefixSign] using pathWord_closing_relation (2*n+1) (by omega) A B hB (2*n+1) le_rfl
  have hQs : star (pathWord A (2*n+1)) = pathWord A (2*n+1) := by
    have h := pathWord_star (2*n+1) A hstar hA (2*n+1) le_rfl
    simpa [pow_mul] using h
  rw [star_mul, hBs, hQs, ← hQB]
end Star
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
def loopSign (n : ℕ) : ℂ := (-1)^n
def normalizedLoop (n : ℕ) (A : ℕ → R) (B : R) : R :=
  loopSign n • (pathWord A (2*n+1) * B)
private lemma loopSign_square (n : ℕ) : loopSign n * loopSign n = 1 := by
  simp [loopSign, ← mul_pow]
private lemma loop_normalization (n : ℕ) (A : ℕ → R) (B : R)
    (hsq : ∀ k, k < 2*n+1 → A k*A k=1) (hBsq : B*B=1)
    (hA : ∀ k j, k<2*n+1 → j<2*n+1 → A k*A j=generatorSign k j • (A j*A k))
    (hB : ∀ k, k<2*n+1 → A k*B=closingSign (2*n+1) k • (B*A k))
    (hn : 1≤n) :
    let K := normalizedLoop n A B
    K*K=1 ∧ K*B=B*K ∧ (∀ j, j<2*n+1 → K*A j=A j*K) ∧
      pathWord A (2*n+1) * (K*B) = loopSign n • (1:R) ∧
      K*B = loopSign n • pathWord A (2*n+1) := by
  dsimp only
  have hc := full_cycle_loop_central (2*n+1) (by omega) A B hA hB
  have hQsq : pathWord A (2*n+1)*pathWord A (2*n+1)=1 := by
    simpa [pow_mul] using pathWord_square (2*n+1) A hsq hA (2*n+1) le_rfl
  have hclose : normalizedLoop n A B * B = loopSign n • pathWord A (2*n+1) := by
    simp [normalizedLoop, smul_mul_assoc, mul_assoc, hBsq]
  refine ⟨?_, ?_, ?_, ?_, hclose⟩
  · rw [normalizedLoop, smul_mul_smul, loopSign_square,
      full_cycle_loop_square n A B hsq hBsq hA hB hn, one_smul]
  · simp only [normalizedLoop, smul_mul_assoc, mul_smul_comm, hc.1]
  · intro j hj
    simp only [normalizedLoop, smul_mul_assoc, mul_smul_comm, hc.2 j hj]
  · rw [hclose, mul_smul_comm, hQsq]
section Star
variable [StarRing R] [StarModule ℂ R]
private lemma normalizedLoop_star (n : ℕ) (A : ℕ → R) (B : R)
    (hs : ∀ k, k<2*n+1 → star (A k)=A k) (hBs : star B=B)
    (hA : ∀ k j, k<2*n+1 → j<2*n+1 → A k*A j=generatorSign k j • (A j*A k))
    (hB : ∀ k, k<2*n+1 → A k*B=closingSign (2*n+1) k • (B*A k))
    (hn : 1≤n) : star (normalizedLoop n A B)=normalizedLoop n A B := by
  rw [normalizedLoop, star_smul, full_cycle_loop_star n A B hs hBs hA hB hn]
  simp [loopSign]
end Star
private lemma pathWord_seed_relation (A : ℕ → R) (q : R) (m : ℕ)
    (h0 : q*A 0=-(A 0*q)) (hrest : ∀ k, 0<k → k < m → q*A k=A k*q) :
    ∀ k, k ≤ m → q*pathWord A k = (if k = 0 then (1:ℂ) else -1) • (pathWord A k*q) := by
  intro k
  induction k with
  | zero => intro _; simp [List.range_succ, pathWord]
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k; simpa [List.range_succ, pathWord] using h0
    · rw [pathWord_step, ← mul_assoc, ih (by omega)]
      simp only [hk0, ↓reduceIte, Nat.succ_ne_zero, neg_one_smul, neg_mul]
      rw [mul_assoc, hrest k (by omega) (by omega), ← mul_assoc]
private lemma antiperiodic_closing_bond (n : ℕ) (A : ℕ → R) (q : R)
    (hq : q*q=1) (h0 : q*A 0=-(A 0*q))
    (hrest : ∀ k, 0<k → k<2*n+1 → q*A k=A k*q) :
    (-Complex.I) • (pathMajorana A q (2*n+1) * q) =
      loopSign n • pathWord A (2*n+1) := by
  have hrel := pathWord_seed_relation A q (2*n+1) h0 hrest (2*n+1) le_rfl
  have hqQq : q*pathWord A (2*n+1)*q = -pathWord A (2*n+1) := by
    rw [hrel]
    simp [mul_assoc, hq]
  have hp : (-Complex.I) * (-Complex.I)^(2*n+1) = -loopSign n := by
    rw [← pow_succ']
    have he : 2*n+1+1 = 2*(n+1) := by omega
    rw [he, pow_mul]
    norm_num [pow_succ, loopSign, Complex.I_sq]
  rw [pathMajorana_word, smul_mul_assoc, smul_smul, hp, hqQq]
  simp
end
open scoped ComplexOrder
noncomputable section
private def sectorProjector {d : ℕ} (K : (Matrix (Fin d) (Fin d) ℂ)) (s : Bool) : (Matrix (Fin d) (Fin d) ℂ) :=
  (1 / 2 : ℂ) • (1 + outcomeSign s • K)
private lemma sectorProjector_hermitian {d : ℕ} (K : (Matrix (Fin d) (Fin d) ℂ)) (hK : K.IsHermitian) (s : Bool) :
    (sectorProjector K s).IsHermitian := by
  change (sectorProjector K s).conjTranspose = sectorProjector K s
  cases s <;> simp [sectorProjector, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, hK.eq]
private lemma sectorProjector_square {d : ℕ} (K : (Matrix (Fin d) (Fin d) ℂ)) (hK2 : K * K = 1) (s : Bool) :
    sectorProjector K s * sectorProjector K s = sectorProjector K s := by
  cases s <;>
    simp only [sectorProjector, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, Bool.not_true, Bool.not_false, Complex.ofReal_neg, Complex.ofReal_one, Bool.false_eq_true, ↓reduceIte, one_smul,
      neg_one_smul, smul_mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, mul_neg, neg_mul, neg_neg, hK2]
  all_goals module
private lemma sectorProjector_sum {d : ℕ} (K : (Matrix (Fin d) (Fin d) ℂ)) : (∑ s, sectorProjector K s) = 1 := by
  simp only [Fintype.sum_bool, sectorProjector, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, Bool.not_true, Bool.not_false, Complex.ofReal_neg, Complex.ofReal_one, Bool.false_eq_true, ↓reduceIte,
    one_smul, neg_one_smul]
  module
private lemma sector_compression_sum {d : ℕ} (K X : (Matrix (Fin d) (Fin d) ℂ)) (hK2 : K * K = 1)
    (hKX : K * X = X * K) : (∑ s, sectorProjector K s * X * sectorProjector K s) = X := by
  have hKXK : K * X * K = X := by rw [hKX, Matrix.mul_assoc, hK2, Matrix.mul_one]
  simp only [Fintype.sum_bool, sectorProjector, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, Bool.not_true, Bool.not_false, Complex.ofReal_neg, Complex.ofReal_one, Bool.false_eq_true, ↓reduceIte,
    one_smul, neg_one_smul, smul_mul_smul, smul_mul_assoc, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, neg_mul, mul_neg,
    neg_neg, hKXK, ← hKX]
  module
private lemma sector_compression_signed {d : ℕ} (K X : (Matrix (Fin d) (Fin d) ℂ)) (hK2 : K * K = 1)
    (hKX : K * X = X * K) :
    (∑ s, outcomeSign s • (sectorProjector K s * X * sectorProjector K s)) = K * X := by
  have hKXK : K * X * K = X := by rw [hKX, Matrix.mul_assoc, hK2, Matrix.mul_one]
  simp only [Fintype.sum_bool, sectorProjector, outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, Bool.not_true, Bool.not_false, Complex.ofReal_neg, Complex.ofReal_one, Bool.false_eq_true, ↓reduceIte,
    one_smul, neg_one_smul, smul_mul_smul, smul_mul_assoc, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, neg_mul, mul_neg,
    neg_neg, hKXK, ← hKX]
  module
private def sectorLabel {m : ℕ} (v₀ : Fin m) (ω : Bool × (Fin m → Bool)) : Fin m → Bool :=
  Function.update ω.2 v₀ (if ω.1 then ω.2 v₀ else !(ω.2 v₀))
private lemma sectorLabel_sign {m : ℕ} (v₀ v : Fin m) (s : Bool) (a : Fin m → Bool) :
    outcomeSign (sectorLabel v₀ (s,a) v) =
      (if v = v₀ then outcomeSign s else 1) * outcomeSign (a v) := by
  simp only [sectorLabel, Function.update_apply]
  by_cases h : v = v₀ <;> simp only [h, ↓reduceIte]
  · subst v
    cases s <;> cases hv : a v₀ <;> simp [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign, hv]
  · simp
lemma central_relabel_parent {m d : ℕ} (A B : Fin m → (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ)
    (v₀ : Fin m) (K : (Matrix (Fin d) (Fin d) ℂ)) (hK : K.IsHermitian) (hK2 : K * K = 1)
    (hcomm : ∀ v, K * A v = A v * K)
    (hB : ∀ v, B v = if v = v₀ then K * A v else A v)
    (htrA : ∀ v, (A v).trace = 0) (htrB : ∀ v, (B v).trace = 0)
    (hJM : JM B t) : JM A t := by
  classical
  obtain ⟨E, hE, hsum, hmarg⟩ := hJM
  let P : Bool × (Fin m → Bool) → (Matrix (Fin d) (Fin d) ℂ) := fun ω =>
    sectorProjector K ω.1 * E ω.2 * sectorProjector K ω.1
  apply labeled_parent_suffices A t (sectorLabel v₀) P
  · intro ω
    have hp := (hE ω.2).conjTranspose_mul_mul_same (sectorProjector K ω.1)
    simpa only [(sectorProjector_hermitian K hK ω.1).eq] using hp
  · rw [Fintype.sum_prod_type]
    dsimp only [P]
    simp only [← Matrix.sum_mul, ← Matrix.mul_sum, hsum, Matrix.mul_one,
      sectorProjector_square K hK2]
    exact sectorProjector_sum K
  · intro v
    rw [Fintype.sum_prod_type, noisy_eq_of_trace_zero A htrA]
    dsimp only [P]
    simp_rw [sectorLabel_sign, mul_smul]
    have hinside : ∀ s, (∑ a, (if v = v₀ then outcomeSign s else 1) •
        (outcomeSign (a v) • (sectorProjector K s * E a * sectorProjector K s))) =
        (if v = v₀ then outcomeSign s else 1) •
          (sectorProjector K s * ((t : ℂ) • B v) * sectorProjector K s) := by
      intro s
      rw [← Finset.smul_sum]
      have hterm : ∀ a, outcomeSign (a v) • (sectorProjector K s * E a * sectorProjector K s) =
          sectorProjector K s * (outcomeSign (a v) • E a) * sectorProjector K s := by
        intro a
        simp only [Matrix.smul_mul, Matrix.mul_smul]
      simp_rw [hterm]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, parent_signed_marginal B t htrB E hmarg v]
    simp_rw [hinside]
    by_cases hv : v = v₀
    · subst v
      simp only [↓reduceIte]
      simp_rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm (outcomeSign _)]
      rw [← Finset.smul_sum]
      have hKB : K * B v₀ = B v₀ * K := by
        rw [hB v₀, if_pos rfl]
        calc
          K * (K * A v₀) = K * (A v₀ * K) := by rw [hcomm v₀]
          _ = (K * A v₀) * K := (Matrix.mul_assoc _ _ _).symm
      rw [sector_compression_signed K (B v₀) hK2 hKB, hB v₀, if_pos rfl,
        ← Matrix.mul_assoc, hK2, Matrix.one_mul]
    · simp only [hv, ↓reduceIte, one_smul]
      simp_rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [← Finset.smul_sum]
      simp_rw [hB v, if_neg hv]
      rw [sector_compression_sum K (A v) hK2 (hcomm v)]
end
noncomputable section
lemma natural_cycle_adj {M : ℕ} (hM : 2 ≤ M) (u v : Fin M) :
    (SimpleGraph.cycleGraph M).Adj u v ↔
      u.val+1=v.val ∨ v.val+1=u.val ∨
        (u.val=0 ∧ v.val+1=M) ∨ (v.val=0 ∧ u.val+1=M) := by
  rw [SimpleGraph.cycleGraph_adj']
  by_cases he : u=v
  · subst v
    have hw : ¬(u.val=0 ∧ u.val+1=M) := by omega
    simp [hw, Fin.sub_val_of_le (show u≤u by rfl)]
  · by_cases huv : u.val < v.val
    · have hvu : u ≤ v := by exact Nat.le_of_lt huv
      rw [Fin.sub_val_of_le hvu, Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
      have := u.isLt
      have := v.isLt
      omega
    · have hvu : v.val < u.val := by
        have hne : u.val ≠ v.val := by simpa [Fin.ext_iff] using he
        omega
      have huv' : v ≤ u := by exact Nat.le_of_lt hvu
      rw [Fin.sub_val_of_le huv', Fin.val_sub, Nat.mod_eq_of_lt (by omega)]
      have := u.isLt
      have := v.isLt
      omega
def cyclePrefix {d M : ℕ} (A : Fin M → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) : (Matrix (Fin d) (Fin d) ℂ) :=
  if hk : k+1 < M then A ⟨k,by omega⟩ else 1
private lemma cycle_prefix_relations {d m : ℕ} (hm : 2 ≤ m)
    (A : Fin (m+1) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph (m+1)) A) :
    (∀ k j, k < m → j < m → cyclePrefix A k*cyclePrefix A j=
      generatorSign k j • (cyclePrefix A j*cyclePrefix A k)) ∧
    ∀ k, k < m → cyclePrefix A k*A ⟨m,by omega⟩=
      closingSign m k • (A ⟨m,by omega⟩*cyclePrefix A k) := by
  constructor
  · intro k j hk hj
    have hk' : k+1 < m+1 := by omega
    have hj' : j+1 < m+1 := by omega
    simp only [cyclePrefix, dif_pos hk', dif_pos hj']
    by_cases hkj : k=j
    · subst j; simp [generatorSign]
    · have hne : (⟨k,by omega⟩:Fin (m+1))≠⟨j,by omega⟩ := by simpa [Fin.ext_iff] using hkj
      have ha : (SimpleGraph.cycleGraph (m+1)).Adj ⟨k,by omega⟩ ⟨j,by omega⟩ ↔ k+1=j ∨ j+1=k := by
        rw [natural_cycle_adj (by omega)]; simp; omega
      by_cases hadj : k+1=j ∨ j+1=k
      · simpa [generatorSign, hadj] using hR.adjacent ⟨k,by omega⟩ ⟨j,by omega⟩ hne (ha.mpr hadj)
      · simpa [generatorSign, hadj] using hR.nonadjacent ⟨k,by omega⟩ ⟨j,by omega⟩ hne (by rwa [ha])
  · intro k hk
    have hk' : k+1 < m+1 := by omega
    simp only [cyclePrefix, dif_pos hk']
    have hne : (⟨k,by omega⟩:Fin (m+1))≠⟨m,by omega⟩ := by simp [Fin.ext_iff]; omega
    have ha : (SimpleGraph.cycleGraph (m+1)).Adj ⟨k,by omega⟩ ⟨m,by omega⟩ ↔ k=0 ∨ k+1=m := by
      rw [natural_cycle_adj (by omega)]; simp; omega
    by_cases hadj : k=0 ∨ k+1=m
    · simpa [closingSign, hadj] using hR.adjacent ⟨k,by omega⟩ ⟨m,by omega⟩ hne (ha.mpr hadj)
    · simpa [closingSign, hadj] using hR.nonadjacent ⟨k,by omega⟩ ⟨m,by omega⟩ hne (by rwa [ha])
lemma realization_cycle_loop {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+2) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph (2*n+2)) A) :
    let K := normalizedLoop n (cyclePrefix A) (A ⟨2*n+1,by omega⟩)
    K.IsHermitian ∧ K*K=1 ∧ (∀ j, K*A j=A j*K) ∧
      K*A ⟨2*n+1,by omega⟩=loopSign n • pathWord (cyclePrefix A) (2*n+1) := by
  have hrel := cycle_prefix_relations (m:=2*n+1) (by omega) A hR
  have hs : ∀ k, k < 2*n+1 → cyclePrefix A k*cyclePrefix A k=1 := by
    intro k hk
    simpa [cyclePrefix, show k+1 < 2*n+2 by omega] using hR.square ⟨k,by omega⟩
  have hstar : ∀ k, k < 2*n+1 → star (cyclePrefix A k)=cyclePrefix A k := by
    intro k hk
    simpa [cyclePrefix, show k+1 < 2*n+2 by omega, Matrix.star_eq_conjTranspose] using (hR.hermitian ⟨k,by omega⟩).eq
  have hnrm := loop_normalization n (cyclePrefix A) (A ⟨2*n+1,by omega⟩) hs
    (hR.square _) hrel.1 hrel.2 hn
  dsimp only
  refine ⟨?_, hnrm.1, ?_, hnrm.2.2.2.2⟩
  · change star (normalizedLoop n (cyclePrefix A) (A _))=normalizedLoop n (cyclePrefix A) (A _)
    apply normalizedLoop_star n _ _ hstar _ hrel.1 hrel.2 hn
    simpa only [Matrix.star_eq_conjTranspose] using (hR.hermitian _).eq
  · intro j
    by_cases hj : j.val=2*n+1
    · have he : j=⟨2*n+1,by omega⟩ := by apply Fin.ext; exact hj
      rw [he]; exact hnrm.2.1
    · have hj' : j.val < 2*n+1 := by have := j.isLt; omega
      have h := hnrm.2.2.1 j.val hj'
      simpa [cyclePrefix, show j.val+1 < 2*n+2 by omega] using h
end
open  D5.S3.Quantum.FiniteDimensional
open scoped Kronecker
noncomputable section
private lemma pathWord_liftPath {d : ℕ} (A : ℕ → (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) :
    pathWord (liftPath A) k = pathWord A k ⊗ₖ (if k=0 then 1 else qubitZ) := by
  induction k with
  | zero => simp [List.range_succ, pathWord]
  | succ k ih =>
    rw [pathWord_step, ih, liftPath, ← Matrix.mul_kronecker_mul, pathWord_step]
    by_cases hk : k=0
    · subst k; simp [List.range_succ, pathWord]
    · simp [hk]
lemma cycle_majorana_extension {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n+2) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.cycleGraph (2*n+2)) A) :
    let P := cyclePrefix A
    let K := normalizedLoop n P (A ⟨2*n+1,by omega⟩)
    let g := pathMajorana (liftPath P) (liftSeed d)
    (∀ k, k ≤ 2*n+1 → g k*g k=1) ∧
    (∀ k, k ≤ 2*n+1 → star (g k)=g k) ∧
    (∀ j, j ≤ 2*n+1 → ∀ i, i < j → g i*g j=-(g j*g i)) ∧
    (∀ k, k < 2*n+1 → Complex.I • (g k*g (k+1))=liftPath P k) ∧
      (-Complex.I) • (g (2*n+1)*g 0) = (K*A ⟨2*n+1,by omega⟩) ⊗ₖ qubitZ := by
  have hrel := cycle_prefix_relations (m:=2*n+1) (by omega) A hR
  have hs : ∀ k, k < 2*n+1 → cyclePrefix A k*cyclePrefix A k=1 := by
    intro k hk
    simpa [cyclePrefix, show k+1 < 2*n+2 by omega] using hR.square ⟨k,by omega⟩
  have hh : ∀ k, k < 2*n+1 → (cyclePrefix A k).IsHermitian := by
    intro k hk
    simpa [cyclePrefix, show k+1 < 2*n+2 by omega] using hR.hermitian ⟨k,by omega⟩
  have hg := arbitrary_path_majorana_extension (cyclePrefix A) hs hh hrel.1
  dsimp only
  refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, ?_⟩
  have h0 : liftSeed d*liftPath (cyclePrefix A) 0=-(liftPath (cyclePrefix A) 0*liftSeed d) := by
    simpa [prefixSign_zero] using liftSeed_relation (cyclePrefix A) 0
  have hrest : ∀ k, 0 < k → k < 2*n+1 →
      liftSeed d*liftPath (cyclePrefix A) k=liftPath (cyclePrefix A) k*liftSeed d := by
    intro k hk _
    simpa [prefixSign_zero, show k ≠ 0 by omega] using liftSeed_relation (cyclePrefix A) k
  rw [show pathMajorana (liftPath (cyclePrefix A)) (liftSeed d) 0=liftSeed d by rfl,
    antiperiodic_closing_bond n _ _ (liftSeed_square d) h0 hrest,
    pathWord_liftPath]
  simp only [show 2*n+1 ≠ 0 by omega, ↓reduceIte]
  have hclose := (realization_cycle_loop hn A hR).2.2.2
  rw [hclose, Matrix.smul_kronecker]
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.CentralCycleRealizations
