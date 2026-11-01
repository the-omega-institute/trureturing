/- GID: D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted path continuants and their edge-parameter variations for Question 5.11. -/

import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

/-! Branch-polynomial algebra for the complete positive-even double-path nSSP event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

open Polynomial Matrix

/-- The ordered arcs of the double path, with exactly the specified loops. -/
def pathPattern {n : ℕ} (L : Finset (Fin n)) (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i = j ∧ i ∈ L)

/-- Definition 1.1: the test matrix is unrestricted and the commutator uses its transpose. -/
def HasNSSP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, A i j * X i j = 0) → A * Xᵀ - Xᵀ * A = 0 → X = 0

/-- The complete existential event of Koljančić–Oblak Question 5.11. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → Even n → ∀ L : Finset (Fin n), L.Nonempty →
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j ≠ 0 ↔ pathPattern L i j) ∧ HasNSSP A

/-- Zero-diagonal branch polynomial; `q k` is the squared weight of edge `k`. -/
def continuant (q : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | k + 2 => X * continuant q (k + 1) - C (q k) * continuant q k

/-- Formal first variation in all edge parameters, including both terms in the product rule. -/
def variation (q dq : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | k + 2 => X * variation q dq (k + 1) -
      C (dq k) * continuant q k - C (q k) * variation q dq k

/-- A simultaneous polynomial perturbation `q k + z * dq k`.
The outer variable is the perturbation parameter; the inner variable is spectral. -/
def deformedContinuant (q dq : ℕ → ℝ) : ℕ → (ℝ[X])[X]
  | 0 => 1
  | 1 => C X
  | k + 2 => C X * deformedContinuant q dq (k + 1) -
      (C (C (q k)) + C (C (dq k)) * X) * deformedContinuant q dq k

/-- The formal recurrence is exactly the constant and linear coefficient of the deformation. -/
theorem continuant_linearization (q dq : ℕ → ℝ) (n : ℕ) :
    (deformedContinuant q dq n).coeff 0 = continuant q n ∧
      (deformedContinuant q dq n).coeff 1 = variation q dq n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp [deformedContinuant, continuant]
      · exact coeff_eq_zero_of_natDegree_lt (by simp [deformedContinuant])
  | one => simp [deformedContinuant, continuant, variation]
  | more n h0 h1 =>
      constructor <;>
        simp [deformedContinuant, continuant, variation, mul_coeff_one,
          h0.1, h0.2, h1.1, h1.2] <;> ring

private lemma continuant_coeff (q : ℕ → ℝ) (n : ℕ) :
    (continuant q n).coeff n = 1 ∧
      ∀ k : ℕ, n < k → (continuant q n).coeff k = 0 := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp [continuant]
      · intro k hk
        exact coeff_eq_zero_of_natDegree_lt (by simpa [continuant] using hk)
  | one =>
      constructor
      · simp [continuant]
      · intro k hk
        exact coeff_eq_zero_of_natDegree_lt (by simpa [continuant] using hk)
  | more n h0 h1 =>
      constructor
      · simp only [continuant, coeff_sub, coeff_X_mul, coeff_C_mul]
        rw [h1.1, h0.2 (n + 2) (by omega)]
        simp
      · intro k hk
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
        simp only [continuant, coeff_sub, coeff_X_mul, coeff_C_mul]
        rw [h1.2 k (by omega), h0.2 (k + 1) (by omega)]
        simp

private lemma variation_coeff (q dq : ℕ → ℝ) (n k : ℕ) (h : n ≤ k) :
    (variation q dq n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [variation]
  | one => simp [variation]
  | more n h0 h1 =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      simp only [variation, coeff_sub, coeff_X_mul, coeff_C_mul]
      rw [h1 k (by omega), (continuant_coeff q n).2 (k + 1) (by omega),
        h0 (k + 1) (by omega)]
      simp

/-- Two consecutive zero branch variations recover every edge variation, uniformly in length.
The length-zero and length-one branches have no edge parameters to recover. -/
theorem branch_variation_injective (q dq : ℕ → ℝ) (n : ℕ)
    (hq : ∀ k < n, q k ≠ 0)
    (h0 : variation q dq n = 0) (h1 : variation q dq (n + 1) = 0) :
    ∀ k < n, dq k = 0 := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      have hr : C (dq n) * continuant q n + C (q n) * variation q dq n = 0 := by
        change X * variation q dq (n + 1) - C (dq n) * continuant q n -
          C (q n) * variation q dq n = 0 at h1
        rw [h0, mul_zero] at h1
        linear_combination -h1
      have hd : dq n = 0 := by
        have hc := congrArg (fun p : ℝ[X] => p.coeff n) hr
        simpa only [coeff_add, coeff_C_mul, (continuant_coeff q n).1,
          variation_coeff q dq n n le_rfl, coeff_zero, mul_one, mul_zero, add_zero] using hc
      have hz : variation q dq n = 0 := by
        rw [hd, C_0, zero_mul, zero_add] at hr
        exact (mul_eq_zero.mp hr).resolve_left (C_ne_zero.mpr (hq n (by omega)))
      have hi := ih (fun k hk => hq k (by omega)) hz h0
      intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
      · exact hi k hlt
      · exact hd

/-- A zero-diagonal weighted path, numbered from the endpoint opposite the recurrence.
Reversing the vertex order makes the newly attached edge have index `n - 2`. -/
def weightedPath (b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val + 1 = j.val then b (n - 2 - i.val)
    else if j.val + 1 = i.val then b (n - 2 - j.val) else 0

/-- The branch recurrence is the actual characteristic polynomial, including empty branches. -/
theorem weighted_path_charpoly (b : ℕ → ℝ) (n : ℕ) :
    (weightedPath b n).charpoly = continuant (fun k => b k ^ 2) n := by
  classical
  induction n using Nat.twoStepInduction with
  | zero => simp [continuant, Matrix.charpoly_isEmpty]
  | one =>
      have hz : weightedPath b 1 = 0 := by
        ext i j
        have hi : i.val = 0 := by omega
        have hj : j.val = 0 := by omega
        simp [weightedPath, hi, hj]
      simp [hz, continuant]
  | more n h0 h1 =>
      have shift1 (i j : Fin (n + 1)) :
          weightedPath b (n + 2) i.succ j.succ = weightedPath b (n + 1) i j := by
        simp only [weightedPath, Fin.val_succ, Nat.add_right_cancel_iff]
        split_ifs <;> first | rfl | (congr 1 <;> omega)
      have shift2 (i j : Fin n) :
          weightedPath b (n + 2) i.succ.succ j.succ.succ = weightedPath b n i j := by
        simp only [weightedPath, Fin.val_succ, Nat.add_right_cancel_iff]
        split_ifs <;> first | rfl | (congr 1 <;> omega)
      have minor1 : (weightedPath b (n + 2)).charmatrix.submatrix Fin.succ Fin.succ =
          (weightedPath b (n + 1)).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift1]
      have minor2 : (weightedPath b (n + 2)).charmatrix.submatrix
          (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ) =
          (weightedPath b n).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift2]
      have row (j : Fin n) : (weightedPath b (n + 2)).charmatrix 0 j.succ.succ = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          weightedPath, show ¬ (0 + 1 = j.val + 1 + 1) by omega]
      have col (i : Fin n) : (weightedPath b (n + 2)).charmatrix i.succ.succ 0 = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          weightedPath, show ¬ (0 + 1 = i.val + 1 + 1) by omega]
      have diag : (weightedPath b (n + 2)).charmatrix 0 0 = X := by
        simp [Matrix.charmatrix_apply_eq, weightedPath]
      have upper : (weightedPath b (n + 2)).charmatrix 0 1 = -C (b n) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, weightedPath]
      have lower : (weightedPath b (n + 2)).charmatrix 1 0 = -C (b n) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, weightedPath]
      unfold Matrix.charpoly
      rw [_root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.det_sparse_front
        _ row col, minor1, minor2, diag, upper, lower]
      change X * (weightedPath b (n + 1)).charpoly -
        (-C (b n)) * (-C (b n)) * (weightedPath b n).charpoly = _
      rw [h0, h1, continuant, map_pow]
      ring

private lemma continuant_monic (q : ℕ → ℝ) (n : ℕ) :
    (continuant q n).IsMonicOfDegree n := by
  apply (isMonicOfDegree_iff _ _).2
  exact ⟨natDegree_le_iff_coeff_eq_zero.2 (continuant_coeff q n).2,
    (continuant_coeff q n).1⟩

private lemma variation_degree (q dq : ℕ → ℝ) (n : ℕ) :
    (variation q dq n).degree < (n - 1 : ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [variation]
  | one => simp [variation]
  | more n h0 h1 =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      simp only [variation, coeff_sub, coeff_X_mul, coeff_C_mul]
      rw [h1 k (by omega), (continuant_coeff q n).2 (k + 1) (by omega),
        h0 (k + 1) (by omega)]
      simp

private lemma branch_parity (q dq : ℕ → ℝ) (n : ℕ) :
    (continuant q n).comp (-X) = (-1 : ℝ[X]) ^ n * continuant q n ∧
      (variation q dq n).comp (-X) = (-1 : ℝ[X]) ^ n * variation q dq n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuant, variation]
  | one => simp [continuant, variation]
  | more n h0 h1 =>
      constructor <;>
        simp [continuant, variation, h0.1, h0.2, h1.1, h1.2, pow_succ] <;> ring

/-- The full variation of `(X-a)UV-FV-UG`, where
`U=P_left(r)`, `V=P_right(s)`, `F=XU-P_left(r+1)` and
`G=XV-P_right(s+1)`. These fluxes are zero for empty branches.
All six product-rule contributions are retained. -/
def joinedVariation (qL qR dqL dqR : ℕ → ℝ) (a da : ℝ) (r s : ℕ) : ℝ[X] :=
  -C da * continuant qL r * continuant qR s +
    (X - C a) * (variation qL dqL r * continuant qR s +
      continuant qL r * variation qR dqR s) -
    (X * variation qL dqL r - variation qL dqL (r + 1)) * continuant qR s -
    (X * continuant qL r - continuant qL (r + 1)) * variation qR dqR s -
    variation qL dqL r * (X * continuant qR s - continuant qR (s + 1)) -
    continuant qL r * (X * variation qR dqR s - variation qR dqR (s + 1))

/-- Simultaneously perturb the loop and all squared edges in the joined
branch expression. The outer variable is the perturbation parameter. -/
def deformedJoinedContinuant (qL qR dqL dqR : ℕ → ℝ) (a da : ℝ) (r s : ℕ) :
    (ℝ[X])[X] :=
  (C X - (C (C a) + C (C da) * X)) *
      deformedContinuant qL dqL r * deformedContinuant qR dqR s -
    (C X * deformedContinuant qL dqL r - deformedContinuant qL dqL (r + 1)) *
      deformedContinuant qR dqR s -
    deformedContinuant qL dqL r *
      (C X * deformedContinuant qR dqR s - deformedContinuant qR dqR (s + 1))

lemma joined_linearization (qL qR dqL dqR : ℕ → ℝ) (a da : ℝ) (r s : ℕ) :
    (deformedJoinedContinuant qL qR dqL dqR a da r s).coeff 1 =
      joinedVariation qL qR dqL dqR a da r s := by
  simp [deformedJoinedContinuant, joinedVariation, mul_coeff_one,
    (continuant_linearization qL dqL r).1, (continuant_linearization qL dqL r).2,
    (continuant_linearization qR dqR s).1, (continuant_linearization qR dqR s).2,
    (continuant_linearization qL dqL (r + 1)).1,
    (continuant_linearization qL dqL (r + 1)).2,
    (continuant_linearization qR dqR (s + 1)).1,
    (continuant_linearization qR dqR (s + 1)).2] <;> ring

private lemma coprime_separation (U V dU dV : ℝ[X]) (hUV : IsCoprime U V)
    (hdU : dU.degree < U.degree) (hdV : dV.degree < V.degree)
    (h : dU * V + U * dV = 0) : dU = 0 ∧ dV = 0 := by
  have hu : U ∣ dU * V := by
    refine ⟨-dV, ?_⟩
    linear_combination h
  have hv : V ∣ U * dV := by
    refine ⟨-dU, ?_⟩
    linear_combination h
  exact ⟨eq_zero_of_dvd_of_degree_lt (hUV.dvd_of_dvd_mul_right hu) hdU,
    eq_zero_of_dvd_of_degree_lt (hUV.symm.dvd_of_dvd_mul_left hv) hdV⟩

/-- At a nonzero central loop, coprime opposite-parity branches separate every
central and edge variation. Either branch may be empty. Edge indices below its
length include the edge attaching that branch to the central vertex. -/
theorem joined_variation_injective (qL qR dqL dqR : ℕ → ℝ) (a da : ℝ) (r s : ℕ)
    (ha : a ≠ 0) (hodd : Odd (r + s))
    (hL : ∀ k < r, qL k ≠ 0) (hR : ∀ k < s, qR k ≠ 0)
    (hcop : IsCoprime (continuant qL r) (continuant qR s))
    (hz : (deformedJoinedContinuant qL qR dqL dqR a da r s).coeff 1 = 0) :
    da = 0 ∧ (∀ k < r, dqL k = 0) ∧ (∀ k < s, dqR k = 0) := by
  rw [joined_linearization] at hz
  let U := continuant qL r
  let V := continuant qR s
  let dU := variation qL dqL r
  let dV := variation qR dqR s
  let T := dU * V + U * dV
  let W := variation qL dqL (r + 1) * V +
    continuant qL (r + 1) * dV + dU * continuant qR (s + 1) +
    U * variation qR dqR (s + 1) - X * T
  have he : W - C a * T - C da * (U * V) = 0 := by
    dsimp [W, T, U, V, dU, dV]
    unfold joinedVariation at hz
    linear_combination hz
  have hsign : (-1 : ℝ[X]) ^ r * (-1 : ℝ[X]) ^ s = -1 := by
    rw [← pow_add, hodd.neg_one_pow]
  have hT : T.comp (-X) = -T := by
    dsimp [T, U, V, dU, dV]
    simp only [add_comp, mul_comp, (branch_parity qL dqL r).1,
      (branch_parity qL dqL r).2, (branch_parity qR dqR s).1,
      (branch_parity qR dqR s).2]
    linear_combination hsign *
      (variation qL dqL r * continuant qR s + continuant qL r * variation qR dqR s)
  have hP : (U * V).comp (-X) = -(U * V) := by
    dsimp [U, V]
    simp only [mul_comp, (branch_parity qL dqL r).1, (branch_parity qR dqR s).1]
    linear_combination hsign * (continuant qL r * continuant qR s)
  have hW : W.comp (-X) = W := by
    dsimp only [W]
    simp only [add_comp, sub_comp, mul_comp, X_comp, hT]
    dsimp only [U, V, dU, dV]
    simp only [(branch_parity qL dqL r).1, (branch_parity qL dqL r).2,
      (branch_parity qR dqR s).1, (branch_parity qR dqR s).2,
      (branch_parity qL dqL (r + 1)).1, (branch_parity qL dqL (r + 1)).2,
      (branch_parity qR dqR (s + 1)).1, (branch_parity qR dqR (s + 1)).2, pow_succ]
    linear_combination -hsign *
      (variation qL dqL (r + 1) * continuant qR s +
        continuant qL (r + 1) * variation qR dqR s +
        variation qL dqL r * continuant qR (s + 1) +
        continuant qL r * variation qR dqR (s + 1))
  have hc := congrArg (fun p : ℝ[X] => p.comp (-X)) he
  simp only [sub_comp, mul_comp, C_comp, hW, hT, hP, zero_comp] at hc
  have hoddpart : C a * T + C da * (U * V) = 0 := by
    have ht : (2 : ℝ[X]) * (C a * T + C da * (U * V)) = 0 := by
      linear_combination hc - he
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
  have mU := continuant_monic qL r
  have mV := continuant_monic qR s
  have hdU : dU.degree < U.degree := by
    change (variation qL dqL r).degree < (continuant qL r).degree
    rw [degree_eq_natDegree mU.monic.ne_zero, mU.natDegree_eq]
    exact lt_of_lt_of_le (variation_degree qL dqL r) (by exact_mod_cast Nat.sub_le r 1)
  have hdV : dV.degree < V.degree := by
    change (variation qR dqR s).degree < (continuant qR s).degree
    rw [degree_eq_natDegree mV.monic.ne_zero, mV.natDegree_eq]
    exact lt_of_lt_of_le (variation_degree qR dqR s) (by exact_mod_cast Nat.sub_le s 1)
  have hTdeg : T.degree < (r + s : ℕ) := by
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact lt_of_le_of_lt (degree_mul_le ..)
        (by simpa [U, V, degree_eq_natDegree mU.monic.ne_zero, degree_eq_natDegree mV.monic.ne_zero,
          mU.natDegree_eq, mV.natDegree_eq] using
          WithBot.add_lt_add_right (degree_ne_bot.mpr mV.monic.ne_zero) hdU)
    · exact lt_of_le_of_lt (degree_mul_le ..)
        (by simpa [U, V, degree_eq_natDegree mU.monic.ne_zero, degree_eq_natDegree mV.monic.ne_zero,
          mU.natDegree_eq, mV.natDegree_eq] using
          WithBot.add_lt_add_left (degree_ne_bot.mpr mU.monic.ne_zero) hdV)
  have hda : da = 0 := by
    have ht := (degree_lt_iff_coeff_zero T (r + s)).1 hTdeg (r + s) le_rfl
    have hp : (U * V).coeff (r + s) = 1 := by
      change (continuant qL r * continuant qR s).coeff (r + s) = 1
      rw [← (mU.mul mV).natDegree_eq]
      exact (mU.mul mV).monic.coeff_natDegree
    have hh := congrArg (fun p : ℝ[X] => p.coeff (r + s)) hoddpart
    simpa [coeff_add, coeff_C_mul, ht, hp] using hh
  have ht : T = 0 := by
    rw [hda, C_0, zero_mul, add_zero] at hoddpart
    exact (mul_eq_zero.mp hoddpart).resolve_left (C_ne_zero.mpr ha)
  obtain ⟨hu, hv⟩ := coprime_separation U V dU dV hcop hdU hdV ht
  have hw : variation qL dqL (r + 1) * V + U * variation qR dqR (s + 1) = 0 := by
    dsimp [W] at he
    rw [hu, hv, ht, hda, C_0] at he
    simpa using he
  have hdL : (variation qL dqL (r + 1)).degree < U.degree := by
    simpa [U, degree_eq_natDegree mU.monic.ne_zero, mU.natDegree_eq] using
      variation_degree qL dqL (r + 1)
  have hdR : (variation qR dqR (s + 1)).degree < V.degree := by
    simpa [V, degree_eq_natDegree mV.monic.ne_zero, mV.natDegree_eq] using
      variation_degree qR dqR (s + 1)
  obtain ⟨hu1, hv1⟩ := coprime_separation U V _ _ hcop hdL hdR hw
  exact ⟨hda, branch_variation_injective qL dqL r hL hu hu1,
    branch_variation_injective qR dqR s hR hv hv1⟩

private def parameterContinuant : ℕ → (ℝ[X])[X]
  | 0 => 1
  | 1 => X
  | k + 2 => X * parameterContinuant (k + 1) - C X * parameterContinuant k

private lemma parameter_map (t : ℝ) (n : ℕ) :
    (parameterContinuant n).map (evalRingHom t) = continuant (fun _ => t) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [parameterContinuant, continuant]
  | one => simp [parameterContinuant, continuant]
  | more n h0 h1 => simp [parameterContinuant, continuant, h0, h1]

private lemma zero_continuant (n : ℕ) : continuant (fun _ => 0) n = X ^ n := by
  have hm : weightedPath (fun _ => 0) n = 0 := by
    ext i j
    simp [weightedPath]
  simpa [hm] using (weighted_path_charpoly (fun _ => 0) n).symm

private lemma even_constant (k : ℕ) :
    (continuant (fun _ => 1) (2 * k)).coeff 0 = (-1 : ℝ) ^ k := by
  induction k with
  | zero => simp [continuant]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, continuant]
      simp [ih, pow_succ]

private lemma positive_coprime_right (r s : ℕ) (hr : Even r) :
    ∃ t : ℝ, 0 < t ∧
      IsCoprime (continuant (fun _ => 1) r) (continuant (fun _ => t) s) := by
  let U := continuant (fun _ => 1) r
  let B := U.map (C : ℝ →+* ℝ[X])
  let R := resultant B (parameterContinuant s) r s
  have hB (t : ℝ) : B.map (evalRingHom t) = U := by
    ext k
    simp [B]
  have hR (t : ℝ) : R.eval t =
      resultant U (continuant (fun _ => t) s) r s := by
    have hm := resultant_map_map B (parameterContinuant s) r s (evalRingHom t)
    rw [hB t, parameter_map] at hm
    exact hm.symm
  have hU : U.coeff 0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hr
    have hrk : r = 2 * k := by omega
    dsimp [U]
    rw [hrk, even_constant]
    exact pow_ne_zero _ (by norm_num)
  have hR0 : R.eval 0 ≠ 0 := by
    rw [hR 0, zero_continuant, resultant_X_pow_right U r s
      (by simpa [U] using (continuant_monic (fun _ => 1) r).natDegree_eq.le)]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hU)
  have hRn : R ≠ 0 := by
    intro h
    exact hR0 (by rw [h, eval_zero])
  obtain ⟨t, ht, hnot⟩ := (Set.Ioi_infinite (0 : ℝ)).exists_notMem_finite
    (finite_setOfPred_isRoot hRn)
  refine ⟨t, ht, ?_⟩
  apply (isUnit_resultant_iff_isCoprime (continuant_monic (fun _ => 1) r).monic).1
  apply isUnit_iff_ne_zero.2
  change resultant U (continuant (fun _ => t) s) U.natDegree
    (continuant (fun _ => t) s).natDegree ≠ 0
  rw [show U.natDegree = r from (continuant_monic (fun _ => 1) r).natDegree_eq,
    (continuant_monic (fun _ => t) s).natDegree_eq, ← hR t]
  exact hnot

/-- Opposite-parity branch lengths admit strictly positive squared edge
parameters with coprime continuants, including zero and one lengths. -/
theorem coprime_positive_branches (r s : ℕ) (hodd : Odd (r + s)) :
    ∃ qL qR : ℕ → ℝ, (∀ k, 0 < qL k) ∧ (∀ k, 0 < qR k) ∧
      IsCoprime (continuant qL r) (continuant qR s) := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨t, ht, hcop⟩ := positive_coprime_right r s hr
    exact ⟨(fun _ => 1), (fun _ => t), (by intro k; norm_num), (fun _ => ht), hcop⟩
  · have hs : Even s := by
      rw [Nat.even_iff]
      have hr' := Nat.odd_iff.mp hr
      have ho' := Nat.odd_iff.mp hodd
      omega
    obtain ⟨t, ht, hcop⟩ := positive_coprime_right s r hs
    exact ⟨(fun _ => t), (fun _ => 1), (fun _ => ht), (by intro k; norm_num), hcop.symm⟩


/-- A path with the loop at vertex `r`; the left edges are read from the far
endpoint and the right edges from the central vertex. Both branches may be empty. -/
def joinedPath (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ) :
    Matrix (Fin (s + 1 + r)) (Fin (s + 1 + r)) ℝ := fun i j =>
  if i = j then (if i.val = r then a else 0)
  else if i.val + 1 = j.val then
    (if i.val < r then bL i.val else bR (s + r - 1 - i.val))
  else if j.val + 1 = i.val then
    (if j.val < r then bL j.val else bR (s + r - 1 - j.val)) else 0

private lemma continuant_front (q : ℕ → ℝ) (n : ℕ) :
    continuant q (n + 2) = X * continuant (fun k => q (k + 1)) (n + 1) -
      C (q 0) * continuant (fun k => q (k + 2)) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuant]
  | one => simp [continuant]; ring
  | more n h0 h1 =>
      simp only [continuant] at h0 h1 ⊢
      linear_combination X * h1 - C (q (n + 2)) * h0

private lemma joined_endpoint_charpoly (bL bR : ℕ → ℝ) (a : ℝ) (s : ℕ) :
    (joinedPath bL bR a 0 s).charpoly =
      continuant (fun k => bR k ^ 2) (s + 1) -
        C a * continuant (fun k => bR k ^ 2) s := by
  classical
  cases s with
  | zero =>
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq,
        joinedPath, continuant]
  | succ s =>
      have minor1 : (joinedPath bL bR a 0 (s + 1)).charmatrix.submatrix
          Fin.succ Fin.succ = (weightedPath bR (s + 1)).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj]
        congr 1
        simp only [joinedPath, weightedPath, Fin.val_succ, Fin.ext_iff]
        split_ifs <;> simp_all <;> first | omega | (congr 1 <;> omega)
      have minor2 : (joinedPath bL bR a 0 (s + 1)).charmatrix.submatrix
          (fun i : Fin s => i.succ.succ) (fun j : Fin s => j.succ.succ) =
          (weightedPath bR s).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj]
        congr 1
        simp only [joinedPath, weightedPath, Fin.val_succ, Fin.ext_iff]
        split_ifs <;> simp_all <;> first | omega | (congr 1 <;> omega)
      have row (j : Fin s) :
          (joinedPath bL bR a 0 (s + 1)).charmatrix 0 j.succ.succ = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          joinedPath, show ¬ (0 + 1 = j.val + 1 + 1) by omega]
      have col (i : Fin s) :
          (joinedPath bL bR a 0 (s + 1)).charmatrix i.succ.succ 0 = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          joinedPath, show ¬ (0 + 1 = i.val + 1 + 1) by omega]
      have diag : (joinedPath bL bR a 0 (s + 1)).charmatrix 0 0 = X - C a := by
        simp [Matrix.charmatrix_apply_eq, joinedPath]
      have upper : (joinedPath bL bR a 0 (s + 1)).charmatrix 0 1 = -C (bR s) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath]
      have lower : (joinedPath bL bR a 0 (s + 1)).charmatrix 1 0 = -C (bR s) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath]
      unfold Matrix.charpoly
      rw [_root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.det_sparse_front
        _ row col, minor1, minor2, diag, upper, lower]
      change (X - C a) * (weightedPath bR (s + 1)).charpoly -
        (-C (bR s)) * (-C (bR s)) * (weightedPath bR s).charpoly = _
      rw [weighted_path_charpoly, weighted_path_charpoly, continuant, map_pow]
      ring

/-- The joined branch expression is the characteristic polynomial of the actual
one-loop weighted path, for every pair of branch lengths, including empty branches. -/
theorem joined_path_charpoly (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ) :
    (joinedPath bL bR a r s).charpoly =
      continuant (fun k => bL k ^ 2) (r + 1) * continuant (fun k => bR k ^ 2) s +
      continuant (fun k => bL k ^ 2) r * continuant (fun k => bR k ^ 2) (s + 1) -
      (X + C a) * continuant (fun k => bL k ^ 2) r *
        continuant (fun k => bR k ^ 2) s := by
  classical
  induction r using Nat.twoStepInduction generalizing bL with
  | zero =>
      rw [joined_endpoint_charpoly]
      simp only [continuant]
      ring
  | one =>
      have shift1 (i j : Fin (s + 1)) :
          joinedPath bL bR a 1 s i.succ j.succ =
            joinedPath (fun k => bL (k + 1)) bR a 0 s i j := by
        have hd : i.val + 1 = 1 ↔ i.val = 0 := by omega
        have he : i.val + 1 + 1 = j.val + 1 ↔ i.val + 1 = j.val := by omega
        have hf : j.val + 1 + 1 = i.val + 1 ↔ j.val + 1 = i.val := by omega
        have hli : i.val + 1 < 1 ↔ i.val < 0 := by omega
        have hii : s + 1 - 1 - (i.val + 1) = s + 0 - 1 - i.val := by omega
        have hlj : j.val + 1 < 1 ↔ j.val < 0 := by omega
        have hij : s + 1 - 1 - (j.val + 1) = s + 0 - 1 - j.val := by omega
        simp only [joinedPath, Fin.val_succ, Fin.succ_inj, hd, he, hf, hli, hlj, hii, hij]
      have shift2 (i j : Fin s) :
          joinedPath bL bR a 1 s i.succ.succ j.succ.succ = weightedPath bR s i j := by
        simp only [joinedPath, weightedPath, Fin.val_succ, Fin.ext_iff]
        split_ifs <;> simp_all <;> first | omega | (congr 1 <;> omega)
      have minor1 : (joinedPath bL bR a 1 s).charmatrix.submatrix Fin.succ Fin.succ =
          (joinedPath (fun k => bL (k + 1)) bR a 0 s).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift1]
      have minor2 : (joinedPath bL bR a 1 s).charmatrix.submatrix
          (fun i : Fin s => i.succ.succ) (fun j : Fin s => j.succ.succ) =
          (weightedPath bR s).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift2]
      have row (j : Fin s) : (joinedPath bL bR a 1 s).charmatrix 0 j.succ.succ = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          joinedPath, show ¬ (0 + 1 = j.val + 1 + 1) by omega]
      have col (i : Fin s) : (joinedPath bL bR a 1 s).charmatrix i.succ.succ 0 = 0 := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff,
          joinedPath, show ¬ (0 + 1 = i.val + 1 + 1) by omega]
      have diag : (joinedPath bL bR a 1 s).charmatrix 0 0 = X := by
        simp [Matrix.charmatrix_apply_eq, joinedPath]
      have upper : (joinedPath bL bR a 1 s).charmatrix 0 1 = -C (bL 0) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath]
      have lower : (joinedPath bL bR a 1 s).charmatrix 1 0 = -C (bL 0) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath]
      unfold Matrix.charpoly
      rw [_root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.det_sparse_front
        _ row col, minor1, minor2, diag, upper, lower]
      change X * (joinedPath (fun k => bL (k + 1)) bR a 0 s).charpoly -
        (-C (bL 0)) * (-C (bL 0)) * (weightedPath bR s).charpoly = _
      rw [joined_endpoint_charpoly, weighted_path_charpoly]
      simp only [continuant, map_pow]
      ring
  | more r h0 h1 =>
      have shift1 (i j : Fin (s + 1 + (r + 1))) :
          joinedPath bL bR a (r + 2) s i.succ j.succ =
            joinedPath (fun k => bL (k + 1)) bR a (r + 1) s i j := by
        have hd : i.val + 1 = (r + 2) ↔ i.val = (r + 1) := by omega
        have he : i.val + 1 + 1 = j.val + 1 ↔ i.val + 1 = j.val := by omega
        have hf : j.val + 1 + 1 = i.val + 1 ↔ j.val + 1 = i.val := by omega
        have hli : i.val + 1 < (r + 2) ↔ i.val < (r + 1) := by omega
        have hii : s + (r + 2) - 1 - (i.val + 1) = s + (r + 1) - 1 - i.val := by omega
        have hlj : j.val + 1 < (r + 2) ↔ j.val < (r + 1) := by omega
        have hij : s + (r + 2) - 1 - (j.val + 1) = s + (r + 1) - 1 - j.val := by omega
        simp only [joinedPath, Fin.val_succ, Fin.succ_inj, hd, he, hf, hli, hlj, hii, hij]
      have shift2 (i j : Fin (s + 1 + r)) :
          joinedPath bL bR a (r + 2) s i.succ.succ j.succ.succ =
            joinedPath (fun k => bL (k + 2)) bR a r s i j := by
        have hd : i.val + 1 + 1 = (r + 2) ↔ i.val = r := by omega
        have he : i.val + 1 + 1 + 1 = j.val + 1 + 1 ↔ i.val + 1 = j.val := by omega
        have hf : j.val + 1 + 1 + 1 = i.val + 1 + 1 ↔ j.val + 1 = i.val := by omega
        have hli : i.val + 1 + 1 < (r + 2) ↔ i.val < r := by omega
        have hii : s + (r + 2) - 1 - (i.val + 1 + 1) = s + r - 1 - i.val := by omega
        have hlj : j.val + 1 + 1 < (r + 2) ↔ j.val < r := by omega
        have hij : s + (r + 2) - 1 - (j.val + 1 + 1) = s + r - 1 - j.val := by omega
        simp only [joinedPath, Fin.val_succ, Fin.succ_inj, hd, he, hf, hli, hlj, hii, hij]
      have minor1 : (joinedPath bL bR a (r + 2) s).charmatrix.submatrix Fin.succ Fin.succ =
          (joinedPath (fun k => bL (k + 1)) bR a (r + 1) s).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift1]
      have minor2 : (joinedPath bL bR a (r + 2) s).charmatrix.submatrix
          (fun i : Fin (s + 1 + r) => i.succ.succ)
          (fun j : Fin (s + 1 + r) => j.succ.succ) =
          (joinedPath (fun k => bL (k + 2)) bR a r s).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply,
          Matrix.diagonal_apply, Fin.succ_inj, shift2]
      have row (j : Fin (s + 1 + r)) :
          (joinedPath bL bR a (r + 2) s).charmatrix 0 j.succ.succ = 0 := by
        have hn : (0 : Fin (s + 1 + (r + 2))) ≠ j.succ.succ := by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_zero, Fin.val_succ] at hv
          omega
        rw [Matrix.charmatrix_apply_ne _ _ _ hn]
        have hm : joinedPath bL bR a (r + 2) s 0 j.succ.succ = 0 := by
          unfold joinedPath
          rw [if_neg hn]
          dsimp only [Fin.val_zero, Fin.val_succ]
          rw [if_neg (show ¬ (0 + 1 = j.val + 1 + 1) by omega),
            if_neg (show ¬ (j.val + 1 + 1 + 1 = 0) by omega)]
        rw [hm, map_zero, neg_zero]
      have col (i : Fin (s + 1 + r)) :
          (joinedPath bL bR a (r + 2) s).charmatrix i.succ.succ 0 = 0 := by
        have hn : i.succ.succ ≠ (0 : Fin (s + 1 + (r + 2))) := by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_zero, Fin.val_succ] at hv
          omega
        rw [Matrix.charmatrix_apply_ne _ _ _ hn]
        have hm : joinedPath bL bR a (r + 2) s i.succ.succ 0 = 0 := by
          unfold joinedPath
          rw [if_neg hn]
          dsimp only [Fin.val_zero, Fin.val_succ]
          rw [if_neg (show ¬ (i.val + 1 + 1 + 1 = 0) by omega),
            if_neg (show ¬ (0 + 1 = i.val + 1 + 1) by omega)]
        rw [hm, map_zero, neg_zero]
      have hone : (1 : Fin (s + 1 + (r + 2))).val = 1 := by
        change 1 % (s + 1 + (r + 2)) = 1
        exact Nat.mod_eq_of_lt (by omega)
      have hmod : 1 % (s + 1 + (r + 2)) = 1 := Nat.mod_eq_of_lt (by omega)
      have diag : (joinedPath bL bR a (r + 2) s).charmatrix 0 0 = X := by
        simp [Matrix.charmatrix_apply_eq, joinedPath]
      have upper : (joinedPath bL bR a (r + 2) s).charmatrix 0 1 = -C (bL 0) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath, hone, hmod]
      have lower : (joinedPath bL bR a (r + 2) s).charmatrix 1 0 = -C (bL 0) := by
        simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.ext_iff, joinedPath, hone, hmod]
      unfold Matrix.charpoly
      rw [_root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.det_sparse_front
        _ row col, minor1, minor2, diag, upper, lower]
      change X * (joinedPath (fun k => bL (k + 1)) bR a (r + 1) s).charpoly -
        (-C (bL 0)) * (-C (bL 0)) *
          (joinedPath (fun k => bL (k + 2)) bR a r s).charpoly = _
      rw [h1, h0, continuant_front (fun k => bL k ^ 2) (r + 1),
        continuant_front (fun k => bL k ^ 2) r, map_pow]
      ring

private lemma continuant_derivative (b db : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (continuant (fun k => (b k + t * db k) ^ 2) n).eval x)
      ((variation (fun k => b k ^ 2) (fun k => 2 * b k * db k) n).eval x) 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [continuant, variation] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | one => simpa [continuant, variation] using hasDerivAt_const (0 : ℝ) x
  | more n h0 h1 =>
      have he : HasDerivAt (fun t : ℝ => (b n + t * db n) ^ 2) (2 * b n * db n) 0 := by
        have hf : HasDerivAt (fun t : ℝ => b n + t * db n) (db n) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (db n)).const_add (b n)
        have ht := hf.mul hf
        refine (ht.congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [zero_mul, add_zero]
          ring
        · exact Filter.Eventually.of_forall (fun t => by simp only [Pi.mul_apply, pow_two])
      have H := (h1.const_mul x).sub (he.mul h0)
      refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [variation, eval_sub, eval_mul, eval_X, eval_C,
          Pi.mul_apply, Pi.pow_apply, zero_mul, add_zero]
        ring
      · exact Filter.Eventually.of_forall (fun t => by
          simp only [continuant, eval_sub, eval_mul, eval_X, eval_C,
            Pi.sub_apply, Pi.mul_apply])

/-- The algebraic joined variation is the actual first derivative of every
spectral evaluation of the characteristic polynomial along arbitrary edge and
central-loop perturbations. Squared-edge variations are `2*b*db`. -/
theorem joined_path_charpoly_derivative (bL bR dbL dbR : ℕ → ℝ)
    (a da : ℝ) (r s : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      ((joinedPath (fun k => bL k + t * dbL k) (fun k => bR k + t * dbR k)
        (a + t * da) r s).charpoly).eval x)
      ((joinedVariation (fun k => bL k ^ 2) (fun k => bR k ^ 2)
        (fun k => 2 * bL k * dbL k) (fun k => 2 * bR k * dbR k) a da r s).eval x) 0 := by
  have hL := continuant_derivative bL dbL r x
  have hL1 := continuant_derivative bL dbL (r + 1) x
  have hR := continuant_derivative bR dbR s x
  have hR1 := continuant_derivative bR dbR (s + 1) x
  have ha : HasDerivAt (fun t : ℝ => x + (a + t * da)) da 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const da).const_add a).const_add x
  have H := ((hL1.mul hR).add (hL.mul hR1)).sub ((ha.mul hL).mul hR)
  refine (H.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [joinedVariation, eval_add, eval_sub, eval_mul, eval_neg, eval_X, eval_C,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, zero_mul, add_zero]
    ring
  · exact Filter.Eventually.of_forall (fun t => by
      simp only [joined_path_charpoly, eval_add, eval_sub, eval_mul, eval_X, eval_C,
        Pi.sub_apply, Pi.add_apply, Pi.mul_apply])

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
