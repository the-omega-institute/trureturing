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
    (hz : joinedVariation qL qR dqL dqR a da r s = 0) :
    da = 0 ∧ (∀ k < r, dqL k = 0) ∧ (∀ k < s, dqR k = 0) := by
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
    linear_combination (hc - he) / 2
  have mU := continuant_monic qL r
  have mV := continuant_monic qR s
  have hdU : dU.degree < U.degree := by
    change (variation qL dqL r).degree < (continuant qL r).degree
    rw [mU.monic.degree_eq_natDegree, mU.natDegree_eq]
    exact lt_of_lt_of_le (variation_degree qL dqL r) (by exact_mod_cast Nat.sub_le r 1)
  have hdV : dV.degree < V.degree := by
    change (variation qR dqR s).degree < (continuant qR s).degree
    rw [mV.monic.degree_eq_natDegree, mV.natDegree_eq]
    exact lt_of_lt_of_le (variation_degree qR dqR s) (by exact_mod_cast Nat.sub_le s 1)
  have hTdeg : T.degree < (r + s : ℕ) := by
    apply degree_add_lt
    · exact lt_of_le_of_lt (degree_mul_le ..)
        (by simpa [U, V, mU.monic.degree_eq_natDegree, mV.monic.degree_eq_natDegree,
          mU.natDegree_eq, mV.natDegree_eq] using
          add_lt_add_right hdU (continuant qR s).degree)
    · exact lt_of_le_of_lt (degree_mul_le ..)
        (by simpa [U, V, mU.monic.degree_eq_natDegree, mV.monic.degree_eq_natDegree,
          mU.natDegree_eq, mV.natDegree_eq] using
          add_lt_add_left hdV (continuant qL r).degree)
  have hda : da = 0 := by
    have ht := (degree_lt_iff_coeff_zero T (r + s)).1 hTdeg (r + s) le_rfl
    have hp : (U * V).coeff (r + s) = 1 := by
      simpa [U, V, mU.natDegree_eq, mV.natDegree_eq] using
        (mU.mul mV).monic.coeff_natDegree
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
    simpa [U, mU.monic.degree_eq_natDegree, mU.natDegree_eq] using
      variation_degree qL dqL (r + 1)
  have hdR : (variation qR dqR (s + 1)).degree < V.degree := by
    simpa [V, mV.monic.degree_eq_natDegree, mV.natDegree_eq] using
      variation_degree qR dqR (s + 1)
  obtain ⟨hu1, hv1⟩ := coprime_separation U V _ _ hcop hdL hdR hw
  exact ⟨hda, branch_variation_injective qL dqL r hL hu hu1,
    branch_variation_injective qR dqR s hR hv hv1⟩

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
