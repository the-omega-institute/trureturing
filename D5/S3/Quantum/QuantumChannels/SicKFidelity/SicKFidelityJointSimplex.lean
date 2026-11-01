/- GID: D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact trace-preserving linear reconstruction and CPTP joint k-fidelity simplex range. -/

import D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight

/-! # Trace-preserving linear reconstruction and CPTP joint `k`-fidelity simplex geometry -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight

/-- Vertices `V_0, …, V_n ∈ ℝ^n` of the joint `k`-fidelity `n`-simplex:
`V_0 = (1, …, 1)` and `(V_w)_k = (-1)^k 3^{-w} C(w - 1, k)` for `1 ≤ w ≤ n`, `0 ≤ k ≤ n - 1`. -/
def simplexVertex (n : ℕ) : Fin (n + 1) → Fin n → ℝ :=
  Fin.cases (fun _ => 1) fun j k =>
    (-1 : ℝ) ^ k.val * (3 : ℝ)⁻¹ ^ (j.val + 1) * (Nat.choose j.val k.val : ℝ)
/-- Joint vector `(F_0(Λ), …, F_{n-1}(Λ)) ∈ ℝ^n` of real SIC `k`-fidelities of an `n`-qubit map. -/
def jointKFidelityVec {n : ℕ} (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (Λ : QubitMap n) : Fin n → ℝ :=
  fun k => realKFidelity ρ k.val Λ
/-- Set of joint `k`-fidelity vectors `(F_0(Λ), …, F_{n-1}(Λ))` realized by `n`-qubit CPTP maps. -/
def jointKFidelityRange (n : ℕ) (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    Set (Fin n → ℝ) :=
  {v | ∃ Λ : QubitMap n, Λ.IsCompletelyPositive ∧ Λ.IsTracePreserving ∧
    v = jointKFidelityVec ρ Λ}

private theorem geom_neg_two_sum_complex (n : ℕ) :
    3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k + (-2 : ℂ) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linear_combination ih
private theorem geom_neg_two_sum_real (n : ℕ) :
    3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k + (-2 : ℝ) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linear_combination ih
private theorem binom_two_pow_three_inv_complex {n w : ℕ} (hw : w ∈ Finset.Icc 1 n) :
    3 * (3 : ℂ)⁻¹ ^ w *
      ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * (-1 : ℂ) ^ k * (Nat.choose (w - 1) k : ℂ) = 1 := by
  obtain ⟨hw1, hwn⟩ := Finset.mem_Icc.mp hw
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, (Nat.sub_add_cancel hw1).symm⟩
  simp only [Nat.add_sub_cancel]
  have hsub : ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * (-1 : ℂ) ^ k * (Nat.choose m k : ℂ) =
      ∑ k ∈ Finset.range (m + 1), (2 : ℂ) ^ k * (1 : ℂ) ^ (m - k) * (Nat.choose m k : ℂ) := by
    rw [← Finset.sum_subset (Finset.range_mono hwn)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_pow, show (-2 : ℂ) * (-1 : ℂ) = 2 by norm_num, one_pow, mul_one]
    · intro k _ hk; simp only [Finset.mem_range, not_lt] at hk
      simp [Nat.choose_eq_zero_of_lt (by omega : m < k)]
  rw [hsub, ← add_pow, show (2 : ℂ) + 1 = 3 by norm_num, pow_succ, ← mul_assoc]
  calc 3 * (3 : ℂ)⁻¹ ^ m * (3 : ℂ)⁻¹ * (3 : ℂ) ^ m
      = (3 * (3 : ℂ)⁻¹) * ((3 : ℂ)⁻¹ ^ m * (3 : ℂ) ^ m) := by ring
    _ = 1 := by rw [← mul_pow]; norm_num
private theorem binom_two_pow_three_inv_real {n m : ℕ} (hmn : m < n) :
    3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val *
      ((-1 : ℝ) ^ k.val * (3 : ℝ)⁻¹ ^ (m + 1) * (Nat.choose m k.val : ℝ)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (-2 : ℝ) ^ k *
    ((-1 : ℝ) ^ k * (3 : ℝ)⁻¹ ^ (m + 1) * (Nat.choose m k : ℝ))) n]
  have hc := binom_two_pow_three_inv_complex (n := n) (w := m + 1)
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hre := congrArg Complex.re hc
  simp only [Nat.add_sub_cancel] at hre
  have hlhs : (3 * (3 : ℂ)⁻¹ ^ (m + 1) *
      ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * (-1 : ℂ) ^ k * (Nat.choose m k : ℂ)) =
      ((3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * (3 : ℝ)⁻¹ ^ (m + 1) * (Nat.choose m k : ℝ)) : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hlhs, Complex.ofReal_re, Complex.one_re] at hre; exact hre

/-- Universal linear relation among all `n` SIC `k`-fidelities `F_0, …, F_{n-1}` and the
entanglement process fidelity `F` for every trace-preserving `ℂ`-linear `n`-qubit map (without
requiring complete positivity), together with exact alternating reconstruction of `F(Λ)` and its
real projection for completely positive trace-preserving maps. -/
theorem tp_exact_fidelity_reconstruction (n : ℕ)
    (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ∀ i : Fin n, IsQubitSICProjector (ρ i))
    (Λ : QubitMap n) (hTP : Λ.IsTracePreserving) :
    3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * kFidelity ρ k Λ +
        (-2 : ℂ) ^ n * processFidelity Λ = 1 ∧
    processFidelity Λ =
      ((-2 : ℂ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * kFidelity ρ k Λ) ∧
    (Λ.IsCompletelyPositive →
      3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ +
          (-2 : ℝ) ^ n * realProcessFidelity Λ = 1 ∧
      realProcessFidelity Λ =
        ((-2 : ℝ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ)) := by
  have hchar := pauli_process_matrix_and_fidelity_characterization n
  have hF0 : processFidelity Λ = pauliWeightSum Λ 0 :=
    ((hchar.2.1 Λ).1).trans ((hchar.2.1 Λ).2.1).symm
  have hsum1 : ∑ w ∈ Finset.range (n + 1), pauliWeightSum Λ w = 1 := ((hchar.2.2.1 Λ).2 hTP).2
  have hrel : 3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * kFidelity ρ k Λ +
      (-2 : ℂ) ^ n * processFidelity Λ = 1 := by
    simp_rw [(kFidelity_eq_pauliWeight_alternating_sum n _ ρ hρ Λ).1, hF0]
    trans (3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k + (-2 : ℂ) ^ n) * pauliWeightSum Λ 0 +
        ∑ w ∈ Finset.Icc 1 n, (3 * (3 : ℂ)⁻¹ ^ w *
          ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * (-1 : ℂ) ^ k * (Nat.choose (w - 1) k : ℂ)) *
            pauliWeightSum Λ w
    · have ha : (3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k + (-2 : ℂ) ^ n) * pauliWeightSum Λ 0 =
          3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * pauliWeightSum Λ 0 +
            (-2 : ℂ) ^ n * pauliWeightSum Λ 0 := by rw [add_mul, mul_assoc, Finset.sum_mul]
      have hb : 3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k *
          (pauliWeightSum Λ 0 + (-1 : ℂ) ^ k * ∑ w ∈ Finset.Icc 1 n,
            ((3 : ℂ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℂ)) * pauliWeightSum Λ w) =
          3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * pauliWeightSum Λ 0 +
          3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * ((-1 : ℂ) ^ k * ∑ w ∈ Finset.Icc 1 n,
            ((3 : ℂ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℂ)) * pauliWeightSum Λ w) := by
        simp_rw [mul_add, Finset.sum_add_distrib]; rw [mul_add]
      rw [ha, hb, add_right_comm]; congr 1
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    · rw [geom_neg_two_sum_complex n, one_mul,
        Finset.sum_congr rfl fun w hw => by rw [binom_two_pow_three_inv_complex hw, one_mul],
        ← hsum1, show Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) by
          ext w; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp)]
  have hinv : processFidelity Λ =
      ((-2 : ℂ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℂ) ^ k * kFidelity ρ k Λ) := by
    have hne : (-2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    apply mul_left_cancel₀ hne
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]; linear_combination hrel
  refine ⟨hrel, hinv, fun hCP => ?_⟩
  have hrel_re : 3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ +
      (-2 : ℝ) ^ n * realProcessFidelity Λ = 1 := by
    have hc : ((3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ +
        (-2 : ℝ) ^ n * realProcessFidelity Λ : ℝ) : ℂ) = 1 := by
      rw [← hrel]; push_cast
      rw [((hchar.2.2.2.1 Λ hCP).2.2)]
      congr 2; exact Finset.sum_congr rfl fun k _ => by
        rw [((kFidelity_eq_pauliWeight_alternating_sum n k ρ hρ Λ).2.2.2 hCP).1]
    exact Complex.ofReal_inj.mp (by simpa using hc)
  have hinv_re : realProcessFidelity Λ =
      ((-2 : ℝ) ^ n)⁻¹ * (1 - 3 * ∑ k ∈ Finset.range n, (-2 : ℝ) ^ k * realKFidelity ρ k Λ) := by
    have hne : (-2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    apply mul_left_cancel₀ hne
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]; linear_combination hrel_re
  exact ⟨hrel_re, hinv_re⟩

private def canonicalLabel (n w : ℕ) : PauliLabel n := fun i => if i.val < w then 3 else 0
private theorem hammingWeight_canonicalLabel {n w : ℕ} (hw : w ≤ n) :
    hammingWeight (canonicalLabel n w) = w := by
  unfold hammingWeight canonicalLabel
  let f : Fin w → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hw⟩
  have himg : Finset.univ.filter (fun i : Fin n => (if i.val < w then (3 : Fin 4) else 0) ≠ 0) =
      Finset.univ.image f := by
    ext i; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, f]
    refine ⟨fun hi => ?_, fun ⟨j, hj⟩ => by rw [← hj]; simp [j.isLt]⟩
    by_cases hlt : i.val < w
    · exact ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    · simp [hlt] at hi
  have hf : Function.Injective f := fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)
  rw [himg, Finset.card_image_of_injective Finset.univ hf]; simp
private theorem simplexVertex_affineIndependent (n : ℕ) :
    AffineIndependent ℝ (simplexVertex n) := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hv] at huv
  let d : Fin (n + 1) → ℝ := fun i => u i - v i
  have hd_sum : ∑ i : Fin (n + 1), d i = 0 := by simp [d, Finset.sum_sub_distrib, hu, hv]
  have hd_vec (k : Fin n) : ∑ i : Fin (n + 1), d i * simplexVertex n i k = 0 := by
    have hk := congrArg (fun f => f k) huv
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
    simp_rw [d, sub_mul, Finset.sum_sub_distrib, hk, sub_self]
  have hd0 : d 0 = 0 := by
    have hlin : 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val *
        (∑ i : Fin (n + 1), d i * simplexVertex n i k) = 0 := by simp_rw [hd_vec]; simp
    have hswap : 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val *
        (∑ i : Fin (n + 1), d i * simplexVertex n i k) =
        ∑ i : Fin (n + 1), d i * (3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val * simplexVertex n i k) := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hswap, Fin.sum_univ_succ] at hlin
    have hv0 : 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val * simplexVertex n 0 k = 1 - (-2 : ℝ) ^ n := by
      simp only [simplexVertex, Fin.cases_zero, mul_one]
      rw [Fin.sum_univ_eq_sum_range (fun k => (-2 : ℝ) ^ k) n]
      linear_combination geom_neg_two_sum_real n
    have hvs (j : Fin n) : 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val * simplexVertex n j.succ k = 1 := by
      simpa [simplexVertex] using binom_two_pow_three_inv_real j.isLt
    simp_rw [hv0, hvs, mul_one] at hlin
    have hsum_succ : d 0 + ∑ j : Fin n, d j.succ = 0 := by rwa [Fin.sum_univ_succ] at hd_sum
    have h0eq : (-2 : ℝ) ^ n * d 0 = 0 := by linear_combination hsum_succ - hlin
    exact (mul_eq_zero.mp h0eq).resolve_left (pow_ne_zero n (by norm_num))
  have hd_succ_all : ∀ r : ℕ, ∀ j : Fin n, n - r ≤ j.val → d j.succ = 0 := by
    intro r; induction r with
    | zero => intro j hj; omega
    | succ r ih =>
      intro j hj
      by_cases hlt : n - r ≤ j.val
      · exact ih j hlt
      · have hjeq : j.val = n - (r + 1) := by omega
        have hk := hd_vec j; rw [Fin.sum_univ_succ, hd0, zero_mul, zero_add] at hk
        rw [Fintype.sum_eq_single j fun m hm => by
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hm) with hmlt | hmgt
          · simp [simplexVertex, Nat.choose_eq_zero_of_lt hmlt]
          · rw [ih m (by omega), zero_mul]] at hk
        simp only [simplexVertex, Fin.cases_succ, Nat.choose_self, Nat.cast_one, mul_one] at hk
        have hnz : (-1 : ℝ) ^ j.val * (3 : ℝ)⁻¹ ^ (j.val + 1) ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
        exact (mul_eq_zero.mp hk).resolve_right hnz
  ext i; refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_eq_zero.mp hd0
  · exact sub_eq_zero.mp (hd_succ_all n j (by simp))

/-- Joint range of `(F_0(Λ), …, F_{n-1}(Λ))` over `n`-qubit CPTP maps `Λ`:
the `n + 1` vertices `V_0, …, V_n` are affinely independent in `ℝ^n`, the realized joint range is
the `n`-simplex `conv{V_0, …, V_n}`, the Pauli-weight sums `(Q_0(Λ), …, Q_n(Λ))` are the unique
barycentric coordinates of `(F_0(Λ), …, F_{n-1}(Λ))` in this simplex, and the process fidelity
`F(Λ) = Q_0(Λ)` is uniquely recovered by the alternating linear formula. -/
theorem cptp_joint_kFidelity_simplex_range (n : ℕ)
    (ρ : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ∀ i : Fin n, IsQubitSICProjector (ρ i)) :
    AffineIndependent ℝ (simplexVertex n) ∧
    jointKFidelityRange n ρ = convexHull ℝ (Set.range (simplexVertex n)) ∧
    (∀ Λ : QubitMap n, Λ.IsCompletelyPositive → Λ.IsTracePreserving →
      (∀ i : Fin (n + 1), 0 ≤ realWeightSum Λ i.val) ∧
      ∑ i : Fin (n + 1), realWeightSum Λ i.val = 1 ∧
      ∑ i : Fin (n + 1), realWeightSum Λ i.val • simplexVertex n i = jointKFidelityVec ρ Λ ∧
      ∀ c : Fin (n + 1) → ℝ, ∑ i : Fin (n + 1), c i = 1 →
        ∑ i : Fin (n + 1), c i • simplexVertex n i = jointKFidelityVec ρ Λ →
          ∀ i : Fin (n + 1), c i = realWeightSum Λ i.val) ∧
    (∀ Λ : QubitMap n, Λ.IsCompletelyPositive → Λ.IsTracePreserving →
      realProcessFidelity Λ = realWeightSum Λ 0 ∧
      realProcessFidelity Λ =
        ((-2 : ℝ) ^ n)⁻¹ * (1 - 3 * ∑ k : Fin n, (-2 : ℝ) ^ k.val * jointKFidelityVec ρ Λ k)) := by
  have haff := simplexVertex_affineIndependent n
  have hchar := pauli_process_matrix_and_fidelity_characterization n
  have hbary (Λ : QubitMap n) (hCP : Λ.IsCompletelyPositive) (hTP : Λ.IsTracePreserving) :
      (∀ i : Fin (n + 1), 0 ≤ realWeightSum Λ i.val) ∧
      ∑ i : Fin (n + 1), realWeightSum Λ i.val = 1 ∧
      ∑ i : Fin (n + 1), realWeightSum Λ i.val • simplexVertex n i = jointKFidelityVec ρ Λ := by
    have h0 (i : Fin (n + 1)) : 0 ≤ realWeightSum Λ i.val := ((hchar.2.2.2.1 Λ hCP).2.1 i.val).2
    have h1 : ∑ i : Fin (n + 1), realWeightSum Λ i.val = 1 := by
      have hre := congrArg Complex.re (((hchar.2.2.1 Λ).2 hTP).2)
      rw [Complex.one_re, Fin.sum_univ_eq_sum_range (fun w => realWeightSum Λ w) (n + 1)] at *
      simpa [realWeightSum] using hre
    refine ⟨h0, h1, ?_⟩
    ext k; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, jointKFidelityVec]
    rw [Fin.sum_univ_succ, ((kFidelity_eq_pauliWeight_alternating_sum n k.val ρ hρ Λ).2.2.2 hCP).2]
    simp only [Fin.val_zero, simplexVertex, Fin.cases_zero, mul_one]; congr 1
    rw [Finset.mul_sum, show Finset.Icc 1 n = Finset.univ.image (fun j : Fin n => j.val + 1) by
      ext w; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨fun ⟨hw1, hwn⟩ => ⟨⟨w - 1, by omega⟩, by dsimp; omega⟩, fun ⟨j, hj⟩ => by omega⟩,
      Finset.sum_image (fun _ _ _ _ h => Fin.ext (by omega))]
    exact Finset.sum_congr rfl fun j _ => by simp [Fin.cases_succ]; ring
  let S : Set (Fin n → ℝ) := {v | ∃ P : Fin (n + 1) → ℝ,
    (∀ i, 0 ≤ P i) ∧ ∑ i, P i = 1 ∧ ∑ i, P i • simplexVertex n i = v}
  have hRS : jointKFidelityRange n ρ = S := by
    ext v; constructor
    · rintro ⟨Λ, hCP, hTP, rfl⟩
      obtain ⟨h0, h1, hv⟩ := hbary Λ hCP hTP
      exact ⟨fun i => realWeightSum Λ i.val, h0, h1, hv⟩
    · rintro ⟨P, hP0, hP1, rfl⟩
      let q : PauliLabel n → ℝ :=
        fun β => ∑ i : Fin (n + 1), if β = canonicalLabel n i.val then P i else 0
      have hq0 (β : PauliLabel n) : 0 ≤ q β :=
        Finset.sum_nonneg fun i _ => by by_cases h : β = canonicalLabel n i.val <;> simp [h, hP0 i]
      have hq1 : ∑ β : PauliLabel n, q β = 1 := by dsimp [q]; rw [Finset.sum_comm]; simp [hP1]
      have hpc := hchar.2.2.2.2 q
      have hCP := hpc.2.1 hq0; have hTP := hpc.2.2 hq1
      have hWi (i : Fin (n + 1)) : realWeightSum (pauliChannel q) i.val = P i := by
        unfold realWeightSum pauliWeightSum
        have htw (β : PauliLabel n) : pauliTwirlWeight (pauliChannel q) β = (q β : ℂ) := by
          simpa [pauliTwirlWeight] using hpc.1 β β
        simp_rw [htw]; rw [← Complex.ofReal_sum, Complex.ofReal_re]
        dsimp [q]; rw [Finset.sum_comm]
        rw [Fintype.sum_eq_single i fun j hj => Finset.sum_eq_zero fun β hβ => by
          by_cases hEq : β = canonicalLabel n j.val
          · subst hEq; exfalso; apply hj; apply Fin.ext
            have hw := (Finset.mem_filter.mp hβ).2
            rw [hammingWeight_canonicalLabel (Nat.lt_succ_iff.mp j.isLt)] at hw; exact hw
          · simp [hEq]]
        rw [Finset.sum_eq_single (canonicalLabel n i.val)]
        · simp
        · intro β _ hne; simp [hne]
        · intro hnot; exfalso; apply hnot
          simp [hammingWeight_canonicalLabel (Nat.lt_succ_iff.mp i.isLt)]
      refine ⟨pauliChannel q, hCP, hTP, ?_⟩
      rw [← (hbary (pauliChannel q) hCP hTP).2.2]
      exact Finset.sum_congr rfl fun i _ => by rw [hWi i]
  have hrange : jointKFidelityRange n ρ = convexHull ℝ (Set.range (simplexVertex n)) := by
    rw [hRS]; apply Set.Subset.antisymm
    · rintro _ ⟨P, hP0, hP1, rfl⟩
      exact (convex_convexHull ℝ (Set.range (simplexVertex n))).sum_mem (fun i _ => hP0 i) hP1
        (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
    · refine convexHull_min ?_ ?_
      · rintro _ ⟨i, rfl⟩
        exact ⟨fun j => if j = i then 1 else 0, fun j => by dsimp; split_ifs <;> norm_num,
          by simp, by simp [ite_smul]⟩
      · rintro _ ⟨P₁, hP₁0, hP₁1, rfl⟩ _ ⟨P₂, hP₂0, hP₂1, rfl⟩ a b ha hb hab
        refine ⟨fun i => a * P₁ i + b * P₂ i, fun i => add_nonneg (mul_nonneg ha (hP₁0 i))
          (mul_nonneg hb (hP₂0 i)), ?_, ?_⟩
        · simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP₁1, hP₂1, mul_one, hab]
        · simp_rw [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  refine ⟨haff, hrange, fun Λ hCP hTP => ?_, fun Λ hCP hTP => ?_⟩
  · obtain ⟨h0, h1, hv⟩ := hbary Λ hCP hTP
    refine ⟨h0, h1, hv, fun c hc1 hcv => ?_⟩
    have hinj := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ
      (simplexVertex n)).mp haff
    have heq := hinj c (fun i => realWeightSum Λ i.val) hc1 h1 (by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hc1,
        Finset.affineCombination_eq_linear_combination _ _ _ h1, hcv, hv])
    exact fun i => congrFun heq i
  · refine ⟨Complex.ofReal_inj.mp (by
      rw [(hchar.2.2.2.1 Λ hCP).2.2, ((hchar.2.2.2.1 Λ hCP).2.1 0).1,
        (hchar.2.1 Λ).1, (hchar.2.1 Λ).2.1]), ?_⟩
    dsimp [jointKFidelityVec]
    rw [((tp_exact_fidelity_reconstruction n ρ hρ Λ hTP).2.2 hCP).2,
      ← Fin.sum_univ_eq_sum_range (fun k => (-2 : ℝ) ^ k * realKFidelity ρ k Λ) n]

end D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityJointSimplex
