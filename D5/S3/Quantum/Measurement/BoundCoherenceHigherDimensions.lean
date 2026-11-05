/- GID: D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/BoundCoherenceHigherDimensions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bound coherent states exist in every dimension at least three. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FiniteDensityPurification

/-! Uniform populations with coherence between the extremal number levels. -/

noncomputable section

namespace D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions

open scoped BigOperators Kronecker Matrix ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The truncated number observable on a system of dimension `d`. -/
def numberOp (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun n => (n.val : ℂ)

/-- An allowed unitary conserves the sum of the two local number observables. -/
def IsAllowedUnitary {d : ℕ} (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  v ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
    v * (numberOp d ⊗ₖ 1 + 1 ⊗ₖ numberOp d) =
      (numberOp d ⊗ₖ 1 + 1 ⊗ₖ numberOp d) * v

/-- The matrix entries with the specified signed number difference. -/
def mode {d : ℕ} (j : ℤ) (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun r s => if (r.val : ℤ) - s.val = j then ρ r s else 0

/-- Coherence in one mode is the trace norm of that mode. -/
def modeCoherence {d : ℕ} (j : ℤ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  traceNorm (mode j ρ)

/-- The first marginal after an allowed interaction of two identical input copies. -/
def concentrated {d : ℕ} (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (v * (ρ ⊗ₖ ρ) * vᴴ)

/-- A maximally coherent pure state has equal modulus in every number eigenvector. -/
def IsMaximallyCoherent {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ θ : Fin d → ℝ,
    ρ = Matrix.vecMulVec
      (fun n => Complex.exp (θ n * Complex.I) / (Real.sqrt d : ℂ))
      (star (fun n => Complex.exp (θ n * Complex.I) / (Real.sqrt d : ℂ)))

/-- Every dimension at least three admits a coherent, nonmaximal state whose every
positive mode fails to increase under any allowed two-copy unitary. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ ρ : Matrix (Fin d) (Fin d) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ * numberOp d ≠ numberOp d * ρ ∧
      ¬ IsMaximallyCoherent ρ ∧
      ∀ v, IsAllowedUnitary v → ∀ j : ℕ, 1 ≤ j → j ≤ d - 1 →
        modeCoherence j (concentrated v ρ) ≤ modeCoherence j ρ

private def witness (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun r s => (d : ℂ)⁻¹ * ((if r = s then 1 else 0) +
    (if r.val = d - 1 ∧ s.val = 0 then 1 else 0) +
    (if r.val = 0 ∧ s.val = d - 1 then 1 else 0))

private theorem witness_diagonal {d : ℕ} (hd : 3 ≤ d) (i : Fin d) :
    witness d i i = (d : ℂ)⁻¹ := by
  have h₁ : ¬ (i.val = d - 1 ∧ i.val = 0) := by omega
  have h₂ : ¬ (i.val = 0 ∧ i.val = d - 1) := by omega
  change (d : ℂ)⁻¹ * ((if i = i then 1 else 0) +
    (if i.val = d - 1 ∧ i.val = 0 then 1 else 0) +
    (if i.val = 0 ∧ i.val = d - 1 then 1 else 0)) = _
  simp only [ite_true, h₁, h₂, ite_false, add_zero, mul_one]

private theorem witness_endpoint {d : ℕ} (hd : 3 ≤ d) :
    witness d ⟨d - 1, by omega⟩ ⟨0, by omega⟩ = (d : ℂ)⁻¹ := by
  have hn : d - 1 ≠ 0 := by omega
  change (d : ℂ)⁻¹ * ((if (⟨d - 1, by omega⟩ : Fin d) = ⟨0, by omega⟩ then 1 else 0) +
    (if d - 1 = d - 1 ∧ (0 : ℕ) = 0 then 1 else 0) +
    (if d - 1 = 0 ∧ 0 = d - 1 then 1 else 0)) = _
  simp only [Fin.ext_iff, hn, Ne.symm hn, and_self, ite_true, ite_false,
    add_zero, zero_add, mul_one]

private theorem total_number_diagonal (d : ℕ) :
    numberOp d ⊗ₖ 1 + 1 ⊗ₖ numberOp d =
      Matrix.diagonal (fun a : Fin d × Fin d => ((a.1.val + a.2.val : ℕ) : ℂ)) := by
  change Matrix.diagonal (fun n : Fin d => (n.val : ℂ)) ⊗ₖ 1 +
    1 ⊗ₖ Matrix.diagonal (fun n : Fin d => (n.val : ℂ)) = _
  ext a b
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Prod.ext_iff, Nat.cast_add]
  split_ifs <;> simp_all

private theorem allowed_entry_zero {d : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (a b : Fin d × Fin d) (h : a.1.val + a.2.val ≠ b.1.val + b.2.val) : v a b = 0 := by
  by_contra hn
  have he := congrFun₂ hv.2 a b
  rw [total_number_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hc : ((a.1.val + a.2.val : ℕ) : ℂ) = (b.1.val + b.2.val : ℕ) :=
    mul_right_cancel₀ hn (he.symm.trans (mul_comm _ _))
  exact h (by exact_mod_cast hc)

private theorem top_gap_tensor {d : ℕ} (hd : 3 ≤ d) (k : Fin d)
    (a b : Fin d × Fin d)
    (ha : a.1.val + a.2.val = d - 1 + k.val) (hb : b.1.val + b.2.val = k.val) :
    (witness d ⊗ₖ witness d) a b = (d : ℂ)⁻¹ ^ 2 *
      ((if a = (⟨d - 1, by omega⟩, k) ∧ b = (⟨0, by omega⟩, k) then 1 else 0) +
        (if a = (k, ⟨d - 1, by omega⟩) ∧ b = (k, ⟨0, by omega⟩) then 1 else 0)) := by
  let l : Fin d := ⟨d - 1, by omega⟩
  let z : Fin d := ⟨0, by omega⟩
  change (witness d ⊗ₖ witness d) a b = (d : ℂ)⁻¹ ^ 2 *
    ((if a = (l, k) ∧ b = (z, k) then 1 else 0) +
      (if a = (k, l) ∧ b = (k, z) then 1 else 0))
  by_cases h₁ : a.1 = b.1
  · have ha₂ : a.2 = l := Fin.ext (by dsimp [l]; have := congrArg Fin.val h₁; omega)
    have hb₂ : b.2 = z := Fin.ext (by dsimp [z]; have := congrArg Fin.val h₁; omega)
    have ha₁ : a.1 = k := by
      apply Fin.ext
      have hb₀ := congrArg Fin.val hb₂
      have hab := congrArg Fin.val h₁
      dsimp [z] at hb₀
      omega
    have hb₁ : b.1 = k := h₁.symm.trans ha₁
    have hea : a = (k, l) := Prod.ext ha₁ ha₂
    have heb : b = (k, z) := Prod.ext hb₁ hb₂
    rw [hea, heb, Matrix.kroneckerMap_apply]
    rw [witness_diagonal hd, witness_endpoint hd]
    have hn : ¬ ((k, l) = (l, k) ∧ (k, z) = (z, k)) := by
      intro h
      have h₁ := congrArg (fun p => p.1.val) h.1
      have h₂ := congrArg (fun p => p.1.val) h.2
      dsimp [l, z] at h₁ h₂
      omega
    rw [ite_eq_right hn, ite_eq_left ⟨rfl, rfl⟩]
    ring
  · by_cases h₂ : a.1.val = d - 1 ∧ b.1.val = 0
    · have ha₁ : a.1 = l := Fin.ext h₂.1
      have hb₁ : b.1 = z := Fin.ext h₂.2
      have ha₂ : a.2 = k := Fin.ext (by omega)
      have hb₂ : b.2 = k := Fin.ext (by omega)
      rw [show a = (l, k) from Prod.ext ha₁ ha₂,
        show b = (z, k) from Prod.ext hb₁ hb₂, Matrix.kroneckerMap_apply]
      rw [witness_endpoint hd, witness_diagonal hd]
      have hn : ¬ ((l, k) = (k, l) ∧ (z, k) = (k, z)) := by
        intro h
        have h₁ := congrArg (fun p => p.1.val) h.1
        have h₂ := congrArg (fun p => p.1.val) h.2
        dsimp [l, z] at h₁ h₂
        omega
      rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right hn]
      ring
    · by_cases h₃ : a.1.val = 0 ∧ b.1.val = d - 1
      · omega
      · have hz : witness d a.1 b.1 = 0 := by
          change (d : ℂ)⁻¹ * ((if a.1 = b.1 then 1 else 0) +
            (if a.1.val = d - 1 ∧ b.1.val = 0 then 1 else 0) +
            (if a.1.val = 0 ∧ b.1.val = d - 1 then 1 else 0)) = 0
          simp only [h₁, h₂, h₃, ite_false, zero_add, mul_zero]
        have hn₁ : ¬ (a = (l, k) ∧ b = (z, k)) := by
          rintro ⟨hea, heb⟩
          exact h₂ ⟨congrArg (fun p => p.1.val) hea, congrArg (fun p => p.1.val) heb⟩
        have hn₂ : ¬ (a = (k, l) ∧ b = (k, z)) := by
          rintro ⟨hea, heb⟩
          exact h₁ ((congrArg Prod.fst hea).trans (congrArg Prod.fst heb).symm)
        rw [Matrix.kroneckerMap_apply, hz, zero_mul, ite_eq_right hn₁, ite_eq_right hn₂]
        ring

private theorem concentrated_last_entry {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v) :
    concentrated v (witness d) ⟨d - 1, by omega⟩ ⟨0, by omega⟩ =
      (d : ℂ)⁻¹ ^ 2 * ∑ k : Fin d,
        (v (⟨d - 1, by omega⟩, k) (⟨d - 1, by omega⟩, k) *
          star (v (⟨0, by omega⟩, k) (⟨0, by omega⟩, k)) +
        v (⟨d - 1, by omega⟩, k) (k, ⟨d - 1, by omega⟩) *
          star (v (⟨0, by omega⟩, k) (k, ⟨0, by omega⟩))) := by
  let l : Fin d := ⟨d - 1, by omega⟩
  let z : Fin d := ⟨0, by omega⟩
  change (∑ k, (v * (witness d ⊗ₖ witness d) * vᴴ) (l, k) (z, k)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (a b : Fin d × Fin d) :
      v (l, k) a * (witness d ⊗ₖ witness d) a b * star (v (z, k) b) =
      v (l, k) a * ((d : ℂ)⁻¹ ^ 2 *
        ((if a = (l, k) ∧ b = (z, k) then 1 else 0) +
          (if a = (k, l) ∧ b = (k, z) then 1 else 0))) * star (v (z, k) b) := by
    by_cases ha : a.1.val + a.2.val = d - 1 + k.val
    · by_cases hb : b.1.val + b.2.val = k.val
      · rw [top_gap_tensor hd k a b ha hb]
      · have hvb := allowed_entry_zero v hv (z, k) b (by dsimp [z]; omega)
        rw [hvb, star_zero, mul_zero, mul_zero]
    · have hva := allowed_entry_zero v hv (l, k) a (by dsimp [l]; omega)
      rw [hva, zero_mul, zero_mul, zero_mul, zero_mul]
  simp_rw [he]
  simp only [ite_and, mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem interior_term_bound {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (k : Fin d) (hk : k.val ≠ 0) (hkd : k.val ≠ d - 1) :
    ‖v (⟨d - 1, by omega⟩, k) (⟨d - 1, by omega⟩, k) *
        star (v (⟨0, by omega⟩, k) (⟨0, by omega⟩, k)) +
      v (⟨d - 1, by omega⟩, k) (k, ⟨d - 1, by omega⟩) *
        star (v (⟨0, by omega⟩, k) (k, ⟨0, by omega⟩))‖ ≤ 1 := by
  let z : Fin d := ⟨0, by omega⟩
  let l : Fin d := ⟨d - 1, by omega⟩
  have hp (r a b : Fin d × Fin d) (hab : a ≠ b) :
      ‖v r a‖ ^ 2 + ‖v r b‖ ^ 2 ≤ 1 := by
    have hr := Matrix.unitaryGroup_row_norm
      (star (⟨v, hv.1⟩ : Matrix.unitaryGroup (Fin d × Fin d) ℂ)) r
    change (∑ a, ‖star (v r a)‖ ^ 2) = 1 at hr
    simp only [norm_star] at hr
    calc
      _ = ∑ a ∈ ({a, b} : Finset (Fin d × Fin d)), ‖v r a‖ ^ 2 :=
        (Finset.sum_pair hab).symm
      _ ≤ ∑ a, ‖v r a‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = 1 := hr
  have htop := hp (l, k) (l, k) (k, l) (by
    intro h; have := congrArg (fun a => a.1.val) h; exact hkd this.symm)
  have hbottom := hp (z, k) (z, k) (k, z) (by
    intro h; have := congrArg (fun a => a.1.val) h; exact hk this.symm)
  calc
    _ ≤ ‖v (l, k) (l, k) * star (v (z, k) (z, k))‖ +
        ‖v (l, k) (k, l) * star (v (z, k) (k, z))‖ := norm_add_le _ _
    _ = ‖v (l, k) (l, k)‖ * ‖v (z, k) (z, k)‖ +
        ‖v (l, k) (k, l)‖ * ‖v (z, k) (k, z)‖ := by
      rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ 1 := by
      nlinarith [sq_nonneg (‖v (l, k) (l, k)‖ - ‖v (z, k) (z, k)‖),
        sq_nonneg (‖v (l, k) (k, l)‖ - ‖v (z, k) (k, z)‖)]

private theorem endpoint_terms_bound {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v) :
    let z : Fin d := ⟨0, by omega⟩
    let l : Fin d := ⟨d - 1, by omega⟩
    ‖(v (l, z) (l, z) + v (l, z) (z, l)) * star (v (z, z) (z, z))‖ +
      ‖v (l, l) (l, l) * star (v (z, l) (z, l) + v (z, l) (l, z))‖ ≤ 2 := by
  intro z l
  have hzl : (l, z) ≠ (z, l) := by
    intro h; have := congrArg (fun a => a.1.val) h; dsimp [l, z] at this; omega
  have hc : vᴴ * v = 1 := hv.1.1
  have hcol (a b : Fin d × Fin d) :
      (∑ r, star (v r a) * v r b) = if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun₂ hc a b
  have ht : (∑ r, star (v r (l, z) + v r (z, l)) *
      (v r (l, z) + v r (z, l))) = (2 : ℂ) := by
    simp only [star_add, add_mul, mul_add, Finset.sum_add_distrib]
    rw [hcol, hcol, hcol, hcol]
    simp only [hzl, Ne.symm hzl, ite_false, ite_true]
    norm_num
  have htotal : (∑ r, ‖v r (l, z) + v r (z, l)‖ ^ 2) = (2 : ℝ) := by
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq] at ht
    exact_mod_cast ht
  have hp : ‖v (l, z) (l, z) + v (l, z) (z, l)‖ ^ 2 +
      ‖v (z, l) (l, z) + v (z, l) (z, l)‖ ^ 2 ≤ 2 := by
    calc
      _ = ∑ r ∈ ({(l, z), (z, l)} : Finset (Fin d × Fin d)),
          ‖v r (l, z) + v r (z, l)‖ ^ 2 := (Finset.sum_pair hzl).symm
      _ ≤ ∑ r, ‖v r (l, z) + v r (z, l)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
      _ = 2 := htotal
  have he (r : Fin d × Fin d) : ‖v r r‖ ≤ 1 := by
    have hr := Matrix.unitaryGroup_row_norm
      (⟨v, hv.1⟩ : Matrix.unitaryGroup (Fin d × Fin d) ℂ) r
    have hle : ‖v r r‖ ^ 2 ≤ ∑ a, ‖v a r‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖v a r‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ r)
    change (∑ a, ‖v a r‖ ^ 2) = 1 at hr
    nlinarith [norm_nonneg (v r r)]
  calc
    _ = ‖v (l, z) (l, z) + v (l, z) (z, l)‖ * ‖v (z, z) (z, z)‖ +
        ‖v (l, l) (l, l)‖ * ‖v (z, l) (l, z) + v (z, l) (z, l)‖ := by
      rw [norm_mul, norm_mul, norm_star, norm_star, add_comm (v (z, l) (z, l))]
    _ ≤ ‖v (l, z) (l, z) + v (l, z) (z, l)‖ +
        ‖v (z, l) (l, z) + v (z, l) (z, l)‖ := by
      have h₁ := mul_le_mul_of_nonneg_left (he (z, z))
        (norm_nonneg (v (l, z) (l, z) + v (l, z) (z, l)))
      have h₂ := mul_le_mul_of_nonneg_right (he (l, l))
        (norm_nonneg (v (z, l) (l, z) + v (z, l) (z, l)))
      nlinarith
    _ ≤ 2 := by
      nlinarith [sq_nonneg (‖v (l, z) (l, z) + v (l, z) (z, l)‖ -
        ‖v (z, l) (l, z) + v (z, l) (z, l)‖),
        norm_nonneg (v (l, z) (l, z) + v (l, z) (z, l)),
        norm_nonneg (v (z, l) (l, z) + v (z, l) (z, l))]

private theorem concentrated_last_entry_bound {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v) :
    ‖concentrated v (witness d) ⟨d - 1, by omega⟩ ⟨0, by omega⟩‖ ≤ (d : ℝ)⁻¹ := by
  let z : Fin d := ⟨0, by omega⟩
  let l : Fin d := ⟨d - 1, by omega⟩
  let t : Fin d → ℂ := fun k =>
    v (l, k) (l, k) * star (v (z, k) (z, k)) +
      v (l, k) (k, l) * star (v (z, k) (k, z))
  let s := (Finset.univ.erase z).erase l
  have hzl : z ≠ l := by intro h; have := congrArg Fin.val h; dsimp [z, l] at this; omega
  have hl : l ∈ Finset.univ.erase z := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hzl.symm
  have hsum : (∑ k, t k) = (∑ k ∈ s, t k) + t l + t z := by
    rw [← Finset.sum_erase_add Finset.univ t (Finset.mem_univ z),
      ← Finset.sum_erase_add (Finset.univ.erase z) t hl]
  have hcard : s.card + 2 = d := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem (Finset.mem_univ z),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hinterior : (∑ k ∈ s, ‖t k‖) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum fun k hk => by
        have hk₁ := (Finset.mem_erase.mp hk).1
        have hk₂ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        exact interior_term_bound hd v hv k
          (fun h => hk₂ (Fin.ext h)) (fun h => hk₁ (Fin.ext h))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have ht₀ : t z = (v (l, z) (l, z) + v (l, z) (z, l)) *
      star (v (z, z) (z, z)) := by dsimp [t]; ring
  have ht₁ : t l = v (l, l) (l, l) *
      star (v (z, l) (z, l) + v (z, l) (l, z)) := by
    simp only [t, star_add, mul_add]
  have hend : ‖t z‖ + ‖t l‖ ≤ 2 := by
    rw [ht₀, ht₁]
    exact endpoint_terms_bound hd v hv
  have hn : ‖∑ k, t k‖ ≤ (d : ℝ) := by
    rw [hsum]
    calc
      _ ≤ (∑ k ∈ s, ‖t k‖) + ‖t l‖ + ‖t z‖ := by
        have h₁ := norm_add_le (∑ k ∈ s, t k) (t l)
        have h₂ := norm_add_le ((∑ k ∈ s, t k) + t l) (t z)
        have h₃ := norm_sum_le s t
        linarith
      _ ≤ (s.card : ℝ) + 2 := by linarith
      _ = d := by exact_mod_cast hcard
  rw [concentrated_last_entry hd v hv, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast]
  calc
    _ ≤ (d : ℝ)⁻¹ ^ 2 * d := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    _ = (d : ℝ)⁻¹ := by
      have hn : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      field_simp

private theorem witness_posSemidef {d : ℕ} (hd : 3 ≤ d) :
    (witness d).PosSemidef := by
  let u : Fin d → ℂ := fun i => if i.val = 0 ∨ i.val = d - 1 then 1 else 0
  let f : Fin d → ℂ := fun i => if i.val = 0 ∨ i.val = d - 1 then 0 else 1
  have hf : (Matrix.diagonal f).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr fun i => by
    dsimp [f]
    split_ifs <;> positivity
  have he : witness d = (d : ℝ)⁻¹ • (Matrix.vecMulVec u (star u) + Matrix.diagonal f) := by
    ext r s
    change (d : ℂ)⁻¹ * ((if r = s then 1 else 0) +
      (if r.val = d - 1 ∧ s.val = 0 then 1 else 0) +
      (if r.val = 0 ∧ s.val = d - 1 then 1 else 0)) = _
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul,
      u, f, Fin.ext_iff]
    split_ifs <;> simp only [map_inv₀, map_natCast, star_one, star_zero, mul_one,
      mul_zero, zero_mul, zero_add, add_zero] <;> first | omega | ring
  rw [he]
  exact ((Matrix.posSemidef_vecMulVec_self_star u).add hf).smul (by positivity :
    0 ≤ (d : ℝ)⁻¹)

private theorem witness_trace {d : ℕ} (hd : 3 ≤ d) : (witness d).trace = 1 := by
  change (∑ i, witness d i i) = 1
  simp only [witness_diagonal hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (show d ≠ 0 by omega))

private theorem witness_coherent {d : ℕ} (hd : 3 ≤ d) :
    witness d * numberOp d ≠ numberOp d * witness d := by
  let l : Fin d := ⟨d - 1, by omega⟩
  let z : Fin d := ⟨0, by omega⟩
  have hx : witness d l z = (d : ℂ)⁻¹ := witness_endpoint hd
  intro h
  have he := congrFun₂ h l z
  change (witness d * Matrix.diagonal (fun n : Fin d => (n.val : ℂ))) l z =
    (Matrix.diagonal (fun n : Fin d => (n.val : ℂ)) * witness d) l z at he
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hx] at he
  dsimp only [l, z] at he
  rw [Nat.cast_zero, mul_zero] at he
  exact (mul_ne_zero (by exact_mod_cast (show d - 1 ≠ 0 by omega))
    (inv_ne_zero (by exact_mod_cast (show d ≠ 0 by omega)))) he.symm

private theorem witness_not_maximal {d : ℕ} (hd : 3 ≤ d) :
    ¬ IsMaximallyCoherent (witness d) := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  have hx : witness d z o = 0 := by
    change (d : ℂ)⁻¹ * ((if z = o then 1 else 0) +
      (if z.val = d - 1 ∧ o.val = 0 then 1 else 0) +
      (if z.val = 0 ∧ o.val = d - 1 then 1 else 0)) = 0
    simp only [Fin.ext_iff]
    dsimp [z, o]
    split_ifs <;> first | omega | ring
  rintro ⟨θ, hθ⟩
  have he := congrFun₂ hθ z o
  rw [hx, Matrix.vecMulVec_apply] at he
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (d : ℝ))).ne'
  exact (mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _) hs)
    (star_ne_zero.mpr (div_ne_zero (Complex.exp_ne_zero _) hs))) he.symm

private theorem tensor_gap_zero {d : ℕ} (hd : 3 ≤ d) (a b : Fin d × Fin d)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j < d - 1)
    (hgap : a.1.val + a.2.val = b.1.val + b.2.val + j) :
    (witness d ⊗ₖ witness d) a b = 0 := by
  rw [Matrix.kroneckerMap_apply]
  change ((d : ℂ)⁻¹ * ((if a.1 = b.1 then 1 else 0) +
    (if a.1.val = d - 1 ∧ b.1.val = 0 then 1 else 0) +
    (if a.1.val = 0 ∧ b.1.val = d - 1 then 1 else 0))) *
    ((d : ℂ)⁻¹ * ((if a.2 = b.2 then 1 else 0) +
    (if a.2.val = d - 1 ∧ b.2.val = 0 then 1 else 0) +
    (if a.2.val = 0 ∧ b.2.val = d - 1 then 1 else 0))) = 0
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | ring

private theorem concentrated_lower_mode {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j < d - 1) :
    mode (j : ℤ) (concentrated v (witness d)) = 0 := by
  ext r s
  change (if (r.val : ℤ) - s.val = (j : ℤ) then _ else 0) = 0
  split_ifs with hrs
  · change (∑ k, (v * (witness d ⊗ₖ witness d) * vᴴ) (r, k) (s, k)) = 0
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a.1.val + a.2.val = r.val + k.val
    · by_cases hb : b.1.val + b.2.val = s.val + k.val
      · rw [tensor_gap_zero hd a b j hj hjd (by omega), mul_zero, zero_mul]
      · rw [allowed_entry_zero v hv (s, k) b (by dsimp only; omega), star_zero, mul_zero]
    · rw [allowed_entry_zero v hv (r, k) a (by dsimp only; omega), zero_mul, zero_mul]
  · rfl

private theorem last_mode_traceNorm {d : ℕ} (hd : 3 ≤ d)
    (x : Matrix (Fin d) (Fin d) ℂ) :
    modeCoherence (d - 1 : ℕ) x = ‖x ⟨d - 1, by omega⟩ ⟨0, by omega⟩‖ := by
  let l : Fin d := ⟨d - 1, by omega⟩
  let z : Fin d := ⟨0, by omega⟩
  have hm : mode (d - 1 : ℕ) x = Matrix.single l z (x l z) := by
    ext r s
    rw [Matrix.single_apply]
    change (if (r.val : ℤ) - s.val = (d - 1 : ℕ) then x r s else 0) = _
    by_cases h : r = l ∧ s = z
    · obtain ⟨rfl, rfl⟩ := h
      rw [ite_eq_left (by dsimp [l, z]; omega), ite_eq_left ⟨rfl, rfl⟩]
    · have hg : (r.val : ℤ) - s.val ≠ (d - 1 : ℕ) := by
        intro hg
        apply h
        constructor <;> apply Fin.ext <;> dsimp [l, z] <;> omega
      rw [ite_eq_right hg, ite_eq_right (fun hh => h ⟨hh.1.symm, hh.2.symm⟩)]
  have hy : (Matrix.single z z (‖x l z‖ : ℂ)).PosSemidef := by
    rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hs : CFC.sqrt ((Matrix.single l z (x l z))ᴴ * Matrix.single l z (x l z)) =
      Matrix.single z z (‖x l z‖ : ℂ) := by
    apply (CFC.sqrt_eq_iff _ _ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
      hy.nonneg).mpr
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same,
      Matrix.single_mul_single_same]
    congr 1
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, ← pow_two, Complex.ofReal_pow]
  change traceNorm (mode (d - 1 : ℕ) x) = _
  rw [hm, traceNorm, hs, Matrix.trace_single_eq_same]
  rfl

private theorem witness_last_coherence {d : ℕ} (hd : 3 ≤ d) :
    modeCoherence (d - 1 : ℕ) (witness d) = (d : ℝ)⁻¹ := by
  rw [last_mode_traceNorm hd]
  rw [witness_endpoint hd, norm_inv, Complex.norm_natCast]

private theorem witness_no_concentration {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d - 1) :
    modeCoherence j (concentrated v (witness d)) ≤ modeCoherence j (witness d) := by
  rcases hjd.eq_or_lt with h | h
  · subst j
    rw [last_mode_traceNorm hd, witness_last_coherence hd]
    exact concentrated_last_entry_bound hd v hv
  · change traceNorm (mode j (concentrated v (witness d))) ≤ traceNorm (mode j (witness d))
    rw [concentrated_lower_mode hd v hv j hj h]
    have hz : traceNorm (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
      rw [traceNorm, Matrix.conjTranspose_zero, Matrix.zero_mul, CFC.sqrt_zero,
        Matrix.trace_zero]
      rfl
    rw [hz]
    exact traceNorm_nonneg _

theorem result : claim := by
  intro d hd
  exact ⟨witness d, witness_posSemidef hd, witness_trace hd, witness_coherent hd,
    witness_not_maximal hd, fun v hv j hj hjd => witness_no_concentration hd v hv j hj hjd⟩

end D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
