/- GID: D5/S3/QuantumBounds/HighSpinCHSHNonviolation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/HighSpinCHSHNonviolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Local spin components satisfy the CHSH bound for every spin at least one. -/

import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import D5.S3.QuantumBounds.LandauCommutingCollapse
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Analysis.Matrix.Order

/-! The symmetric-qubit dilation of linear spin observables gives the CHSH bound. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder symmDiff
open Matrix Complex
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (spinComponent)

namespace D5.S3.QuantumBounds.HighSpinCHSHNonviolation

/-- A measurement direction has Euclidean length one. -/
def unit (u : Fin 3 → ℝ) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

/-- The CHSH operator for the source's linear spin observables. -/
def chshOperator (n : ℕ) (a c b d : Fin 3 → ℝ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  spinComponent n a ⊗ₖ spinComponent n b +
    spinComponent n a ⊗ₖ spinComponent n d +
    spinComponent n c ⊗ₖ spinComponent n b -
    spinComponent n c ⊗ₖ spinComponent n d

/-- Nonviolation for every density matrix and every four local spin directions, n = 2s ≥ 2. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → ∀ a c b d : Fin 3 → ℝ,
        unit a → unit c → unit b → unit d →
          ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2

private def dicke (n : ℕ) : Matrix (Finset (Fin n)) (Fin (n + 1)) ℂ :=
  fun x k => if x.card = k.val then (1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) else 0

private def slotPauli (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun x y =>
    (if x = y then (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) else 0) +
    (if y = x ∆ {r} then
      (u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ)) else 0)

private def dilation (n : ℕ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  dicke n ⊗ₖ dicke n

private def liftedOperator (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Finset (Fin n) × Finset (Fin n)) ℂ :=
  let r : Fin n := ⟨0, by omega⟩
  let t : Fin n := ⟨1, by omega⟩
  let α := slotPauli n r a ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let γ := slotPauli n t c ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let β := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n r b
  let δ := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n t d
  α * (β + δ) + γ * (β - δ)

private lemma weight_count (n k : ℕ) :
    (Finset.univ.filter (fun x : Finset (Fin n) => x.card = k)).card = n.choose k := by
  have hf : Finset.univ.filter (fun x : Finset (Fin n) => x.card = k) =
      (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext x
    simp
  rw [hf, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma dicke_entry (n : ℕ) (x : Finset (Fin n)) (k : Fin (n + 1)) :
    dicke n x k = if x.card = k.val then
      ((1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) : ℂ) else 0 := rfl

private lemma dicke_isometry (n : ℕ) : (dicke n)ᴴ * dicke n = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    have hh (x : Finset (Fin n)) :
        (dicke n)ᴴ i x * dicke n x i = if x.card = i.val then
          (((1 / Real.sqrt (n.choose i.val : ℝ) : ℝ) : ℂ)) ^ 2 else 0 := by
      by_cases hx : x.card = i.val <;>
        simp [conjTranspose_apply, dicke_entry, hx, pow_two]
    simp_rw [hh]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, weight_count, Matrix.one_apply_eq]
    have hc : (n.choose i.val : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : i.val ≤ n)))
    have hn : (n.choose i.val : ℝ) * (1 / Real.sqrt (n.choose i.val : ℝ)) ^ 2 = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp [hc]
    exact_mod_cast hn
  · rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hi : x.card = i.val
    · have hj : x.card ≠ j.val := fun hj => hij (Fin.ext (hi.symm.trans hj))
      simp [conjTranspose_apply, dicke_entry, hj]
    · simp [conjTranspose_apply, dicke_entry, hi]

private lemma slot_compression (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (dicke n)ᴴ * slotPauli n r u * dicke n = (2 / n : ℂ) • spinComponent n u := by
  sorry

private lemma slot_entry (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ)
    (x y : Finset (Fin n)) : slotPauli n r u x y =
      (if x = y then (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) else 0) +
      (if y = x ∆ {r} then
        (u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ)) else 0) := rfl

private lemma flip_ne (n : ℕ) (r : Fin n) (x : Finset (Fin n)) : x ∆ {r} ≠ x := by
  intro h
  have he := Finset.ext_iff.mp h r
  by_cases hr : r ∈ x <;> simp [Finset.mem_symmDiff, hr] at he

private lemma flip_eq (n : ℕ) (r : Fin n) (x y : Finset (Fin n)) :
    x = y ∆ {r} ↔ y = x ∆ {r} := by
  constructor <;> intro h <;> rw [h, symmDiff_symmDiff_cancel_right]

private lemma slot_left_mul {κ : Type*} (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ)
    (m : Matrix (Finset (Fin n)) κ ℂ) (x : Finset (Fin n)) (y : κ) :
    (slotPauli n r u * m) x y =
      (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) * m x y +
      ((u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ))) *
        m (x ∆ {r}) y := by
  simp only [Matrix.mul_apply, slot_entry, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  simp

private lemma slot_hermitian (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (slotPauli n r u).IsHermitian := by
  change (slotPauli n r u)ᴴ = slotPauli n r u
  ext x y
  change star (slotPauli n r u y x) = slotPauli n r u x y
  by_cases hxy : x = y
  · subst y
    have hf := flip_ne n r x
    by_cases hr : r ∈ x <;> simp [slot_entry, hf.symm, hr]
  · by_cases hy : y = x ∆ {r}
    · subst y
      have hf := flip_ne n r x
      by_cases hr : r ∈ x <;>
        simp [slot_entry, hf, hf.symm, symmDiff_symmDiff_cancel_right,
          Finset.mem_symmDiff, hr]
    · have hx : x ≠ y ∆ {r} := fun h => hy ((flip_eq n r x y).mp h)
      simp [slot_entry, hxy, Ne.symm hxy, hy, hx]

private lemma slot_square (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) (hu : unit u) :
    slotPauli n r u * slotPauli n r u = 1 := by
  have huC : (u 0 : ℂ) ^ 2 + (u 1 : ℂ) ^ 2 + (u 2 : ℂ) ^ 2 = 1 := by
    exact_mod_cast hu
  ext x y
  rw [slot_left_mul, slot_entry, slot_entry, symmDiff_symmDiff_cancel_right]
  have hf := flip_ne n r x
  by_cases hxy : x = y
  · subst y
    by_cases hr : r ∈ x <;>
      simp [hf, hf.symm, Finset.mem_symmDiff, hr]
    all_goals ring_nf; simp only [I_sq]; linear_combination huC
  · by_cases hy : y = x ∆ {r}
    · subst y
      by_cases hr : r ∈ x <;>
        simp [hf, hf.symm, Finset.mem_symmDiff, hr]
      all_goals ring
    · have hfy : x ∆ {r} ≠ y := Ne.symm hy
      simp [hxy, Ne.symm hxy, hy, hfy]

private lemma slots_commute (n : ℕ) (r t : Fin n) (hrt : r ≠ t)
    (u v : Fin 3 → ℝ) : Commute (slotPauli n r u) (slotPauli n t v) := by
  change slotPauli n r u * slotPauli n t v = slotPauli n t v * slotPauli n r u
  ext x y
  rw [slot_left_mul, slot_left_mul]
  have hr : r ∈ x ∆ {t} ↔ r ∈ x := by simp [Finset.mem_symmDiff, hrt]
  have ht : t ∈ x ∆ {r} ↔ t ∈ x := by simp [Finset.mem_symmDiff, hrt.symm]
  simp only [slot_entry, hr, ht, symmDiff_right_comm x {r} {t},
    (eq_comm : x ∆ {r} = y ↔ y = x ∆ {r}),
    (eq_comm : x ∆ {t} = y ↔ y = x ∆ {t})]
  split_ifs <;> ring

private lemma dilation_isometry (n : ℕ) : (dilation n)ᴴ * dilation n = 1 := by
  change (dicke n ⊗ₖ dicke n)ᴴ * (dicke n ⊗ₖ dicke n) = 1
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, dicke_isometry, one_kronecker_one]

private lemma lifted_expansion (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    liftedOperator n hn a c b d =
      slotPauli n ⟨0, by omega⟩ a ⊗ₖ slotPauli n ⟨0, by omega⟩ b +
      slotPauli n ⟨0, by omega⟩ a ⊗ₖ slotPauli n ⟨1, by omega⟩ d +
      slotPauli n ⟨1, by omega⟩ c ⊗ₖ slotPauli n ⟨0, by omega⟩ b -
      slotPauli n ⟨1, by omega⟩ c ⊗ₖ slotPauli n ⟨1, by omega⟩ d := by
  change (_ ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)) *
      ((1 ⊗ₖ _) + (1 ⊗ₖ _)) + (_ ⊗ₖ 1) * ((1 ⊗ₖ _) - (1 ⊗ₖ _)) = _
  simp only [mul_add, mul_sub, ← mul_kronecker_mul, mul_one, one_mul]
  abel

private lemma chsh_dilation (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    chshOperator n a c b d = ((n : ℂ) / 2) ^ 2 •
      ((dilation n)ᴴ * liftedOperator n hn a c b d * dilation n) := by
  have hk (r t : Fin n) (u v : Fin 3 → ℝ) :
      (dilation n)ᴴ * (slotPauli n r u ⊗ₖ slotPauli n t v) * dilation n =
        (2 / n : ℂ) ^ 2 • (spinComponent n u ⊗ₖ spinComponent n v) := by
    change (dicke n ⊗ₖ dicke n)ᴴ * _ * (dicke n ⊗ₖ dicke n) = _
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
      slot_compression, slot_compression, smul_kronecker, kronecker_smul, smul_smul,
      ← pow_two]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hscale : ((n : ℂ) / 2) ^ 2 * (2 / n : ℂ) ^ 2 = 1 := by
    field_simp
  rw [lifted_expansion]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    hk, ← smul_add, ← smul_sub,
    smul_smul, hscale, one_smul]
  rfl

private lemma lifted_hermitian (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    (liftedOperator n hn a c b d).IsHermitian := by
  rw [lifted_expansion]
  have hh (r t : Fin n) (u v : Fin 3 → ℝ) :
      (slotPauli n r u ⊗ₖ slotPauli n t v).IsHermitian := by
    change (_ ⊗ₖ _)ᴴ = _
    rw [conjTranspose_kronecker, (slot_hermitian n r u).eq,
      (slot_hermitian n t v).eq]
  exact (((hh _ _ _ _).add (hh _ _ _ _)).add (hh _ _ _ _)).sub (hh _ _ _ _)

private lemma lifted_square (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    (liftedOperator n hn a c b d) ^ 2 = (4 : ℂ) • 1 := by
  rw [lifted_expansion]
  have hfour : (4 : ℂ) • (1 : Matrix (Finset (Fin n) × Finset (Fin n))
      (Finset (Fin n) × Finset (Fin n)) ℂ) = (4 : ℕ) • 1 := by
    ext x y
    by_cases h : x = y <;> simp [h]
  rw [hfour]
  exact D5.S3.QuantumBounds.LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes
    (slotPauli n ⟨0, by omega⟩ a) (slotPauli n ⟨1, by omega⟩ c)
    (slotPauli n ⟨0, by omega⟩ b) (slotPauli n ⟨1, by omega⟩ d)
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ ha⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hc⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hb⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hd⟩
    (Or.inl (slots_commute n _ _ (by intro h; have := congrArg Fin.val h; simp at this) a c).eq)

private lemma dilated_density (n : ℕ)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (dilation n * ρ * (dilation n)ᴴ).PosSemidef ∧
      (dilation n * ρ * (dilation n)ᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same _, ?_⟩
  rw [trace_mul_cycle, dilation_isometry, one_mul, htrace]

private lemma density_involution_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ l : Matrix ι ι ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hl : l.IsHermitian) (hs : l ^ 2 = (4 : ℂ) • 1) : ‖(τ * l).trace‖ ≤ 2 := by
  letI := τ.toMatrixSeminormedAddCommGroup hτ
  letI := τ.toMatrixInnerProductSpace hτ
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) (1 : Matrix ι ι ℂ) l
  change ‖(l * τ * (1 : Matrix ι ι ℂ)ᴴ).trace‖ * ‖(1 * τ * lᴴ).trace‖ ≤
    ((1 * τ * (1 : Matrix ι ι ℂ)ᴴ).trace).re * ((l * τ * lᴴ).trace).re at hcs
  have hlt : (l * τ * lᴴ).trace = 4 := by
    rw [hl.eq, trace_mul_cycle, ← pow_two, hs, Matrix.smul_mul, one_mul,
      trace_smul, ht]
    simp
  rw [hlt] at hcs
  simp only [conjTranspose_one, mul_one, one_mul, hl.eq, ht,
    trace_mul_comm l τ] at hcs
  norm_num at hcs
  nlinarith [norm_nonneg (τ * l).trace]

private lemma expectation_bound (n : ℕ) (hn : 2 ≤ n)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2 := by
  have hτ := dilated_density n ρ hρ ht
  have hbnd := density_involution_bound _ _ hτ.1 hτ.2
    (lifted_hermitian n hn a c b d) (lifted_square n hn a c b d ha hc hb hd)
  have he := chsh_dilation n hn a c b d
  have htrace : (ρ * ((dilation n)ᴴ * liftedOperator n hn a c b d * dilation n)).trace =
      ((dilation n * ρ * (dilation n)ᴴ) * liftedOperator n hn a c b d).trace := by
    calc
      _ = ((ρ * (dilation n)ᴴ * liftedOperator n hn a c b d) * dilation n).trace := by
        simp only [Matrix.mul_assoc]
      _ = (dilation n * (ρ * (dilation n)ᴴ * liftedOperator n hn a c b d)).trace :=
        trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he, Matrix.mul_smul, trace_smul, norm_smul, htrace]
  have hnorm : ‖((n : ℂ) / 2) ^ 2‖ = ((n : ℝ) / 2) ^ 2 := by
    simp only [norm_pow, norm_div, Complex.norm_natCast, norm_ofNat]
  rw [hnorm]
  calc
    _ ≤ ((n : ℝ) / 2) ^ 2 * 2 := mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
    _ = (n : ℝ) ^ 2 / 2 := by ring

theorem result : claim := by
  intro n hn ρ hρ ht a c b d ha hc hb hd
  exact expectation_bound n hn ρ hρ ht a c b d ha hc hb hd

end D5.S3.QuantumBounds.HighSpinCHSHNonviolation
