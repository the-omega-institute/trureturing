/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoProgression
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoProgression
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw]
   utility: none
   digest: Jaco maximum degrees along arithmetic progressions, and the exact multiple-of-five blocks. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

/-! Maximum degrees of finite linear Jaco graphs along the orders `d k`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoProgression

/-
proof_shape:
  beta, blockStart, block, lower: definition
  two_div, inv_phi, alpha_phi, phi_bounds, five_div, floor_five, beta_five, beta_lt: bind-only
    (consumers: progression, blockStart_eq_ceil, block_delta, result)
  beta_pos, correction_iff: bind-only (consumers: blockStart_eq_ceil, block_delta, result)
  blockStart_pos, blockStart_succ, lower_succ, mem_block, blockStart_lt, lower_strictMono,
    block_pos, block_nonempty: bind-only (consumers: blocks_partition, block_delta, result)
  progression: bind-only (consumers: block_delta, result)
  blockStart_eq_ceil, blocks_partition, block_delta: content (consumer: result)
  result: content
escape_witness: the closed-form ceiling of blockStart_eq_ceil, obtained from the inverse
  (5 phi - 8)^-1 = 3 + 5 phi and the irrationality of (5q - 1) phi; the Nat.find construction
  of blocks_partition; and their composition with the correction range in block_delta.
admission_basis: escape-witness
-/

open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

/-- The golden fractional part `β_d = d / φ - ⌊d / φ⌋`. -/
noncomputable def beta (d : ℕ) : ℝ := Int.fract ((d : ℝ) / Real.goldenRatio)

private theorem two_div : 2 / Real.goldenRatio = 1 + alpha := by
  rw [alpha, div_eq_mul_inv, Real.inv_goldenRatio, Real.goldenConj]; ring

private theorem beta_pos (d : ℕ) (hd : 1 ≤ d) : 0 < beta d := by
  rw [beta, Int.fract_pos]
  intro h
  have hirr := (Real.goldenRatio_irrational.inv.natCast_mul (m := d) (by omega)).ne_int
    ⌊(d : ℝ) / Real.goldenRatio⌋
  apply hirr
  rw [← div_eq_mul_inv]
  exact h

/-- Along the progression `d k`, the maximum degree is `⌊d / φ⌋ k` plus the
correction `⌊β_d k + α⌋`. -/
private theorem progression (d k : ℕ) :
    delta (d * k) = ⌊(d : ℝ) / Real.goldenRatio⌋ * k + ⌊beta d * k + alpha⌋ := by
  rw [delta_eq_floor]
  have h : (((d * k : ℕ) : ℝ) + 2) / Real.goldenRatio =
      (beta d * k + alpha) + ((⌊(d : ℝ) / Real.goldenRatio⌋ * k + 1 : ℤ) : ℝ) := by
    have h2 := two_div
    rw [beta, Int.fract]
    push_cast
    rw [add_div, h2]
    ring
  rw [h, Int.floor_add_intCast]
  ring

/-- The correction equals `q` exactly on the stated range of `k`. -/
private theorem correction_iff (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (q : ℤ) :
    ⌊beta d * k + alpha⌋ = q ↔
      max 1 ⌈((q : ℝ) - alpha) / beta d⌉ ≤ k ∧ (k : ℤ) < ⌈((q : ℝ) + 1 - alpha) / beta d⌉ := by
  have hb := beta_pos d hd
  rw [Int.floor_eq_iff, max_le_iff, Int.ceil_le, Int.lt_ceil, div_le_iff₀ hb, lt_div_iff₀ hb]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by exact_mod_cast hk, by linarith⟩, by linarith⟩
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨by linarith, by linarith⟩


private theorem inv_phi : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  rw [Real.inv_goldenRatio, Real.goldenConj, Real.goldenRatio]; ring

private theorem alpha_phi : alpha = 2 * Real.goldenRatio - 3 := by
  rw [alpha, Real.goldenRatio]; ring

private theorem phi_bounds : (8 : ℝ) / 5 < Real.goldenRatio ∧ Real.goldenRatio < 13 / 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 5
  constructor <;> (rw [Real.goldenRatio]; nlinarith)

private theorem five_div : (5 : ℝ) / Real.goldenRatio = 5 * Real.goldenRatio - 5 := by
  rw [div_eq_mul_inv, inv_phi]; ring

private theorem floor_five : ⌊((5 : ℕ) : ℝ) / Real.goldenRatio⌋ = 3 := by
  obtain ⟨hl, hh⟩ := phi_bounds
  rw [Int.floor_eq_iff]; push_cast; rw [five_div]; constructor <;> linarith

private theorem beta_five : beta 5 = 5 * Real.goldenRatio - 8 := by
  rw [beta, Int.fract, floor_five]; push_cast; rw [five_div]; ring

/-- The block starts `k_q`, with `k_0 = 1`. -/
noncomputable def blockStart (q : ℕ) : ℕ :=
  if q = 0 then 1 else ⌊((5 * q - 1 : ℕ) : ℝ) * Real.goldenRatio⌋₊ + 3 * q

/-- The block `P_q` of positive orders. -/
noncomputable def block (q : ℕ) : Finset ℕ :=
  Finset.Icc (if q = 0 then 1 else 5 * blockStart q) (5 * blockStart (q + 1) - 1)

/-- For `q ≥ 1`, `⌈(q - α) / β_5⌉ = ⌊(5q - 1) φ⌋ + 3q`. -/
private theorem blockStart_eq_ceil (q : ℕ) (hq : 1 ≤ q) :
    ⌈((q : ℝ) - alpha) / beta 5⌉ = (blockStart q : ℤ) := by
  obtain ⟨hl, hh⟩ := phi_bounds
  have hsq := Real.goldenRatio_sq
  have hb : 0 < beta 5 := beta_pos 5 (by norm_num)
  have hid : ((q : ℝ) - alpha) / beta 5 =
      ((5 * q - 1 : ℕ) : ℝ) * Real.goldenRatio + ((3 * q - 1 : ℤ) : ℝ) := by
    rw [div_eq_iff hb.ne', beta_five, alpha_phi]
    push_cast [show 1 ≤ 5 * q by omega]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    linear_combination (-(5 * (q : ℝ)) + 1) * hsq + (1 - 5 * (q : ℝ)) * h5
  have hirr := (Real.goldenRatio_irrational.natCast_mul (m := 5 * q - 1) (by omega)).ne_int
  rw [blockStart]
  simp only [show q ≠ 0 by omega, ↓reduceIte]
  set t := ((5 * q - 1 : ℕ) : ℝ) * Real.goldenRatio with ht
  have ht0 : 0 ≤ t := by positivity
  rw [hid, Int.ceil_add_intCast]
  have hc : ⌈t⌉ = ⌊t⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem t).mpr (fun ⟨z, hz⟩ => hirr z hz.symm)
  rw [hc, ← Int.natCast_floor_eq_floor ht0]
  push_cast
  omega


private theorem blockStart_pos (q : ℕ) : 1 ≤ blockStart q := by
  unfold blockStart; split_ifs <;> omega

private theorem blockStart_succ (q : ℕ) :
    blockStart (q + 1) = ⌊((5 * (q + 1) - 1 : ℕ) : ℝ) * Real.goldenRatio⌋₊ + 3 * (q + 1) := by
  simp only [blockStart, Nat.succ_ne_zero, ↓reduceIte]

private theorem blockStart_lt (q : ℕ) : blockStart q < blockStart (q + 1) := by
  rw [blockStart_succ]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [blockStart, ↓reduceIte]; omega
  · have : ⌊((5 * q - 1 : ℕ) : ℝ) * Real.goldenRatio⌋₊ ≤
        ⌊((5 * (q + 1) - 1 : ℕ) : ℝ) * Real.goldenRatio⌋₊ := by
      apply Nat.floor_le_floor
      apply mul_le_mul_of_nonneg_right _ Real.goldenRatio_pos.le
      exact_mod_cast (by omega : 5 * q - 1 ≤ 5 * (q + 1) - 1)
    simp only [blockStart, show q ≠ 0 by omega, ↓reduceIte]
    omega

/-- The lower end of the block `P_q`. -/
private noncomputable def lower (q : ℕ) : ℕ := if q = 0 then 1 else 5 * blockStart q

private theorem lower_succ (q : ℕ) : lower (q + 1) = 5 * blockStart (q + 1) := by
  simp only [lower, Nat.succ_ne_zero, ↓reduceIte]

private theorem mem_block (q m : ℕ) : m ∈ block q ↔ lower q ≤ m ∧ m < lower (q + 1) := by
  have := blockStart_pos (q + 1)
  rw [block, Finset.mem_Icc, lower_succ]
  change (if q = 0 then 1 else 5 * blockStart q) ≤ m ∧ _ ↔
    (if q = 0 then 1 else 5 * blockStart q) ≤ m ∧ _
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

private theorem lower_strictMono : StrictMono lower := by
  apply strictMono_nat_of_lt_succ
  intro q
  have h1 := blockStart_lt q
  have h3 := blockStart_pos (q + 1)
  rw [lower_succ]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [lower, ↓reduceIte]; omega
  · simp only [lower, show q ≠ 0 by omega, ↓reduceIte]; omega

/-- The blocks `P_q` partition the positive integers. -/
private theorem blocks_partition (m : ℕ) (hm : 1 ≤ m) : ∃! q, m ∈ block q := by
  have hex : ∃ q, m < lower (q + 1) :=
    ⟨m, lt_of_lt_of_le (by omega) (show m + 1 ≤ lower (m + 1) from lower_strictMono.le_apply)⟩
  classical
  refine ⟨Nat.find hex, (mem_block _ _).mpr ⟨?_, Nat.find_spec hex⟩, ?_⟩
  · by_cases h0 : Nat.find hex = 0
    · rw [h0, lower]; simpa using hm
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at this
      omega
  · intro q hq
    rw [mem_block] at hq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Nat.find_min hex h hq.2
    · have h1 := lower_strictMono.monotone (show Nat.find hex + 1 ≤ q by omega)
      have h2 := Nat.find_spec hex
      omega

/-- On the block `P_q`, the maximum degree at order `5k` is `3k + q`. -/
private theorem block_delta (q k : ℕ) (hk : 5 * k ∈ block q) : delta (5 * k) = 3 * k + q := by
  obtain ⟨hl, hh⟩ := phi_bounds
  have hf := floor_five
  rw [mem_block] at hk
  have hup : k < blockStart (q + 1) := by
    have := hk.2; rw [lower_succ] at this; omega
  have hk1 : 1 ≤ k := by
    have := hk.1; have := blockStart_pos q; unfold lower at *; split_ifs at * <;> omega
  rw [progression, hf]
  have hc : ⌊beta 5 * k + alpha⌋ = q := by
    rw [correction_iff 5 k (by norm_num) hk1]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos q with rfl | hq
      · have hb := beta_pos 5 (by norm_num)
        have ha : 0 < alpha := by
          rw [alpha_phi]; linarith
        have : ⌈((((0 : ℕ) : ℤ) : ℝ) - alpha) / beta 5⌉ ≤ 0 := by
          rw [Int.ceil_le]; push_cast
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
        exact max_le (by exact_mod_cast hk1) (by omega)
      · have := blockStart_eq_ceil q hq
        have h1 := hk.1
        unfold lower at h1
        simp only [show q ≠ 0 by omega, ↓reduceIte] at h1
        push_cast at this ⊢
        rw [this]
        exact max_le (by exact_mod_cast hk1) (by exact_mod_cast (by omega : blockStart q ≤ k))
    · have := blockStart_eq_ceil (q + 1) (by omega)
      push_cast at this ⊢
      rw [this]
      exact_mod_cast hup
  rw [hc]

private theorem beta_lt (d : ℕ) : beta d < 1 := Int.fract_lt_one _

private theorem block_pos (q m : ℕ) (hm : m ∈ block q) : 1 ≤ m := by
  rw [mem_block] at hm
  have := blockStart_pos q
  have := hm.1
  unfold lower at this
  split_ifs at this <;> omega

private theorem block_nonempty (q : ℕ) : (block q).Nonempty :=
  ⟨lower q, (mem_block q (lower q)).mpr ⟨le_rfl, lower_strictMono (Nat.lt_succ_self q)⟩⟩

/-- The maximum degree along every progression `d k`, the exact range of `k` for each
correction value, and for `d = 5` the closed-form block starts, the block partition of
the positive orders and the maximum degree on each block. -/
theorem result :
    (∀ d k : ℕ, delta (d * k) = ⌊(d : ℝ) / Real.goldenRatio⌋ * k + ⌊beta d * k + alpha⌋) ∧
    (∀ d : ℕ, 1 ≤ d → 0 < beta d ∧ beta d < 1) ∧
    (⌊((5 : ℕ) : ℝ) / Real.goldenRatio⌋ = 3 ∧ beta 5 = 5 / Real.goldenRatio - 3) ∧
    (∀ d k : ℕ, 1 ≤ d → 1 ≤ k → ∀ q : ℤ,
      (⌊beta d * k + alpha⌋ = q ↔
        max 1 ⌈((q : ℝ) - alpha) / beta d⌉ ≤ k ∧ (k : ℤ) < ⌈((q : ℝ) + 1 - alpha) / beta d⌉)) ∧
    (∀ q : ℕ, 1 ≤ q → ⌈((q : ℝ) - alpha) / beta 5⌉ = (blockStart q : ℤ)) ∧
    (∀ m : ℕ, 1 ≤ m → ∃! q, m ∈ block q) ∧
    (∀ q m : ℕ, m ∈ block q → 1 ≤ m) ∧ (∀ q : ℕ, (block q).Nonempty) ∧
    (∀ q k : ℕ, 5 * k ∈ block q → delta (5 * k) = 3 * k + q) :=
  ⟨progression, fun d hd => ⟨beta_pos d hd, beta_lt d⟩,
    ⟨floor_five, by rw [beta_five, five_div]; ring⟩, correction_iff, blockStart_eq_ceil,
    blocks_partition, block_pos, block_nonempty, block_delta⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoProgression
