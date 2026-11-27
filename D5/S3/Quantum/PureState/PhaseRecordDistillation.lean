/- GID: D5/S3/Quantum/PureState/PhaseRecordDistillation
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseRecordDistillation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier character records have an exact optimum in memory dimension one below the carrier size. -/

import D5.S3.Quantum.PureState.FourierMemoryEncoder

namespace PhaseRecordDistillation

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open JointRecordDecoding

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The actual success probabilities of a common CPTP encoder followed by a POVM. -/
def characterMemorySuccessSet (A : Finset G) (t : G → ℝ) (ht : ∑ i, t i ^ 2 = 1) :
    Set ℝ :=
  {s | ∃ Φ : QuantumChannel G A, s ∈ successProbabilitySet (uniformPrior (AddChar G ℂ))
    (fun χ => Φ.mapState (characterState t ht χ))}

/-- The translate condition makes the clipped relaxation exact for the common encoder. -/
theorem isGreatest_characterMemory_of_translate (A : Finset G) (a₀ : A)
    (b d r t : G → ℝ) (c : ℝ)
    (hb : ∀ z, 0 ≤ b z) (hs : ∑ z, b z = 1)
    (hd : Feasible d (Fintype.card A)) (hm : ∑ i, d i = Fintype.card A)
    (hc : 0 ≤ c) (hr : ∀ i, c ≤ r i)
    (ht0 : ∀ i, 0 ≤ t i) (ht : ∀ i, t i = Real.sqrt (d i) * r i)
    (hclip : ∀ i, d i < 1 → r i = c)
    (hnorm : ∑ i, t i ^ 2 = 1)
    (htranslate : ∀ i, d i = ∑ a : A, b (i - a)) :
    IsGreatest (characterMemorySuccessSet A t hnorm)
      ((Fintype.card G : ℝ)⁻¹ * profileValue t d ^ 2) := by
  constructor
  · obtain ⟨Φ, _, hΦ⟩ :=
      character_encoder_attains A a₀ b d r t c hb hs hd.1 hd.2.1 ht hclip hnorm htranslate
    refine ⟨Φ, characterEffect A, characterEffect_posSemidef A, sum_characterEffect A, ?_⟩
    simp only [successProbability, uniformPrior, hΦ, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, AddChar.card_eq]
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (Fintype.card G : ℝ) ≠ 0), one_mul]
  · rintro s ⟨Φ, D, hD, hsD, rfl⟩
    obtain ⟨v, hv, hbound⟩ := exists_success_le_profile t ht0
      (fun (χ : AddChar G ℂ) i => χ i) (fun χ => χ.norm_apply)
      (characterVector_norm t hnorm) Φ D hD hsD
    have hprofile := profileValue_le_of_certificate t d v r c _ hd hv hm hc hr ht hclip
    rw [AddChar.card_eq] at hbound
    refine hbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hprofile 2)
      (by positivity))
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ht0 i) (Real.sqrt_nonneg _)

/-- The canonical memory carrier of dimension `|G| - 1`. -/
def oneDeficit (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] : Finset G :=
  Finset.univ.erase 0

@[simp]
theorem card_oneDeficit : Fintype.card (oneDeficit G) = Fintype.card G - 1 := by
  rw [Fintype.card_coe, oneDeficit, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

private theorem oneDeficit_translate (d : G → ℝ) (h : ∑ i, (1 - d i) = 1) (i : G) :
    d i = ∑ a : oneDeficit G, (1 - d (i - (a : G))) := by
  classical
  let f : G → ℝ := fun a => 1 - d (i - a)
  have hall : ∑ a, f a = 1 := by
    rw [← h]
    change (∑ a : G, (1 - d (i - a))) = _
    simp only [sub_eq_add_neg]
    exact Equiv.sum_comp ((Equiv.neg G).trans (Equiv.addLeft i)) fun z => 1 - d z
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : G))
  rw [hall] at hsplit
  have hz : f 0 = 1 - d i := by simp [f]
  rw [hz] at hsplit
  change d i = ∑ a : oneDeficit G, f a
  rw [Finset.sum_coe_sort]
  change d i = ∑ a ∈ Finset.univ.erase 0, f a
  linarith

/-- A saturated profile certificate yields exact decoding with dimension `|G| - 1`. -/
theorem isGreatest_oneDeficit_of_certificate (hG : 2 ≤ Fintype.card G)
    (t d r : G → ℝ) (c : ℝ) (ht0 : ∀ i, 0 ≤ t i) (hnorm : ∑ i, t i ^ 2 = 1)
    (hd : Feasible d (Fintype.card (oneDeficit G)))
    (hm : ∑ i, d i = Fintype.card (oneDeficit G))
    (hc : 0 ≤ c) (hr : ∀ i, c ≤ r i)
    (ht : ∀ i, t i = Real.sqrt (d i) * r i) (hclip : ∀ i, d i < 1 → r i = c) :
    IsGreatest (characterMemorySuccessSet (oneDeficit G) t hnorm)
      ((Fintype.card G : ℝ)⁻¹ * profileValue t d ^ 2) := by
  have hA : 0 < Fintype.card (oneDeficit G) := by rw [card_oneDeficit]; omega
  let a₀ : oneDeficit G := (Fintype.card_pos_iff.mp hA).some
  have hdef : ∑ i, (1 - d i) = 1 := by
    rw [Finset.sum_sub_distrib, hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_oneDeficit, Nat.cast_sub (by omega : 1 ≤ Fintype.card G), Nat.cast_one]
    ring
  exact isGreatest_characterMemory_of_translate (oneDeficit G) a₀ (fun i => 1 - d i) d r t c
    (fun i => sub_nonneg.mpr (hd.2.1 i)) hdef hd hm hc hr ht0 ht hclip
    hnorm (oneDeficit_translate d hdef)

/-- With positive amplitudes the exact optimum is the clipped-profile value. -/
theorem isGreatest_oneDeficit_clipped (hG : 2 ≤ Fintype.card G)
    (t : G → ℝ) (ht : ∀ i, 0 < t i) (hnorm : ∑ i, t i ^ 2 = 1) :
    ∃ c : ℝ, 0 < c ∧ (∑ i, clippedProfile t c i) = Fintype.card (oneDeficit G) ∧
      IsGreatest (characterMemorySuccessSet (oneDeficit G) t hnorm)
        ((Fintype.card G : ℝ)⁻¹ * profileValue t (clippedProfile t c) ^ 2) := by
  have hM : 0 < (Fintype.card (oneDeficit G) : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card (oneDeficit G) by rw [card_oneDeficit]; omega)
  have hs : (Fintype.card (oneDeficit G) : ℝ) ≤ ∑ i, (if 0 < t i then (1 : ℝ) else 0) := by
    simp only [ht, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_oneDeficit]
    exact_mod_cast Nat.sub_le (Fintype.card G) 1
  obtain ⟨c, hc, hm⟩ := exists_clippedProfile_sum t (fun i => (ht i).le) _ hM hs
  obtain ⟨hd0, hd1, hfact, hclip⟩ :=
    clippedProfile_certificate t (fun i => (ht i).le) c hc
  refine ⟨c, hc, hm, isGreatest_oneDeficit_of_certificate hG t (clippedProfile t c)
    (fun i => max (t i) c) c (fun i => (ht i).le) hnorm ⟨hd0, hd1, hm.le⟩ hm
    hc.le (fun i => le_max_right _ _) hfact hclip⟩

/-- When an amplitude vanishes, `|G| - 1` memory dimensions already attain the
full-carrier optimum. -/
theorem isGreatest_oneDeficit_of_zero (hG : 2 ≤ Fintype.card G)
    (t : G → ℝ) (ht : ∀ i, 0 ≤ t i) (hnorm : ∑ i, t i ^ 2 = 1)
    (z : G) (hz : t z = 0) :
    IsGreatest (characterMemorySuccessSet (oneDeficit G) t hnorm)
      ((Fintype.card G : ℝ)⁻¹ * (∑ i, t i) ^ 2) := by
  classical
  let d (i : G) : ℝ := if i = z then 0 else 1
  have hm : ∑ i, d i = Fintype.card (oneDeficit G) := by
    rw [card_oneDeficit, Nat.cast_sub (by omega : 1 ≤ Fintype.card G), Nat.cast_one]
    have hsum : ∑ i, (if i = z then (1 : ℝ) else 0) = 1 := by simp
    have he (i : G) : d i = 1 - (if i = z then (1 : ℝ) else 0) := by
      by_cases hi : i = z <;> simp [d, hi]
    simp only [he, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hfact (i : G) : t i = Real.sqrt (d i) * t i := by
    by_cases hi : i = z
    · simp [d, hi, hz]
    · simp [d, hi]
  have hclip (i : G) (hi : d i < 1) : t i = 0 := by
    by_cases hi' : i = z
    · simpa [hi'] using hz
    · simp [d, hi'] at hi
  have hval : profileValue t d = ∑ i, t i := by
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact (hfact i).symm
  rw [← hval]
  exact isGreatest_oneDeficit_of_certificate hG t d t 0 ht hnorm
    ⟨fun i => by dsimp [d]; split_ifs <;> norm_num,
      fun i => by dsimp [d]; split_ifs <;> norm_num, hm.le⟩
    hm le_rfl ht hfact hclip

end

end PhaseRecordDistillation
