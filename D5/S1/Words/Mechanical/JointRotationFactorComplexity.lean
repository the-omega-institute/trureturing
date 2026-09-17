/- GID: D5/S1/Words/Mechanical/JointRotationFactorComplexity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/JointRotationFactorComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous integer-scale rotation words have complexity at most the total circular boundary count. -/

import D5.S1.Words.Mechanical.FloorFractShift

set_option autoImplicit false

noncomputable section

namespace D5.S1.Words.Mechanical.JointRotationFactorComplexity

open scoped BigOperators

open Classical in
/-- The length-`h` vector word at phase `x`, with threshold `{a * α}` at scale `a`. -/
def jointRotationFactor (α : ℝ) (b : ℕ → ℤ) (A : Finset ℕ) (h : ℕ)
    (x : ℝ) : Fin h → A → ℤ := fun j a =>
  b a - if 1 - Int.fract ((a : ℝ) * α) ≤
    Int.fract ((a : ℝ) * (x + (j : ℝ) * α) + α) then 1 else 0

/-- The vector words realized by phases on the unit circle, represented by `[0,1)`. -/
def jointRotationFactorSet (α : ℝ) (b : ℕ → ℤ) (A : Finset ℕ) (h : ℕ) :
    Set (Fin h → A → ℤ) :=
  jointRotationFactor α b A h '' Set.Ico 0 1

/-- For an irrational rotation and nonempty positive scales, the number of simultaneous
rotation words of positive length `h` is at most `(h + 1) * ∑ a ∈ A, a`. -/
theorem joint_rotation_factor_complexity (α : {r : ℝ // Irrational r}) (b : ℕ → ℤ)
    (A : Finset ℕ) (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a)
    (h : {n : ℕ // 1 ≤ n}) :
    (jointRotationFactorSet α b A h).Finite ∧
      (jointRotationFactorSet α b A h).ncard ≤ (h + 1) * ∑ a ∈ A, a := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  have ha₀pos : (0 : ℝ) < a₀ := by exact_mod_cast hpos a₀ ha₀
  let t : ℝ := -α / a₀
  have ht : (a₀ : ℝ) * t + α = 0 := by
    dsimp [t]
    field_simp
    ring
  let I := A × Fin (h + 1)
  let f (i : I) (x : ℝ) : ℤ :=
    ⌊(i.1 : ℝ) * (x + (i.2 : ℝ) * α) + α⌋
  let y (x : ℝ) : ℝ := t + Int.fract (x - t)
  let rank (x : ℝ) : ℤ := ∑ i : I, (f i (y x) - f i t)
  let K : ℕ := (h + 1) * ∑ a ∈ A, a
  have hK : (∑ i : I, (i.1 : ℤ)) = (K : ℤ) := by
    simp [I, K, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_attach A (fun a => ((h : ℤ) + 1) * (a : ℤ))
  have hy (x : ℝ) : t ≤ y x ∧ y x < t + 1 := by
    dsimp [y]
    constructor
    · linarith [Int.fract_nonneg (x - t)]
    · linarith [Int.fract_lt_one (x - t)]
  have hmono (i : I) {u v : ℝ} (huv : u ≤ v) : f i u ≤ f i v := by
    apply Int.floor_mono
    nlinarith [Nat.cast_nonneg (α := ℝ) i.1.val]
  have hstep (i : I) : f i (t + 1) = f i t + (i.1 : ℤ) := by
    dsimp [f]
    have heq : (i.1 : ℝ) * (t + 1 + (i.2 : ℝ) * α) + α =
        ((i.1 : ℝ) * (t + (i.2 : ℝ) * α) + α) + (i.1.val : ℤ) := by
      push_cast
      ring
    rw [heq, Int.floor_add_intCast]
  have hbounds (x : ℝ) (i : I) :
      0 ≤ f i (y x) - f i t ∧ f i (y x) - f i t ≤ (i.1 : ℤ) := by
    have hlo := hmono i (hy x).1
    have hhi := hmono i (hy x).2.le
    rw [hstep] at hhi
    omega
  have hrank (x : ℝ) : 0 ≤ rank x ∧ rank x < (K : ℤ) := by
    constructor
    · exact Finset.sum_nonneg fun i _ => (hbounds x i).1
    · rw [← hK]
      apply Finset.sum_lt_sum (fun i _ => (hbounds x i).2)
      let i₀ : I := (⟨a₀, ha₀⟩, ⟨0, Nat.zero_lt_succ h⟩)
      refine ⟨i₀, Finset.mem_univ _, ?_⟩
      have hf₀ : f i₀ t = 0 := by simp [f, i₀, ht]
      rw [hf₀, sub_zero]
      apply Int.floor_lt.mpr
      dsimp [i₀]
      norm_num
      nlinarith [(hy x).2]
  have hfloor_eq {x z : ℝ} (heq : rank x = rank z) :
      ∀ i : I, f i (y x) = f i (y z) := by
    have ordered {u v : ℝ} (huv : y u ≤ y v) (hr : rank u = rank v) :
        ∀ i : I, f i (y u) = f i (y v) := by
      intro i
      by_contra hi
      have hlt : rank u < rank v := Finset.sum_lt_sum
        (fun j _ => sub_le_sub_right (hmono j huv) _) ⟨i, Finset.mem_univ _,
          sub_lt_sub_right (lt_of_le_of_ne (hmono i huv) hi) _⟩
      omega
    rcases le_total (y x) (y z) with hxz | hzx
    · exact ordered hxz heq
    · exact fun i => (ordered hzx heq.symm i).symm
  have hformula (x : ℝ) (j : Fin h) (a : A) :
      jointRotationFactor α b A h x j a = b a + ⌊(a : ℝ) * α⌋ +
        f (a, ⟨j.val, by omega⟩) (y x) - f (a, ⟨j.val + 1, by omega⟩) (y x) := by
    have hshift : (a : ℝ) * (x + (j : ℝ) * α) + α =
        ((a : ℝ) * (y x + (j : ℝ) * α) + α) +
          (((a.val : ℤ) * ⌊x - t⌋ : ℤ) : ℝ) := by
      simp only [y, Int.fract]
      push_cast
      ring
    have hcarry := FloorFractShift.floor_fract_add_indicator
      ((a : ℝ) * (y x + (j : ℝ) * α) + α) ((a : ℝ) * α)
    rw [← FloorFractShift.floor_add_sub_floor] at hcarry
    have hnext : (a : ℝ) * (y x + ((j.val + 1 : ℕ) : ℝ) * α) + α =
        ((a : ℝ) * (y x + (j : ℝ) * α) + α) + (a : ℝ) * α := by
      push_cast
      ring
    dsimp [jointRotationFactor]
    rw [hshift, Int.fract_add_intCast]
    dsimp [f]
    rw [hnext]
    omega
  have hword {x z : ℝ} (heq : rank x = rank z) :
      jointRotationFactor α b A h x = jointRotationFactor α b A h z := by
    funext j a
    rw [hformula, hformula, hfloor_eq heq (a, ⟨j.val, by omega⟩),
      hfloor_eq heq (a, ⟨j.val + 1, by omega⟩)]
  let W := jointRotationFactorSet α b A h
  let phase (w : W) : ℝ := Classical.choose w.2
  have hphase (w : W) : jointRotationFactor α b A h (phase w) = w.val :=
    (Classical.choose_spec w.2).2
  let encode (w : W) : Fin K :=
    ⟨(rank (phase w)).toNat, (Int.toNat_lt (hrank (phase w)).1).mpr (hrank (phase w)).2⟩
  have hinj : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    rw [← hphase u, ← hphase v]
    apply hword
    have hn : (rank (phase u)).toNat = (rank (phase v)).toNat :=
      congrArg Fin.val huv
    have hu := Int.toNat_of_nonneg (hrank (phase u)).1
    have hv := Int.toNat_of_nonneg (hrank (phase v)).1
    omega
  have : Finite W := Finite.of_injective encode hinj
  refine ⟨Set.toFinite _, ?_⟩
  have hc := Nat.card_le_card_of_injective encode hinj
  simpa [W, K, Nat.card_coe_set_eq] using hc

end D5.S1.Words.Mechanical.JointRotationFactorComplexity
