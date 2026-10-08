/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdRecurrence
   mirror-E: none(waiver:coloured-uniform-recurrence)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.Real]
   utility: none
   digest: Irrational rotation returns coloured factors with both palette phases intact. -/

import Mathlib.Topology.Instances.AddCircle.Real
import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import D5.S1.Words.BalancedThreshold.BalancedThresholdPalettes
import D5.S1.Words.BalancedThreshold.BalancedThresholdBispecial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open Set D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- A compact rotation cover returns all endpoint floors and both occurrence-rank phases. -/
theorem coloured_word_uniformly_recurrent {alpha rho : ℝ}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (hirr : Irrational alpha)
    (t : ℕ) (ht : 0 < t) :
    UniformlyRecurrentWord (colouredMechanicalWord alpha rho t ht) := by
  classical
  intro n s
  let P := 2 * t * (t + 1)
  have hP : 0 < P := by dsimp [P]; positivity
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  let X := fun k : ℕ => rho + ((s + k : ℕ) : ℝ) * alpha
  have stable : ∀ m : ℕ, ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧
      ∀ k ≤ m, ∀ u : ℝ, 0 < u → u < e → ⌊X k + u⌋ = ⌊X k⌋ := by
    intro m
    induction m with
    | zero =>
      refine ⟨min 1 (1 - Int.fract (X 0)), lt_min (by norm_num)
        (sub_pos.mpr (Int.fract_lt_one _)), min_le_left _ _, ?_⟩
      intro k hk u hu hue
      have hk0 : k = 0 := by omega
      subst k
      apply Int.floor_eq_iff.mpr
      have hsmall := hue.trans_le (min_le_right 1 (1 - Int.fract (X 0)))
      have hfloor := Int.floor_le (X 0)
      have hfract := Int.floor_add_fract (X 0)
      constructor <;> linarith
    | succ m ih =>
      obtain ⟨e, he, he1, heq⟩ := ih
      refine ⟨min e (1 - Int.fract (X (m + 1))),
        lt_min he (sub_pos.mpr (Int.fract_lt_one _)),
        (min_le_left _ _).trans he1, ?_⟩
      intro k hk u hu hue
      by_cases hkm : k ≤ m
      · exact heq k hkm u hu (hue.trans_le (min_le_left _ _))
      · have hks : k = m + 1 := by omega
        subst k
        apply Int.floor_eq_iff.mpr
        have hsmall := hue.trans_le (min_le_right e (1 - Int.fract (X (m + 1))))
        have hfloor := Int.floor_le (X (m + 1))
        have hfract := Int.floor_add_fract (X (m + 1))
        constructor <;> linarith
  obtain ⟨e, he, he1, heq⟩ := stable n
  let step : AddCircle (1 : ℝ) := (alpha : AddCircle (1 : ℝ))
  have hdense : DenseRange (fun q : ℕ => q • step) := by
    apply denseRange_zsmul_iff_nsmul.mp
    dsimp [step]
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using hirr
  let U : Set (AddCircle (1 : ℝ)) :=
    (fun v : ℝ => (v : AddCircle (1 : ℝ))) '' Ioo 0 (e / P)
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨((e / P / 2 : ℝ) : AddCircle (1 : ℝ)), e / P / 2, ?_, rfl⟩
    have hep : 0 < e / (P : ℝ) := div_pos he hPr
    constructor <;> linarith
  let V := fun q : ℕ => {y : AddCircle (1 : ℝ) | y + q • step ∈ U}
  have hV : ∀ q, IsOpen (V q) := fun q => hU.preimage (by fun_prop)
  have hcover : (univ : Set (AddCircle (1 : ℝ))) ⊆ ⋃ q, V q := by
    intro y _
    have htrans : Function.Surjective (fun z : AddCircle (1 : ℝ) => y + z) := by
      intro z
      exact ⟨z - y, by simp⟩
    have hd : DenseRange (fun q : ℕ => y + q • step) :=
      htrans.denseRange.comp hdense (by fun_prop)
    obtain ⟨q, hq⟩ := hd.exists_mem_open hU hUne
    exact mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨F, hF⟩ :=
    (isCompact_univ : IsCompact (univ : Set (AddCircle (1 : ℝ)))).elim_finite_subcover
      V hV hcover
  let B := F.sup id
  refine ⟨P * (B + 2), fun i => ?_⟩
  let j0 := P * (i / P + 1) + s % P
  let y : AddCircle (1 : ℝ) :=
    ((((j0 : ℝ) - s) * alpha / P : ℝ) : AddCircle (1 : ℝ))
  obtain ⟨q, hqF, hqy⟩ := mem_iUnion₂.mp (hF (mem_univ y))
  have hqB : q ≤ B := Finset.le_sup (f := id) hqF
  let j := j0 + P * q
  have hjlo : i ≤ j := by
    have hi := Nat.mod_add_div i P
    have hiP := Nat.mod_lt i hP
    dsimp [j, j0]
    simp only [mul_add, mul_one]
    omega
  have hjhi : j ≤ i + P * (B + 2) := by
    have hi := Nat.mod_add_div i P
    have hsP := Nat.mod_lt s hP
    have hq := Nat.mul_le_mul_left P hqB
    dsimp [j, j0]
    simp only [mul_add, mul_one]
    omega
  have hjmod : j ≡ s [MOD P] := by
    dsimp [j, j0, Nat.ModEq]
    simp [Nat.add_mod]
  change y + q • step ∈ U at hqy
  obtain ⟨v, hv, hvy⟩ := hqy
  have hcircle :
      ((((j : ℝ) - s) * alpha / P : ℝ) : AddCircle (1 : ℝ)) =
        (v : AddCircle (1 : ℝ)) := by
    have hid : ((j : ℝ) - s) * alpha / P =
        ((j0 : ℝ) - s) * alpha / P + (q : ℝ) * alpha := by
      dsimp [j]
      push_cast
      field_simp
      ring
    rw [hid, AddCircle.coe_add]
    simpa [y, step, AddCircle.coe_nsmul, nsmul_eq_mul] using hvy.symm
  have hzero :
      ((((j : ℝ) - s) * alpha / P - v : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, hcircle, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hz' : (z : ℝ) = ((j : ℝ) - s) * alpha / P - v := by
    simpa [zsmul_eq_mul] using hz
  let u := v * P
  have hu : 0 < u := mul_pos hv.1 hPr
  have hue : u < e := (lt_div_iff₀ hPr).mp hv.2
  have hshift : (j : ℝ) * alpha = (s : ℝ) * alpha + u + z * P := by
    have hzP := congrArg (fun r : ℝ => r * P) hz'
    rw [sub_mul, div_mul_cancel₀ _ hPr.ne'] at hzP
    dsimp [u]
    nlinarith
  have hfloor : ∀ k ≤ n,
      ⌊rho + ((j + k : ℕ) : ℝ) * alpha⌋ = ⌊X k⌋ + z * (P : ℤ) := by
    intro k hk
    have hid : rho + ((j + k : ℕ) : ℝ) * alpha = X k + u + (z * P : ℤ) := by
      dsimp [X]
      push_cast
      nlinarith [hshift]
    rw [hid, Int.floor_add_intCast, heq k hk u hu hue]
  let c := lowerMechanicalWindowTrueCount alpha rho 0
  have hc : ∀ k, c k ≤ k := by
    intro k
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hcounts : ∀ k < n, c (j + k) ≡ c (s + k) [MOD P] := by
    intro k hk
    apply Int.natCast_modEq_iff.mp
    have hjc := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) h0 h1 0 (j + k)
    have hsc := lowerMechanicalWindowTrueCount_eq_floor (rho := rho) h0 h1 0 (s + k)
    simp only [zero_add, Nat.cast_zero, zero_mul, add_zero] at hjc hsc
    have hid : (c (j + k) : ℤ) = c (s + k) + z * (P : ℤ) := by
      dsimp [c]
      rw [hjc, hsc, hfloor k hk.le]
      ring
    rw [hid, Int.add_mul_modulus_modEq_iff]
  refine ⟨j, hjlo, hjhi, ?_⟩
  funext k
  change colouredMechanicalWord alpha rho t ht (j + k) =
    colouredMechanicalWord alpha rho t ht (s + k)
  have hword : lowerMechanicalWord alpha rho (j + k) =
      lowerMechanicalWord alpha rho (s + k) := by
    unfold lowerMechanicalWord lowerMechanicalLetter
    have hfk := hfloor k k.isLt.le
    have hfnext := hfloor (k + 1) (by omega)
    have hid : ⌊rho + ((j + k + 1 : ℕ) : ℝ) * alpha⌋ -
        ⌊rho + ((j + k : ℕ) : ℝ) * alpha⌋ =
        ⌊rho + ((s + k + 1 : ℕ) : ℝ) * alpha⌋ -
        ⌊rho + ((s + k : ℕ) : ℝ) * alpha⌋ := by
      simpa [X, Nat.add_assoc] using sub_eq_sub_iff_add_eq_add.mpr
        (show ⌊rho + ((j + k + 1 : ℕ) : ℝ) * alpha⌋ + ⌊X k⌋ =
          ⌊X (k + 1)⌋ + ⌊rho + ((j + k : ℕ) : ℝ) * alpha⌋ by
            rw [Nat.add_assoc, hfnext, hfk]; ring)
    rw [hid]
  have ha := hcounts k k.isLt
  have hb : (j + k - c (j + k)) ≡ (s + k - c (s + k)) [MOD P] := by
    apply Int.natCast_modEq_iff.mp
    rw [Int.natCast_sub (hc _), Int.natCast_sub (hc _)]
    exact (Int.natCast_modEq_iff.mpr (hjmod.add_right k)).sub
      (Int.natCast_modEq_iff.mpr ha)
  have hd2 : 2 ∣ P := by exact ⟨t * (t + 1), by dsimp [P]; ring⟩
  have had2 : c (j + k) % 2 = c (s + k) % 2 := ha.of_dvd hd2
  have hbd2 : (j + k - c (j + k)) % 2 = (s + k - c (s + k)) % 2 :=
    hb.of_dvd hd2
  have hbdiv : (j + k - c (j + k)) / 2 ≡
      (s + k - c (s + k)) / 2 [MOD t * (t + 1)] := by
    have hid : P = 2 * (t * (t + 1)) := by dsimp [P]; ring
    have hdiv := congrArg (fun r : ℕ => r / 2) hb
    simpa only [Nat.ModEq, hid, Nat.mod_mul_right_div_self] using hdiv
  have hbt : ((j + k - c (j + k)) / 2) % t =
      ((s + k - c (s + k)) / 2) % t := hbdiv.of_dvd (dvd_mul_right _ _)
  have hbt1 : ((j + k - c (j + k)) / 2) % (t + 1) =
      ((s + k - c (s + k)) / 2) % (t + 1) := hbdiv.of_dvd (dvd_mul_left _ _)
  have label (l : ℕ) : (colouredMechanicalWord alpha rho t ht l).val =
      if lowerMechanicalWord alpha rho l = true then c l % 2
      else if (l - c l) % 2 = 0 then 2 + ((l - c l) / 2) % t
      else 2 + t + ((l - c l) / 2) % (t + 1) := by
    simp only [colouredMechanicalWord, c]
    split_ifs <;> rfl
  apply Fin.ext
  rw [label, label, hword, had2, hbd2, hbt, hbt1]

end D5.S1.Words.BalancedThreshold
