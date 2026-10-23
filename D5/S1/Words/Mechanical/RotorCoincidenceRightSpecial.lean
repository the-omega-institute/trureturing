/- GID: D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial
   generality: I
   mirror-B: D5/B/S1/Words/Mechanical/RotorCoincidenceRightSpecial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unique right-special rotor factor is the reversed prefix after the initial zero. -/
import D5.S1.Words.Mechanical.MechanicalRightSpecial
import D5.S1.Words.Complexity.MechanicalSubshiftIntercept

/-! Right-special factors of the separator encoding of an irrational cutting sequence. -/

namespace D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial

open private lowerMechanicalFactor_succ from
  D5.S1.Words.Mechanical.MechanicalRightSpecial

noncomputable def cutting (σ : ℝ) (m : ℕ) : ℕ := by
  classical
  exact if ∃ k : ℕ, 1 ≤ k ∧ m = ⌊(k : ℝ) * σ⌋₊ + k then 3 else 1

noncomputable def rotor (σ : ℝ) (m : ℕ) : ℕ :=
  if m = 0 then 0 else if m % 2 = 1 then 2 else cutting σ (m / 2)

def IsFactor (R : ℕ → ℕ) (w : List ℕ) : Prop :=
  ∃ i, ∀ t : ℕ, ∀ h : t < w.length, R (i + t) = w[t]

def IsRightSpecial (R : ℕ → ℕ) (w : List ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ IsFactor R (w ++ [a]) ∧ IsFactor R (w ++ [b])

def claim : Prop :=
  ∀ σ : ℝ, Irrational σ → 1 < σ → ∀ n : ℕ, 2 ≤ n →
    ∀ w : List ℕ, w.length = n - 1 →
      (IsRightSpecial (rotor σ) w ↔
        w = (List.ofFn (fun t : Fin (n - 1) => rotor σ (t + 1))).reverse)

private theorem beatty_jump {d : ℝ} (hd : 1 < d) (hi : Irrational d)
    (m : ℕ) :
    (∃ k : ℕ, 1 ≤ k ∧ m = ⌊(k : ℝ) * d⌋₊) ↔
      ⌊((m : ℝ) + 1) / d⌋ - ⌊(m : ℝ) / d⌋ = (1 : ℤ) := by
  have hd0 : 0 < d := by linarith
  have hstep : 1 / d < 1 := (div_lt_one hd0).mpr hd
  have hdiff : ((m : ℝ) + 1) / d = (m : ℝ) / d + 1 / d := by ring
  constructor
  · rintro ⟨k, hk, hm⟩
    have hk0 : 0 ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd0.le
    have hlo := Nat.floor_le hk0
    have hhi := Nat.lt_floor_add_one ((k : ℝ) * d)
    rw [← hm] at hlo hhi
    have hstrict : (m : ℝ) < (k : ℝ) * d := by
      refine lt_of_le_of_ne hlo ?_
      intro heq
      exact (hi.natCast_mul (by omega : k ≠ 0)).ne_int m (by simpa using heq.symm)
    have hx : (m : ℝ) / d < k := (div_lt_iff₀ hd0).mpr hstrict
    have hy : (k : ℝ) < ((m : ℝ) + 1) / d := (lt_div_iff₀ hd0).mpr hhi
    have hfx : ⌊(m : ℝ) / d⌋ = (k : ℤ) - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hfy : ⌊((m : ℝ) + 1) / d⌋ = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact hy.le
      · push_cast
        linarith
    rw [hfx, hfy]
    omega
  · intro h
    let z : ℤ := ⌊((m : ℝ) + 1) / d⌋
    have hz : 0 < z := by
      have hx0 : 0 ≤ ⌊(m : ℝ) / d⌋ :=
        Int.floor_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hd0.le)
      dsimp [z]
      omega
    let k := z.toNat
    have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz.le
    have hk : 1 ≤ k := by omega
    have hy : (k : ℝ) * d ≤ (m : ℝ) + 1 := by
      apply (le_div_iff₀ hd0).mp
      have hf := Int.floor_le (((m : ℝ) + 1) / d)
      have hkreal : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
      rw [hkreal]
      exact hf
    have hx : (m : ℝ) < (k : ℝ) * d := by
      apply (div_lt_iff₀ hd0).mp
      have hf := Int.lt_floor_add_one ((m : ℝ) / d)
      have hh : ⌊(m : ℝ) / d⌋ + 1 = (k : ℤ) := by dsimp [z] at hkz; omega
      rw [← Int.cast_one, ← Int.cast_add, hh, Int.cast_natCast] at hf
      exact hf
    have hy' : (k : ℝ) * d < (m : ℝ) + 1 := by
      refine lt_of_le_of_ne hy ?_
      intro heq
      exact (hi.natCast_mul (by omega : k ≠ 0)).ne_int (m + 1) (by
        push_cast
        exact heq)
    refine ⟨k, hk, (Nat.floor_eq_iff (by positivity)).mpr ⟨hx.le, hy'⟩ |>.symm⟩

private theorem cutting_mechanical {σ : ℝ} (hσ : Irrational σ) (hσ1 : 1 < σ)
    (j : ℕ) :
    cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1 := by
  classical
  have hi : Irrational (σ + 1) := by simpa using hσ.add_ratCast 1
  have he : (∃ k : ℕ, 1 ≤ k ∧ j + 1 = ⌊(k : ℝ) * σ⌋₊ + k) ↔
      lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j = true := by
    rw [lowerMechanicalWord_eq_true_iff]
    have hj := beatty_jump (by linarith : 1 < σ + 1) hi (j + 1)
    have hfloor (k : ℕ) : ⌊(k : ℝ) * (σ + 1)⌋₊ = ⌊(k : ℝ) * σ⌋₊ + k := by
      rw [mul_add, mul_one, Nat.floor_add_natCast (by positivity)]
    simp_rw [hfloor] at hj
    have hl : lowerMechanicalLetter (1 / (σ + 1)) (1 / (σ + 1)) j =
        ⌊(((j + 1 : ℕ) : ℝ) + 1) / (σ + 1)⌋ - ⌊((j + 1 : ℕ) : ℝ) / (σ + 1)⌋ := by
      unfold lowerMechanicalLetter
      congr 1 <;> congr 1 <;> push_cast <;> ring
    rw [hl]
    exact hj
  simp only [cutting, he]

private theorem finite_floor_left {α : ℝ} (hα : Irrational α) (N : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℕ, 1 ≤ q → q ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ < ε → ⌊-(q : ℝ) * α - δ⌋ = ⌊-(q : ℝ) * α⌋ := by
  induction N with
  | zero => exact ⟨1, by norm_num, by intro q hq hq'; omega⟩
  | succ N ih =>
    obtain ⟨ε, hε, he⟩ := ih
    let x := -((N + 1 : ℕ) : ℝ) * α
    have hx : (⌊x⌋ : ℝ) < x := by
      apply Int.floor_lt_self_iff.mpr
      rintro ⟨z, hz⟩
      exact ((hα.natCast_mul (by omega : N + 1 ≠ 0)).neg).ne_int z (by
        simpa [x, neg_mul] using hz.symm)
    refine ⟨min ε (x - ⌊x⌋), lt_min hε (by linarith), ?_⟩
    intro q hq hqN δ hδ hδe
    rcases Nat.eq_or_lt_of_le hqN with rfl | hqN
    · apply Int.floor_eq_iff.mpr
      change (⌊x⌋ : ℝ) ≤ x - δ ∧ x - δ < (⌊x⌋ : ℝ) + 1
      constructor
      · have := (lt_min_iff.mp hδe).2; linarith
      · linarith [Int.lt_floor_add_one x]
    · exact he q hq (by omega) δ hδ (lt_min_iff.mp hδe).1

private theorem mechanical_reversed_extension {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hα : Irrational α) (m : ℕ) (b : Bool) :
    (lowerMechanicalFactor α α m 0).reverse ++ [b] ∈
      lowerMechanicalFactorSet α α (m + 1) := by
  obtain ⟨ε, hε, he⟩ := finite_floor_left hα (m + 1)
  let δ : ℝ := if b then 0 else min ε (1 - α) / 2
  have hδ0 : 0 ≤ δ := by dsimp [δ]; split <;> positivity
  have hδε : δ < ε := by
    dsimp [δ]
    split
    · exact hε
    · have := min_le_left ε (1 - α)
      have := lt_min hε (by linarith : 0 < 1 - α)
      linarith
  have hδ1 : δ < 1 - α := by
    dsimp [δ]
    split
    · linarith
    · have := min_le_right ε (1 - α)
      have := lt_min hε (by linarith : 0 < 1 - α)
      linarith
  have hneg (q : ℕ) (hq : 1 ≤ q) :
      ⌊-(q : ℝ) * α⌋ = -⌊(q : ℝ) * α⌋ - 1 := by
    rw [neg_mul, Int.floor_neg,
      (Int.ceil_eq_floor_add_one_iff_notMem _).mpr ?_]
    · omega
    · rintro ⟨z, hz⟩
      exact (hα.natCast_mul (by omega : q ≠ 0)).ne_int z hz.symm
  have htarget : lowerMechanicalFactor α (-((m + 1 : ℕ) : ℝ) * α - δ) (m + 1) 0 =
      (lowerMechanicalFactor α α m 0).reverse ++ [b] := by
    apply List.ext_getElem
    · simp [lowerMechanicalFactor]
    · intro t ht ht'
      have htm : t < m + 1 := by simpa [lowerMechanicalFactor] using ht
      simp only [lowerMechanicalFactor, List.getElem_ofFn, zero_add]
      by_cases hlt : t < m
      · rw [List.getElem_append_left (by simpa [lowerMechanicalFactor] using hlt),
          List.getElem_reverse]
        simp only [lowerMechanicalFactor, List.length_ofFn, List.getElem_ofFn, zero_add]
        have ha : -((m + 1 : ℕ) : ℝ) * α - δ + ((t + 1 : ℕ) : ℝ) * α =
            -((m - t : ℕ) : ℝ) * α - δ := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have hb : -((m + 1 : ℕ) : ℝ) * α - δ + (t : ℝ) * α =
            -((m + 1 - t : ℕ) : ℝ) * α - δ := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        have hc : α + ((m - 1 - t + 1 : ℕ) : ℝ) * α =
            ((m + 1 - t : ℕ) : ℝ) * α := by
          have heq : m - 1 - t + 2 = m + 1 - t := by omega
          have := congrArg (fun n : ℕ => (n : ℝ)) heq
          push_cast at this ⊢
          nlinarith
        have hd : α + ((m - 1 - t : ℕ) : ℝ) * α =
            ((m - t : ℕ) : ℝ) * α := by
          have heq : m - 1 - t + 1 = m - t := by omega
          have := congrArg (fun n : ℕ => (n : ℝ)) heq
          push_cast at this ⊢
          nlinarith
        simp only [lowerMechanicalWord, lowerMechanicalLetter, ha, hb, hc, hd,
          he (m - t) (by omega) (by omega) δ hδ0 hδε,
          he (m + 1 - t) (by omega) (by omega) δ hδ0 hδε,
          hneg (m - t) (by omega), hneg (m + 1 - t) (by omega)]
        congr 1
        apply propext
        omega
      · have htm' : t = m := by omega
        subst t
        rw [List.getElem_append_right (by simp [lowerMechanicalFactor])]
        simp only [List.length_reverse, List.length_ofFn, Nat.sub_self,
          List.getElem_cons_zero]
        have ha : -((m + 1 : ℕ) : ℝ) * α - δ + ((m + 1 : ℕ) : ℝ) * α = -δ := by ring
        have hb : -((m + 1 : ℕ) : ℝ) * α - δ + (m : ℝ) * α = -α - δ := by
          push_cast
          ring
        have hf : ⌊-α - δ⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by
          norm_num
          constructor <;> linarith)
        simp only [lowerMechanicalWord, lowerMechanicalLetter, ha, hb, hf]
        cases b with
        | true => norm_num [δ]
        | false =>
          have hδpos : 0 < δ := by
            dsimp [δ]
            exact div_pos (lt_min hε (by linarith)) (by norm_num)
          have hf0 : ⌊-δ⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by
            norm_num
            constructor <;> linarith)
          simp [hf0]
  rw [← htarget]
  exact Complexity.MechanicalSubshiftIntercept.lowerMechanicalFactor_mem_factorSet hα α _ _ 0

private theorem mechanical_reverse_prefix_special {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hα : Irrational α) (m : ℕ) :
    MechanicalRightSpecial.IsLowerMechanicalRightSpecial α α m
      (lowerMechanicalFactor α α m 0).reverse := by
  refine ⟨?_, mechanical_reversed_extension hα0 hα1 hα m false,
    mechanical_reversed_extension hα0 hα1 hα m true⟩
  obtain ⟨i, hi⟩ := mem_lowerMechanicalFactorSet.mp
    (mechanical_reversed_extension hα0 hα1 hα m false)
  refine mem_lowerMechanicalFactorSet.mpr ⟨i, ?_⟩
  rw [lowerMechanicalFactor_succ] at hi
  exact List.append_inj_left hi (by simp [lowerMechanicalFactor])

private theorem cutting_values (σ : ℝ) (i : ℕ) :
    cutting σ i = 1 ∨ cutting σ i = 3 := by
  classical
  unfold cutting
  split <;> simp_all

private theorem rotor_zero_iff (σ : ℝ) (i : ℕ) : rotor σ i = 0 ↔ i = 0 := by
  by_cases hi : i = 0
  · subst i; simp [rotor]
  · rcases cutting_values σ (i / 2) with hc | hc <;>
      by_cases hm : i % 2 = 1 <;> simp [rotor, hi, hm, hc]

private theorem rotor_two_iff (σ : ℝ) (i : ℕ) : rotor σ i = 2 ↔ i % 2 = 1 := by
  by_cases hi : i = 0
  · subst i; simp [rotor]
  · rcases cutting_values σ (i / 2) with hc | hc <;> simp [rotor, hi, hc]

private theorem rotor_next_of_not_two {σ : ℝ} {i : ℕ} (h : rotor σ i ≠ 2) :
    rotor σ (i + 1) = 2 := by
  apply (rotor_two_iff σ (i + 1)).mpr
  have h' : i % 2 ≠ 1 := fun hc => h ((rotor_two_iff σ i).mpr hc)
  omega

private theorem rotor_window {σ α : ℝ}
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord α α j then 3 else 1)
    {ℓ i : ℕ} (hi : 0 < i) (hpar : (i + ℓ) % 2 = 0) (t : ℕ) :
    rotor σ (i + t) = if (t + ℓ) % 2 = 1 then 2 else
      if lowerMechanicalWord α α ((i - 1) / 2 + t / 2) then 3 else 1 := by
  by_cases ht : (t + ℓ) % 2 = 1
  · rw [if_pos ht]
    exact (rotor_two_iff σ _).mpr (by omega)
  · rw [if_neg ht]
    have hpos : i + t ≠ 0 := by omega
    have hmod : (i + t) % 2 ≠ 1 := by omega
    have hidx : (i + t) / 2 = (i - 1) / 2 + t / 2 + 1 := by omega
    simp only [rotor, if_neg hpos, if_neg hmod, hidx, hcut]

private theorem rotor_special_projection {σ α : ℝ}
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord α α j then 3 else 1)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {w : List ℕ} (hw : w.length = ℓ)
    (hs : IsRightSpecial (rotor σ) w) :
    ∃ i : ℕ, 0 < i ∧ (i + ℓ) % 2 = 0 ∧
      MechanicalRightSpecial.IsLowerMechanicalRightSpecial α α (ℓ / 2)
        (lowerMechanicalFactor α α (ℓ / 2) ((i - 1) / 2)) ∧
      ∀ t : ℕ, ∀ ht : t < w.length, rotor σ (i + t) = w[t] := by
  obtain ⟨a, b, hab, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hs
  have ha : rotor σ (i + ℓ) = a := by
    simpa [hw] using hi ℓ (by simp [hw])
  have hb : rotor σ (j + ℓ) = b := by
    simpa [hw] using hj ℓ (by simp [hw])
  have hsame (t : ℕ) (ht : t < ℓ) : rotor σ (i + t) = rotor σ (j + t) := by
    have hi' := hi t (by simp [hw]; omega)
    have hj' := hj t (by simp [hw]; omega)
    rw [List.getElem_append_left (by omega)] at hi' hj'
    exact hi'.trans hj'.symm
  have hip : 0 < i := by
    by_contra hn
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := (rotor_zero_iff σ j).mp (by
      simpa [hi0, rotor] using (hsame 0 hℓ).symm)
    apply hab
    rw [hi0] at ha
    rw [hj0] at hb
    exact ha.symm.trans hb
  have hjp : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    have hi0 : i = 0 := (rotor_zero_iff σ i).mp (by
      simpa [hj0, rotor] using hsame 0 hℓ)
    apply hab
    rw [hi0] at ha
    rw [hj0] at hb
    exact ha.symm.trans hb
  have hend : rotor σ (i + (ℓ - 1)) = 2 := by
    by_contra hn
    have hni := rotor_next_of_not_two hn
    have hnj := rotor_next_of_not_two (σ := σ) (i := j + (ℓ - 1)) (by
      rw [← hsame (ℓ - 1) (by omega)]; exact hn)
    have heqi : i + (ℓ - 1) + 1 = i + ℓ := by omega
    have heqj : j + (ℓ - 1) + 1 = j + ℓ := by omega
    rw [heqi, ha] at hni
    rw [heqj, hb] at hnj
    exact hab (hni.trans hnj.symm)
  have hpari : (i + ℓ) % 2 = 0 := by
    have := (rotor_two_iff σ _).mp hend
    omega
  have hparj : (j + ℓ) % 2 = 0 := by
    have := (rotor_two_iff σ _).mp ((hsame (ℓ - 1) (by omega)).symm.trans hend)
    omega
  have hbase : lowerMechanicalFactor α α (ℓ / 2) ((i - 1) / 2) =
      lowerMechanicalFactor α α (ℓ / 2) ((j - 1) / 2) := by
    apply List.ext_getElem
    · simp [lowerMechanicalFactor]
    · intro q hq hq'
      have hq0 : q < ℓ / 2 := by simpa [lowerMechanicalFactor] using hq
      let t := 2 * q + ℓ % 2
      have ht : t < ℓ := by dsimp [t]; omega
      have htpar : (t + ℓ) % 2 ≠ 1 := by dsimp [t]; omega
      have htdiv : t / 2 = q := by dsimp [t]; omega
      have hp := hsame t ht
      rw [rotor_window hcut hip hpari, rotor_window hcut hjp hparj,
        if_neg htpar, if_neg htpar, htdiv] at hp
      simp only [lowerMechanicalFactor, List.getElem_ofFn]
      exact (Bool.injective_iff.mpr (by decide) :
        Function.Injective (fun b : Bool => if b then (3 : ℕ) else 1)) hp
  have hext (k : ℕ) : lowerMechanicalFactor α α (ℓ / 2) k ++
      [lowerMechanicalWord α α (k + ℓ / 2)] ∈ lowerMechanicalFactorSet α α (ℓ / 2 + 1) := by
    rw [← lowerMechanicalFactor_succ]
    exact mem_lowerMechanicalFactorSet.mpr ⟨k, rfl⟩
  have hbits : lowerMechanicalWord α α ((i - 1) / 2 + ℓ / 2) ≠
      lowerMechanicalWord α α ((j - 1) / 2 + ℓ / 2) := by
    intro heq
    have hai := rotor_window hcut hip hpari ℓ
    have hbj := rotor_window hcut hjp hparj ℓ
    have hpar : (ℓ + ℓ) % 2 ≠ 1 := by omega
    rw [if_neg hpar, ha, heq] at hai
    rw [if_neg hpar, hb] at hbj
    exact hab (hai.trans hbj.symm)
  refine ⟨i, hip, hpari, ⟨mem_lowerMechanicalFactorSet.mpr ⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
  · have hei := hext ((i - 1) / 2)
    have hej := hext ((j - 1) / 2)
    rw [← hbase] at hej
    cases hbi : lowerMechanicalWord α α ((i - 1) / 2 + ℓ / 2) <;>
      cases hbj : lowerMechanicalWord α α ((j - 1) / 2 + ℓ / 2) <;> simp_all
  · have hei := hext ((i - 1) / 2)
    have hej := hext ((j - 1) / 2)
    rw [← hbase] at hej
    cases hbi : lowerMechanicalWord α α ((i - 1) / 2 + ℓ / 2) <;>
      cases hbj : lowerMechanicalWord α α ((j - 1) / 2 + ℓ / 2) <;> simp_all
  · intro t ht
    have h := hi t (by simp; omega)
    simpa only [List.getElem_append_left ht] using h

private theorem rotor_special_unique {σ : ℝ} (hσ : Irrational σ) (hσ1 : 1 < σ)
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∀ u v : List ℕ, u.length = ℓ → v.length = ℓ →
      IsRightSpecial (rotor σ) u → IsRightSpecial (rotor σ) v → u = v := by
  intro u v hu hv hsu hsv
  obtain ⟨i, hip, hpari, hsi, hi⟩ := rotor_special_projection hcut hℓ hu hsu
  obtain ⟨j, hjp, hparj, hsj, hj⟩ := rotor_special_projection hcut hℓ hv hsv
  have hα0 : 0 ≤ 1 / (σ + 1) := le_of_lt (one_div_pos.mpr (by linarith))
  have hα1 : 1 / (σ + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hα : Irrational (1 / (σ + 1)) := by simpa using (hσ.add_ratCast 1).inv
  obtain ⟨z, hz, huniq⟩ := MechanicalRightSpecial.exists_unique_lower_mechanical_right_special
    (rho := 1 / (σ + 1)) hα0 hα1 hα (ℓ / 2)
  have hbase := (huniq _ hsi).trans (huniq _ hsj).symm
  apply List.ext_getElem
  · omega
  · intro t ht ht'
    have htℓ : t < ℓ := by omega
    rw [← hi t ht, ← hj t ht', rotor_window hcut hip hpari, rotor_window hcut hjp hparj]
    by_cases hpar : (t + ℓ) % 2 = 1
    · rw [if_pos hpar, if_pos hpar]
    · rw [if_neg hpar, if_neg hpar]
      have htd : t / 2 < ℓ / 2 := by omega
      have hp := congrArg (fun w : List Bool => w[t / 2]?) hbase
      simp only [lowerMechanicalFactor, List.getElem?_ofFn, dif_pos htd,
        Option.some.injEq] at hp
      rw [hp]

private theorem rotor_reverse_prefix_special {σ : ℝ}
    (hσ : Irrational σ) (hσ1 : 1 < σ)
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1)
    (hrev : ∀ m : ℕ,
      MechanicalRightSpecial.IsLowerMechanicalRightSpecial
        (1 / (σ + 1)) (1 / (σ + 1)) m
        (lowerMechanicalFactor (1 / (σ + 1)) (1 / (σ + 1)) m 0).reverse)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    IsRightSpecial (rotor σ)
      (List.ofFn (fun t : Fin ℓ => rotor σ (t + 1))).reverse := by
  sorry

theorem result : claim := by
  intro σ hσ hσ1 n hn w hw
  have hα0 : 0 < 1 / (σ + 1) := one_div_pos.mpr (by linarith)
  have hα1 : 1 / (σ + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hα : Irrational (1 / (σ + 1)) := by
    simpa using (hσ.add_ratCast 1).inv
  have hc := cutting_mechanical hσ hσ1
  have hr := mechanical_reverse_prefix_special hα0 hα1 hα
  have hs := rotor_reverse_prefix_special hσ hσ1 hc hr (n - 1) (by omega)
  constructor
  · intro h
    exact rotor_special_unique hσ hσ1 hc (n - 1) (by omega) w _ hw
      (by simp) h hs
  · rintro rfl
    exact hs

end D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
