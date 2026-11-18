/- GID: D5/S1/Dynamics/Shadowing/LacunaryPhaseCover
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LacunaryPhaseCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodic phase covers avoiding triples in every sufficiently lacunary polygon. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Open arcs with integer lifts give phase masks with a uniform window margin. -/

namespace D5.S1.Dynamics.Shadowing

private def phaseArc (m : ℕ) (a b t : ℝ) : Prop :=
  ∃ z : ℤ, a < t - (m : ℝ) * z ∧ t - (m : ℝ) * z < b

private theorem phaseArc_period (m : ℕ) (a b t : ℝ) (z : ℤ) :
    phaseArc m a b (t + (m : ℝ) * z) ↔ phaseArc m a b t := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w - z, ?_⟩
    push_cast
    constructor <;> linarith [hw.1, hw.2]
  · rintro ⟨w, hw⟩
    refine ⟨w + z, ?_⟩
    push_cast
    constructor <;> linarith [hw.1, hw.2]

private theorem polygon_lifts_ne {m : ℕ} (i j : Fin m) (hij : i ≠ j) (z w : ℤ) :
    (i : ℤ) - (m : ℤ) * z ≠ (j : ℤ) - (m : ℤ) * w := by
  intro h
  have hi : (i : ℤ) % (m : ℤ) = i := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hj : (j : ℤ) % (m : ℤ) = j := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  have he := congrArg (fun x : ℤ => x % (m : ℤ)) h
  simp only [Int.sub_emod, Int.mul_emod_right, sub_zero, hi, hj] at he
  exact hij (Fin.ext (by exact_mod_cast he))

private theorem phaseArc_pair {m : ℕ} {a b t : ℝ} (hab : b ≤ a + 1)
    (i j : Fin m) (hij : i ≠ j) :
    ¬ (phaseArc m a b (t + i) ∧ phaseArc m a b (t + j)) := by
  rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
  have hlo : (-1 : ℤ) < ((i : ℤ) - (m : ℤ) * z) - ((j : ℤ) - (m : ℤ) * w) := by
    exact_mod_cast (show (-1 : ℝ) < ((i : ℤ) - (m : ℤ) * z : ℤ) -
      ((j : ℤ) - (m : ℤ) * w : ℤ) by push_cast; linarith [hz.1, hw.2])
  have hhi : ((i : ℤ) - (m : ℤ) * z) - ((j : ℤ) - (m : ℤ) * w) < 1 := by
    exact_mod_cast (show (((i : ℤ) - (m : ℤ) * z : ℤ) : ℝ) -
      ((j : ℤ) - (m : ℤ) * w : ℤ) < 1 by push_cast; linarith [hz.2, hw.1])
  exact polygon_lifts_ne i j hij z w (by omega)

private theorem phaseArc_triple {m : ℕ} {a b t : ℝ} (hab : b ≤ a + 2)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (phaseArc m a b (t + i) ∧ phaseArc m a b (t + j) ∧
      phaseArc m a b (t + k)) := by
  rintro ⟨⟨z, hz⟩, ⟨w, hw⟩, ⟨v, hv⟩⟩
  let x : ℤ := i - (m : ℤ) * z
  let y : ℤ := j - (m : ℤ) * w
  let q : ℤ := k - (m : ℤ) * v
  have hxy : x ≠ y := polygon_lifts_ne i j hij z w
  have hxq : x ≠ q := polygon_lifts_ne i k hik z v
  have hyq : y ≠ q := polygon_lifts_ne j k hjk w v
  have hx : a < t + (x : ℝ) ∧ t + (x : ℝ) < b := by
    dsimp [x]
    push_cast
    constructor <;> linarith [hz.1, hz.2]
  have hy : a < t + (y : ℝ) ∧ t + (y : ℝ) < b := by
    dsimp [y]
    push_cast
    constructor <;> linarith [hw.1, hw.2]
  have hq : a < t + (q : ℝ) ∧ t + (q : ℝ) < b := by
    dsimp [q]
    push_cast
    constructor <;> linarith [hv.1, hv.2]
  have hdiff (u v : ℤ) (hu : a < t + u) (hv : t + v < b) : v - u < 2 := by
    exact_mod_cast (show (v : ℝ) - u < 2 by linarith)
  have := hdiff x y hx.1 hy.2
  have := hdiff y x hy.1 hx.2
  have := hdiff x q hx.1 hq.2
  have := hdiff q x hq.1 hx.2
  have := hdiff y q hy.1 hq.2
  have := hdiff q y hq.1 hy.2
  omega

private theorem grid_cover (n : ℕ) (hn : 0 < n) (h e t : ℝ) (_hh : 0 ≤ h) (he : 0 ≤ e)
    (ht : -e ≤ t ∧ t ≤ (n : ℝ) * h + e) :
    ∃ j : Fin n, (j : ℝ) * h - e ≤ t ∧ t ≤ ((j : ℝ) + 1) * h + e := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa using ht⟩
    by_cases hlast : t ≤ (n : ℝ) * h + e
    · obtain ⟨j, hj⟩ := ih (by omega) ⟨ht.1, hlast⟩
      exact ⟨j.castSucc, by simpa using hj⟩
    · refine ⟨⟨n, by omega⟩, ?_, ?_⟩
      · change (n : ℝ) * h - e ≤ t
        linarith
      · simpa only [Nat.cast_add, Nat.cast_one] using ht.2

private def phaseSet (m : ℕ) (a : Fin (m - 1)) (t : ℝ) : Prop :=
  if a.val = 0 then phaseArc m (-1/4) (7/4) t
  else if a.val = 1 then phaseArc m ((m : ℝ) - 7/4) ((m : ℝ) + 1/4) t
  else phaseArc m (-1/4) (1/4) t ∨
    phaseArc m (7/4 + ((a : ℝ) - 3/2) * (1 - 1/(2*(m-3 : ℕ))) - 1/2)
      (7/4 + ((a : ℝ) - 3/2) * (1 - 1/(2*(m-3 : ℕ))) + 1/2) t

private theorem phaseSet_period (m : ℕ) (a : Fin (m - 1)) (t : ℝ) (z : ℤ) :
    phaseSet m a (t + (m : ℝ) * z) ↔ phaseSet m a t := by
  simp only [phaseSet]
  split_ifs <;> simp only [phaseArc_period]

private theorem phaseSet_common {m : ℕ} (hm : 3 ≤ m) (a : Fin (m - 1))
    (t : ℝ) (ht : |t| < 1/4) : phaseSet m a t := by
  have ht := abs_lt.mp ht
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  simp only [phaseSet]
  split_ifs
  · exact ⟨0, by simp only [Int.cast_zero, mul_zero, sub_zero]; constructor <;> linarith⟩
  · refine ⟨-1, ?_⟩
    simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, sub_neg_eq_add]
    constructor <;> linarith
  · left
    refine ⟨0, ?_⟩
    simp only [Int.cast_zero, mul_zero, sub_zero]
    constructor <;> linarith [ht.1, ht.2]

private theorem phaseSet_triple {m : ℕ} (a : Fin (m - 1)) (t : ℝ)
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (phaseSet m a (t + i) ∧ phaseSet m a (t + j) ∧ phaseSet m a (t + k)) := by
  simp only [phaseSet]
  split_ifs
  · exact phaseArc_triple (by norm_num) i j k hij hik hjk
  · exact phaseArc_triple (by linarith) i j k hij hik hjk
  · have hsmall := phaseArc_pair (m := m) (t := t) (a := (-1/4 : ℝ))
      (b := (1/4 : ℝ)) (by norm_num)
    have hlarge := phaseArc_pair (m := m) (t := t)
      (a := 7/4 + ((a : ℝ) - 3/2) * (1 - 1/(2*(m-3 : ℕ))) - 1/2)
      (b := 7/4 + ((a : ℝ) - 3/2) * (1 - 1/(2*(m-3 : ℕ))) + 1/2) (by linarith)
    rintro ⟨hi, hj, hk⟩
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
    · exact hsmall i j hij ⟨hi, hj⟩
    · exact hsmall i j hij ⟨hi, hj⟩
    · exact hsmall i k hik ⟨hi, hk⟩
    · exact hlarge j k hjk ⟨hj, hk⟩
    · exact hsmall j k hjk ⟨hj, hk⟩
    · exact hlarge i k hik ⟨hi, hk⟩
    · exact hlarge i j hij ⟨hi, hj⟩
    · exact hlarge i j hij ⟨hi, hj⟩

private theorem phaseSet_cover_normalized {m : ℕ} (hm : 3 ≤ m) (e : ℝ)
    (he : 0 < e) (hes : 16 * (m : ℝ) * e ≤ 1) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ m) :
    ∃ a : Fin (m - 1), ∀ u : ℝ, |u - t| < e → phaseSet m a u := by
  have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hequarter : e < 1/4 := by nlinarith
  let a₀ : Fin (m - 1) := ⟨0, by omega⟩
  let a₁ : Fin (m - 1) := ⟨1, by omega⟩
  have hleft (htop : t < 7/4 - e) :
      ∀ u : ℝ, |u - t| < e → phaseSet m a₀ u := by
    intro u hu
    have hu := abs_lt.mp hu
    change phaseArc m (-1/4) (7/4) u
    exact ⟨0, by simp only [Int.cast_zero, mul_zero, sub_zero]; constructor <;> linarith [ht.1]⟩
  have hright (hbot : (m : ℝ) - 7/4 + e < t) :
      ∀ u : ℝ, |u - t| < e → phaseSet m a₁ u := by
    intro u hu
    have hu := abs_lt.mp hu
    change phaseArc m ((m : ℝ) - 7/4) ((m : ℝ) + 1/4) u
    exact ⟨0, by simp only [Int.cast_zero, mul_zero, sub_zero]; constructor <;> linarith [ht.2]⟩
  by_cases htl : t < 7/4 - e
  · exact ⟨a₀, hleft htl⟩
  by_cases htr : (m : ℝ) - 7/4 + e < t
  · exact ⟨a₁, hright htr⟩
  have hm4 : 4 ≤ m := by
    by_contra h
    have hm3 : m = 3 := by omega
    norm_num [hm3] at hmr hes htr
    nlinarith
  let n := m - 3
  have hn : 0 < n := by dsimp [n]; omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : (m : ℝ) = (n : ℝ) + 3 := by
    have : m = n + 3 := by dsimp [n]; omega
    exact_mod_cast this
  let h : ℝ := 1 - 1/(2*(n : ℝ))
  have hprod : (n : ℝ) * h = (n : ℝ) - 1/2 := by
    dsimp [h]
    field_simp
  have hh : 0 ≤ h := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [h]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    linarith
  have hmargin : h / 2 + 2 * e < 1/2 := by
    have hne : (n : ℝ) * e < 1/8 := by nlinarith
    have hpos : (0 : ℝ) < n := hnreal
    nlinarith [hprod]
  obtain ⟨j, hj⟩ := grid_cover n hn h e (t - 7/4) hh he.le
    ⟨by linarith, by rw [hprod]; linarith⟩
  let a : Fin (m - 1) := ⟨j.val + 2, by have := j.isLt; dsimp [n] at *; omega⟩
  refine ⟨a, fun u hu => ?_⟩
  have hu := abs_lt.mp hu
  have ha0 : a.val ≠ 0 := by dsimp [a]; omega
  have ha1 : a.val ≠ 1 := by dsimp [a]; omega
  simp only [phaseSet, ite_eq_right ha0, ite_eq_right ha1]
  right
  refine ⟨0, ?_⟩
  have hac : (a : ℝ) = (j : ℝ) + 2 := by dsimp [a]; push_cast; rfl
  simp only [Int.cast_zero, mul_zero, sub_zero]
  change 7/4 + ((a : ℝ) - 3/2) * h - 1/2 < u ∧
    u < 7/4 + ((a : ℝ) - 3/2) * h + 1/2
  rw [hac]
  constructor <;> nlinarith [hj.1, hj.2]

private theorem phaseSet_cover {m : ℕ} (hm : 3 ≤ m) (e : ℝ)
    (he : 0 < e) (hes : 16 * (m : ℝ) * e ≤ 1) (t : ℝ) :
    ∃ a : Fin (m - 1), ∀ u : ℝ, |u - t| < e → phaseSet m a u := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let z : ℤ := ⌊t / (m : ℝ)⌋
  let r := t - (m : ℝ) * z
  have hr : 0 ≤ r ∧ r ≤ m := by
    have h₀ := Int.floor_le (t / (m : ℝ))
    have h₁ := Int.lt_floor_add_one (t / (m : ℝ))
    have h₀' := (le_div_iff₀ hmp).mp h₀
    have h₁' := (div_lt_iff₀ hmp).mp h₁
    dsimp [r, z]
    constructor <;> nlinarith
  obtain ⟨a, ha⟩ := phaseSet_cover_normalized hm e he hes r hr
  refine ⟨a, fun u hu => ?_⟩
  have hnear : |(u - (m : ℝ) * z) - r| < e := by
    convert hu using 1
    congr 1
    dsimp [r]
    ring
  have hau := ha (u - (m : ℝ) * z) hnear
  have hp := (phaseSet_period m a (u - (m : ℝ) * z) z).mpr hau
  simpa only [sub_add_cancel] using hp

private theorem lacunary_power_residue (m l : ℕ) :
    ∃ z : ℤ, (((m + 1) ^ l : ℕ) : ℤ) = 1 + (m : ℤ) * z := by
  induction l with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z * (m + 1) + 1, ?_⟩
    push_cast at *
    rw [pow_succ, hz]
    ring

/-- There are `m - 1` masks containing the initial signed window, and some mask
contains every later signed window. No mask contains three vertices of any
translated length-`m` polygon with step `(m + 1)^k`, once `k ≥ K`.
The power in the signed coordinates is the natural power, coerced to `ℤ`. -/
theorem lacunary_phase_cover (m R : ℕ) (hm : 3 ≤ m) :
    ∃ K : ℕ, R ≤ (m - 1) * (m + 1)^K ∧
      ∃ mask : Fin (m - 1) → ℤ → Prop,
        (∀ a n, |n| ≤ (R : ℤ) → mask a n) ∧
        (∀ i : ℕ, ∃ a, ∀ n : ℤ, |n| ≤ (R : ℤ) → mask a ((i : ℤ) + n)) ∧
        (∀ a s k, K ≤ k → ∀ (j₁ j₂ j₃ : Fin m),
          j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
          ¬ (mask a (s + (j₁ : ℤ) * ((m + 1)^k : ℕ)) ∧
            mask a (s + (j₂ : ℤ) * ((m + 1)^k : ℕ)) ∧
            mask a (s + (j₃ : ℤ) * ((m + 1)^k : ℕ)))) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt
    (16 * (m : ℝ) * ((R : ℝ) + 1)) (show (1 : ℝ) < m + 1 by linarith)
  let Q : ℕ := (m + 1)^K
  have hQ : (0 : ℝ) < Q := by dsimp [Q]; positivity
  have hKQ : 16 * (m : ℝ) * ((R : ℝ) + 1) < Q := by
    simpa only [Q, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hK
  let e : ℝ := 1 / (16 * (m : ℝ))
  have he : 0 < e := by dsimp [e]; positivity
  have hes : 16 * (m : ℝ) * e ≤ 1 := by dsimp [e]; field_simp; rfl
  have hequarter : e < 1/4 := by
    have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp [e]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * m)).mpr
    linarith
  have hsmall : (R : ℝ) / Q < e := by
    dsimp [e]
    apply (div_lt_div_iff₀ hQ (by positivity : (0 : ℝ) < 16 * m)).mpr
    nlinarith
  have hwindow (n : ℤ) (hn : |n| ≤ (R : ℤ)) : |(n : ℝ) / Q| < e := by
    have hn' : |(n : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hQ]
    exact (div_le_div_of_nonneg_right hn' hQ.le).trans_lt hsmall
  refine ⟨K, ?_, (fun a n => phaseSet m a ((n : ℝ) / Q)), ?_, ?_, ?_⟩
  · have hRQ : (R : ℝ) ≤ Q := by
      have hmr : (3 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have hRQ' : R ≤ Q := by exact_mod_cast hRQ
    have hm1 : 1 ≤ m - 1 := by omega
    apply hRQ'.trans
    change Q ≤ (m - 1) * Q
    nlinarith
  · intro a n hn
    exact phaseSet_common hm a _ ((hwindow n hn).trans hequarter)
  · intro i
    obtain ⟨a, ha⟩ := phaseSet_cover hm e he hes ((i : ℝ) / Q)
    refine ⟨a, fun n hn => ha _ ?_⟩
    have heq : (((i : ℤ) + n : ℤ) : ℝ) / Q - (i : ℝ) / Q = (n : ℝ) / Q := by
      push_cast
      ring
    rw [heq]
    exact hwindow n hn
  · intro a s k hk j₁ j₂ j₃ h₁₂ h₁₃ h₂₃ hmask
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨z, hz⟩ := lacunary_power_residue m l
    have hzreal : (((m + 1)^l : ℕ) : ℝ) = 1 + (m : ℝ) * z := by exact_mod_cast hz
    have hstep : (((m + 1)^(K + l) : ℕ) : ℝ) = (Q : ℝ) * (1 + (m : ℝ) * z) := by
      rw [pow_add, Nat.cast_mul, hzreal]
    push_cast at hstep
    have hphase (j : Fin m) :
        (((s + (j : ℤ) * ((m + 1)^(K + l) : ℕ) : ℤ) : ℝ) / Q) =
          (s : ℝ) / Q + (j : ℝ) + (m : ℝ) * ((j : ℤ) * z : ℤ) := by
      push_cast
      rw [hstep]
      field_simp
      <;> ring
    have hmem (j : Fin m)
        (hj : phaseSet m a (((s + (j : ℤ) * ((m + 1)^(K + l) : ℕ) : ℤ) : ℝ) / Q)) :
        phaseSet m a ((s : ℝ) / Q + (j : ℝ)) := by
      rw [hphase] at hj
      exact (phaseSet_period m a _ ((j : ℤ) * z)).mp hj
    exact phaseSet_triple a ((s : ℝ) / Q) j₁ j₂ j₃ h₁₂ h₁₃ h₂₃
      ⟨hmem j₁ hmask.1, hmem j₂ hmask.2.1, hmem j₃ hmask.2.2⟩

end D5.S1.Dynamics.Shadowing
