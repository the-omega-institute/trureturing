/- GID: D5/S3/Arith/Additive/Waring/WaringLemma3
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringLemma3.lean#L1-L785
   Modified for this repository. Local imports use their D5 module paths.
   Selected declaration closure and supporting source.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringDensity.lean. -/

import D5.S3.Arith.Additive.Waring.WaringCount

open Finset

namespace Waring

/-- 同余类在 `[0,M]` 中的个数 ≤ `M/a + 1`。 -/
theorem card_diff_dvd_le {a M : ℕ} (ha : 0 < a) (c : ℤ) :
    ((Finset.Icc (0 : ℤ) (M : ℤ)).filter (fun y => (a : ℤ) ∣ y - c)).card ≤ M / a + 1 := by
  classical
  set T : Finset ℤ := (Finset.Icc (0 : ℤ) (M : ℤ)).filter (fun y => (a : ℤ) ∣ y - c) with hT
  have hTmem : ∀ y, y ∈ T ↔ (0 : ℤ) ≤ y ∧ y ≤ (M : ℤ) ∧ (a : ℤ) ∣ y - c := by
    intro y
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    simp
  · set y₀ := T.min' hne with hy₀def
    have hy₀mem : y₀ ∈ T := Finset.min'_mem T hne
    obtain ⟨hy₀0, hy₀M, hy₀dvd⟩ := (hTmem y₀).mp hy₀mem
    have hge : ∀ y ∈ T, y₀ ≤ y := fun y hy => Finset.min'_le T y hy
    have hdvd : ∀ y ∈ T, (a : ℤ) ∣ y - y₀ := by
      intro y hy
      obtain ⟨-, -, hydvd⟩ := (hTmem y).mp hy
      have := dvd_sub hydvd hy₀dvd
      simpa using this
    have hdvdNat : ∀ y ∈ T, a ∣ (y - y₀).toNat := by
      intro y hy
      obtain ⟨k, hk⟩ := hdvd y hy
      have hnonneg : (0 : ℤ) ≤ y - y₀ := by linarith [hge y hy]
      have hk0 : 0 ≤ k := by
        have hdiv : (y - y₀) / (a : ℤ) = k := by
          rw [hk, mul_comm]
          exact Int.mul_ediv_cancel k (by exact_mod_cast ha.ne')
        rw [← hdiv]
        exact Int.ediv_nonneg hnonneg (by exact_mod_cast ha.le)
      refine ⟨k.toNat, ?_⟩
      rw [hk, Int.toNat_mul (by exact_mod_cast ha.le) hk0, Int.toNat_natCast]
    have hmaps : Set.MapsTo (fun y : ℤ => (y - y₀).toNat / a) (↑T : Set ℤ)
        (↑(Finset.Icc 0 (M / a)) : Set ℕ) := by
      intro y hy
      have hyT : y ∈ T := Finset.mem_coe.mp hy
      obtain ⟨hy0, hyM, -⟩ := (hTmem y).mp hyT
      rw [Finset.mem_coe, Finset.mem_Icc]
      have hnonneg : (0 : ℤ) ≤ y - y₀ := by linarith [hge y hyT]
      have hlt : y - y₀ ≤ (M : ℤ) := by linarith
      have h1 : (y - y₀).toNat ≤ M := Int.toNat_le.mpr hlt
      exact ⟨Nat.zero_le _, Nat.div_le_div_right h1⟩
    have hinj : Set.InjOn (fun y : ℤ => (y - y₀).toNat / a) (↑T : Set ℤ) := by
      intro y hy y' hy' heq
      have hyT : y ∈ T := Finset.mem_coe.mp hy
      have hy'T : y' ∈ T := Finset.mem_coe.mp hy'
      have h1 := hdvdNat y hyT
      have h2 := hdvdNat y' hy'T
      have hnonneg : (0 : ℤ) ≤ y - y₀ := by linarith [hge y hyT]
      have hnonneg' : (0 : ℤ) ≤ y' - y₀ := by linarith [hge y' hy'T]
      have key : a * ((y - y₀).toNat / a) = a * ((y' - y₀).toNat / a) :=
        congrArg (fun t => a * t) heq
      rw [Nat.mul_div_cancel' h1, Nat.mul_div_cancel' h2] at key
      have h3 : y - y₀ = y' - y₀ := by
        rw [← Int.toNat_of_nonneg hnonneg, ← Int.toNat_of_nonneg hnonneg', key]
      linarith
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    calc T.card ≤ (Finset.Icc 0 (M / a)).card := hcard
      _ = M / a + 1 := by
          rw [Nat.card_Icc]
          simp

/-! ## 交换两个坐标 -/

/-- 交换 `Fin 2 → ℤ` 的两个坐标。 -/
def swap2 (m : Fin 2 → ℤ) : Fin 2 → ℤ := fun i => m (if i = 0 then 1 else 0)

theorem swap2_zero (m : Fin 2 → ℤ) : swap2 m 0 = m 1 := by simp [swap2]

theorem swap2_one (m : Fin 2 → ℤ) : swap2 m 1 = m 0 := by simp [swap2]

theorem swap2_involutive : Function.Involutive swap2 := by
  intro m
  funext i
  fin_cases i <;> simp [swap2]

/-- 交换坐标把 `(a₁,a₂)` 的纤维变成 `(a₂,a₁)` 的纤维。 -/
theorem fiber_swap (a₁ a₂ : ℤ) (M : ℕ) (f : ℤ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => a₁ * m 0 + a₂ * m 1 = f)).card
      = ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => a₂ * m 0 + a₁ * m 1 = f)).card := by
  classical
  refine Finset.card_bij (fun m _ => swap2 m) ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨?_, ?_⟩
    · rw [box2, Fintype.mem_piFinset] at hm ⊢
      intro i
      fin_cases i
      · simpa [swap2] using hm.1 1
      · simpa [swap2] using hm.1 0
    · rw [swap2_zero, swap2_one]
      linarith [hm.2]
  · intro m hm m' hm' heq
    funext i
    fin_cases i
    · have h := congrFun heq 1
      rwa [swap2_one, swap2_one] at h
    · have h := congrFun heq 0
      rwa [swap2_zero, swap2_zero] at h
  · intro m hm
    refine ⟨swap2 m, ?_, ?_⟩
    · rw [Finset.mem_filter] at hm ⊢
      refine ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset] at hm ⊢
        intro i
        fin_cases i
        · simpa [swap2] using hm.1 1
        · simpa [swap2] using hm.1 0
      · rw [swap2_zero, swap2_one]
        linarith [hm.2]
    · exact swap2_involutive m

/-! ## 纤维计数：线性方程在 `[0,M]²` 中的解数 -/

/-- 辅助：`a₁ ≠ 0` 时投影到第二坐标，得到 `M/|a₁| + 1`。 -/
theorem fiber_le_aux {a₁ a₂ : ℤ} (hcop : IsCoprime a₁ a₂) (ha₁ : a₁ ≠ 0) (M : ℕ) (f : ℤ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => a₁ * m 0 + a₂ * m 1 = f)).card
      ≤ M / a₁.natAbs + 1 := by
  classical
  set S : Finset (Fin 2 → ℤ) :=
    (box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => a₁ * m 0 + a₂ * m 1 = f) with hS
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    simp
  · obtain ⟨m₀, hm₀⟩ := hne
    have hSbox : ∀ m ∈ S, m ∈ box2 (0 : ℤ) (M : ℤ) := fun m hm => (Finset.mem_filter.mp hm).1
    have hSeq : ∀ m ∈ S, a₁ * m 0 + a₂ * m 1 = f := fun m hm => (Finset.mem_filter.mp hm).2
    have hinj : Set.InjOn (fun m : Fin 2 → ℤ => m 1) ↑S := by
      intro m hm m' hm' heq
      have h1 := hSeq m (Finset.mem_coe.mp hm)
      have h2 := hSeq m' (Finset.mem_coe.mp hm')
      funext i
      fin_cases i
      · have h3 : a₁ * m 0 = a₁ * m' 0 := by
          have h4 : a₂ * m 1 = a₂ * m' 1 := congrArg (fun t => a₂ * t) heq
          linarith
        exact mul_left_cancel₀ ha₁ h3
      · exact heq
    have himage : S.image (fun m => m 1)
        ⊆ (Finset.Icc (0 : ℤ) (M : ℤ)).filter (fun y => (a₁.natAbs : ℤ) ∣ y - m₀ 1) := by
      intro y hy
      obtain ⟨m, hmS, rfl⟩ := Finset.mem_image.mp hy
      have hbox : m ∈ box2 (0 : ℤ) (M : ℤ) := hSbox m hmS
      rw [box2, Fintype.mem_piFinset] at hbox
      refine Finset.mem_filter.mpr ⟨hbox 1, ?_⟩
      have hdiff : a₁ * (m 0 - m₀ 0) + a₂ * (m 1 - m₀ 1) = 0 := by
        have h1 := hSeq m hmS
        have h2 := hSeq m₀ hm₀
        linarith
      have hdvd : a₁ ∣ a₂ * (m 1 - m₀ 1) := by
        refine ⟨-(m 0 - m₀ 0), ?_⟩
        linarith
      have hdvd' : a₁ ∣ (m 1 - m₀ 1) := hcop.dvd_of_dvd_mul_left hdvd
      rw [Int.natCast_dvd]
      exact Int.natAbs_dvd_natAbs.mpr hdvd'
    calc S.card = (S.image (fun m => m 1)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.Icc (0 : ℤ) (M : ℤ)).filter (fun y => (a₁.natAbs : ℤ) ∣ y - m₀ 1)).card :=
          Finset.card_le_card himage
      _ ≤ M / a₁.natAbs + 1 := card_diff_dvd_le (Int.natAbs_pos.mpr ha₁) (m₀ 1)

/-- **纤维计数**：`a₁m₁ + a₂m₂ = f` 在 `[0,M]²` 中的解数 ≤ `M/max(|a₁|,|a₂|) + 1`。 -/
theorem fiber_le {a₁ a₂ : ℤ} (hcop : IsCoprime a₁ a₂) (M : ℕ) (f : ℤ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => a₁ * m 0 + a₂ * m 1 = f)).card
      ≤ M / max a₁.natAbs a₂.natAbs + 1 := by
  rcases le_or_gt a₂.natAbs a₁.natAbs with hle | hlt
  · have hmax : max a₁.natAbs a₂.natAbs = a₁.natAbs := max_eq_left hle
    rw [hmax]
    have ha₁ : a₁ ≠ 0 := by
      intro h
      rw [h] at hle
      have h2 : a₂.natAbs = 0 := le_antisymm hle (Nat.zero_le _)
      have h3 : a₂ = 0 := by
        have := Int.natAbs_eq_zero.mp h2
        exact this
      obtain ⟨x, y, hxy⟩ := hcop
      rw [h, h3] at hxy
      linarith
    exact fiber_le_aux hcop ha₁ M f
  · have hmax : max a₁.natAbs a₂.natAbs = a₂.natAbs := max_eq_right hlt.le
    rw [hmax]
    rw [fiber_swap a₁ a₂ M f]
    have ha₂ : a₂ ≠ 0 := by
      intro h
      rw [h] at hlt
      simp at hlt
    exact fiber_le_aux hcop.symm ha₂ M f

/-! ## 把 `Q` 拆成纤维卡片和 -/

/-- `Q` 按 `h` 拆成纤维的卡片和。 -/
theorem Q_eq_sum_fiber (H M : ℕ) (n : ℤ) :
    Q H M n = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ),
        ((box2 (0 : ℤ) (M : ℤ)).filter
          (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card := by
  classical
  rw [Q, Finset.card_filter]
  rw [show (∑ i ∈ (box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ)),
        (if i.1 0 * i.2 0 + i.1 1 * i.2 1 = n then (1 : ℕ) else 0))
      = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ), ∑ m ∈ box2 (0 : ℤ) (M : ℤ),
        (if h 0 * m 0 + h 1 * m 1 = n then (1 : ℕ) else 0) from
    Finset.sum_product (box2 (-(H : ℤ)) (H : ℤ)) (box2 (0 : ℤ) (M : ℤ))
      (fun i : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
        if i.1 0 * i.2 0 + i.1 1 * i.2 1 = n then (1 : ℕ) else 0)]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.card_filter]

/-- 盒子里非零元素的个数：`(2H+1)² − 1`。 -/
theorem card_box2_ne_zero (H : ℕ) :
    ((box2 (-(H : ℤ)) (H : ℤ)).filter (fun h : Fin 2 → ℤ => h ≠ 0)).card
      = (2 * H + 1) ^ 2 - 1 := by
  classical
  have hbox : (box2 (-(H : ℤ)) (H : ℤ)).card = (2 * H + 1) ^ 2 := by
    rw [box2, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Int.card_Icc]
    have h : (H : ℤ) + 1 - (-(H : ℤ)) = 2 * (H : ℤ) + 1 := by ring
    rw [h]
    omega
  have hzero : (0 : Fin 2 → ℤ) ∈ box2 (-(H : ℤ)) (H : ℤ) := by
    rw [box2, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    constructor <;> simp
  have hcompl : (box2 (-(H : ℤ)) (H : ℤ)).filter (fun h : Fin 2 → ℤ => h ≠ 0)
      = (box2 (-(H : ℤ)) (H : ℤ)).erase 0 := by
    ext h
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩
  rw [hcompl, Finset.card_erase_of_mem hzero, hbox]

/-! ## 按 `gcd(h₀,h₁)` 归约到原语部分 -/

/-- `h` 除以 `gcd(h₀,h₁)` 后的原语部分。 -/
noncomputable def prim (h : Fin 2 → ℤ) : Fin 2 → ℤ :=
  fun i => h i / ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ)

/-- `gcd(h₀,h₁) > 0`（`h ≠ 0`）。 -/
theorem gcd_pos_of_ne_zero {h : Fin 2 → ℤ} (hh : h ≠ 0) :
    0 < Nat.gcd (h 0).natAbs (h 1).natAbs := by
  rcases eq_or_ne (h 0) 0 with h0 | h0
  · rcases eq_or_ne (h 1) 0 with h1 | h1
    · exact absurd (by funext i; fin_cases i <;> assumption) hh
    · rw [h0]
      have : 0 < (h 1).natAbs := Int.natAbs_pos.mpr h1
      exact Nat.gcd_pos_of_pos_right 0 this
  · have : 0 < (h 0).natAbs := Int.natAbs_pos.mpr h0
    exact Nat.gcd_pos_of_pos_left (h 1).natAbs this

/-- `h i = gcd · prim h i`。 -/
theorem h_eq_gcd_mul_prim (h : Fin 2 → ℤ) (i : Fin 2) :
    h i = ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) * prim h i := by
  have hdvd0 : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 0 := by
    have h := Int.gcd_dvd_left (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h
    exact h
  have hdvd1 : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 1 := by
    have h := Int.gcd_dvd_right (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h
    exact h
  fin_cases i
  · exact (Int.mul_ediv_cancel' hdvd0).symm
  · exact (Int.mul_ediv_cancel' hdvd1).symm

/-- 乘积形式，方便改写。 -/
theorem h_mul_eq (h : Fin 2 → ℤ) (i : Fin 2) (x : ℤ) :
    h i * x = ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) * (prim h i * x) := by
  rw [h_eq_gcd_mul_prim h i]
  ring

/-- 原语部分的互素性。 -/
theorem isCoprime_prim {h : Fin 2 → ℤ} (hh : h ≠ 0) : IsCoprime (prim h 0) (prim h 1) := by
  have hg := gcd_pos_of_ne_zero hh
  have h1 : (h 0).gcd (h 1) = Nat.gcd (h 0).natAbs (h 1).natAbs := Int.gcd_eq_natAbs
  have hg' : 0 < (h 0).gcd (h 1) := by
    rw [h1]
    exact hg
  have h2 := Int.gcd_div_gcd_div_gcd (i := h 0) (j := h 1) hg'
  have h3 : prim h 0 = h 0 / ↑((h 0).gcd (h 1)) := by
    simp only [prim]
    rw [h1]
  have h4 : prim h 1 = h 1 / ↑((h 0).gcd (h 1)) := by
    simp only [prim]
    rw [h1]
  rw [Int.isCoprime_iff_gcd_eq_one, h3, h4]
  exact h2

/-- **逐 `h` 的纤维界**：`h ≠ 0` 时，解数 ≤ `M/max(|prim h₀|,|prim h₁|) + 1`。 -/
theorem fiber_le_gcd {h : Fin 2 → ℤ} (hh : h ≠ 0) (M : ℕ) (n : ℤ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card
      ≤ M / max (prim h 0).natAbs (prim h 1).natAbs + 1 := by
  classical
  have hg := gcd_pos_of_ne_zero hh
  have hgZ : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast hg.ne'
  have hsum : ∀ m : Fin 2 → ℤ, h 0 * m 0 + h 1 * m 1
      = ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) * (prim h 0 * m 0 + prim h 1 * m 1) := by
    intro m
    rw [h_mul_eq h 0 (m 0), h_mul_eq h 1 (m 1)]
    ring
  by_cases hdvd : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ n
  · have hfilter : (box2 (0 : ℤ) (M : ℤ)).filter
          (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)
        = (box2 (0 : ℤ) (M : ℤ)).filter
          (fun m : Fin 2 → ℤ =>
            prim h 0 * m 0 + prim h 1 * m 1 = n / ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ)) := by
      apply Finset.filter_congr
      intro m _
      rw [hsum m]
      constructor
      · intro hm
        have hmul : n = (prim h 0 * m 0 + prim h 1 * m 1)
            * ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) := by
          rw [← hm, mul_comm]
        exact (Int.ediv_eq_of_eq_mul_left hgZ hmul).symm
      · intro hm
        rw [hm]
        exact Int.mul_ediv_cancel' hdvd
    rw [hfilter]
    exact fiber_le (isCoprime_prim hh) M (n / ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ))
  · have hempty : (box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro m _ hm
      apply hdvd
      refine ⟨prim h 0 * m 0 + prim h 1 * m 1, ?_⟩
      rw [← hm, hsum m]
    rw [hempty]
    exact Nat.zero_le _

/-! ## `Σ 1/max(|a₀|,|a₁|) ≤ 8X` -/

/-- `box2 (-X) X` 的基数。 -/
theorem card_box2 (X : ℕ) : (box2 (-(X : ℤ)) (X : ℤ)).card = (2 * X + 1) ^ 2 := by
  rw [box2, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  have h : (X : ℤ) + 1 - (-(X : ℤ)) = 2 * (X : ℤ) + 1 := by ring
  rw [h]
  omega

/-- `a ∈ box2 (-X) X` ⟹ `|a i| ≤ X`。 -/
theorem abs_le_of_mem_box2 {X : ℕ} {a : Fin 2 → ℤ} (ha : a ∈ box2 (-(X : ℤ)) (X : ℤ))
    (i : Fin 2) : |a i| ≤ (X : ℤ) := by
  rw [box2, Fintype.mem_piFinset] at ha
  rw [abs_le]
  exact Finset.mem_Icc.mp (ha i)

/-- 反方向：`|a i| ≤ X` 对每个 `i` ⟹ `a ∈ box2 (-X) X`。 -/
theorem mem_box2_of_abs_le {X : ℕ} {a : Fin 2 → ℤ} (h : ∀ i, |a i| ≤ (X : ℤ)) :
    a ∈ box2 (-(X : ℤ)) (X : ℤ) := by
  rw [box2, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact abs_le.mp (h i)

/-- **核**：`Σ_{a ∈ [-X,X]², a≠0} 1/max(|a₀|,|a₁|) ≤ 8X`。 -/
theorem sum_inv_max_le (X : ℕ) :
    (∑ a ∈ (box2 (-(X : ℤ)) (X : ℤ)).filter (fun a : Fin 2 → ℤ => a ≠ 0),
        (1 : ℚ) / max (a 0).natAbs (a 1).natAbs) ≤ 8 * (X : ℚ) := by
  classical
  induction X with
  | zero =>
    simp only [Nat.cast_zero]
    have hempty : (box2 (-(0 : ℤ)) (0 : ℤ)).filter (fun a : Fin 2 → ℤ => a ≠ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a ha hne
      apply hne
      funext i
      have h := abs_le_of_mem_box2 ha i
      simp only [Nat.cast_zero] at h
      rw [abs_nonpos_iff] at h
      exact h
    rw [hempty, Finset.sum_empty]
    simp
  | succ n ih =>
    set Bn : Finset (Fin 2 → ℤ) := box2 (-(((n + 1 : ℕ) : ℤ))) (((n + 1 : ℕ) : ℤ)) with hBn
    set Bo : Finset (Fin 2 → ℤ) := box2 (-(n : ℤ)) (n : ℤ) with hBo
    have hsub : Bo ⊆ Bn := by
      intro a ha
      refine mem_box2_of_abs_le (fun i => ?_)
      have h1 := abs_le_of_mem_box2 ha i
      have h2 : (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by push_cast; linarith
      linarith
    have hzero : (0 : Fin 2 → ℤ) ∈ Bo := by
      refine mem_box2_of_abs_le (fun i => ?_)
      simp
    -- shell 上 max = n+1
    have hshell : ∀ a ∈ Bn \ Bo, max (a 0).natAbs (a 1).natAbs = n + 1 := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      obtain ⟨haBn, haBo⟩ := ha
      have hle : ∀ i : Fin 2, (a i).natAbs ≤ n + 1 := by
        intro i
        have h1 := abs_le_of_mem_box2 haBn i
        have h2 : ((a i).natAbs : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]
          exact h1
        exact_mod_cast h2
      have hex : ∃ i : Fin 2, (a i).natAbs = n + 1 := by
        by_contra hall
        apply haBo
        refine mem_box2_of_abs_le (fun i => ?_)
        have h1 : (a i).natAbs ≠ n + 1 := by
          intro hc
          exact hall ⟨i, hc⟩
        have hli := hle i
        have h2 : (a i).natAbs ≤ n := by omega
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h2
      obtain ⟨i, hi⟩ := hex
      have hmax1 : n + 1 ≤ max (a 0).natAbs (a 1).natAbs := by
        have h01 : i = 0 ∨ i = 1 := by
          fin_cases i
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases h01 with h | h
        · rw [h] at hi
          rw [hi]
          exact le_max_left _ _
        · rw [h] at hi
          rw [hi]
          exact le_max_right _ _
      have hmax2 : max (a 0).natAbs (a 1).natAbs ≤ n + 1 := max_le (hle 0) (hle 1)
      omega
    -- 拆成旧盒子 + shell
    have hsubsetF : Bo.filter (fun a : Fin 2 → ℤ => a ≠ 0)
        ⊆ Bn.filter (fun a : Fin 2 → ℤ => a ≠ 0) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨hsub ha.1, ha.2⟩
    have hset : (Bn.filter (fun a : Fin 2 → ℤ => a ≠ 0))
          \ (Bo.filter (fun a : Fin 2 → ℤ => a ≠ 0)) = Bn \ Bo := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, hne⟩, h2⟩
        refine ⟨h1, ?_⟩
        intro hbo
        exact h2 ⟨hbo, hne⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, fun hc => h2 hc.1⟩
        intro h0
        apply h2
        rw [h0]
        exact hzero
    have hsplit : (∑ a ∈ Bn.filter (fun a : Fin 2 → ℤ => a ≠ 0),
          (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
        = (∑ a ∈ Bo.filter (fun a : Fin 2 → ℤ => a ≠ 0),
            (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
          + ∑ a ∈ Bn \ Bo, (1 : ℚ) / max (a 0).natAbs (a 1).natAbs := by
      have hs := Finset.sum_sdiff hsubsetF
        (f := fun a : Fin 2 → ℤ => (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
      rw [hset] at hs
      linarith [hs]
    rw [hsplit]
    -- shell 上和 = card · 1/(n+1)
    have hshellsum : (∑ a ∈ Bn \ Bo, (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
        = ((Bn \ Bo).card : ℚ) * (1 / ((n + 1 : ℕ) : ℚ)) := by
      have hconst : ∀ a ∈ Bn \ Bo, (1 : ℚ) / max (a 0).natAbs (a 1).natAbs
          = 1 / ((n + 1 : ℕ) : ℚ) := by
        intro a ha
        rw [hshell a ha]
      rw [Finset.sum_congr rfl hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hshellsum]
    have hcardNat : (Bn \ Bo).card = (2 * (n + 1) + 1) ^ 2 - (2 * n + 1) ^ 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hBn, hBo, card_box2, card_box2]
    have hcard : ((Bn \ Bo).card : ℚ)
        = (2 * ((n + 1 : ℕ) : ℚ) + 1) ^ 2 - (2 * ((n : ℕ) : ℚ) + 1) ^ 2 := by
      rw [hcardNat]
      have hle : (2 * n + 1) ^ 2 ≤ (2 * (n + 1) + 1) ^ 2 := by
        apply Nat.pow_le_pow_left
        omega
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hcard]
    have hkey : ((2 * ((n + 1 : ℕ) : ℚ) + 1) ^ 2 - (2 * ((n : ℕ) : ℚ) + 1) ^ 2)
        * (1 / ((n + 1 : ℕ) : ℚ)) = 8 := by
      have h1 : ((2 * ((n + 1 : ℕ) : ℚ) + 1) ^ 2 - (2 * ((n : ℕ) : ℚ) + 1) ^ 2)
          = 8 * ((n + 1 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [h1]
      have h2 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by
        have : (0 : ℕ) < n + 1 := Nat.succ_pos n
        exact_mod_cast this.ne'
      field_simp
    rw [hkey]
    have hcast2 : ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [← hcast2]
    linarith

/-! ## 按 `gcd` 重索引 -/

/-- 除数条件：`gcd(h₀,h₁) ∣ n`。 -/
def gcond (n : ℤ) (h : Fin 2 → ℤ) : Prop :=
  ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ n

instance (n : ℤ) : DecidablePred (gcond n) := fun h => Int.decidableDvd _ _

/-- `gcd(h₀,h₁) ≤ H`（`h` 在盒子里且非零）。 -/
theorem gcd_le_of_mem_box2 {H : ℕ} {h : Fin 2 → ℤ}
    (hbox : h ∈ box2 (-(H : ℤ)) (H : ℤ)) (hne : h ≠ 0) :
    Nat.gcd (h 0).natAbs (h 1).natAbs ≤ H := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, h i ≠ 0 := by
    by_contra hall
    apply hne
    funext i
    by_contra hc
    exact hall ⟨i, hc⟩
  have hdvd0 : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 0 := by
    have h := Int.gcd_dvd_left (h 0) (h 1)
    rwa [Int.gcd_eq_natAbs] at h
  have hdvd1 : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 1 := by
    have h := Int.gcd_dvd_right (h 0) (h 1)
    rwa [Int.gcd_eq_natAbs] at h
  have hdvd : Nat.gcd (h 0).natAbs (h 1).natAbs ∣ (h i).natAbs := by
    fin_cases i
    · rw [← Int.natCast_dvd]
      exact hdvd0
    · rw [← Int.natCast_dvd]
      exact hdvd1
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hi) hdvd
  have h2 := abs_le_of_mem_box2 hbox i
  rw [Int.abs_eq_natAbs] at h2
  have h3 : (h i).natAbs ≤ H := by exact_mod_cast h2
  linarith

/-- **gcd 重索引**：`Σ_{h≠0, gcd|n} 1/max(|prim h|) ≤ 8H·σ₋₁(|n|)`。 -/
theorem sum_inv_prim_le {n : ℤ} (hn : n ≠ 0) (H : ℕ) :
    (∑ h ∈ (box2 (-(H : ℤ)) (H : ℤ)).filter (fun h : Fin 2 → ℤ => h ≠ 0 ∧ gcond n h),
        (1 : ℚ) / max (prim h 0).natAbs (prim h 1).natAbs)
      ≤ 8 * (H : ℚ) * sigmaMinusOne n.natAbs := by
  classical
  set S := (box2 (-(H : ℤ)) (H : ℤ)).filter (fun h : Fin 2 → ℤ => h ≠ 0 ∧ gcond n h) with hS
  set 𝔽 : (Σ g : ℕ, Fin 2 → ℤ) → ℚ :=
    fun y => (1 : ℚ) / max (y.2 0).natAbs (y.2 1).natAbs with h𝔽
  set Φ : (Fin 2 → ℤ) → (Σ g : ℕ, Fin 2 → ℤ) :=
    fun h => ⟨Nat.gcd (h 0).natAbs (h 1).natAbs, prim h⟩ with hΦ
  set s : Finset ℕ := (Finset.Icc 1 H).filter (fun g => g ∣ n.natAbs) with hs
  set T : Finset (Σ g : ℕ, Fin 2 → ℤ) := s.sigma (fun g =>
      (box2 (-(((H / g : ℕ) : ℤ))) (((H / g : ℕ) : ℤ))).filter (fun a => a ≠ 0)) with hT
  -- 单射
  have hinj : ∀ h ∈ S, ∀ h' ∈ S, Φ h = Φ h' → h = h' := by
    intro h _ h' _ heq
    have hg : Nat.gcd (h 0).natAbs (h 1).natAbs = Nat.gcd (h' 0).natAbs (h' 1).natAbs :=
      congrArg Sigma.fst heq
    have hp : prim h = prim h' := congrArg Sigma.snd heq
    funext i
    calc h i = ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) * prim h i :=
          h_eq_gcd_mul_prim h i
      _ = ((Nat.gcd (h' 0).natAbs (h' 1).natAbs : ℕ) : ℤ) * prim h' i := by rw [hg, hp]
      _ = h' i := (h_eq_gcd_mul_prim h' i).symm
  -- 像落在 T 中
  have hmap : ∀ h ∈ S, Φ h ∈ T := by
    intro h hh
    rw [hS, Finset.mem_filter] at hh
    obtain ⟨hbox, hne, hcond⟩ := hh
    have hgpos := gcd_pos_of_ne_zero hne
    have hgnat : Nat.gcd (h 0).natAbs (h 1).natAbs ∣ n.natAbs := by
      rw [← Int.natCast_dvd]
      exact hcond
    rw [hT, Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · simp only [hs, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hgpos, gcd_le_of_mem_box2 hbox hne⟩, hgnat⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine mem_box2_of_abs_le (fun i => ?_)
        have hnat : (h i).natAbs = Nat.gcd (h 0).natAbs (h 1).natAbs * (prim h i).natAbs := by
          rw [h_eq_gcd_mul_prim h i, Int.natAbs_mul]
          simp
        have hleH : (h i).natAbs ≤ H := by
          have h1 := abs_le_of_mem_box2 hbox i
          rw [Int.abs_eq_natAbs] at h1
          exact_mod_cast h1
        have hdiv : (prim h i).natAbs ≤ H / Nat.gcd (h 0).natAbs (h 1).natAbs := by
          rw [Nat.le_div_iff_mul_le hgpos, mul_comm, ← hnat]
          exact hleH
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hdiv
      · intro hp0
        apply hne
        funext i
        have hpi : prim h i = 0 := congrFun hp0 i
        rw [h_eq_gcd_mul_prim h i, hpi]
        simp
  -- 求和
  have hsum1 : (∑ h ∈ S, 𝔽 (Φ h)) = ∑ y ∈ S.image Φ, 𝔽 y :=
    (Finset.sum_image (f := 𝔽) (g := Φ) hinj).symm
  have hsum2 : (∑ y ∈ S.image Φ, 𝔽 y) ≤ ∑ y ∈ T, 𝔽 y := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => ?_)
    · intro y hy
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
      exact hmap h hh
    · positivity
  have hsum3 : (∑ y ∈ T, 𝔽 y)
      = ∑ g ∈ s, ∑ a ∈ (box2 (-(((H / g : ℕ) : ℤ))) (((H / g : ℕ) : ℤ))).filter
          (fun a : Fin 2 → ℤ => a ≠ 0), (1 : ℚ) / max (a 0).natAbs (a 1).natAbs := by
    rw [hT, Finset.sum_sigma]
  -- 逐 g 用 sum_inv_max_le
  have hstep : ∀ g ∈ s, (∑ a ∈ (box2 (-(((H / g : ℕ) : ℤ))) (((H / g : ℕ) : ℤ))).filter
        (fun a : Fin 2 → ℤ => a ≠ 0), (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
      ≤ 8 * ((H / g : ℕ) : ℚ) := by
    intro g _
    exact sum_inv_max_le (H / g)
  have htotal : (∑ g ∈ s, ∑ a ∈ (box2 (-(((H / g : ℕ) : ℤ))) (((H / g : ℕ) : ℤ))).filter
        (fun a : Fin 2 → ℤ => a ≠ 0), (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
      ≤ 8 * (H : ℚ) * (∑ g ∈ s, (1 : ℚ) / (g : ℚ)) := by
    calc (∑ g ∈ s, ∑ a ∈ (box2 (-(((H / g : ℕ) : ℤ))) (((H / g : ℕ) : ℤ))).filter
          (fun a : Fin 2 → ℤ => a ≠ 0), (1 : ℚ) / max (a 0).natAbs (a 1).natAbs)
        ≤ ∑ g ∈ s, 8 * ((H / g : ℕ) : ℚ) := Finset.sum_le_sum hstep
      _ ≤ ∑ g ∈ s, 8 * ((H : ℚ) / (g : ℚ)) := by
          refine Finset.sum_le_sum (fun g _ => ?_)
          have := Nat.cast_div_le (α := ℚ) (m := H) (n := g)
          nlinarith
      _ = 8 * (H : ℚ) * (∑ g ∈ s, (1 : ℚ) / (g : ℚ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [mul_one_div]
          ring
  -- σ₋₁ 对接
  have hnn : (n.natAbs : ℕ) ≠ 0 := by
    intro h
    exact hn (Int.natAbs_eq_zero.mp h)
  have hsigma : (∑ g ∈ s, (1 : ℚ) / (g : ℚ)) ≤ sigmaMinusOne n.natAbs := by
    unfold sigmaMinusOne
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => by positivity)
    intro g hg
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hg
    exact Nat.mem_divisors.mpr ⟨hg.2, hnn⟩
  calc (∑ h ∈ S, 𝔽 (Φ h)) = ∑ y ∈ S.image Φ, 𝔽 y := hsum1
    _ ≤ ∑ y ∈ T, 𝔽 y := hsum2
    _ = _ := hsum3
    _ ≤ 8 * (H : ℚ) * (∑ g ∈ s, (1 : ℚ) / (g : ℚ)) := htotal
    _ ≤ 8 * (H : ℚ) * sigmaMinusOne n.natAbs := by
        have hH : (0 : ℚ) ≤ 8 * (H : ℚ) := by positivity
        exact mul_le_mul_of_nonneg_left hsigma hH

/-! ## Lemma 3：`Q ≤ 4H(H+1) + 8HM·σ₋₁` -/

/-- `g ∤ n` 时纤维为空。 -/
theorem fiber_eq_zero_of_not_gcond {h : Fin 2 → ℤ} {n : ℤ} (_hne : h ≠ 0)
    (hc : ¬ gcond n h) (M : ℕ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hm
  apply hc
  have hsum : ∀ m : Fin 2 → ℤ, h 0 * m 0 + h 1 * m 1
      = ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) * (prim h 0 * m 0 + prim h 1 * m 1) := by
    intro m
    rw [h_mul_eq h 0 (m 0), h_mul_eq h 1 (m 1)]
    ring
  refine ⟨prim h 0 * m 0 + prim h 1 * m 1, ?_⟩
  rw [← hm, hsum m]

/-- `h = 0` 时纤维为空（`n ≠ 0`）。 -/
theorem fiber_zero_eq_zero {n : ℤ} (hn : n ≠ 0) (M : ℕ) :
    ((box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => (0 : Fin 2 → ℤ) 0 * m 0 + (0 : Fin 2 → ℤ) 1 * m 1 = n)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hm
  apply hn
  simpa using hm.symm

/-- **Lemma 3（本项目的版本）**：`Q ≤ 4H(H+1) + 8HM·σ₋₁(|n|)`（`n ≠ 0`）。 -/
theorem Q_le_sigma (H M : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (Q H M n : ℚ) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1)
      + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by
  classical
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set D : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hD
  set F : (Fin 2 → ℤ) → ℕ :=
    fun h => (D.filter (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card with hF
  set Sf : Finset (Fin 2 → ℤ) := B.filter (fun h : Fin 2 → ℤ => h ≠ 0 ∧ gcond n h) with hSf
  have hQ : Q H M n = ∑ h ∈ B, F h := Q_eq_sum_fiber H M n
  -- 去掉 h = 0
  have h1 : (∑ h ∈ B, F h) = ∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h := by
    have hzero : F 0 = 0 := by
      rw [hF]
      exact fiber_zero_eq_zero hn M
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro h hB hnotmem
    by_cases h0 : h = 0
    · rw [h0]
      exact hzero
    · exact absurd (by rw [Finset.mem_filter]; exact ⟨hB, h0⟩) hnotmem
  -- 去掉 g ∤ n 的项
  have h2 : (∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h) = ∑ h ∈ Sf, F h := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro h hh
      rw [Finset.mem_filter] at hh ⊢
      exact ⟨hh.1, hh.2.1⟩
    · intro h hh hnotmem
      rw [Finset.mem_filter] at hh
      obtain ⟨hB, hne⟩ := hh
      have hc : ¬ gcond n h := by
        intro hc'
        exact hnotmem (by rw [hSf, Finset.mem_filter]; exact ⟨hB, hne, hc'⟩)
      rw [hF]
      exact fiber_eq_zero_of_not_gcond hne hc M
  -- 逐项界
  have h3 : ((∑ h ∈ Sf, F h : ℕ) : ℚ) ≤ ∑ h ∈ Sf,
      ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := by
    push_cast
    refine Finset.sum_le_sum (fun h hh => ?_)
    rw [hSf, Finset.mem_filter] at hh
    obtain ⟨-, hne, -⟩ := hh
    have hb := fiber_le_gcd hne M n
    rw [← hD] at hb
    rw [hF]
    have hcast : ((D.filter (fun m : Fin 2 → ℤ => h 0 * m 0 + h 1 * m 1 = n)).card : ℚ) ≤
        ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) + 1 := by
      exact_mod_cast hb
    refine le_trans hcast ?_
    have hdiv : (↑(M / max (prim h 0).natAbs (prim h 1).natAbs) : ℚ) ≤
        (M : ℚ) / max (↑(prim h 0).natAbs) (↑(prim h 1).natAbs) := by
      have h := Nat.cast_div_le (α := ℚ) (m := M)
        (n := max (prim h 0).natAbs (prim h 1).natAbs)
      rwa [Nat.cast_max] at h
    linarith [hcast, hdiv]
  -- 拆成 M·Σ1/max + Σ1
  have h4 : (∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1))
      = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [mul_one_div]
  have h5 : (∑ h ∈ Sf, (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
      ≤ 8 * (H : ℚ) * sigmaMinusOne n.natAbs := by
    rw [hSf, hB]
    exact sum_inv_prim_le hn H
  have h6 : (∑ h ∈ Sf, (1 : ℚ)) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : Sf.card ≤ 4 * H * (H + 1) := by
      have hsub : Sf ⊆ B.filter (fun h : Fin 2 → ℤ => h ≠ 0) := by
        intro h hh
        rw [hSf, Finset.mem_filter] at hh
        exact Finset.mem_filter.mpr ⟨hh.1, hh.2.1⟩
      have hc1 : Sf.card ≤ (B.filter (fun h : Fin 2 → ℤ => h ≠ 0)).card :=
        Finset.card_le_card hsub
      rw [hB, card_box2_ne_zero H] at hc1
      refine le_trans hc1 ?_
      have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
      rw [hsq, Nat.add_sub_cancel]
    exact_mod_cast hcard
  calc (Q H M n : ℚ) = ((∑ h ∈ Sf, F h : ℕ) : ℚ) := by rw [hQ, h1, h2]
    _ ≤ ∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := h3
    _ = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := h4
    _ ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs)
        + 4 * (H : ℚ) * ((H : ℚ) + 1) := by
        have hM : (0 : ℚ) ≤ (M : ℚ) := by positivity
        have hMA : (M : ℚ) * (∑ h ∈ Sf,
            (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
            ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs) :=
          mul_le_mul_of_nonneg_left h5 hM
        linarith [hMA, h6]
    _ = 4 * (H : ℚ) * ((H : ℚ) + 1)
        + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by ring

end Waring
