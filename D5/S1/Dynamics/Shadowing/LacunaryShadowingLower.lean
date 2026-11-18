/- GID: D5/S1/Dynamics/Shadowing/LacunaryShadowingLower
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LacunaryShadowingLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The initial diameter contract forces at least m minus one lacunary tracers. -/

import D5.S1.Dynamics.Shadowing.LacunaryProgressionSubshift

/-! The common initial symbol limits each whole tracer to one future hit. -/

open Set Function SymbolicDynamics.FullShift
open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- A windowed progression gives an actual pseudo-orbit of legal configurations.
Its small initial tracer diameter forces a common one at zero; distinct later
progression hits then require distinct tracers. -/
theorem lacunary_not_neighborhood_smaller (m : ℕ) (hm : 3 ≤ m) :
    ¬ NeighborhoodFiniteShadowing (m - 2) (lacunaryShift m) := by
  classical
  obtain ⟨η, hη, hcontrol⟩ := return_window_control 0
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεη : ε < η := by dsimp [ε]; linarith
  intro hshadow
  obtain ⟨δ, hδ, htrace⟩ := hshadow ε hε
  obtain ⟨R, hwindow⟩ := return_metric_window δ hδ
  let L : ℕ := R + 2
  let k : ℕ := 2 * L + 2
  let q : ℕ := (m + 1)^k
  have hq : 2 * L + 1 < q := by
    have htwo : k < 2^k := Nat.lt_two_pow_self
    have hpow : 2^k ≤ q := Nat.pow_le_pow_left (by omega : 2 ≤ m + 1) k
    have hk : 2 * L + 1 < k := by dsimp [k]; omega
    exact hk.trans (htwo.trans_le hpow)
  have hqZ : 2 * (L : ℤ) + 1 < (q : ℤ) := by exact_mod_cast hq
  have hqnonneg : (0 : ℤ) ≤ q := by positivity
  have hL : (L : ℤ) = (R : ℤ) + 2 := by simp [L]
  let P : ℕ → Set ℤ := fun t =>
    {r | -(L : ℤ) ≤ r ∧ r ≤ L ∧
      ∃ j : Fin m, (t : ℤ) + r = (j.val : ℤ) * (q : ℤ)}
  have hP (t : ℕ) : (P t).Subsingleton := by
    intro u hu v hv
    obtain ⟨hul, huu, i, hi⟩ := hu
    obtain ⟨hvl, hvu, j, hj⟩ := hv
    have hij : i.val = j.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hgap : (i.val : ℤ) * (q : ℤ) + (q : ℤ) ≤
            (j.val : ℤ) * (q : ℤ) := by
          calc
            _ = ((i.val : ℤ) + 1) * (q : ℤ) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (by omega) hqnonneg
        omega
      · have hgap : (j.val : ℤ) * (q : ℤ) + (q : ℤ) ≤
            (i.val : ℤ) * (q : ℤ) := by
          calc
            _ = ((j.val : ℤ) + 1) * (q : ℤ) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (by omega) hqnonneg
        omega
    rw [hij] at hi
    omega
  let z : ℕ → LacunaryPoint m := fun t =>
    ⟨supportPoint (P t), lacunary_legal_of_subsingleton_support
      (by simpa only [one_support_point] using hP t)⟩
  have hz : MetricPseudoOrbit (lacunaryShift m) δ z := by
    intro t
    change dist (shift (1 : ℤ) (supportPoint (P t)))
      (supportPoint (P (t + 1))) < δ
    apply hwindow
    intro r hrl hru
    change supportPoint (P t) (1 + r) = supportPoint (P (t + 1)) r
    apply return_bit_ext
    change (1 + r ∈ oneSupport (supportPoint (P t))) ↔
      (r ∈ oneSupport (supportPoint (P (t + 1))))
    rw [one_support_point, one_support_point]
    have hrL : -(L : ℤ) ≤ r ∧ r ≤ L := by constructor <;> omega
    have hr1L : -(L : ℤ) ≤ 1 + r ∧ 1 + r ≤ L := by constructor <;> omega
    have ht : ((t + 1 : ℕ) : ℤ) + r = (t : ℤ) + (1 + r) := by
      push_cast
      ring
    constructor
    · rintro ⟨_, _, j, hj⟩
      exact ⟨hrL.1, hrL.2, j, ht.trans hj⟩
    · rintro ⟨_, _, j, hj⟩
      exact ⟨hr1L.1, hr1L.2, j, ht.symm.trans hj⟩
  have hzcenter (j : ℕ) (hj : j < m) : (z (j * q)).1 0 = returnOne := by
    have hmem : (0 : ℤ) ∈ P (j * q) := by
      refine ⟨by omega, by omega, ⟨j, hj⟩, ?_⟩
      simp
    change (0 : ℤ) ∈ oneSupport (supportPoint (P (j * q)))
    rw [one_support_point]
    exact hmem
  obtain ⟨A, hAn, hcard, hdiam, hclose⟩ := htrace z hz
  have himage (t : ℕ) :
      ((lacunaryShift m)^[t] '' (A : Set (LacunaryPoint m))).Nonempty := by
    obtain ⟨a, ha⟩ := hAn
    exact ⟨(lacunaryShift m)^[t] a, a, ha, rfl⟩
  have hnear (t : ℕ) : ∃ a ∈ A,
      dist (z t) ((lacunaryShift m)^[t] a) < ε := by
    obtain ⟨b, ⟨a, ha, rfl⟩, hab⟩ :=
      (Metric.infDist_lt_iff (himage t)).mp (hclose t)
    exact ⟨a, ha, hab⟩
  obtain ⟨a₀, ha₀, hnear₀⟩ := hnear 0
  have ha₀zero : a₀.1 0 = returnOne := by
    have hsmall : dist (z 0).1 a₀.1 < η := by
      have hh : dist (z 0) a₀ < ε := by simpa using hnear₀
      exact hh.trans hεη
    have he := hcontrol (z 0).1 a₀.1 hsmall 0 (by simp) (by simp)
    exact he.symm.trans (by simpa using hzcenter 0 (by omega))
  have hallzero (a : LacunaryPoint m) (ha : a ∈ A) : a.1 0 = returnOne := by
    have hsmall : dist a a₀ < η :=
      (Metric.dist_le_diam_of_mem
        (@Set.Finite.isBounded (LacunaryPoint m) PseudoMetricSpace.toBornology
          (A : Set (LacunaryPoint m)) A.finite_toSet) ha ha₀).trans_lt
        (hdiam.trans hεη)
    exact (hcontrol a.1 a₀.1 hsmall 0 (by simp) (by simp)).trans ha₀zero
  have hex (j : Fin (m - 1)) : ∃ a : ↥A,
      a.1.1 ((((j.val + 1) * q : ℕ) : ℤ)) = returnOne := by
    let t : ℕ := (j.val + 1) * q
    obtain ⟨a, ha, hta⟩ := hnear t
    have he := hcontrol (z t).1 (((lacunaryShift m)^[t] a).1)
      (hta.trans hεη) 0 (by simp) (by simp)
    rw [lacunary_shift_iterate] at he
    have hcenter : (z t).1 0 = returnOne :=
      hzcenter (j.val + 1) (by have := j.isLt; omega)
    refine ⟨⟨a, ha⟩, ?_⟩
    simpa only [add_zero] using he.symm.trans hcenter
  choose g hg using hex
  have hginj : Injective g := by
    intro i j heq
    by_contra hne
    let o : Fin m := ⟨0, by omega⟩
    let ii : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
    let jj : Fin m := ⟨j.val + 1, by have := j.isLt; omega⟩
    have hoi : o ≠ ii := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [o, ii] at hh
      omega
    have hoj : o ≠ jj := by
      intro he
      have hh := congrArg Fin.val he
      dsimp [o, jj] at hh
      omega
    have hij : ii ≠ jj := by
      intro he
      apply hne
      apply Fin.ext
      have hh := congrArg Fin.val he
      dsimp [ii, jj] at hh
      omega
    apply ((g i).1).2 0 k o ii jj hoi hoj hij
    refine ⟨?_, ?_, ?_⟩
    · simpa [o] using hallzero (g i).1 (g i).2
    · simpa [ii, q] using hg i
    · have hj : (g i).1.1 ((((j.val + 1) * q : ℕ) : ℤ)) = returnOne := by
        rw [heq]
        exact hg j
      simpa [jj, q] using hj
  have hcount : m - 1 ≤ A.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective g hginj
  omega

end D5.S1.Dynamics.Shadowing
