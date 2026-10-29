/- GID: D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/LatticeLindbladianZeroSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite-range translation-invariant lattice Lindbladians have zero in their spectrum. -/

import D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization

/-! Matrix kernels of finite-range translation-invariant Lindblad generators. -/

noncomputable section

namespace D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum

open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open scoped ENNReal

/-- Matrix support of the Hamiltonian and the localized jump operators. -/
def IsFiniteRange (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ) : Prop :=
  (∀ x y, (r : ℤ) < |x - y| → h x y = 0) ∧
  (∀ k x y, (r : ℤ) < max |x - k| |y - k| → ℓ k x y = 0)

/-- Simultaneous translation of all matrix indices by one lattice site. -/
def IsTranslationInvariant (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ) : Prop :=
  (∀ x y, h (x + 1) (y + 1) = h x y) ∧
  (∀ k x y, ℓ (k + 1) (x + 1) (y + 1) = ℓ k x y)

/-- The Lindblad generator in matrix elements; all index sums are unconditional sums. -/
def lindbladEntry (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ρ : ℤ × ℤ → ℂ) (x y : ℤ) : ℂ :=
  -Complex.I * ((∑' z, h x z * ρ (z, y)) - ∑' z, ρ (x, z) * h z y) +
    (g : ℂ) * ∑' k,
      ((∑' u, ∑' v, ℓ k x u * ρ (u, v) * star (ℓ k y v)) -
        (1 / 2 : ℂ) * ∑' z, (∑' w, star (ℓ k w x) * ℓ k w z) * ρ (z, y) -
        (1 / 2 : ℂ) * ∑' z, ρ (x, z) * (∑' w, star (ℓ k w z) * ℓ k w y))

private lemma h_difference (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ht : IsTranslationInvariant h ℓ) (x y : ℤ) : h x y = h 0 (y - x) := by
  have hp : Function.Periodic (fun z : ℤ => h z (y - x + z)) 1 := fun z => by
    simpa only [add_assoc] using ht.1 z (y - x + z)
  simpa only [mul_one, Int.cast_id, sub_add_cancel, add_zero] using hp.int_mul_eq x

private lemma jump_difference (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ht : IsTranslationInvariant h ℓ) (k x y : ℤ) :
    ℓ k x y = ℓ 0 (x - k) (y - k) := by
  have hp : Function.Periodic (fun z : ℤ => ℓ z (x - k + z) (y - k + z)) 1 := fun z => by
    simpa only [add_assoc] using ht.2 z (x - k + z) (y - k + z)
  simpa only [mul_one, Int.cast_id, sub_add_cancel, add_zero] using hp.int_mul_eq k

private lemma matrix_bound (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (ht : IsTranslationInvariant h ℓ) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ x y, ‖h x y‖ ≤ m) ∧ (∀ k x y, ‖ℓ k x y‖ ≤ m) := by
  let s := Finset.Icc (-(r : ℤ)) r
  let a := ∑ z ∈ s, ‖h 0 z‖
  let b := ∑ z ∈ s, ∑ w ∈ s, ‖ℓ 0 z w‖
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨a + b, add_nonneg ha hb, ?_, ?_⟩
  · intro x y
    by_cases hs : y - x ∈ s
    · rw [h_difference h ℓ ht]
      exact (Finset.single_le_sum (fun z _ => norm_nonneg (h 0 z)) hs).trans
        (le_add_of_nonneg_right hb)
    · have hz : h x y = 0 := hf.1 x y (by
        simp only [s, Finset.mem_Icc] at hs
        rw [abs_sub_comm, lt_abs]
        omega)
      rw [hz, norm_zero]
      exact add_nonneg ha hb
  · intro k x y
    by_cases hx : x - k ∈ s
    · by_cases hy : y - k ∈ s
      · rw [jump_difference h ℓ ht]
        have hi := Finset.single_le_sum (fun z _ => norm_nonneg (ℓ 0 (x - k) z)) hy
        have hj := Finset.single_le_sum (s := s)
          (f := fun z => ∑ w ∈ s, ‖ℓ 0 z w‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hx
        exact (hi.trans hj).trans (le_add_of_nonneg_left ha)
      · have hz : ℓ k x y = 0 := hf.2 k x y (by
          simp only [s, Finset.mem_Icc] at hy
          have : (r : ℤ) < |y - k| := by rw [lt_abs]; omega
          exact this.trans_le (le_max_right _ _))
        rw [hz, norm_zero]
        exact add_nonneg ha hb
    · have hz : ℓ k x y = 0 := hf.2 k x y (by
        simp only [s, Finset.mem_Icc] at hx
        have : (r : ℤ) < |x - k| := by rw [lt_abs]; omega
        exact this.trans_le (le_max_left _ _))
      rw [hz, norm_zero]
      exact add_nonneg ha hb

private lemma weighted_shift_exists (w : ℤ × ℤ) (c : ℤ × ℤ → ℂ) (m : ℝ)
    (hm : 0 ≤ m) (hc : ∀ p, ‖c p‖ ≤ m) :
    ∃ t : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ),
      (∀ ρ p, t ρ p = c p * ρ (p + w)) ∧ ‖t‖ ≤ m := by
  let c' : lp (fun _ : ℤ × ℤ => ℂ) ∞ :=
    ⟨c, memℓp_infty_iff.mpr ⟨m, by rintro _ ⟨p, rfl⟩; exact hc p⟩⟩
  let s := updateLinearIsometryEquiv (Equiv.addRight w).symm
  refine ⟨(diagonalOperator c').comp s.toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
  · intro ρ p
    rfl
  · calc
      _ ≤ ‖diagonalOperator c'‖ * ‖s.toLinearIsometry.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ m * 1 := mul_le_mul
        (by rw [diagonalOperator_norm]; exact lp.norm_le_of_forall_le hm hc)
        s.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _) hm
      _ = m := mul_one _

private def coefficient (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (w p : ℤ × ℤ) : ℂ :=
  lindbladEntry g h ℓ (Pi.single (p + w) 1) p.1 p.2

private lemma tsum_interval (r : ℕ) (k : ℤ) (f : ℤ → ℂ)
    (hf : ∀ z, (r : ℤ) < |z - k| → f z = 0) :
    ∑' z, f z = ∑ z ∈ Finset.Icc (k - r) (k + r), f z := by
  apply tsum_eq_sum
  intro z hz
  apply hf
  simp only [Finset.mem_Icc] at hz
  rw [lt_abs]
  omega

private lemma jump_zero_left (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (k x y : ℤ) (hx : (r : ℤ) < |x - k|) :
    ℓ k x y = 0 := hf.2 k x y (hx.trans_le (le_max_left _ _))

private lemma jump_zero_right (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (k x y : ℤ) (hy : (r : ℤ) < |y - k|) :
    ℓ k x y = 0 := hf.2 k x y (hy.trans_le (le_max_right _ _))

private def finiteEntry (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (ρ : ℤ × ℤ → ℂ) (x y : ℤ) : ℂ :=
  -Complex.I * ((∑ z ∈ Finset.Icc (x - r) (x + r), h x z * ρ (z, y)) -
    ∑ z ∈ Finset.Icc (y - r) (y + r), ρ (x, z) * h z y) +
    (g : ℂ) * ∑ k ∈ (Finset.Icc (x - r) (x + r) ∪ Finset.Icc (y - r) (y + r)),
      ((∑ u ∈ Finset.Icc (k - r) (k + r), ∑ v ∈ Finset.Icc (k - r) (k + r),
        ℓ k x u * ρ (u, v) * star (ℓ k y v)) -
        (1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) * ρ (z, y) -
        (1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
          ρ (x, z) * (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y))

private lemma entry_finite (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ρ : ℤ × ℤ → ℂ) (x y : ℤ) :
    lindbladEntry g h ℓ ρ x y = finiteEntry r g h ℓ ρ x y := by
  classical
  have hhleft : (∑' z, h x z * ρ (z, y)) =
      ∑ z ∈ Finset.Icc (x - r) (x + r), h x z * ρ (z, y) :=
    tsum_interval r x _ fun z hz => by rw [hf.1 x z (by rwa [abs_sub_comm]), zero_mul]
  have hhright : (∑' z, ρ (x, z) * h z y) =
      ∑ z ∈ Finset.Icc (y - r) (y + r), ρ (x, z) * h z y :=
    tsum_interval r y _ fun z hz => by rw [hf.1 z y hz, mul_zero]
  rw [lindbladEntry.eq_1, finiteEntry.eq_1]
  rw [hhleft, hhright]
  congr 2
  rw [tsum_eq_sum (s := Finset.Icc (x - r) (x + r) ∪ Finset.Icc (y - r) (y + r))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hgain : (∑' u, ∑' v, ℓ k x u * ρ (u, v) * star (ℓ k y v)) =
        ∑ u ∈ Finset.Icc (k - r) (k + r), ∑ v ∈ Finset.Icc (k - r) (k + r),
          ℓ k x u * ρ (u, v) * star (ℓ k y v) := by
      rw [tsum_interval r k _ (fun u hu => by
        simp only [jump_zero_right r h ℓ hf k x u hu, zero_mul, tsum_zero])]
      apply Finset.sum_congr rfl
      intro u hu
      exact tsum_interval r k _ fun v hv => by
        rw [jump_zero_right r h ℓ hf k y v hv, star_zero, mul_zero]
    have hw (a b : ℤ) : (∑' w, star (ℓ k w a) * ℓ k w b) =
        ∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w a) * ℓ k w b :=
      tsum_interval r k _ fun w hw => by
        rw [jump_zero_left r h ℓ hf k w a hw, star_zero, zero_mul]
    have hal : (∑' z, (∑' w, star (ℓ k w x) * ℓ k w z) * ρ (z, y)) =
        ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) * ρ (z, y) := by
      rw [tsum_interval r k _ (fun z hz => by
        simp only [jump_zero_right r h ℓ hf k _ z hz, mul_zero, tsum_zero, zero_mul])]
      simp only [hw]
    have har : (∑' z, ρ (x, z) * (∑' w, star (ℓ k w z) * ℓ k w y)) =
        ∑ z ∈ Finset.Icc (k - r) (k + r),
          ρ (x, z) * (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y) := by
      rw [tsum_interval r k _ (fun z hz => by
        simp only [jump_zero_right r h ℓ hf k _ z hz, star_zero, zero_mul,
          tsum_zero, mul_zero])]
      simp only [hw]
    rw [hgain, hal, har]
  · intro k hk
    have hx : (r : ℤ) < |x - k| := by
      simp only [Finset.mem_union, Finset.mem_Icc] at hk
      rw [lt_abs]; omega
    have hy : (r : ℤ) < |y - k| := by
      simp only [Finset.mem_union, Finset.mem_Icc] at hk
      rw [lt_abs]; omega
    simp only [jump_zero_left r h ℓ hf k x _ hx,
      jump_zero_right r h ℓ hf k _ x hx, jump_zero_right r h ℓ hf k _ y hy,
      star_zero, zero_mul, mul_zero, tsum_zero, sub_zero]

private def entryLinear (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (x y : ℤ) : ((ℤ × ℤ) → ℂ) →ₗ[ℂ] ℂ :=
  -Complex.I • ((∑ z ∈ Finset.Icc (x - r) (x + r), h x z • LinearMap.proj (z, y)) -
    ∑ z ∈ Finset.Icc (y - r) (y + r), h z y • LinearMap.proj (x, z)) +
    (g : ℂ) • ∑ k ∈ (Finset.Icc (x - r) (x + r) ∪ Finset.Icc (y - r) (y + r)),
      ((∑ u ∈ Finset.Icc (k - r) (k + r), ∑ v ∈ Finset.Icc (k - r) (k + r),
        (ℓ k x u * star (ℓ k y v)) • LinearMap.proj (u, v)) -
        (1 / 2 : ℂ) • ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) •
            LinearMap.proj (z, y) -
        (1 / 2 : ℂ) • ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y) •
            LinearMap.proj (x, z))

private lemma entryLinear_apply (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ρ : ℤ × ℤ → ℂ) (x y : ℤ) :
    entryLinear r g h ℓ x y ρ = lindbladEntry g h ℓ ρ x y := by
  rw [entry_finite r g h ℓ hf]
  rw [entryLinear.eq_1, finiteEntry.eq_1]
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, smul_eq_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]

private lemma entry_locality (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ρ σ : ℤ × ℤ → ℂ) (x y : ℤ)
    (he : ∀ u v, |u - x| ≤ 2 * (r : ℤ) → |v - y| ≤ 2 * (r : ℤ) →
      ρ (u, v) = σ (u, v)) : lindbladEntry g h ℓ ρ x y = lindbladEntry g h ℓ σ x y := by
  have hl (k a b : ℤ) (hn : ℓ k a b ≠ 0) :
      -(r : ℤ) ≤ a - k ∧ a - k ≤ r ∧ -(r : ℤ) ≤ b - k ∧ b - k ≤ r := by
    have hh : max |a - k| |b - k| ≤ (r : ℤ) := le_of_not_gt fun ht => hn (hf.2 k a b ht)
    exact ⟨(abs_le.mp ((le_max_left _ _).trans hh)).1,
      (abs_le.mp ((le_max_left _ _).trans hh)).2,
      (abs_le.mp ((le_max_right _ _).trans hh)).1,
      (abs_le.mp ((le_max_right _ _).trans hh)).2⟩
  have hρ (u v : ℤ) (hu : -(2 * r : ℤ) ≤ u - x ∧ u - x ≤ 2 * r)
      (hv : -(2 * r : ℤ) ≤ v - y ∧ v - y ≤ 2 * r) : ρ (u, v) = σ (u, v) :=
    he u v (abs_le.mpr hu) (abs_le.mpr hv)
  unfold lindbladEntry
  apply congrArg₂ (fun a b : ℂ => -Complex.I * a + (g : ℂ) * b)
  · apply congrArg₂ (fun a b : ℂ => a - b)
    · apply tsum_congr
      intro z
      by_cases hz : h x z = 0
      · rw [hz, zero_mul, zero_mul]
      · have hh : |x - z| ≤ (r : ℤ) := le_of_not_gt fun ht => hz (hf.1 x z ht)
        rw [hρ z y (by have := abs_le.mp hh; constructor <;> omega)
          (by constructor <;> omega)]
    · apply tsum_congr
      intro z
      by_cases hz : h z y = 0
      · rw [hz, mul_zero, mul_zero]
      · have hh : |z - y| ≤ (r : ℤ) := le_of_not_gt fun ht => hz (hf.1 z y ht)
        rw [hρ x z (by constructor <;> omega)
          (by have := abs_le.mp hh; constructor <;> omega)]
  · apply tsum_congr
    intro k
    apply congrArg₂ (fun a b : ℂ => a - b)
    · apply congrArg₂ (fun a b : ℂ => a - b)
      · apply tsum_congr
        intro u
        apply tsum_congr
        intro v
        by_cases hu : ℓ k x u = 0
        · simp only [hu, zero_mul]
        by_cases hv : ℓ k y v = 0
        · simp only [hv, star_zero, mul_zero]
        have hx := hl k x u hu
        have hy := hl k y v hv
        rw [hρ u v (by constructor <;> omega) (by constructor <;> omega)]
      · apply congrArg (fun a : ℂ => (1 / 2 : ℂ) * a)
        apply tsum_congr
        intro z
        rw [← tsum_mul_right, ← tsum_mul_right]
        apply tsum_congr
        intro w
        by_cases hx : ℓ k w x = 0
        · simp only [hx, star_zero, zero_mul]
        by_cases hz : ℓ k w z = 0
        · simp only [hz, mul_zero, zero_mul]
        have hxk := hl k w x hx
        have hzk := hl k w z hz
        rw [hρ z y (by constructor <;> omega) (by constructor <;> omega)]
    · apply congrArg (fun a : ℂ => (1 / 2 : ℂ) * a)
      apply tsum_congr
      intro z
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro w
      by_cases hz : ℓ k w z = 0
      · simp only [hz, star_zero, zero_mul, mul_zero]
      by_cases hy : ℓ k w y = 0
      · simp only [hy, mul_zero]
      have hzk := hl k w z hz
      have hyk := hl k w y hy
      rw [hρ x z (by constructor <;> omega) (by constructor <;> omega)]

private lemma finite_window (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ρ : ObserverHilbertSpace (ℤ × ℤ)) (p : ℤ × ℤ) :
    lindbladEntry g h ℓ ρ p.1 p.2 =
      ∑ w ∈ (Finset.Icc (-(2 * r : ℤ)) (2 * r) ×ˢ
        Finset.Icc (-(2 * r : ℤ)) (2 * r)), coefficient g h ℓ w p * ρ (p + w) := by
  classical
  let s := Finset.Icc (-(2 * r : ℤ)) (2 * r) ×ˢ Finset.Icc (-(2 * r : ℤ)) (2 * r)
  let σ : ℤ × ℤ → ℂ := ∑ w ∈ s, ρ (p + w) • Pi.single (p + w) 1
  have he : lindbladEntry g h ℓ ρ p.1 p.2 = lindbladEntry g h ℓ σ p.1 p.2 := by
    apply entry_locality r g h ℓ hf
    intro u v hu hv
    have hw : (u - p.1, v - p.2) ∈ s := by
      simp only [s, Finset.mem_product, Finset.mem_Icc]
      exact ⟨abs_le.mp hu, abs_le.mp hv⟩
    have hpw : p + (u - p.1, v - p.2) = (u, v) := by ext <;> simp
    dsimp only [σ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single (u - p.1, v - p.2)]
    · simp only [hpw, ite_true, mul_one]
    · intro w hws hne
      have hn : (u, v) ≠ p + w := by
        intro hh
        apply hne
        have hh1 := congrArg Prod.fst hh
        have hh2 := congrArg Prod.snd hh
        apply Prod.ext <;> dsimp at * <;> omega
      simp only [ite_eq_right hn, mul_zero]
    · exact fun hn => (hn hw).elim
  rw [he, ← entryLinear_apply r g h ℓ hf σ]
  change entryLinear r g h ℓ p.1 p.2 (∑ w ∈ s, ρ (p + w) • Pi.single (p + w) 1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, entryLinear_apply r g h ℓ hf]
  exact mul_comm _ _

private lemma norm_sum_bound {α : Type*} (s : Finset α) (f : α → ℂ) (b : ℝ)
    (hf : ∀ a ∈ s, ‖f a‖ ≤ b) : ‖∑ a ∈ s, f a‖ ≤ s.card * b := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using norm_sum_le_of_le s hf

private lemma interval_card (r : ℕ) (x : ℤ) :
    (Finset.Icc (x - r) (x + r)).card = 2 * r + 1 := by
  rw [Int.card_Icc]
  omega

private lemma entry_norm_bound (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ) (m : ℝ) (hm : 0 ≤ m)
    (hh : ∀ x y, ‖h x y‖ ≤ m) (hl : ∀ k x y, ‖ℓ k x y‖ ≤ m)
    (ρ : ℤ × ℤ → ℂ) (hρ : ∀ p, ‖ρ p‖ ≤ 1) (x y : ℤ) :
    ‖lindbladEntry g h ℓ ρ x y‖ ≤
      2 * (2 * (r : ℝ) + 1) * m + |g| * (6 * (2 * (r : ℝ) + 1) ^ 3 * m ^ 2) := by
  classical
  let b : ℝ := 2 * r + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc (k : ℤ) : ((Finset.Icc (k - r) (k + r)).card : ℝ) = b := by
    rw [interval_card]; dsimp [b]; push_cast; rfl
  have hhm (a z : ℤ) : ‖h a z * ρ (z, y)‖ ≤ m := by
    rw [norm_mul]
    exact (mul_le_mul (hh a z) (hρ _) (norm_nonneg _) hm).trans_eq (mul_one _)
  have hmh (z a : ℤ) : ‖ρ (x, z) * h z a‖ ≤ m := by
    rw [norm_mul]
    exact (mul_le_mul (hρ _) (hh z a) (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
  have hpair (k a z w : ℤ) : ‖star (ℓ k w a) * ℓ k w z‖ ≤ m ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hl _ _ _) (hl _ _ _) (norm_nonneg _) hm
  have hjump (k : ℤ) :
      ‖(∑ u ∈ Finset.Icc (k - r) (k + r), ∑ v ∈ Finset.Icc (k - r) (k + r),
        ℓ k x u * ρ (u, v) * star (ℓ k y v)) -
        (1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) * ρ (z, y) -
        (1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
          ρ (x, z) * (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y)‖ ≤
          3 * (b * (b * m ^ 2)) := by
    have hg : ‖∑ u ∈ Finset.Icc (k - r) (k + r),
        ∑ v ∈ Finset.Icc (k - r) (k + r), ℓ k x u * ρ (u, v) * star (ℓ k y v)‖ ≤
          b * (b * m ^ 2) := by
      apply (norm_sum_bound _ _ _ fun u hu => ?_).trans_eq (by rw [hc])
      apply (norm_sum_bound _ _ _ fun v hv => ?_).trans_eq (by rw [hc])
      rw [norm_mul, norm_mul, norm_star]
      have hi := mul_le_mul (hl k x u) (hρ (u, v)) (norm_nonneg _) hm
      have hj := mul_le_mul (hi.trans_eq (mul_one m)) (hl k y v) (norm_nonneg _) hm
      simpa only [pow_two] using hj
    have hs (a z : ℤ) : ‖∑ w ∈ Finset.Icc (k - r) (k + r),
        star (ℓ k w a) * ℓ k w z‖ ≤ b * m ^ 2 :=
      (norm_sum_bound _ _ _ fun w hw => hpair k a z w).trans_eq (by rw [hc])
    have ha : ‖∑ z ∈ Finset.Icc (k - r) (k + r),
        (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) * ρ (z, y)‖ ≤
          b * (b * m ^ 2) := by
      apply (norm_sum_bound _ _ _ fun z hz => ?_).trans_eq (by rw [hc])
      rw [norm_mul]
      exact (mul_le_mul (hs x z) (hρ _) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    have hbnd : ‖∑ z ∈ Finset.Icc (k - r) (k + r),
        ρ (x, z) * (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y)‖ ≤
          b * (b * m ^ 2) := by
      apply (norm_sum_bound _ _ _ fun z hz => ?_).trans_eq (by rw [hc])
      rw [norm_mul]
      exact (mul_le_mul (hρ _) (hs z y) (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
    have hhalf : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    have hn := norm_sub_le
      ((∑ u ∈ Finset.Icc (k - r) (k + r), ∑ v ∈ Finset.Icc (k - r) (k + r),
        ℓ k x u * ρ (u, v) * star (ℓ k y v)) -
        (1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
          (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w x) * ℓ k w z) * ρ (z, y))
      ((1 / 2 : ℂ) * ∑ z ∈ Finset.Icc (k - r) (k + r),
        ρ (x, z) * (∑ w ∈ Finset.Icc (k - r) (k + r), star (ℓ k w z) * ℓ k w y))
    calc
      _ ≤ _ := hn
      _ ≤ 3 * (b * (b * m ^ 2)) := by
        grw [norm_sub_le, norm_mul, norm_mul, hg, ha, hbnd, hhalf]
        ring_nf
        exact le_rfl
  rw [entry_finite r g h ℓ hf]
  unfold finiteEntry
  have hunion : ((Finset.Icc (x - r) (x + r) ∪
      Finset.Icc (y - r) (y + r)).card : ℝ) ≤ 2 * b := by
    calc
      _ ≤ ((Finset.Icc (x - r) (x + r)).card : ℝ) +
          ((Finset.Icc (y - r) (y + r)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le (Finset.Icc (x - r) (x + r))
          (Finset.Icc (y - r) (y + r))
      _ = 2 * b := by rw [hc, hc]; ring
  have hal := norm_sum_bound (Finset.Icc (x - r) (x + r)) _ m (fun z hz => hhm x z)
  have har := norm_sum_bound (Finset.Icc (y - r) (y + r)) _ m (fun z hz => hmh z y)
  rw [hc] at hal har
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * b * m + |g| * (6 * b ^ 3 * m ^ 2) := by
      grw [norm_mul, norm_mul, norm_sub_le, hal, har, norm_sum_bound _ _ _ (fun k _ => hjump k),
        hunion]
      simp only [norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      ring_nf
      exact le_rfl
    _ = _ := rfl

private lemma coefficient_bound (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ w p, ‖coefficient g h ℓ w p‖ ≤ m := by
  obtain ⟨m, hm, hh, hl⟩ := matrix_bound r h ℓ hf ht
  refine ⟨2 * (2 * (r : ℝ) + 1) * m + |g| * (6 * (2 * (r : ℝ) + 1) ^ 3 * m ^ 2),
    by positivity, ?_⟩
  intro w p
  apply entry_norm_bound r g h ℓ hf m hm hh hl
  intro q
  classical
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

private lemma bounded_operator (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ t : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ),
      ∀ ρ : ObserverHilbertSpace (ℤ × ℤ), ∀ x y,
      t ρ (x, y) = lindbladEntry g h ℓ ρ x y := by
  classical
  obtain ⟨m, hm, hc⟩ := coefficient_bound r g h ℓ hf ht
  choose t he hn using fun w => weighted_shift_exists w (coefficient g h ℓ w) m hm (hc w)
  refine ⟨∑ w ∈ (Finset.Icc (-(2 * r : ℤ)) (2 * r) ×ˢ
    Finset.Icc (-(2 * r : ℤ)) (2 * r)), t w, ?_⟩
  intro ρ x y
  rw [finite_window r g h ℓ hf ρ (x, y)]
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, he]

private def projection (n : ℕ) : ObserverHilbertSpace (ℤ × ℤ) :=
  ∑ x ∈ Finset.Icc (-(n : ℤ)) n, lp.single 2 (x, x) 1

private lemma projection_trace (n : ℕ) (ρ : ObserverHilbertSpace (ℤ × ℤ)) :
    inner ℂ (projection n) ρ = ∑ x ∈ Finset.Icc (-(n : ℤ)) n, ρ (x, x) := by
  classical
  unfold projection
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]

private lemma projection_norm_sq (n : ℕ) : ‖projection n‖ ^ 2 = 2 * (n : ℝ) + 1 := by
  classical
  let s := (Finset.Icc (-(n : ℤ)) n).image fun x : ℤ => (x, x)
  have hi : Function.Injective (fun x : ℤ => (x, x)) := fun _ _ h => congrArg Prod.fst h
  have he : projection n = ∑ q ∈ s, lp.single 2 q (1 : ℂ) := by
    rw [Finset.sum_image]
    · rfl
    · exact fun _ _ _ _ h => hi h
  have hn := lp.norm_sum_single (E := fun _ : ℤ × ℤ => ℂ) (p := 2)
    (by norm_num) (fun _ => (1 : ℂ)) s
  have hc : s.card = 2 * n + 1 := by
    rw [Finset.card_image_of_injective _ hi, Int.card_Icc]
    omega
  rw [he]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_one, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one, hc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hn

private lemma entry_single_support (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ) (q : ℤ × ℤ) (x y : ℤ)
    (hq : 2 * (r : ℤ) < |q.1 - x| ∨ 2 * (r : ℤ) < |q.2 - y|) :
    lindbladEntry g h ℓ (Pi.single q 1) x y = 0 := by
  classical
  calc
    _ = lindbladEntry g h ℓ (fun _ => 0) x y := by
      apply entry_locality r g h ℓ hf
      intro u v hu hv
      have hn : (u, v) ≠ q := by
        intro he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        dsimp at h1 h2
        rcases hq with hq | hq <;> simp only [h1, h2] at hu hv <;> omega
      exact Pi.single_eq_of_ne hn 1
    _ = 0 := by simp only [lindbladEntry, mul_zero, zero_mul, tsum_zero, sub_zero, add_zero]

private lemma entry_single_formula (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (u v x y : ℤ) :
    lindbladEntry g h ℓ (Pi.single (u, v) 1) x y =
      -Complex.I * ((if y = v then h x u else 0) - (if x = u then h v y else 0)) +
      (g : ℂ) * ∑' k, (ℓ k x u * star (ℓ k y v) -
        (1 / 2 : ℂ) * (if y = v then ∑' w, star (ℓ k w x) * ℓ k w u else 0) -
        (1 / 2 : ℂ) * (if x = u then ∑' w, star (ℓ k w v) * ℓ k w y else 0)) := by
  classical
  have hg (k : ℤ) : (∑' a, ∑' b,
      ℓ k x a * (Pi.single (u, v) 1 : ℤ × ℤ → ℂ) (a, b) * star (ℓ k y b)) =
        ℓ k x u * star (ℓ k y v) := by
    rw [tsum_eq_single u]
    · rw [tsum_eq_single v]
      · simp only [Pi.single_eq_same, mul_one]
      · intro b hb
        simp [Prod.mk.injEq, hb]
    · intro a ha
      simp [Prod.mk.injEq, ha]
  unfold lindbladEntry
  simp only [hg]
  by_cases hx : x = u <;> by_cases hy : y = v <;>
    simp [Pi.single_apply, Prod.mk.injEq, hx, hy, mul_ite, ite_mul]

private lemma trace_single_zero (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ) (u v : ℤ) :
    ∑' x, lindbladEntry g h ℓ (Pi.single (u, v) 1) x x = 0 := by
  classical
  let s := Finset.Icc (min u v - 2 * r) (max u v + 2 * r)
  let t := Finset.Icc (u - r) (u + r) ∪ Finset.Icc (v - r) (v + r)
  let d (k x : ℤ) : ℂ := ℓ k x u * star (ℓ k x v) -
    (1 / 2 : ℂ) * (if x = v then ∑' w, star (ℓ k w x) * ℓ k w u else 0) -
    (1 / 2 : ℂ) * (if x = u then ∑' w, star (ℓ k w v) * ℓ k w x else 0)
  have hu : u ∈ s := by simp only [s, Finset.mem_Icc]; constructor <;> omega
  have hv : v ∈ s := by simp only [s, Finset.mem_Icc]; constructor <;> omega
  have hfinite (x : ℤ) : ∑' k, d k x = ∑ k ∈ t, d k x := by
    apply tsum_eq_sum
    intro k hk
    have huk : (r : ℤ) < |u - k| := by
      simp only [t, Finset.mem_union, Finset.mem_Icc] at hk
      rw [lt_abs]; omega
    have hvk : (r : ℤ) < |v - k| := by
      simp only [t, Finset.mem_union, Finset.mem_Icc] at hk
      rw [lt_abs]; omega
    dsimp only [d]
    split_ifs <;>
      simp only [jump_zero_right r h ℓ hf k _ u huk,
        jump_zero_right r h ℓ hf k _ v hvk, star_zero, zero_mul, mul_zero,
        tsum_zero, sub_zero]
  have htrace (k : ℤ) (hk : k ∈ t) : ∑ x ∈ s, d k x = 0 := by
    have hw : (∑' w, star (ℓ k w v) * ℓ k w u) =
        ∑ w ∈ s, star (ℓ k w v) * ℓ k w u := by
      apply tsum_eq_sum
      intro w hws
      have hwk : (r : ℤ) < |w - k| := by
        simp only [s, Finset.mem_Icc] at hws
        simp only [t, Finset.mem_union, Finset.mem_Icc] at hk
        rw [lt_abs]; omega
      rw [jump_zero_left r h ℓ hf k w v hwk, star_zero, zero_mul]
    have hg : (∑ x ∈ s, ℓ k x u * star (ℓ k x v)) =
        ∑' w, star (ℓ k w v) * ℓ k w u := by
      rw [hw]
      apply Finset.sum_congr rfl
      intro x hx
      exact mul_comm _ _
    simp only [d, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', hu, hv, ite_true]
    rw [hg]
    ring
  have he (x : ℤ) : lindbladEntry g h ℓ (Pi.single (u, v) 1) x x =
      -Complex.I * ((if x = v then h x u else 0) - (if x = u then h v x else 0)) +
      (g : ℂ) * ∑ k ∈ t, d k x := by
    rw [entry_single_formula]
    change _ + (g : ℂ) * ∑' k, d k x = _
    rw [hfinite]
  rw [tsum_eq_sum (s := s)]
  · simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hh : (∑ x ∈ s, ((if x = v then h x u else 0) -
        (if x = u then h v x else 0))) = 0 := by
      simp [Finset.sum_sub_distrib, hu, hv]
    rw [hh, mul_zero, zero_add, Finset.sum_comm]
    rw [show (∑ k ∈ t, ∑ x ∈ s, d k x) = 0 from Finset.sum_eq_zero htrace, mul_zero]
  · intro x hx
    apply entry_single_support r g h ℓ hf
    left
    simp only [s, Finset.mem_Icc] at hx
    rw [lt_abs]
    omega

private lemma boundary_estimate (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ (n : ℕ) (ρ : ObserverHilbertSpace (ℤ × ℤ)),
      ‖∑ x ∈ Finset.Icc (-(n : ℤ)) n, lindbladEntry g h ℓ ρ x x‖ ≤ k * ‖ρ‖ := by
  classical
  obtain ⟨m, hm, hc⟩ := coefficient_bound r g h ℓ hf ht
  let c : ℕ := 2 * (4 * r + 1) * (8 * r + 1)
  let b : ℝ := (4 * (r : ℝ) + 1) * m
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he_bound (q : ℤ × ℤ) (x : ℤ) :
      ‖lindbladEntry g h ℓ (Pi.single q 1) x x‖ ≤ m := by
    have he : (x, x) + (q - (x, x)) = q := by abel
    simpa only [coefficient.eq_1, he] using hc (q - (x, x)) (x, x)
  refine ⟨(c : ℝ) * b, mul_nonneg (Nat.cast_nonneg _) hb, ?_⟩
  intro n ρ
  let i := Finset.Icc (-(n : ℤ)) n
  let j := Finset.Icc (-(n : ℤ) - 2 * r) ((n : ℤ) + 2 * r)
  let qset := j ×ˢ j
  let ends := Finset.Icc ((n : ℤ) - 2 * r) ((n : ℤ) + 2 * r) ∪
    Finset.Icc (-(n : ℤ) - 2 * r) (-(n : ℤ) + 2 * r)
  let edge := ends.biUnion fun u =>
    (Finset.Icc (u - 4 * r) (u + 4 * r)).image fun v => (u, v)
  let κ (q : ℤ × ℤ) : ℂ := ∑ x ∈ i, lindbladEntry g h ℓ (Pi.single q 1) x x
  have hκ_bound (q : ℤ × ℤ) : ‖κ q‖ ≤ b := by
    let s := Finset.Icc (q.1 - 2 * r) (q.1 + 2 * r)
    have he : κ q = ∑ x ∈ i ∩ s, lindbladEntry g h ℓ (Pi.single q 1) x x := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro x hxi hx
      apply entry_single_support r g h ℓ hf
      left
      simp only [Finset.mem_inter, hxi, true_and, s, Finset.mem_Icc] at hx
      rw [lt_abs]; omega
    have hcard : (i ∩ s).card ≤ 4 * r + 1 := by
      apply (Finset.card_le_card (Finset.inter_subset_right)).trans_eq
      dsimp only [s]
      rw [Int.card_Icc]
      omega
    rw [he]
    calc
      _ ≤ ((i ∩ s).card : ℝ) * m := norm_sum_bound _ _ m fun x _ => he_bound q x
      _ ≤ ((4 * r + 1 : ℕ) : ℝ) * m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hm
      _ = b := by dsimp only [b]; push_cast; rfl
  have hκ_zero (q : ℤ × ℤ) (hq : q ∉ edge) : κ q = 0 := by
    by_cases hd : 4 * (r : ℤ) < |q.2 - q.1|
    · apply Finset.sum_eq_zero
      intro x hx
      apply entry_single_support r g h ℓ hf
      by_contra hn
      push Not at hn
      have h1 := abs_le.mp hn.1
      have h2 := abs_le.mp hn.2
      rw [lt_abs] at hd
      omega
    have hu : q.1 ∉ ends := by
      intro hu
      apply hq
      apply Finset.mem_biUnion.mpr
      refine ⟨q.1, hu, Finset.mem_image.mpr ⟨q.2, ?_, Prod.eta q⟩⟩
      simp only [Finset.mem_Icc]
      have hv := abs_le.mp (le_of_not_gt hd)
      constructor <;> omega
    have hcases : q.1 < -(n : ℤ) - 2 * r ∨ (n : ℤ) + 2 * r < q.1 ∨
        (-(n : ℤ) + 2 * r < q.1 ∧ q.1 < (n : ℤ) - 2 * r) := by
      simp only [ends, Finset.mem_union, Finset.mem_Icc] at hu
      omega
    rcases hcases with hout | hout | hin
    · apply Finset.sum_eq_zero
      intro x hx
      apply entry_single_support r g h ℓ hf
      left
      simp only [i, Finset.mem_Icc] at hx
      rw [lt_abs]; omega
    · apply Finset.sum_eq_zero
      intro x hx
      apply entry_single_support r g h ℓ hf
      left
      simp only [i, Finset.mem_Icc] at hx
      rw [lt_abs]; omega
    · have hfull : (∑' x, lindbladEntry g h ℓ (Pi.single q 1) x x) = κ q := by
        apply tsum_eq_sum
        intro x hx
        apply entry_single_support r g h ℓ hf
        left
        simp only [i, Finset.mem_Icc] at hx
        rw [lt_abs]; omega
      rw [← hfull]
      exact trace_single_zero r g h ℓ hf q.1 q.2
  have hcard_edge : edge.card ≤ c := by
    have hs (u : ℤ) : ((Finset.Icc (u - 4 * r) (u + 4 * r)).image
        (fun v => (u, v))).card ≤ 8 * r + 1 := by
      apply Finset.card_image_le.trans_eq
      rw [Int.card_Icc]; omega
    have he : ends.card ≤ 2 * (4 * r + 1) := by
      apply (Finset.card_union_le _ _).trans
      have h1 : (Finset.Icc ((n : ℤ) - 2 * r) ((n : ℤ) + 2 * r)).card = 4 * r + 1 := by
        rw [Int.card_Icc]; omega
      have h2 : (Finset.Icc (-(n : ℤ) - 2 * r) (-(n : ℤ) + 2 * r)).card = 4 * r + 1 := by
        rw [Int.card_Icc]; omega
      rw [h1, h2]; omega
    calc
      edge.card ≤ ∑ u ∈ ends,
          ((Finset.Icc (u - 4 * r) (u + 4 * r)).image fun v => (u, v)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ ends, (8 * r + 1) := Finset.sum_le_sum fun u _ => hs u
      _ = ends.card * (8 * r + 1) := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ c := Nat.mul_le_mul_right _ he
  have hdecomp (x : ℤ) (hx : x ∈ i) : lindbladEntry g h ℓ ρ x x =
      ∑ q ∈ qset, lindbladEntry g h ℓ (Pi.single q 1) x x * ρ q := by
    let σ : ℤ × ℤ → ℂ := ∑ q ∈ qset, ρ q • Pi.single q 1
    have he : lindbladEntry g h ℓ ρ x x = lindbladEntry g h ℓ σ x x := by
      apply entry_locality r g h ℓ hf
      intro u v hu hv
      have hq : (u, v) ∈ qset := by
        simp only [qset, Finset.mem_product, j, Finset.mem_Icc]
        simp only [i, Finset.mem_Icc] at hx
        have h1 := abs_le.mp hu
        have h2 := abs_le.mp hv
        constructor <;> constructor <;> omega
      simp [σ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, hq]
    rw [he, ← entryLinear_apply r g h ℓ hf σ]
    change entryLinear r g h ℓ x x (∑ q ∈ qset, ρ q • Pi.single q 1) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [map_smul, entryLinear_apply r g h ℓ hf]
    exact mul_comm _ _
  have he : (∑ x ∈ i, lindbladEntry g h ℓ ρ x x) = ∑ q ∈ qset, κ q * ρ q := by
    calc
      _ = ∑ x ∈ i, ∑ q ∈ qset, lindbladEntry g h ℓ (Pi.single q 1) x x * ρ q :=
        Finset.sum_congr rfl hdecomp
      _ = _ := by rw [Finset.sum_comm]; simp only [κ, Finset.sum_mul]
  have hs : (∑ q ∈ qset, κ q * ρ q) = ∑ q ∈ qset ∩ edge, κ q * ρ q := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    rw [hκ_zero q (by simpa only [Finset.mem_inter, hq, true_and] using hn), zero_mul]
  change ‖∑ x ∈ i, lindbladEntry g h ℓ ρ x x‖ ≤ _
  rw [he, hs]
  calc
    _ ≤ ((qset ∩ edge).card : ℝ) * (b * ‖ρ‖) := norm_sum_bound _ _ _ fun q hq => by
      rw [norm_mul]
      exact mul_le_mul (hκ_bound q) (lp.norm_apply_le_norm (by norm_num) ρ q) (norm_nonneg _) hb
    _ ≤ (c : ℝ) * (b * ‖ρ‖) := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hcard_edge)
      (by positivity)
    _ = (c : ℝ) * b * ‖ρ‖ := by ring

private lemma nonunit_from_boundary
    (t : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ))
    (hb : ∃ k : ℝ, 0 ≤ k ∧ ∀ (n : ℕ) (ρ : ObserverHilbertSpace (ℤ × ℤ)),
      ‖inner ℂ (projection n) (t ρ)‖ ≤ k * ‖ρ‖) : ¬IsUnit t := by
  rintro ⟨u, rfl⟩
  obtain ⟨k, hk, hb⟩ := hb
  let s : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ) := ↑(u⁻¹)
  obtain ⟨n, hn⟩ := exists_nat_gt ((k * ‖s‖) ^ 2)
  have hi : (u : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ))
      (s (projection n)) = projection n := by
    have he := congrArg
      (fun f : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ) =>
        f (projection n)) u.mul_inv
    exact he
  have hineq := hb n (s (projection n))
  rw [hi, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hineq
  have hbound := s.le_opNorm (projection n)
  have hsq := projection_norm_sq n
  have hp : 0 < ‖projection n‖ := by nlinarith [norm_nonneg (projection n)]
  have hsmall : ‖projection n‖ ≤ k * ‖s‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hbound hk]
  have hnonneg : 0 ≤ k * ‖s‖ := mul_nonneg hk (norm_nonneg _)
  have hcomp : ‖projection n‖ ^ 2 ≤ (k * ‖s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsmall 2
  nlinarith

/-- The finite-range translation-invariant matrix Lindbladian is bounded and has spectral zero. -/
theorem result (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (ht : IsTranslationInvariant h ℓ) :
    ∃ t : ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ),
      (∀ ρ : ObserverHilbertSpace (ℤ × ℤ), ∀ x y, t ρ (x, y) = lindbladEntry g h ℓ ρ x y) ∧
      (0 : ℂ) ∈ spectrum ℂ t := by
  obtain ⟨t, he⟩ := bounded_operator r g h ℓ hf ht
  refine ⟨t, he, (spectrum.zero_mem_iff ℂ).mpr (nonunit_from_boundary t ?_)⟩
  obtain ⟨k, hk, hb⟩ := boundary_estimate r g h ℓ hf ht
  refine ⟨k, hk, ?_⟩
  intro n ρ
  rw [projection_trace]
  simpa only [he] using hb n ρ

end D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
