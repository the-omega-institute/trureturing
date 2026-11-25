/- GID: D5/S3/Fourier/Asymptotics/CyclicParityCorrection
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicParityCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An antipodal-root certificate for the two-cosine cyclic minimum. -/

import D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

/-! The minimum sampled cosine is a root of the quadratic dual polynomial.
A mass transfer at the center, its neighbors, and the antipodal level can saturate
both cosine constraints. -/

open Finset
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicParityCorrection

set_option autoImplicit false

/-- The angular spacing of the cycle. -/
def mesh (q : ℕ) : ℝ := 2 * Real.pi / q

/-- The cosine at the centered representative of a residue. -/
def sample {q : ℕ} (i : ZMod q) : ℝ := Real.cos (centeredAngle i)

theorem centeredAngle_eq_mesh {q : ℕ} (i : ZMod q) :
    let spacing := mesh
    centeredAngle i = (i.valMinAbs : ℝ) * spacing q := by
  dsimp only
  unfold centeredAngle mesh
  ring

theorem mesh_pos {q : ℕ} [NeZero q] :
    let spacing := mesh
    0 < spacing q :=
  div_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))

theorem half_mesh_le_pi {q : ℕ} [NeZero q] :
    (↑(q / 2) : ℝ) * mesh q ≤ Real.pi := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hhalf : (2 : ℝ) * (↑(q / 2) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  unfold mesh
  rw [← mul_div_assoc, div_le_iff₀ hq]
  nlinarith only [mul_le_mul_of_nonneg_left hhalf Real.pi_pos.le]

private theorem sample_cast {q : ℕ} [NeZero q] (j : ℤ)
    (hlo : -(q : ℤ) < j * 2) (hhi : j * 2 ≤ q) :
    sample (j : ZMod q) = Real.cos ((j : ℝ) * mesh q) := by
  unfold sample
  rw [centeredAngle_eq_mesh, (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, hlo, hhi⟩]

theorem sample_antipode {q : ℕ} [NeZero q] :
    sample ((↑(q / 2) : ℤ) : ZMod q) = -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqn : 0 < q := NeZero.pos q
  rw [sample_cast _ (by omega) (by omega), Int.cast_natCast, ← Real.cos_pi_sub]
  congr 1
  have hhalf : (2 : ℝ) * (↑(q / 2) : ℝ) + (↑(q % 2) : ℝ) = q := by
    exact_mod_cast (show 2 * (q / 2) + q % 2 = q by omega)
  calc
    _ = (2 * (↑(q / 2) : ℝ)) * Real.pi / q := by unfold mesh; ring
    _ = ((q : ℝ) - (↑(q % 2) : ℝ)) * Real.pi / q := by
      rw [show 2 * (↑(q / 2) : ℝ) = (q : ℝ) - (↑(q % 2) : ℝ) by linarith only [hhalf]]
    _ = _ := by unfold mesh; field_simp [ne_of_gt hq]

theorem sample_antipode_le {q : ℕ} [NeZero q] (i : ZMod q) :
    sample ((↑(q / 2) : ℤ) : ZMod q) ≤ sample i := by
  have hqn : 0 < q := NeZero.pos q
  rw [sample_cast _ (by omega) (by omega), Int.cast_natCast, sample, centeredAngle_eq_mesh,
    ← Real.cos_abs ((i.valMinAbs : ℝ) * mesh q), abs_mul, abs_of_pos mesh_pos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (abs_nonneg _) mesh_pos.le) half_mesh_le_pi
  apply mul_le_mul_of_nonneg_right _ mesh_pos.le
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  exact_mod_cast ZMod.natAbs_valMinAbs_le i

private theorem dual_factor {c C t H Z : ℝ} (hC : C < 1) (hH : 0 < H) :
    let β := (t - H * (1 - C ^ 2)) / (1 - C)
    let ρ := -C - β / H
    (t - H * (1 - c ^ 2) - β * (1 - c)) / Z = H * (c - C) * (c - ρ) / Z := by
  dsimp
  congr 1
  field_simp [ne_of_gt hH, ne_of_gt (sub_pos.mpr hC)]
  ring

private theorem dual_le_zero_or_positive {c C ρ H Z : ℝ}
    (hc : C ≤ c) (hH : 0 < H) (hZ : 0 < Z) :
    0 < max 0 (H * (c - C) * (c - ρ) / Z) ↔ C < c ∧ ρ < c := by
  rw [lt_max_iff, or_iff_right (lt_irrefl (0 : ℝ)), div_pos_iff_of_pos_right hZ]
  constructor
  · intro h
    have hfirst : 0 < H * (c - C) := lt_of_le_of_ne
      (mul_nonneg hH.le (sub_nonneg.mpr hc)) (by
        intro he
        rw [← he, zero_mul] at h
        exact (lt_irrefl _ h))
    exact ⟨sub_pos.mp ((mul_pos_iff_of_pos_left hH).mp hfirst),
      sub_pos.mp ((mul_pos_iff_of_pos_left hfirst).mp h)⟩
  · rintro ⟨hc', hρ⟩
    exact mul_pos (mul_pos hH (sub_pos.mpr hc')) (sub_pos.mpr hρ)

theorem sum_sample_deficits {q : ℕ} [NeZero q] {v : ZMod q → ℝ}
    (hmass : ∑ i, v i = 1) :
    (∑ i, v i * (1 - sample i)) = 1 - cosineMoment 1 v ∧
    (∑ i, v i * (1 - sample i ^ 2)) = (1 - cosineMoment 2 v) / 2 := by
  constructor
  · rw [cosineMoment_eq_centered]
    simp_rw [Nat.cast_one, one_mul, mul_sub, mul_one, sample]
    rw [sum_sub_distrib, hmass]
  · rw [cosineMoment_eq_centered]
    simp only [Nat.cast_ofNat]
    simp_rw [sample, Real.cos_two_mul]
    have h (i : ZMod q) : v i * (2 * Real.cos (centeredAngle i) ^ 2 - 1) =
        v i - 2 * (v i * (1 - Real.cos (centeredAngle i) ^ 2)) := by ring
    simp_rw [h]
    rw [sum_sub_distrib, ← mul_sum, hmass]
    ring

/-- On the whole grid the clipped quadratic is positive exactly above both roots.
The energy separates into the dual bound, a squared distance, and three terms for
complementary slackness. The terms are nonnegative when the first multiplier is nonnegative. -/
theorem antipodal_dual_certificate (q : ℕ) [NeZero q] (t H Z a : ℝ)
    (hH : 0 < H) (hZ : 0 < Z)
    (hC : -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q) < 1) :
    let clip := fun x : ℝ => max 0 x
    let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
    let β := (t - H * (1 - C ^ 2)) / (1 - C)
    let ρ := -C - β / H
    let p := fun i : ZMod q =>
      (t - H * (1 - sample i ^ 2) - β * (1 - sample i)) / Z
    sample ((↑(q / 2) : ℤ) : ZMod q) = C ∧
    (∀ i, C ≤ sample i ∧ p i = H * (sample i - C) * (sample i - ρ) / Z ∧
      (0 < clip (p i) ↔ C < sample i ∧ ρ < sample i)) ∧
    ∀ v ∈ feasible q a,
      energy v =
        (2 * (t - (H / 2 + β) * (1 - a)) / Z - ∑ i, (clip (p i)) ^ 2) +
        (∑ i, (v i - clip (p i)) ^ 2) +
        2 * (∑ i, v i * (clip (p i) - p i)) +
        (2 * β / Z) * (cosineMoment 1 v - a) +
        (H / Z) * (cosineMoment 2 v - a) := by
  let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
  let β := (t - H * (1 - C ^ 2)) / (1 - C)
  let p : ZMod q → ℝ := fun i =>
    (t - H * (1 - sample i ^ 2) - β * (1 - sample i)) / Z
  refine ⟨sample_antipode, ?_, ?_⟩
  · intro i
    have hc : C ≤ sample i := by
      change -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q) ≤ sample i
      rw [← sample_antipode]
      exact sample_antipode_le i
    have hp := dual_factor (c := sample i) (t := t) (Z := Z) hC hH
    dsimp only at hp ⊢
    refine ⟨hc, hp, ?_⟩
    rw [hp]
    exact dual_le_zero_or_positive hc hH hZ
  · intro v hv
    have he (i : ZMod q) : v i * p i =
        (t * v i - H * (v i * (1 - sample i ^ 2)) - β * (v i * (1 - sample i))) / Z := by
      dsimp [p]
      ring
    have hdot : (∑ i, v i * p i) =
        (t - H * ((1 - cosineMoment 2 v) / 2) - β * (1 - cosineMoment 1 v)) / Z := by
      simp_rw [he]
      rw [← sum_div, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
        hv.2.1, (sum_sample_deficits hv.2.1).1, (sum_sample_deficits hv.2.1).2, mul_one]
    have hterm (i : ZMod q) : v i ^ 2 =
        -(max 0 (p i)) ^ 2 + (v i - max 0 (p i)) ^ 2 +
        2 * (v i * (max 0 (p i) - p i)) + 2 * (v i * p i) := by ring
    dsimp only
    unfold energy
    conv_lhs => arg 2; ext i; rw [hterm]
    simp only [sum_add_distrib, sum_neg_distrib, ← mul_sum, hdot]
    change _ = (2 * (t - (H / 2 + β) * (1 - a)) / Z - ∑ i, (max 0 (p i)) ^ 2) +
      (∑ i, (v i - max 0 (p i)) ^ 2) + 2 * (∑ i, v i * (max 0 (p i) - p i)) +
      (2 * β / Z) * (cosineMoment 1 v - a) + (H / Z) * (cosineMoment 2 v - a)
    ring

/-- Mass transferred from zero to the two closest neighbors and a closest antipode. -/
def adjusted {q : ℕ} (w : ZMod q → ℝ) (δ μ neighbor : ℝ) (i : ZMod q) : ℝ :=
  w i - (Pi.single 0 (δ + μ) : ZMod q → ℝ) i +
    (Pi.single 1 neighbor : ZMod q → ℝ) i + (Pi.single (-1) neighbor : ZMod q → ℝ) i +
    (Pi.single ((↑(q / 2) : ℤ) : ZMod q) μ : ZMod q → ℝ) i

private theorem adjusted_sum {q : ℕ} [NeZero q] (w : ZMod q → ℝ) (δ μ neighbor : ℝ)
    (f : ZMod q → ℝ) :
    (∑ i, adjusted w δ μ neighbor i * f i) =
      (∑ i, w i * f i) - (δ + μ) * f 0 + neighbor * f 1 +
        neighbor * f (-1) + μ * f ((↑(q / 2) : ℤ) : ZMod q) := by
  have hs (j : ZMod q) (x : ℝ) : (∑ i, (Pi.single j x : ZMod q → ℝ) i * f i) = x * f j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  simp only [adjusted, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, hs]

private theorem sample_front {q : ℕ} [NeZero q] (hq : 4 ≤ q) :
    sample (0 : ZMod q) = 1 ∧ sample (1 : ZMod q) = Real.cos (mesh q) ∧
      sample (-1 : ZMod q) = Real.cos (mesh q) := by
  constructor
  · simpa using sample_cast (q := q) 0 (by omega) (by omega)
  · constructor
    · simpa using sample_cast (q := q) 1 (by omega) (by omega)
    · simpa using sample_cast (q := q) (-1) (by omega) (by omega)

private theorem adjusted_nonneg {q : ℕ} [NeZero q] (hq : 4 ≤ q)
    {w : ZMod q → ℝ} {δ μ : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h0 : 0 ≤ w 0 - δ - μ) (h1 : 0 ≤ w 1 + δ / 2) (hneg : 0 ≤ w (-1) + δ / 2)
    (hμ : 0 ≤ μ) : ∀ i, 0 ≤ adjusted w δ μ (δ / 2) i := by
  have hrep (j : ℤ) (hlo : -(q : ℤ) < j * 2) (hhi : j * 2 ≤ q) :
      (j : ZMod q).valMinAbs = j :=
    (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, hlo, hhi⟩
  have hrep0 : (0 : ZMod q).valMinAbs = 0 := by simp
  have hrep1 : (1 : ZMod q).valMinAbs = 1 := by simpa using hrep 1 (by omega) (by omega)
  have hrepneg : (-1 : ZMod q).valMinAbs = -1 := by simpa using hrep (-1) (by omega) (by omega)
  have h01 : (0 : ZMod q) ≠ 1 := by
    intro he
    rw [he, hrep1] at hrep0
    omega
  have h0neg : (0 : ZMod q) ≠ -1 := by
    intro he
    rw [he, hrepneg] at hrep0
    omega
  have h1neg : (1 : ZMod q) ≠ -1 := by
    intro he
    rw [he, hrepneg] at hrep1
    omega
  have hrest (i : ZMod q) : 0 ≤ (Pi.single ((↑(q / 2) : ℤ) : ZMod q) μ : ZMod q → ℝ) i := by
    simp only [Pi.single_apply]
    split <;> simp_all
  intro i
  by_cases hi0 : i = 0
  · subst i
    simp only [adjusted, Pi.single_eq_same, Pi.single_eq_of_ne h01,
      Pi.single_eq_of_ne h0neg, add_zero]
    linarith only [h0, hrest 0]
  by_cases hi1 : i = 1
  · subst i
    simp only [adjusted, Pi.single_eq_same, Pi.single_eq_of_ne hi0,
      Pi.single_eq_of_ne h1neg, sub_zero, add_zero]
    exact add_nonneg h1 (hrest 1)
  by_cases hineg : i = -1
  · subst i
    simp only [adjusted, Pi.single_eq_same, Pi.single_eq_of_ne hi0,
      Pi.single_eq_of_ne hi1, sub_zero, add_zero]
    exact add_nonneg hneg (hrest (-1))
  · simp only [adjusted, Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi1,
      Pi.single_eq_of_ne hineg, sub_zero, add_zero]
    exact add_nonneg (hw i) (hrest i)

/-- The mass transfer matches both cosine deficits exactly. Nonnegative resulting
weights give a feasible comparison. -/
theorem adjusted_matches_moments (q : ℕ) [NeZero q] (hq : 4 ≤ q)
    (w : ZMod q → ℝ) (A : ℝ) (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    let splitMass := fun x : ℝ => x / 2
    let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
    let D₁ := 1 - cosineMoment 1 w
    let D₂ := 1 - cosineMoment 2 w
    let F := 1 - Real.cos (mesh q)
    let G := 1 - Real.cos (2 * mesh q)
    let U := 1 - C
    let V := 2 * (1 - C ^ 2)
    let δ := (A - D₂ - V * (A - D₁) / U) / (G - V * F / U)
    let μ := (A - D₁ - F * δ) / U
    0 ≤ w 0 - δ - μ → 0 ≤ w 1 + splitMass δ → 0 ≤ w (-1) + splitMass δ → 0 ≤ μ →
    let v := adjusted w δ μ (splitMass δ)
    v ∈ feasible q (1 - A) ∧ cosineMoment 1 v = 1 - A ∧ cosineMoment 2 v = 1 - A := by
  dsimp only
  let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
  let D₁ := 1 - cosineMoment 1 w
  let D₂ := 1 - cosineMoment 2 w
  let F := 1 - Real.cos (mesh q)
  let G := 1 - Real.cos (2 * mesh q)
  let U := 1 - C
  let V := 2 * (1 - C ^ 2)
  let δ := (A - D₂ - V * (A - D₁) / U) / (G - V * F / U)
  let μ := (A - D₁ - F * δ) / U
  change 0 ≤ w 0 - δ - μ → 0 ≤ w 1 + δ / 2 → 0 ≤ w (-1) + δ / 2 → 0 ≤ μ → _
  intro h0 h1 hneg hμ
  have hhalf : (1 : ℝ) < (↑(q / 2) : ℝ) := by
    exact_mod_cast (show 1 < q / 2 by omega)
  have hmesh : mesh q < (↑(q / 2) : ℝ) * mesh q := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hhalf (mesh_pos (q := q))
  have hcos : Real.cos (mesh q) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num)
      (hmesh.le.trans half_mesh_le_pi) mesh_pos
  have hC : C < Real.cos (mesh q) := by
    rw [← show sample ((↑(q / 2) : ℤ) : ZMod q) = C from sample_antipode,
      sample_cast _ (by omega) (by omega), Int.cast_natCast]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi mesh_pos.le half_mesh_le_pi hmesh
  have hU : U ≠ 0 := (sub_pos.mpr (hC.trans hcos)).ne'
  have hfactor : G - V * F / U =
      2 * (1 - Real.cos (mesh q)) * (Real.cos (mesh q) - C) := by
    unfold G V F U
    rw [Real.cos_two_mul]
    field_simp [show 1 - C ≠ 0 from hU]
    ring
  have hden : G - V * F / U ≠ 0 := by
    rw [hfactor]
    exact (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hcos)) (sub_pos.mpr hC)).ne'
  let v := adjusted w δ μ (δ / 2)
  have hvmass : ∑ i, v i = 1 := by
    simpa only [mul_one, hmass, show 1 - (δ + μ) + δ / 2 + δ / 2 + μ = 1 by ring] using
      adjusted_sum w δ μ (δ / 2) (fun _ => (1 : ℝ))
  have c0 := (sample_front hq).1
  have c1 := (sample_front hq).2.1
  have cn := (sample_front hq).2.2
  have cA : sample ((↑(q / 2) : ℤ) : ZMod q) = C := sample_antipode
  have hfirst : 1 - cosineMoment 1 v = D₁ + F * δ + U * μ := by
    have h := adjusted_sum w δ μ (δ / 2) (fun i => 1 - sample i)
    rw [(sum_sample_deficits hvmass).1, (sum_sample_deficits hmass).1, c0, c1, cn, cA] at h
    dsimp [D₁, F, U]
    linarith only [h]
  have hsecond : 1 - cosineMoment 2 v = D₂ + G * δ + V * μ := by
    have h := adjusted_sum w δ μ (δ / 2) (fun i => 1 - sample i ^ 2)
    rw [(sum_sample_deficits hvmass).2, (sum_sample_deficits hmass).2, c0, c1, cn, cA] at h
    dsimp [D₂, G, V]
    rw [Real.cos_two_mul]
    linarith only [h]
  have he₁ : μ * U = A - D₁ - F * δ := by
    dsimp only [μ]
    exact div_mul_cancel₀ _ hU
  have he₂ : δ * (G - V * F / U) = A - D₂ - V * (A - D₁) / U := by
    dsimp only [δ]
    exact div_mul_cancel₀ _ hden
  have hM₁ : cosineMoment 1 v = 1 - A := by linarith only [hfirst, he₁]
  have hM₂ : cosineMoment 2 v = 1 - A := by
    have he₃ := congrArg (fun x : ℝ => V / U * x) he₁
    have he₄ : V / U * U = V := div_mul_cancel₀ _ hU
    rw [show V / U * (μ * U) = μ * V by
      calc
        _ = μ * (V / U * U) := by ring
        _ = _ := by rw [he₄]] at he₃
    linear_combination -hsecond - he₂ - he₃
  exact ⟨⟨adjusted_nonneg hq hw h0 h1 hneg hμ, hvmass, hM₁.ge, hM₂.ge⟩, hM₁, hM₂⟩

end D5.S3.Fourier.Asymptotics.CyclicParityCorrection
