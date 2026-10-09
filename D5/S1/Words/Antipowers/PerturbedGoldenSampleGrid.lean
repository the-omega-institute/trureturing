/- GID: D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid
   generality: I
   mirror-B: D5/B/S1/Words/Antipowers/PerturbedGoldenSampleGrid
   mirror-E: none(waiver:analytic-cylinder-separation)
   anchors: []
   utility: none
   digest: Signed golden approximations separate an even-denominator sample grid. -/

/-
golden_sample_grid_rank_injective:
  proof_shape: content
  escape_witness: golden_sample_grid_rank_injective (constructed cuts and parity cells)
sampling_lift_identity:
  proof_shape: bind-only
  consumer: GargFibonacciPrefixAntipower.sampling_phase
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S1/Words/ReturnWords/GoldenRankArcs.golden_mechanical_slope_irrational
    statement_id: sha256:e6ef6da05c2c1bb173242476edb5cf8e95ec8a91c1fa0d01ef4aeb8c9c46ec29
  D5/S1/Words/GoldenMechanicalWord.goldenMechanicalSlope
    statement_id: sha256:74458d9bfe383892695066fba4073ed55f41dbe35ad54a3681d82032e78bf9a8
  D5/S1/Words/ReturnWords/GoldenRankArcs.goldenCylinderEndpoint
    statement_id: sha256:3b428a53c55df449104596f69ba884a750f80e716f131fb549460e9ea2484ee8
  D5/S1/Words/ReturnWords/GoldenRankArcs.goldenCylinderEndpointSet
    statement_id: sha256:706d516bb8e1e95e04ca7ed8e8269feb3b051e4eeb297ce33d96f9d3c54a735d
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.ReturnWords.GoldenRankArcs

namespace D5.S1.Words.Antipowers.PerturbedGoldenSampleGrid


noncomputable def rank (T : Finset ℝ) (x : ℝ) : ℕ :=
  (T.filter fun c => c ≤ x).card

private theorem selected_eq_of_rank_eq {T : Finset ℝ} {x y : ℝ}
    (h : rank T x = rank T y) :
    T.filter (fun c => c ≤ x) = T.filter (fun c => c ≤ y) := by
  rcases le_total x y with hxy | hyx
  · apply Finset.eq_of_subset_of_card_le
    · exact fun c hc => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.trans hxy⟩
    · exact h.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · exact fun c hc => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.trans hyx⟩
    · exact h.le

private theorem rank_ne_of_cut_between {T : Finset ℝ} {x y c : ℝ}
    (hc : c ∈ T) (hxc : x < c) (hcy : c ≤ y) : rank T x ≠ rank T y := by
  intro he
  have hs := selected_eq_of_rank_eq he
  have hy : c ∈ T.filter (fun t => t ≤ y) := Finset.mem_filter.mpr ⟨hc, hcy⟩
  rw [← hs] at hy
  exact (not_le_of_gt hxc) (Finset.mem_filter.mp hy).2

private theorem rank_ne_of_distinct_cells {q : ℕ} {T : Finset ℝ} {c : ℤ → ℝ}
    (hc : StrictMono c)
    (hmem : ∀ r : ℤ, 0 < r → r < q → c r ∈ T)
    {a b : ℤ} (ha : 0 ≤ a ∧ a < q) (hb : 0 ≤ b ∧ b < q)
    {x y : ℝ} (hx : c a ≤ x ∧ x < c (a + 1))
    (hy : c b ≤ y ∧ y < c (b + 1)) (hab : a ≠ b) :
    rank T x ≠ rank T y := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply rank_ne_of_cut_between (hmem (a + 1) (by omega) (by omega)) hx.2
    exact (hc.monotone (by omega)).trans hy.1
  · intro he
    apply rank_ne_of_cut_between (hmem (b + 1) (by omega) (by omega)) hy.2
      ((hc.monotone (by omega)).trans hx.1)
    exact he.symm

/-- A lifted cell in a periodically repeated ordered grid reduces to its residue cell. -/
private theorem fract_mem_residue_cell {q : ℕ} (hq : 0 < q) {C : ℤ → ℝ}
    (hmono : StrictMono C) (hzero : C 0 = 0)
    (hperiod : ∀ r z : ℤ, C (r + (q : ℤ) * z) = C r + (q : ℝ) * z)
    {r : ℤ} {X : ℝ} (hX : C r < X ∧ X < C (r + 1)) :
    C (r % q) / q < Int.fract (X / q) ∧
      Int.fract (X / q) < C (r % q + 1) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ r % q := Int.emod_nonneg r (ne_of_gt hqZ)
  have hrq : r % q < q := Int.emod_lt_of_pos r hqZ
  have hdecomp : r % q + (q : ℤ) * (r / q) = r := Int.emod_add_mul_ediv r q
  have hdecomp1 : (r % q + 1) + (q : ℤ) * (r / q) = r + 1 := by omega
  have hCr : C r = C (r % q) + (q : ℝ) * ((r / (q : ℤ) : ℤ) : ℝ) := by
    calc
      C r = C (r % q + (q : ℤ) * (r / q)) := congrArg C hdecomp.symm
      _ = _ := hperiod _ _
  have hCr1 : C (r + 1) = C (r % q + 1) + (q : ℝ) * ((r / (q : ℤ) : ℤ) : ℝ) := by
    calc
      C (r + 1) = C (r % q + 1 + (q : ℤ) * (r / q)) := congrArg C hdecomp1.symm
      _ = _ := hperiod _ _
  have hCq : C q = q := by
    simpa [hzero] using hperiod 0 1
  have hClo : 0 ≤ C (r % q) := by
    rw [← hzero]
    exact hmono.monotone hr0
  have hChi : C (r % q + 1) ≤ q := by
    rw [← hCq]
    exact hmono.monotone (by omega)
  let Y : ℝ := X / q - (r / q : ℤ)
  have hdiv : X / (q : ℝ) * q = X := div_mul_cancel₀ X hqR.ne'
  have hYlo : C (r % q) / q < Y := by
    dsimp [Y]
    apply (div_lt_iff₀ hqR).mpr
    rw [hCr] at hX
    nlinarith [hX.1, hdiv]
  have hYhi : Y < C (r % q + 1) / q := by
    dsimp [Y]
    apply (lt_div_iff₀ hqR).mpr
    rw [hCr1] at hX
    nlinarith [hX.2, hdiv]
  have hY01 : 0 ≤ Y ∧ Y < 1 := by
    constructor
    · exact (div_nonneg hClo hqR.le).trans hYlo.le
    · exact hYhi.trans_le ((div_le_one hqR).mpr hChi)
  have hfract : Int.fract (X / q) = Y := by
    rw [← Int.fract_sub_intCast (X / q) (r / q), Int.fract_eq_self.mpr hY01]
  simpa [hfract] using And.intro hYlo hYhi




open D5.S1.Words

private def pick (q p : ℕ) (r : ℤ) : ℕ :=
  (-((p : ZMod q)⁻¹) * (r : ZMod q)).val

private theorem pick_lt {q p : ℕ} (hq : 0 < q) (r : ℤ) : pick q p r < q := by
  let : NeZero q := ⟨hq.ne'⟩
  exact ZMod.val_lt _

private theorem pick_zero (q p : ℕ) : pick q p 0 = 0 := by simp [pick]

private theorem pick_period (q p : ℕ) (r z : ℤ) :
    pick q p (r + (q : ℤ) * z) = pick q p r := by
  simp [pick]

private theorem pick_residue {q p : ℕ} (hq : 0 < q) (hp : p.Coprime q) (r : ℤ) :
    (-((pick q p r : ℕ) : ℤ) * (p : ℤ) : ℤ) % q = r % q := by
  let : NeZero q := ⟨hq.ne'⟩
  apply (ZMod.intCast_eq_intCast_iff' _ _ q).mp
  push_cast
  rw [pick, ZMod.natCast_zmod_val]
  have hi := ZMod.coe_mul_inv_eq_one p hp
  calc
    -(-((p : ZMod q)⁻¹) * r) * p = ((p : ZMod q) * (p : ZMod q)⁻¹) * r := by ring
    _ = r := by rw [hi, one_mul]

private noncomputable def C (q p : ℕ) (s d : ℝ) (r : ℤ) : ℝ :=
  (r : ℝ) + s * (pick q p r : ℝ) * d

private theorem C_zero (q p : ℕ) (s d : ℝ) : C q p s d 0 = 0 := by
  simp [C, pick_zero]

private theorem C_period (q p : ℕ) (s d : ℝ) (r z : ℤ) :
    C q p s d (r + (q : ℤ) * z) = C q p s d r + (q : ℝ) * z := by
  simp only [C, pick_period]
  push_cast
  ring

private theorem C_bounds {q p : ℕ} (hq : 0 < q) {s d B : ℝ}
    (hd : 0 < d) (hB : (q : ℝ) * d < B) (r : ℤ) :
    (s = 1 → (r : ℝ) ≤ C q p s d r ∧ C q p s d r < r + B) ∧
    (s = -1 → (r : ℝ) - B < C q p s d r ∧ C q p s d r ≤ r) := by
  have hk0 : (0 : ℝ) ≤ pick q p r := by positivity
  have hkq : (pick q p r : ℝ) < q := by exact_mod_cast pick_lt hq r
  have hkd : (pick q p r : ℝ) * d < B :=
    (mul_lt_mul_of_pos_right hkq hd).trans hB
  have hkd0 : 0 ≤ (pick q p r : ℝ) * d := mul_nonneg hk0 hd.le
  constructor <;> intro he <;> subst s <;> dsimp [C] <;> constructor <;> nlinarith

private theorem C_strictMono {q p : ℕ} (hq : 0 < q) {s d B : ℝ}
    (hs : s = 1 ∨ s = -1) (hd : 0 < d) (hB : (q : ℝ) * d < B) (hB1 : B < 1) :
    StrictMono (C q p s d) := by
  intro a b hab
  have habR : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
  have ha := C_bounds (p := p) (s := s) hq hd hB a
  have hb := C_bounds (p := p) (s := s) hq hd hB b
  rcases hs with hs | hs
  · have ha' := ha.1 hs
    have hb' := hb.1 hs
    linarith
  · have ha' := ha.2 hs
    have hb' := hb.2 hs
    linarith

/-- Each nonzero perturbed grid cut is an actual golden cylinder endpoint. -/
private theorem C_endpoint {q p : ℕ} (hq : 0 < q) (hp : p.Coprime q)
    {s d B : ℝ} (hs : s = 1 ∨ s = -1) (hd : 0 < d)
    (hB : (q : ℝ) * d < B) (hB1 : B < 1)
    (hres : (q : ℝ) * goldenMechanicalSlope = p - s * d)
    (r : ℤ) (hr0 : 0 < r) (hrq : r < q) :
    C q p s d r / q ∈ goldenCylinderEndpointSet (q - 1) := by
  have hmono := C_strictMono (p := p) hq hs hd hB hB1
  have hCq : C q p s d q = q := by simpa [C_zero] using C_period q p s d 0 1
  have hC0 : 0 < C q p s d r := by
    simpa [C_zero] using hmono hr0
  have hC1 : C q p s d r < q := by simpa [hCq] using hmono hrq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hk : pick q p r < q := pick_lt hq r
  have hmod := pick_residue hq hp r
  have hk0 : 0 < pick q p r := by
    by_contra he
    have he' : pick q p r = 0 := by omega
    rw [he'] at hmod
    have hrmod : r % (q : ℤ) = r := Int.emod_eq_of_lt hr0.le hrq
    simp [hrmod] at hmod
    omega
  have hcast : ((-((pick q p r : ℕ) : ℤ) * (p : ℤ) : ℤ) : ZMod q) = (r : ZMod q) :=
    (ZMod.intCast_eq_intCast_iff' _ _ q).mpr hmod
  obtain ⟨z, hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp hcast
  have hzI : r + (pick q p r : ℤ) * p = (q : ℤ) * z := by nlinarith [hz]
  have hzR : (r : ℝ) + (pick q p r : ℝ) * p = (q : ℝ) * z := by exact_mod_cast hzI
  have hfract : Int.fract (-((pick q p r : ℝ) * goldenMechanicalSlope)) =
      C q p s d r / q := by
    apply Int.fract_eq_iff.mpr
    refine ⟨(div_pos hC0 hqR).le, (div_lt_one hqR).mpr hC1, -z, ?_⟩
    have hdiv : C q p s d r / (q : ℝ) * q = C q p s d r :=
      div_mul_cancel₀ _ hqR.ne'
    dsimp [C] at hdiv
    dsimp [C]
    push_cast
    nlinarith [hres, hzR, congrArg (fun x : ℝ => x * (pick q p r : ℝ)) hres]
  refine Finset.mem_image.mpr ⟨pick q p r - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hne : Int.fract ((pick q p r : ℝ) * goldenMechanicalSlope) ≠ 0 := by
    rw [Int.fract_ne_zero_iff]
    rintro ⟨z, hz⟩
    exact (golden_mechanical_slope_irrational.natCast_mul
      (by omega : pick q p r ≠ 0)).ne_int z hz.symm
  simp only [goldenCylinderEndpoint]
  rw [show pick q p r - 1 + 1 = pick q p r by omega, ← Int.fract_neg hne, hfract]





private noncomputable def R (q p : ℕ) (s : ℝ) (j : ℕ) : ℤ :=
  if s = 1 then
    if j % 2 = 0 then (p : ℤ) + (j / 2 : ℕ) - 1
    else (p : ℤ) + (q / 2 : ℕ) + (j / 2 : ℕ)
  else
    if j % 2 = 0 then (p : ℤ) - (j / 2 : ℕ)
    else (p : ℤ) + (q / 2 : ℕ) - (j / 2 : ℕ) - 1

noncomputable def error (s d : ℝ) (j : ℕ) : ℝ := -s * d - (j : ℝ) * d ^ 2 / 2

noncomputable def Y (q p : ℕ) (s d : ℝ) (j : ℕ) : ℝ :=
  (p : ℝ) + (if j % 2 = 0 then 0 else (q : ℝ) / 2) +
    s * (j / 2 : ℕ) + (if j % 2 = 0 then 0 else s / 2) + error s d j

private theorem error_bounds {q : ℕ} {s d : ℝ} (hs : s = 1 ∨ s = -1)
    (hd : 0 < d) (hB : (q : ℝ) * d < 9 / 20)
    (hA : d + (q : ℝ) * d ^ 2 / 2 < 49 / 2000)
    {j : ℕ} (hj : j < q - 1) :
    -49 / 2000 < error s d j ∧ error s d j < 49 / 2000 ∧
      (s = 1 → error s d j < 0) ∧ (s = -1 → 0 < error s d j) := by
  have hjq : (j : ℝ) < q := by exact_mod_cast (show j < q by omega)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjd : (j : ℝ) * d < 9 / 20 := (mul_lt_mul_of_pos_right hjq hd).trans hB
  have hjd2 : (j : ℝ) * d ^ 2 ≤ (q : ℝ) * d ^ 2 :=
    mul_le_mul_of_nonneg_right hjq.le (sq_nonneg _)
  have hnonneg : 0 ≤ (j : ℝ) * d ^ 2 := mul_nonneg hj0 (sq_nonneg _)
  have hplus : d + (j : ℝ) * d ^ 2 / 2 < 49 / 2000 := by linarith
  have hminus : 0 < d - (j : ℝ) * d ^ 2 / 2 := by
    nlinarith [mul_lt_mul_of_pos_right hjd hd]
  rcases hs with hs | hs <;> subst s <;> dsimp [error] <;>
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intros; norm_num at * <;> linarith

private theorem sample_in_lifted_cell {q p : ℕ} (hq : 0 < q) (hqeven : Even q)
    {s d : ℝ} (hs : s = 1 ∨ s = -1) (hd : 0 < d)
    (hB : (q : ℝ) * d < 9 / 20)
    (hA : d + (q : ℝ) * d ^ 2 / 2 < 49 / 2000)
    {j : ℕ} (hj : j < q - 1) :
    C q p s d (R q p s j) < Y q p s d j ∧
      Y q p s d j < C q p s d (R q p s j + 1) := by
  have he := error_bounds hs hd hB hA hj
  have hleft := C_bounds (p := p) (s := s) hq hd hB (R q p s j)
  have hright := C_bounds (p := p) (s := s) hq hd hB (R q p s j + 1)
  obtain ⟨H, hH⟩ := hqeven
  have hqH : q = 2 * H := by omega
  have hdiv : q / 2 = H := by omega
  have hqHR : (q : ℝ) / 2 = H := by rw [hqH]; push_cast; ring
  rcases hs with hs | hs
  · have hl := hleft.1 hs
    have hr := hright.1 hs
    have he0 := he.2.2.1 hs
    subst s
    by_cases hj2 : j % 2 = 0 <;>
      simp only [R, hj2, Y, hdiv, hqHR, if_true, if_false, one_mul,
        Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hl hr ⊢ <;>
      constructor <;> linarith [he.1, he.2.1]
  · have hl := hleft.2 hs
    have hr := hright.2 hs
    have he0 := he.2.2.2 hs
    subst s
    by_cases hj2 : j % 2 = 0 <;>
      simp only [R, hj2, Y, hdiv, hqHR, show (-1 : ℝ) ≠ 1 by norm_num, if_true, if_false,
        neg_one_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hl hr ⊢ <;>
      constructor <;> linarith [he.1, he.2.1]

theorem sampling_lift_identity {q p : ℕ} (s d : ℝ) (j : ℕ) :
    (p : ℝ) + (j : ℝ) * q / 2 + s * j / 2 + error s d j =
      Y q p s d j + (q : ℝ) * (j / 2 : ℕ) := by
  have hj : j = 2 * (j / 2) + j % 2 := by omega
  have hjR : (j : ℝ) = 2 * (j / 2 : ℕ) + (j % 2 : ℕ) := by exact_mod_cast hj
  by_cases hj2 : j % 2 = 0
  · simp only [Y, hj2, if_true]
    rw [hj2] at hjR
    norm_num at hjR
    rw [hjR]
    ring
  · have hj1 : j % 2 = 1 := by omega
    simp only [Y, hj2, if_false]
    rw [hj1] at hjR
    norm_num at hjR
    rw [hjR]
    ring

private theorem eq_of_emod_eq_in_interval {q lo a b : ℤ}
    (ha : lo ≤ a ∧ a < lo + q) (hb : lo ≤ b ∧ b < lo + q)
    (he : a % q = b % q) : a = b := by
  have hmod : Int.ModEq q a b := he
  rcases le_total a b with hab | hba
  · have hd := Int.modEq_iff_dvd.mp hmod
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ b - a)
      (by omega : b - a < q) hd
    omega
  · have hd := Int.modEq_iff_dvd.mp hmod.symm
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ a - b)
      (by omega : a - b < q) hd
    omega

private theorem labels_injective_mod {q p : ℕ} (hq : Even q) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {i j : ℕ} (hi : i < q - 1) (hj : j < q - 1)
    (he : R q p s i % q = R q p s j % q) : i = j := by
  obtain ⟨H, hH⟩ := hq
  have hqH : q = 2 * H := by omega
  have hdiv : q / 2 = H := by omega
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases hs with hs | hs <;> subst s
  · have hbound (k : ℕ) (hk : k < q - 1) :
        (p : ℤ) - 1 ≤ R q p 1 k ∧ R q p 1 k < (p : ℤ) - 1 + q := by
      by_cases hk2 : k % 2 = 0 <;> simp only [R, hk2, if_true, if_false] <;> omega
    have heq := eq_of_emod_eq_in_interval (hbound i hi) (hbound j hj) he
    by_cases hi0 : i % 2 = 0 <;> by_cases hj0 : j % 2 = 0 <;>
      simp only [R, hi0, hj0, if_true, if_false] at heq <;> omega
  · have hbound (k : ℕ) (hk : k < q - 1) :
        (p : ℤ) - H + 1 ≤ R q p (-1) k ∧
          R q p (-1) k < (p : ℤ) - H + 1 + q := by
      by_cases hk2 : k % 2 = 0 <;>
        simp only [R, show (-1 : ℝ) ≠ 1 by norm_num, if_false, hk2, if_true] <;> omega
    have heq := eq_of_emod_eq_in_interval (hbound i hi) (hbound j hj) he
    by_cases hi0 : i % 2 = 0 <;> by_cases hj0 : j % 2 = 0 <;>
      simp only [R, show (-1 : ℝ) ≠ 1 by norm_num, if_false, hi0, hj0, if_true] at heq <;> omega

open D5.S1.Words

/-- A good signed rational approximation separates the complete parity sampling family
by actual golden-word cylinder cuts. The denominator and numerator are arbitrary. -/
theorem golden_sample_grid_rank_injective {q p : ℕ} (hqpos : 0 < q)
    (heven : Even q) (hpq : p.Coprime q) {s d : ℝ}
    (hs : s = 1 ∨ s = -1) (hd : 0 < d)
    (hB : (q : ℝ) * d < 9 / 20) (hA : d + (q : ℝ) * d ^ 2 / 2 < 49 / 2000)
    (hres : (q : ℝ) * goldenMechanicalSlope = p - s * d)
    {i j : ℕ} (hi : i < q - 1) (hj : j < q - 1) (hij : i ≠ j) :
    rank (goldenCylinderEndpointSet (q - 1)) (Int.fract (Y q p s d i / q)) ≠
      rank (goldenCylinderEndpointSet (q - 1)) (Int.fract (Y q p s d j / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hmono := C_strictMono (p := p) hqpos hs hd hB (by norm_num : (9 / 20 : ℝ) < 1)
  have hperiod := C_period q p s d
  have hzero := C_zero q p s d
  have hplace (k : ℕ) (hk : k < q - 1) :
      C q p s d (R q p s k % q) / q < Int.fract (Y q p s d k / q) ∧
      Int.fract (Y q p s d k / q) < C q p s d (R q p s k % q + 1) / q :=
    fract_mem_residue_cell hqpos hmono hzero hperiod
      (sample_in_lifted_cell hqpos heven hs hd hB hA hk)
  have hci := hplace i hi
  have hcj := hplace j hj
  have hlabel : R q p s i % q ≠ R q p s j % q := by
    intro he
    exact hij (labels_injective_mod heven hs hi hj he)
  have hr0 (k : ℕ) : 0 ≤ R q p s k % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have hrq (k : ℕ) : R q p s k % (q : ℤ) < q :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hqpos)
  have hscaledmono : StrictMono (fun r : ℤ => C q p s d r / (q : ℝ)) := by
    intro a b hab
    exact (div_lt_div_iff_of_pos_right hqR).mpr (hmono hab)
  have hmem (r : ℤ) (hr0 : 0 < r) (hrq : r < q) :
      C q p s d r / q ∈ goldenCylinderEndpointSet (q - 1) :=
    C_endpoint hqpos hpq hs hd hB (by norm_num) hres r hr0 hrq
  exact rank_ne_of_distinct_cells hscaledmono hmem
    ⟨hr0 i, hrq i⟩ ⟨hr0 j, hrq j⟩ ⟨hci.1.le, hci.2⟩ ⟨hcj.1.le, hcj.2⟩ hlabel



end D5.S1.Words.Antipowers.PerturbedGoldenSampleGrid
