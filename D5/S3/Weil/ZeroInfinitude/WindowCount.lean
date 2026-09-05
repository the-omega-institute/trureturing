/- GID: D5/S3/Weil/ZeroInfinitude/WindowCount
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroInfinitude/WindowCount
   mirror-E: none(waiver:kernel-verified-logarithmic-window-count-only)
   anchors: []
   digest: A fixed-width zeta-zero count is at least of order log T at every large height. -/

import D5.S3.Weil.ZeroInfinitude.WindowZero

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace D5.S3.Weil.ZeroInfinitude.WindowCount

open D5.S3.Weil.ZeroInfinitude
open Zeta23 WeilEF

/-! ## Multiplicity-weighted logarithmic window count -/

/-- The canonical zeta multiplicity is invariant under complex conjugation. -/
theorem zetaZeroConfig_mult_conj {rho : ℂ}
    (hrho : rho ∈ Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zetaZeroConfig.mult (conj rho) =
      Zeta23.zetaZeroConfig.mult rho := by
  rw [Zeta23.zetaZeroConfig_mult]
  unfold Zeta23.zeroMult
  rw [Zeta23.analyticOrderAt_zeta_conj]
  rw [Zeta23.zetaZeroConfig_carrier] at hrho
  intro h
  rw [h] at hrho
  have hbad := hrho.2.2
  norm_num at hbad

/-- A single radius controls the shifted inverse-square tail outside every
finite central set whose complement lies at distance at least that radius. -/
theorem exists_radius_shifted_inv_sq_tsum_compl
    {ι : Type*} {gamma : ι -> ℝ} {m : ι -> ℕ} {A0 epsilon : ℝ}
    (hN : Zeta23.Tail.LocalCount gamma m A0) (hepsilon : 0 < epsilon) :
    ∃ R : ℝ, 2 <= R ∧ ∀ (T : ℝ) (s : Finset ι),
      (∀ rho : ι, rho ∉ s -> R <= |gamma rho - T|) ->
      Summable (fun rho : {rho : ι // rho ∉ s} =>
        (m rho : ℝ) / (1 + (gamma rho - T) ^ 2)) ∧
      ∑' rho : {rho : ι // rho ∉ s},
          (m rho : ℝ) / (1 + (gamma rho - T) ^ 2) <=
        4 * A0 * (epsilon * Real.log (|T| + 3) + WeilEF.totalWeight) := by
  classical
  obtain ⟨R, hR, hfin⟩ :=
    WindowZero.exists_radius_shifted_inv_sq_finite hN hepsilon
  refine ⟨R, hR, fun T s hgap => ?_⟩
  let e : {rho : ι // rho ∉ s} ↪ ι := Function.Embedding.subtype _
  have hfinite : ∀ u : Finset {rho : ι // rho ∉ s},
      ∑ rho ∈ u, (m rho : ℝ) / (1 + (gamma rho - T) ^ 2) <=
        4 * A0 * (epsilon * Real.log (|T| + 3) + WeilEF.totalWeight) := by
    intro u
    have hu := hfin T (u.map e) (by
      intro rho hrho
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hrho
      exact hgap x x.2)
    simpa [e] using hu
  have hnonneg : 0 <= fun rho : {rho : ι // rho ∉ s} =>
      (m rho : ℝ) / (1 + (gamma rho - T) ^ 2) :=
    fun rho => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hs := summable_of_sum_le hnonneg hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- Window/tail split for the zero side. The positive semi-open window and
its conjugate image each carry exactly `N (T-R) (T+R)` total multiplicity. -/
theorem zero_side_norm_le_window_count
    {K A0 epsilon : ℝ} (hK : 0 <= K)
    (hdecay : ∀ z : ℂ, |z.im| <= 1 / 2 ->
      ‖Zeta23.paperFT (CosinePacket.packetSquare : ℝ -> ℂ) z‖ <=
        K / (1 + z.re ^ 2))
    (hLC : Zeta23.Tail.LocalCount
      (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : ℂ).im)
      (fun rho : Zeta23.zetaZeroConfig.carrier =>
        Zeta23.zetaZeroConfig.mult rho) A0)
    (hepsilon : 0 < epsilon) :
    ∃ R : ℝ, 2 <= R ∧ ∀ T : ℝ, 0 <= T ->
      ‖∑' rho : Zeta23.zetaZeroConfig.carrier,
          (Zeta23.zetaZeroConfig.mult rho : ℂ) *
            Zeta23.paperFT
              (CosinePacket.cosineModulation
                CosinePacket.packetSquare T : ℝ -> ℂ)
              (Zeta23.gammaOf rho)‖ <=
        K * (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
          4 * K * A0 *
            (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by
  classical
  obtain ⟨R, hR, htail⟩ :=
    exists_radius_shifted_inv_sq_tsum_compl hLC hepsilon
  refine ⟨R, hR, fun T hT => ?_⟩
  have hwinFin :
      (Zeta23.zetaZeroConfig.window (T - R) (T + R)).Finite :=
    Zeta23.zetaZeroConfig.finite_window (T - R) (T + R)
  let winEmbed : ↥hwinFin.toFinset ↪
      Zeta23.zetaZeroConfig.carrier :=
    ⟨fun rho => ⟨rho, (hwinFin.mem_toFinset.mp rho.2).1⟩, fun x y h => by
      apply Subtype.ext
      exact congrArg (fun z : Zeta23.zetaZeroConfig.carrier => (z : ℂ)) h⟩
  let sminus : Finset Zeta23.zetaZeroConfig.carrier :=
    hwinFin.toFinset.attach.map winEmbed
  have hsminus_spec (rho : Zeta23.zetaZeroConfig.carrier) :
      rho ∈ sminus <-> T - R < (rho : ℂ).im ∧ (rho : ℂ).im <= T + R := by
    constructor
    · intro hrho
      obtain ⟨x, hx, hxrho⟩ := Finset.mem_map.mp hrho
      have hxwin := (hwinFin.mem_toFinset.mp x.2).2
      have heq : (x : ℂ) = (rho : ℂ) :=
        congrArg (fun z : Zeta23.zetaZeroConfig.carrier => (z : ℂ)) hxrho
      rw [← heq]
      exact hxwin
    · intro hrho
      have hwin : (rho : ℂ) ∈
          Zeta23.zetaZeroConfig.window (T - R) (T + R) := ⟨rho.2, hrho⟩
      have hfin : (rho : ℂ) ∈ hwinFin.toFinset := hwinFin.mem_toFinset.mpr hwin
      rw [show sminus = hwinFin.toFinset.attach.map winEmbed from rfl,
        Finset.mem_map]
      refine ⟨⟨rho, hfin⟩, by simp, ?_⟩
      apply Subtype.ext
      rfl
  have hsminus_sum :
      ∑ rho ∈ sminus, (Zeta23.zetaZeroConfig.mult rho : ℝ) =
        (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
    rw [Zeta23.ZeroConfig.N,
      finsum_mem_eq_finite_toFinset_sum _ hwinFin, Nat.cast_sum]
    rw [show sminus = hwinFin.toFinset.attach.map winEmbed from rfl,
      Finset.sum_map]
    exact Finset.sum_attach hwinFin.toFinset
      (fun rho : ℂ => (Zeta23.zetaZeroConfig.mult rho : ℝ))
  let conjCarrier : Zeta23.zetaZeroConfig.carrier ↪
      Zeta23.zetaZeroConfig.carrier :=
    ⟨fun rho => ⟨conj rho, WindowZero.zetaZeroConfig_conj_mem rho.2⟩, by
      intro rho sigma h
      apply Subtype.ext
      have hc := congrArg Subtype.val h
      simpa using congrArg conj hc⟩
  let splus : Finset Zeta23.zetaZeroConfig.carrier :=
    sminus.map conjCarrier
  have hsplus_sum :
      ∑ rho ∈ splus, (Zeta23.zetaZeroConfig.mult rho : ℝ) =
        (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
    rw [show splus = sminus.map conjCarrier from rfl, Finset.sum_map]
    calc
      ∑ rho ∈ sminus,
          (Zeta23.zetaZeroConfig.mult (conjCarrier rho) : ℝ) =
          ∑ rho ∈ sminus,
            (Zeta23.zetaZeroConfig.mult rho : ℝ) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact_mod_cast zetaZeroConfig_mult_conj rho.2
      _ = _ := hsminus_sum
  have hgapMinus : ∀ rho : Zeta23.zetaZeroConfig.carrier,
      rho ∉ sminus -> R <= |(rho : ℂ).im - T| := by
    intro rho hrho
    apply le_of_not_gt
    intro hlt
    apply hrho
    rw [hsminus_spec]
    rcases abs_lt.mp hlt with ⟨hl, hr⟩
    constructor <;> linarith
  have hgapPlus : ∀ rho : Zeta23.zetaZeroConfig.carrier,
      rho ∉ splus -> R <= |(rho : ℂ).im + T| := by
    intro rho hrho
    apply le_of_not_gt
    intro hlt
    apply hrho
    have hc : conjCarrier rho ∈ sminus := by
      rw [hsminus_spec]
      rcases abs_lt.mp hlt with ⟨hl, hr⟩
      change T - R < -(rho : ℂ).im ∧ -(rho : ℂ).im <= T + R
      constructor <;> linarith
    rw [show splus = sminus.map conjCarrier from rfl, Finset.mem_map]
    refine ⟨conjCarrier rho, hc, ?_⟩
    apply Subtype.ext
    change conj (conj (rho : ℂ)) = (rho : ℂ)
    simp
  have hminusTail := htail T sminus hgapMinus
  have hplusTailRaw := htail (-T) splus (by
    intro rho hrho
    simpa using hgapPlus rho hrho)
  let fminus : Zeta23.zetaZeroConfig.carrier -> ℝ := fun rho =>
    (Zeta23.zetaZeroConfig.mult rho : ℝ) /
      (1 + ((rho : ℂ).im - T) ^ 2)
  let fplus : Zeta23.zetaZeroConfig.carrier -> ℝ := fun rho =>
    (Zeta23.zetaZeroConfig.mult rho : ℝ) /
      (1 + ((rho : ℂ).im + T) ^ 2)
  have hminusTail' :
      Summable (fun rho : {rho : Zeta23.zetaZeroConfig.carrier // rho ∉ sminus} =>
        fminus rho) ∧
      ∑' rho : {rho : Zeta23.zetaZeroConfig.carrier // rho ∉ sminus}, fminus rho <=
        4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by
    simpa [fminus, abs_of_nonneg hT] using hminusTail
  have hplusTail' :
      Summable (fun rho : {rho : Zeta23.zetaZeroConfig.carrier // rho ∉ splus} =>
        fplus rho) ∧
      ∑' rho : {rho : Zeta23.zetaZeroConfig.carrier // rho ∉ splus}, fplus rho <=
        4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by
    simpa [fplus, abs_of_nonneg hT] using hplusTailRaw
  have hfminus : Summable fminus := by
    apply Summable.add_compl (s := sminus) Summable.of_finite
    exact hminusTail'.1
  have hfplus : Summable fplus := by
    apply Summable.add_compl (s := splus) Summable.of_finite
    exact hplusTail'.1
  have hcentralMinus : ∑ rho ∈ sminus, fminus rho <=
      (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
    calc
      ∑ rho ∈ sminus, fminus rho <=
          ∑ rho ∈ sminus, (Zeta23.zetaZeroConfig.mult rho : ℝ) := by
        apply Finset.sum_le_sum
        intro rho hrho
        dsimp [fminus]
        have hm : (0 : ℝ) <= Zeta23.zetaZeroConfig.mult rho := Nat.cast_nonneg _
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hm (sq_nonneg ((rho : ℂ).im - T))]
      _ = _ := hsminus_sum
  have hcentralPlus : ∑ rho ∈ splus, fplus rho <=
      (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
    calc
      ∑ rho ∈ splus, fplus rho <=
          ∑ rho ∈ splus, (Zeta23.zetaZeroConfig.mult rho : ℝ) := by
        apply Finset.sum_le_sum
        intro rho hrho
        dsimp [fplus]
        have hm : (0 : ℝ) <= Zeta23.zetaZeroConfig.mult rho := Nat.cast_nonneg _
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hm (sq_nonneg ((rho : ℂ).im + T))]
      _ = _ := hsplus_sum
  have hfminusBound : ∑' rho, fminus rho <=
      (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
        4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by
    rw [← hfminus.sum_add_tsum_subtype_compl sminus]
    exact add_le_add hcentralMinus hminusTail'.2
  have hfplusBound : ∑' rho, fplus rho <=
      (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
        4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by
    rw [← hfplus.sum_add_tsum_subtype_compl splus]
    exact add_le_add hcentralPlus hplusTail'.2
  let k := CosinePacket.cosineModulation CosinePacket.packetSquare T
  obtain ⟨hzeroSummable, hEF⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (k : ℝ -> ℂ)
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) <=
        ((⊤ : ℕ∞) : WithTop ℕ∞) by exact WithTop.coe_le_coe.mpr le_top))
      k.hasCompactSupport
  let upper : Zeta23.zetaZeroConfig.carrier -> ℝ := fun rho =>
    (K / 2) * (fplus rho + fminus rho)
  have hupperSummable : Summable upper :=
    (hfplus.add hfminus).mul_left (K / 2)
  have hpoint : ∀ rho : Zeta23.zetaZeroConfig.carrier,
      ‖(Zeta23.zetaZeroConfig.mult rho : ℂ) *
        Zeta23.paperFT (k : ℝ -> ℂ) (Zeta23.gammaOf rho)‖ <= upper rho := by
    intro rho
    have h := WindowZero.zero_summand_norm_le hdecay T rho
    calc
      ‖(Zeta23.zetaZeroConfig.mult rho : ℂ) *
          Zeta23.paperFT (k : ℝ -> ℂ) (Zeta23.gammaOf rho)‖ <=
        (Zeta23.zetaZeroConfig.mult rho : ℝ) * (K / 2) *
          (1 / (1 + ((rho : ℂ).im + T) ^ 2) +
            1 / (1 + ((rho : ℂ).im - T) ^ 2)) := by
        simpa [k] using h
      _ = upper rho := by dsimp [upper, fplus, fminus]; ring
  calc
    ‖∑' rho : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zetaZeroConfig.mult rho : ℂ) *
          Zeta23.paperFT (k : ℝ -> ℂ) (Zeta23.gammaOf rho)‖ <=
        ∑' rho : Zeta23.zetaZeroConfig.carrier,
          ‖(Zeta23.zetaZeroConfig.mult rho : ℂ) *
            Zeta23.paperFT (k : ℝ -> ℂ) (Zeta23.gammaOf rho)‖ :=
      norm_tsum_le_tsum_norm hzeroSummable.norm
    _ <= ∑' rho, upper rho :=
      hzeroSummable.norm.tsum_le_tsum hpoint hupperSummable
    _ = (K / 2) * ((∑' rho, fplus rho) + ∑' rho, fminus rho) := by
      rw [show upper = fun rho => (K / 2) * (fplus rho + fminus rho) from rfl,
        (hfplus.add hfminus).tsum_mul_left, hfplus.tsum_add hfminus]
    _ <= (K / 2) *
        (((Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
            4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight)) +
          ((Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
            4 * A0 * (epsilon * Real.log (T + 3) + WeilEF.totalWeight))) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hfplusBound hfminusBound)
      positivity
    _ = K * (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) +
          4 * K * A0 *
            (epsilon * Real.log (T + 3) + WeilEF.totalWeight) := by ring

theorem window_count_lower_log :
    ∃ R T₀ c' : ℝ, 0 < R ∧ 0 < c' ∧ ∀ T : ℝ, T₀ ≤ T →
      c' * Real.log (T + 3) ≤
        (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
  classical
  obtain ⟨A0, hA0, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount
    Zeta23.zetaZeroConfig hA0 hloc
  obtain ⟨K, hK, hdecay⟩ := WindowZero.H_closed_strip_decay
  have hK1 : 1 <= K := by
    have h := hdecay 0 (by norm_num)
    rw [CosinePacket.packetTransform_zero] at h
    norm_num at h
    simpa using h
  obtain ⟨c, M, TR, hc, hRHS⟩ := WindowZero.literatureRHS_re_lower_log
  let epsilon : ℝ := c / (8 * K * A0)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨R, hR2, hsplit⟩ :=
    zero_side_norm_le_window_count hK hdecay hLC hepsilon
  let Ctail : ℝ := 4 * K * A0 * WeilEF.totalWeight
  let D : ℝ := |M| + |Ctail| + 1
  let T₀ : ℝ := max TR (Real.exp (4 * D / c))
  refine ⟨R, T₀, c / (4 * K), by linarith, by positivity, fun T hT => ?_⟩
  have hTR : TR <= T := (le_max_left _ _).trans hT
  have hTexp : Real.exp (4 * D / c) <= T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hTexp
  have hloglarge : 4 * D / c <= Real.log (T + 3) := by
    rw [← Real.log_exp (4 * D / c)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hDpos : 0 < D := by
    dsimp [D]
    linarith [abs_nonneg M, abs_nonneg Ctail]
  have hdom : M + Ctail < c / 4 * Real.log (T + 3) := by
    have hscaled := mul_le_mul_of_nonneg_left hloglarge
      (show 0 <= c / 4 by positivity)
    have hMD : M + Ctail < D := by
      dsimp [D]
      linarith [le_abs_self M, le_abs_self Ctail]
    have heq : c / 4 * (4 * D / c) = D := by field_simp
    rw [heq] at hscaled
    linarith
  let k := CosinePacket.cosineModulation CosinePacket.packetSquare T
  obtain ⟨hzeroSummable, hEF⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (k : ℝ -> ℂ)
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) <=
        ((⊤ : ℕ∞) : WithTop ℕ∞) by exact WithTop.coe_le_coe.mpr le_top))
      k.hasCompactSupport
  have hlower : c * Real.log (T + 3) - M <=
      (Zeta23.EF.literatureRHS (k : ℝ -> ℂ)).re := by
    simpa [k] using hRHS T hTR
  have hreNorm :
      (Zeta23.EF.literatureRHS (k : ℝ -> ℂ)).re <=
        ‖Zeta23.EF.literatureRHS (k : ℝ -> ℂ)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  rw [← hEF] at hlower hreNorm
  have hsplitT := hsplit T hTpos.le
  have hwindow : c / 4 * Real.log (T + 3) <=
      K * (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
    have htailIdentity :
        4 * K * A0 *
            (epsilon * Real.log (T + 3) + WeilEF.totalWeight) =
          c / 2 * Real.log (T + 3) + Ctail := by
      dsimp [epsilon, Ctail]
      field_simp
      ring
    rw [htailIdentity] at hsplitT
    linarith
  calc
    c / (4 * K) * Real.log (T + 3) =
        (c / 4 * Real.log (T + 3)) / K := by field_simp
    _ <= (K * (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ)) / K :=
      div_le_div_of_nonneg_right hwindow (by linarith)
    _ = (Zeta23.zetaZeroConfig.N (T - R) (T + R) : ℝ) := by
      field_simp

/-! The examples below witness that the quantified domains and the hypotheses
of the conditional estimates are inhabited in the pinned theory. -/

example : ℝ := 0

example : ∃ K A0 epsilon : ℝ,
    0 <= K ∧
      (∀ z : ℂ, |z.im| <= 1 / 2 ->
        ‖Zeta23.paperFT (CosinePacket.packetSquare : ℝ -> ℂ) z‖ <=
          K / (1 + z.re ^ 2)) ∧
      Zeta23.Tail.LocalCount
        (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : ℂ).im)
        (fun rho : Zeta23.zetaZeroConfig.carrier =>
          Zeta23.zetaZeroConfig.mult rho) A0 ∧
      0 < epsilon := by
  obtain ⟨K, hK, hdecay⟩ := WindowZero.H_closed_strip_decay
  obtain ⟨A0, hA0, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨K, A0, 1, hK, hdecay, ?_, by norm_num⟩
  exact Zeta23.Tail.LocalCount.ofWindowCount Zeta23.zetaZeroConfig hA0 hloc

#print axioms zetaZeroConfig_mult_conj
#print axioms exists_radius_shifted_inv_sq_tsum_compl
#print axioms zero_side_norm_le_window_count
#print axioms window_count_lower_log

end D5.S3.Weil.ZeroInfinitude.WindowCount
