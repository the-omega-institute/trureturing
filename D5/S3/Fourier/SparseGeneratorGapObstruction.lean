/- GID: D5/S3/Fourier/SparseGeneratorGapObstruction
   generality: G
   mirror-B: D5/B/S3/Fourier/SparseGeneratorGapObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/SparseGeneratorGapObstruction.claim; result=D5/S3/Fourier/SparseGeneratorGapObstruction.result; claim=D5/S3/Fourier/SparseGeneratorGapObstruction.claim
   digest: Sparse calibrated cyclic generators obstruct a uniform ordinary-gap coefficient. -/

import D5.S3.Fourier.SparseGeneratorFamily

namespace D5.S3.Fourier.SparseGeneratorGapObstruction

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate
open FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)

noncomputable section

private lemma cayley_shift {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    {u v : ZMod N} (h : (SimpleGraph.addCayley (S : Set (ZMod N))).Reachable u v)
    (a : ZMod N) : (SimpleGraph.addCayley (S : Set (ZMod N))).Reachable (a + u) (a + v) := by
  let F : SimpleGraph.addCayley (S : Set (ZMod N)) →g
      SimpleGraph.addCayley (S : Set (ZMod N)) :=
    { toFun := fun k => a + k
      map_rel' := fun {_ _} hk => by simpa using hk }
  obtain ⟨w⟩ := h
  exact ⟨w.map F⟩

private lemma cayley_connected {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hS : generating S) : (SimpleGraph.addCayley (S : Set (ZMod N))).Connected := by
  let G := SimpleGraph.addCayley (S : Set (ZMod N))
  let H : AddSubgroup (ZMod N) :=
    { carrier := {k | G.Reachable 0 k}
      zero_mem' := SimpleGraph.Reachable.refl 0
      add_mem' := by
        intro a b ha hb
        exact ha.trans (by simpa using cayley_shift S hb a)
      neg_mem' := by
        intro a ha
        simpa using (cayley_shift S ha (-a)).symm }
  have hsub : AddSubgroup.closure (S : Set (ZMod N)) ≤ H := by
    apply (AddSubgroup.closure_le H).mpr
    intro s hs
    by_cases h0 : s = 0
    · subst s
      exact H.zero_mem
    · exact SimpleGraph.Adj.reachable
        ((SimpleGraph.addCayley_adj' _ 0 s).2 ⟨Ne.symm h0, s, hs, by simp⟩)
  have htop : H = ⊤ := by
    apply top_unique
    change AddSubgroup.closure (S : Set (ZMod N)) = ⊤ at hS
    rw [hS] at hsub
    exact hsub
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨0, fun k => ?_⟩
  have hk : k ∈ H := by rw [htop]; trivial
  exact hk

def familyGraph (N : ℕ) [NeZero N] : SimpleGraph (ZMod N) :=
  SimpleGraph.addCayley (familySet N : Set (ZMod N))

def anchors (N : ℕ) [NeZero N] : Finset (ZMod N) := insert 0 (familySet N)

def anchorDistance (N : ℕ) [NeZero N] (k : ZMod N) : ℕ := by
  classical
  exact (anchors N).inf' ⟨0, by simp [anchors]⟩ (fun a => (familyGraph N).dist k a)

def phaseAngle (N : ℕ) [NeZero N] (k : ZMod N) : ℝ :=
  Real.pi / 2 * min ((anchorDistance N k : ℝ) / radius N) 1

def phaseSpectrum (N : ℕ) [NeZero N] (k : ZMod N) : ℂ :=
  Complex.exp (Complex.I * (phaseAngle N k : ℂ))

def sourceSignal (N : ℕ) : ZMod N → ℂ :=
  if h : N = 0 then fun _ => 0 else
    letI : NeZero N := ⟨h⟩
    ZMod.dft.symm (fun _ => 1)

def targetSignal (N : ℕ) : ZMod N → ℂ :=
  if h : N = 0 then fun _ => 0 else
    letI : NeZero N := ⟨h⟩
    ZMod.dft.symm (phaseSpectrum N)

private lemma family_connected {N : ℕ} [NeZero N] (hN : familyDomain N) :
    (familyGraph N).Connected :=
  cayley_connected _ (gap_generating _ (lt_of_lt_of_le zero_lt_one (familySet_good hN).2.2.2))

private lemma distance_anchor {N : ℕ} [NeZero N] (a : ZMod N) (ha : a ∈ anchors N) :
    anchorDistance N a = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  exact (inf'_le (fun b => (familyGraph N).dist a b) ha).trans_eq SimpleGraph.dist_self

private lemma distance_attained {N : ℕ} [NeZero N] (k : ZMod N) :
    ∃ a ∈ anchors N, (familyGraph N).dist k a = anchorDistance N k := by
  classical
  obtain ⟨a, ha, he⟩ := exists_mem_eq_inf'
    (s := anchors N) ⟨0, by simp [anchors]⟩ (fun a => (familyGraph N).dist k a)
  exact ⟨a, ha, he.symm⟩

private lemma distance_edge {N : ℕ} [NeZero N] (hN : familyDomain N)
    (k s : ZMod N) (hs : s ∈ familySet N) :
    |(anchorDistance N (k + s) : ℝ) - anchorDistance N k| ≤ 1 := by
  classical
  have h0 := (familySet_good hN).1
  have hadj : (familyGraph N).Adj k (k + s) :=
    (SimpleGraph.addCayley_adj' _ _ _).2 ⟨by
      intro he
      have hz : k + s = k + 0 := by simpa only [add_zero] using he.symm
      have : s = 0 := add_left_cancel hz
      exact h0 (this ▸ hs), s, hs, Or.inl rfl⟩
  have hd : (familyGraph N).dist k (k + s) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  obtain ⟨a, ha, hea⟩ := distance_attained k
  obtain ⟨b, hb, heb⟩ := distance_attained (k + s)
  have h₁ : anchorDistance N (k + s) ≤ anchorDistance N k + 1 := by
    calc
      _ ≤ (familyGraph N).dist (k + s) a := by
        exact inf'_le (fun b => (familyGraph N).dist (k + s) b) ha
      _ ≤ (familyGraph N).dist (k + s) k + (familyGraph N).dist k a :=
        (family_connected hN).dist_triangle
      _ = _ := by rw [SimpleGraph.dist_comm, hd, hea, Nat.add_comm]
  have h₂ : anchorDistance N k ≤ anchorDistance N (k + s) + 1 := by
    calc
      _ ≤ (familyGraph N).dist k b := by
        exact inf'_le (fun b => (familyGraph N).dist k b) hb
      _ ≤ (familyGraph N).dist k (k + s) + (familyGraph N).dist (k + s) b :=
        (family_connected hN).dist_triangle
      _ = _ := by rw [hd, heb, Nat.add_comm]
  have h₁R : (anchorDistance N (k + s) : ℝ) ≤ anchorDistance N k + 1 := by exact_mod_cast h₁
  have h₂R : (anchorDistance N k : ℝ) ≤ anchorDistance N (k + s) + 1 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private def histogramEndpoint {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    {r : ℕ} (w : Sym (Option {s : ZMod N // s ∈ S}) r) : ZMod N :=
  (w.val.map (fun s => s.elim 0 Subtype.val)).sum

private lemma walk_histogram {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hS : ∀ s, s ∈ S ↔ -s ∈ S) {u v : ZMod N}
    (w : (SimpleGraph.addCayley (S : Set (ZMod N))).Walk u v) :
    ∃ c : Multiset {s : ZMod N // s ∈ S}, c.card = w.length ∧
      (c.map Subtype.val).sum = v - u := by
  induction w with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons u x v h w ih =>
    obtain ⟨c, hc, he⟩ := ih
    have hd : x - u ∈ S := by
      rcases ((SimpleGraph.addCayley_adj _ _ _).mp h).2 with hh | hh
      · simpa [sub_eq_add_neg, add_comm] using hh
      · apply (hS _).mpr
        simpa [sub_eq_add_neg, add_comm] using hh
    refine ⟨⟨x - u, hd⟩ ::ₘ c, by simp [hc], ?_⟩
    simp only [Multiset.map_cons, Multiset.sum_cons, he]
    abel

private lemma walk_padded_histogram {N : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hS : ∀ s, s ∈ S ↔ -s ∈ S) {r : ℕ} {k : ZMod N}
    (w : (SimpleGraph.addCayley (S : Set (ZMod N))).Walk 0 k) (hw : w.length ≤ r) :
    ∃ c : Sym (Option {s : ZMod N // s ∈ S}) r, histogramEndpoint S c = k := by
  obtain ⟨c, hc, he⟩ := walk_histogram S hS w
  let d : Multiset (Option {s : ZMod N // s ∈ S}) :=
    c.map some + Multiset.replicate (r - w.length) none
  have hd : d.card = r := by simp [d, hc, Nat.add_sub_of_le hw]
  refine ⟨⟨d, hd⟩, ?_⟩
  simp [histogramEndpoint, d, Multiset.map_map, Function.comp_def, he]

def phaseSupport (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  univ.filter (fun k => anchorDistance N k < radius N)

private lemma support_histogram {N : ℕ} [NeZero N] (hN : familyDomain N)
    (k : ZMod N) (hk : k ∈ phaseSupport N) :
    ∃ c : Sym (Option {s : ZMod N // s ∈ familySet N}) (radius N),
      histogramEndpoint (familySet N) c = k := by
  classical
  have hk' : anchorDistance N k < radius N := (mem_filter.mp hk).2
  obtain ⟨a, ha, he⟩ := distance_attained k
  obtain ⟨w, hw⟩ := (family_connected hN).exists_walk_length_eq_dist a k
  have hlen : w.length = anchorDistance N k := by
    rw [hw, SimpleGraph.dist_comm, he]
  have hwl : w.length + 1 ≤ radius N := by omega
  change (SimpleGraph.addCayley (familySet N : Set (ZMod N))).Walk a k at w
  have hs := (familySet_good hN).2.1
  rcases mem_insert.mp ha with h0 | haS
  · subst a
    exact walk_padded_histogram _ hs w (Nat.le_of_succ_le hwl)
  · have ha0 : a ≠ 0 := fun hh => (familySet_good hN).1 (hh ▸ haS)
    have hadj : (SimpleGraph.addCayley (familySet N : Set (ZMod N))).Adj 0 a :=
      (SimpleGraph.addCayley_adj' _ _ _).2 ⟨Ne.symm ha0, a, haS, by simp⟩
    exact walk_padded_histogram _ hs (SimpleGraph.Walk.cons hadj w) (by
      simp only [SimpleGraph.Walk.length_cons]
      exact hwl)

private lemma support_card {N : ℕ} [NeZero N] (hN : familyDomain N) :
    ((phaseSupport N).card : ℝ) ≤ Real.sqrt N := by
  classical
  let H := Sym (Option {s : ZMod N // s ∈ familySet N}) (radius N)
  have hsub : phaseSupport N ⊆ (univ : Finset H).image (histogramEndpoint (familySet N)) := by
    intro k hk
    obtain ⟨c, hc⟩ := support_histogram hN k hk
    exact mem_image.mpr ⟨c, mem_univ _, hc⟩
  have hcard : (phaseSupport N).card ≤ ((familySet N).card + radius N).choose (radius N) := by
    calc
      _ ≤ ((univ : Finset H).image (histogramEndpoint (familySet N))).card := card_le_card hsub
      _ ≤ Fintype.card H := card_image_le.trans_eq (card_univ)
      _ = _ := by simp [H, Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_coe]
  have hp : ((familySet N).card : ℝ) ≤ 34 * logOrder N := by
    rw [(familySet_good hN).2.2.1]
    push_cast
    linarith [(parameters_bounds hN).2.1]
  have hcardR : ((phaseSupport N).card : ℝ) ≤
      (((familySet N).card + radius N).choose (radius N) : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (volume_numeric_bound hN _ hp)

private lemma phase_unit {N : ℕ} [NeZero N] (k : ZMod N) : ‖phaseSpectrum N k‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

private lemma angle_bounds {N : ℕ} [NeZero N] (k : ZMod N) :
    0 ≤ phaseAngle N k ∧ phaseAngle N k ≤ Real.pi / 2 := by
  have hmin : 0 ≤ min ((anchorDistance N k : ℝ) / radius N) 1 := by positivity
  unfold phaseAngle
  exact ⟨mul_nonneg (by positivity) hmin, by
    have h := mul_le_mul_of_nonneg_left (min_le_right
      ((anchorDistance N k : ℝ) / radius N) 1) (by positivity : 0 ≤ Real.pi / 2)
    simpa using h⟩

private lemma phase_anchor {N : ℕ} [NeZero N] (a : ZMod N) (ha : a ∈ anchors N) :
    phaseSpectrum N a = 1 := by
  simp [phaseSpectrum, phaseAngle, distance_anchor a ha]

private lemma phase_plateau {N : ℕ} [NeZero N] (hN : familyDomain N)
    (k : ZMod N) (hk : k ∉ phaseSupport N) : phaseSpectrum N k = Complex.I := by
  classical
  have hd : radius N ≤ anchorDistance N k := by simpa [phaseSupport] using hk
  have hr : 0 < (radius N : ℝ) := by
    have h := (parameters_bounds hN).2.2.1
    exact_mod_cast (by omega : 0 < radius N)
  have hmin : min ((anchorDistance N k : ℝ) / radius N) 1 = 1 :=
    min_eq_right ((le_div_iff₀ hr).2 (by simpa using (show
      (radius N : ℝ) ≤ anchorDistance N k by exact_mod_cast hd)))
  rw [phaseSpectrum, phaseAngle, hmin, mul_one, mul_comm, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma phase_plateau_distance {N : ℕ} [NeZero N] (k : ZMod N) :
    ‖phaseSpectrum N k - Complex.I‖ ≤ Real.sqrt 2 := by
  have hθ := angle_bounds k
  have him : 0 ≤ (phaseSpectrum N k).im := by
    unfold phaseSpectrum
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos]⟩
  have hs : ‖phaseSpectrum N k - Complex.I‖ ^ 2 ≤ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, phase_unit, Complex.norm_I]
    simp only [one_pow, Complex.conj_I, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, mul_zero, mul_neg, mul_one, zero_sub]
    linarith
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (phaseSpectrum N k - Complex.I), Real.sqrt_nonneg 2]

private lemma angle_edge {N : ℕ} [NeZero N] (hN : familyDomain N)
    (k s : ZMod N) (hs : s ∈ familySet N) :
    |phaseAngle N k - phaseAngle N (k + s)| ≤ observationTolerance N := by
  have hr : 0 < (radius N : ℝ) := by
    have h := (parameters_bounds hN).2.2.1
    exact_mod_cast (by omega : 0 < radius N)
  have hm := abs_min_sub_min_le_max
    ((anchorDistance N k : ℝ) / radius N) 1
    ((anchorDistance N (k + s) : ℝ) / radius N) 1
  have hd : |(anchorDistance N k : ℝ) - anchorDistance N (k + s)| ≤ 1 := by
    rw [abs_sub_comm]
    exact distance_edge hN k s hs
  have hdiv : |(anchorDistance N k : ℝ) / radius N -
      (anchorDistance N (k + s) : ℝ) / radius N| ≤ 1 / radius N := by
    rw [← sub_div, abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right hd hr.le
  simp only [sub_self, abs_zero] at hm
  rw [max_eq_left (abs_nonneg _)] at hm
  unfold phaseAngle observationTolerance
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  calc
    _ ≤ (Real.pi / 2) * (1 / radius N) :=
      mul_le_mul_of_nonneg_left (hm.trans hdiv) (by positivity)
    _ = _ := by ring

private lemma phase_chord (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have he : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (b : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

private lemma phase_row {N : ℕ} [NeZero N] (hN : familyDomain N)
    (k s : ZMod N) (hs : s ∈ familySet N) :
    ‖bispectrum (phaseSpectrum N) k s - 1‖ ≤ observationTolerance N := by
  have hs1 : phaseSpectrum N s = 1 := phase_anchor s (mem_insert_of_mem hs)
  have he : bispectrum (phaseSpectrum N) k s - 1 =
      (phaseSpectrum N k - phaseSpectrum N (k + s)) * conj (phaseSpectrum N (k + s)) := by
    unfold bispectrum
    rw [hs1, mul_one, sub_mul, unit_mul_conj _ (phase_unit _)]
  rw [he, norm_mul, Complex.norm_conj, phase_unit, mul_one]
  exact (phase_chord _ _).trans (angle_edge hN k s hs)

private lemma source_dft {N : ℕ} [NeZero N] :
    ZMod.dft (sourceSignal N) = fun _ => (1 : ℂ) := by
  rw [sourceSignal, dif_neg (NeZero.ne N)]
  exact ZMod.dft.apply_symm_apply _

private lemma target_dft {N : ℕ} [NeZero N] :
    ZMod.dft (targetSignal N) = phaseSpectrum N := by
  rw [targetSignal, dif_neg (NeZero.ne N)]
  exact ZMod.dft.apply_symm_apply _

private lemma source_energy {N : ℕ} [NeZero N] :
    GeneratorRowStability.sourceEnergy (sourceSignal N) = ((N : ℝ) - 1) / N := by
  classical
  unfold GeneratorRowStability.sourceEnergy
  rw [source_dft]
  simp only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one,
    card_erase_of_mem (mem_univ (0 : ZMod N)), card_univ, ZMod.card]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))]
  push_cast
  ring

private def correlation {N : ℕ} [NeZero N] (t : ZMod N) : ℂ :=
  ∑ k : ZMod N, phaseSpectrum N k * conj (ZMod.stdAddChar (-(k * t)))

private lemma correlation_bound {N : ℕ} [NeZero N] (hN : familyDomain N) (t : ZMod N) :
    |(correlation t).re| ≤ Real.sqrt N * Real.sqrt 2 := by
  classical
  have hplateau : (∑ k : ZMod N,
      Complex.I * conj (ZMod.stdAddChar (-(k * t)))).re = 0 := by
    rw [← mul_sum, ← map_sum]
    have he : (∑ k : ZMod N, ZMod.stdAddChar (-(k * t))) =
        if t = 0 then (N : ℂ) else 0 := by
      simpa [neg_mul, mul_comm] using char_sum (-t)
    rw [he]
    split_ifs <;> simp [Complex.mul_re]
  have hsum : correlation t =
      (∑ k ∈ phaseSupport N, (phaseSpectrum N k - Complex.I) *
        conj (ZMod.stdAddChar (-(k * t)))) +
      ∑ k : ZMod N, Complex.I * conj (ZMod.stdAddChar (-(k * t))) := by
    have hs : ∑ k ∈ phaseSupport N, (phaseSpectrum N k - Complex.I) *
        conj (ZMod.stdAddChar (-(k * t))) =
      ∑ k : ZMod N, (phaseSpectrum N k - Complex.I) *
        conj (ZMod.stdAddChar (-(k * t))) := by
      apply sum_subset (subset_univ _)
      intro k _ hk
      rw [phase_plateau hN k hk, sub_self, zero_mul]
    rw [hs, ← sum_add_distrib]
    unfold correlation
    apply sum_congr rfl
    intro k _
    ring
  rw [hsum, Complex.add_re, hplateau, add_zero]
  calc
    _ ≤ ‖∑ k ∈ phaseSupport N, (phaseSpectrum N k - Complex.I) *
        conj (ZMod.stdAddChar (-(k * t)))‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ phaseSupport N, ‖(phaseSpectrum N k - Complex.I) *
        conj (ZMod.stdAddChar (-(k * t)))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ phaseSupport N, Real.sqrt 2 := by
      apply sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_conj, (ZMod.stdAddChar (N := N)).norm_apply, mul_one]
      exact phase_plateau_distance k
    _ = ((phaseSupport N).card : ℝ) * Real.sqrt 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (support_card hN) (Real.sqrt_nonneg _)

private lemma translation_error {N : ℕ} [NeZero N] (t : ZMod N) :
    countingError (sourceSignal N) (targetSignal N) t =
      2 - 2 * (correlation t).re / N := by
  classical
  rw [countingError, dif_neg (NeZero.ne N)]
  rw [cyclic_parseval, Fintype.expect_eq_sum_div_card, ZMod.card]
  have hcoef (k : ZMod N) :
      ZMod.dft (fun x => targetSignal N x - sourceSignal N (x - t)) k =
        phaseSpectrum N k - ZMod.stdAddChar (-(k * t)) := by
    have h := congr_fun ((ZMod.dft (N := N) (E := ℂ)).map_sub
      (targetSignal N) (fun x => sourceSignal N (x - t))) k
    change ZMod.dft (fun x => targetSignal N x - sourceSignal N (x - t)) k =
      ZMod.dft (targetSignal N) k - ZMod.dft (fun x => sourceSignal N (x - t)) k at h
    rw [dft_translation, source_dft, target_dft] at h
    simpa using h
  simp_rw [hcoef, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
    Complex.normSq_eq_norm_sq, phase_unit, (ZMod.stdAddChar (N := N)).norm_apply, one_pow]
  rw [sum_sub_distrib, ← mul_sum, ← Complex.re_sum]
  simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card]
  unfold correlation
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]
  ring

private lemma translation_bounds {N : ℕ} [NeZero N] (hN : familyDomain N)
    (t : ZMod N) :
    countingError (sourceSignal N) (targetSignal N) t ∈
      Set.Icc (2 - 2 * Real.sqrt 2 / Real.sqrt N) (2 + 2 * Real.sqrt 2 / Real.sqrt N) := by
  have h := abs_le.mp (correlation_bound hN t)
  have hn : 0 < (N : ℝ) := by exact_mod_cast large_order_pos hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hn
  have he : 2 * Real.sqrt 2 / Real.sqrt N * (N : ℝ) =
      2 * (Real.sqrt N * Real.sqrt 2) := by
    field_simp [hs.ne']
    nlinarith [Real.sq_sqrt hn.le]
  rw [translation_error]
  constructor
  · have hd := (div_le_iff₀ hn).2 (show 2 * (correlation t).re ≤
        (2 * Real.sqrt 2 / Real.sqrt N) * N by rw [he]; linarith [h.2])
    linarith
  · have he' : (-2 * Real.sqrt 2 / Real.sqrt N) * N =
        -(2 * (Real.sqrt N * Real.sqrt 2)) := by
      calc
        _ = -(2 * Real.sqrt 2 / Real.sqrt N * N) := by ring
        _ = _ := by rw [he]
    have hd := (le_div_iff₀ hn).2 (show (-(2 * Real.sqrt 2 / Real.sqrt N)) * N ≤
        2 * (correlation t).re by
      have he'' : (-(2 * Real.sqrt 2 / Real.sqrt N)) * N =
        -(2 * (Real.sqrt N * Real.sqrt 2)) := by simpa [neg_div, neg_mul] using he'
      rw [he'']; linarith [h.1])
    linarith

private lemma order_numeric {N : ℕ} (hN : familyDomain N) : (128 : ℝ) ≤ N := by
  have hL := large_log hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast large_order_pos hN
  have h := Real.add_one_le_exp (logOrder N)
  rw [logOrder, Real.exp_log hn] at h
  change 128 ≤ Real.log (N : ℝ) at hL
  linarith

private lemma lower_endpoint {N : ℕ} (hN : familyDomain N) :
    1 ≤ 2 - 2 * Real.sqrt 2 / Real.sqrt N := by
  have hN128 := order_numeric hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hs := Real.sq_sqrt hN0
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have h20 := Real.sqrt_nonneg 2
  have hle : 2 * Real.sqrt 2 ≤ Real.sqrt N := by nlinarith
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have he : 2 * Real.sqrt 2 / Real.sqrt N ≤ 1 := (div_le_one hspos).2 hle
  linarith

private lemma translation_lower {N : ℕ} [NeZero N] (hN : familyDomain N) (t : ZMod N) :
    1 ≤ countingError (sourceSignal N) (targetSignal N) t :=
  (lower_endpoint hN).trans (translation_bounds hN t).1

private lemma coefficient_necessary {N : ℕ} [NeZero N] (hN : familyDomain N) (K : ℝ)
    (hbound : ∃ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t ≤
      K * observationTolerance N ^ 2 * GeneratorRowStability.sourceEnergy (sourceSignal N) /
        ordinaryGap (familySet N)) :
    logOrder N ^ 2 / (256 * Real.pi ^ 2) ≤ K := by
  obtain ⟨t, ht⟩ := hbound
  have hg : 1 ≤ ordinaryGap (familySet N) := (familySet_good hN).2.2.2
  have hgpos : 0 < ordinaryGap (familySet N) := by linarith
  have hN128 := order_numeric hN
  have hn : 0 < (N : ℝ) := by linarith
  have henergy0 : 0 < GeneratorRowStability.sourceEnergy (sourceSignal N) := by
    rw [source_energy]
    exact div_pos (by linarith) hn
  have henergy : GeneratorRowStability.sourceEnergy (sourceSignal N) ≤ 1 := by
    rw [source_energy]
    exact (div_le_one hn).2 (by linarith)
  have heps : 0 < observationTolerance N ^ 2 := sq_pos_of_pos (tolerance_bounds hN).1
  have hlow := translation_lower hN t
  have hprod : 1 ≤ K * observationTolerance N ^ 2 *
      GeneratorRowStability.sourceEnergy (sourceSignal N) / ordinaryGap (familySet N) :=
    hlow.trans ht
  have hmul := (le_div_iff₀ hgpos).mp hprod
  have hKpos : 0 < K := by
    by_contra hk
    have hnon : K * observationTolerance N ^ 2 *
        GeneratorRowStability.sourceEnergy (sourceSignal N) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hk) heps.le) henergy0.le
    nlinarith
  have hones : 1 ≤ K * observationTolerance N ^ 2 := by
    have hle := mul_le_mul_of_nonneg_left henergy (mul_pos hKpos heps).le
    nlinarith
  have hr : 0 < (radius N : ℝ) := by
    have h := (parameters_bounds hN).2.2.1
    exact_mod_cast (by omega : 0 < radius N)
  have heps_eq : observationTolerance N ^ 2 = Real.pi ^ 2 / (4 * (radius N : ℝ) ^ 2) := by
    unfold observationTolerance
    ring
  rw [heps_eq] at hones
  have hfour : 4 * (radius N : ℝ) ^ 2 ≤ K * Real.pi ^ 2 := by
    have h := (le_div_iff₀ (show 0 < 4 * (radius N : ℝ) ^ 2 by positivity)).mp
      (show 1 ≤ K * Real.pi ^ 2 / (4 * (radius N : ℝ) ^ 2) by simpa [mul_div_assoc] using hones)
    simpa using h
  have hL := large_log hN
  have hrL := (parameters_bounds hN).2.2.2.2
  apply (div_le_iff₀ (by positivity : 0 < 256 * Real.pi ^ 2)).2
  have hsq := sq_le_sq₀ (show 0 ≤ logOrder N / 32 by linarith) hr.le |>.mpr hrL
  nlinarith

theorem parameter_family (N : ℕ) [NeZero N] (hN : familyDomain N) :
    0 ∉ familySet N ∧
    (∀ s, s ∈ familySet N ↔ -s ∈ familySet N) ∧
    (familySet N).card = 2 * sampleSize N ∧
    (familySet N).Nonempty ∧ generating (familySet N) ∧
    1 ≤ ordinaryGap (familySet N) ∧
    (∀ k : ZMod N, ZMod.dft (sourceSignal N) k = 1) ∧
    ZMod.dft (targetSignal N) = phaseSpectrum N ∧
    (∀ k : ZMod N, ‖ZMod.dft (sourceSignal N) k‖ = 1 ∧
      ‖ZMod.dft (targetSignal N) k‖ = 1) ∧
    phaseSpectrum N 0 = 1 ∧ (∀ s ∈ familySet N, phaseSpectrum N s = 1) ∧
    ZMod.dft (sourceSignal N) 0 = 1 ∧ ZMod.dft (targetSignal N) 0 = 1 ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal N)) k 0 =
      bispectrum (ZMod.dft (sourceSignal N)) k 0) ∧
    (∀ s ∈ familySet N, ∀ k,
      ‖bispectrum (ZMod.dft (targetSignal N)) k s -
        bispectrum (ZMod.dft (sourceSignal N)) k s‖ ≤ observationTolerance N) ∧
    0 < observationTolerance N ∧ observationTolerance N ≤ Real.pi / 16 ∧
    Real.pi / 16 < 1 / 4 ∧
    GeneratorRowStability.sourceEnergy (sourceSignal N) = ((N : ℝ) - 1) / N ∧
    (∀ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t ∈
      Set.Icc (2 - 2 * Real.sqrt 2 / Real.sqrt N) (2 + 2 * Real.sqrt 2 / Real.sqrt N)) ∧
    ∀ K : ℝ, (∃ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t ≤
      K * observationTolerance N ^ 2 * GeneratorRowStability.sourceEnergy (sourceSignal N) /
        ordinaryGap (familySet N)) → logOrder N ^ 2 / (256 * Real.pi ^ 2) ≤ K := by
  classical
  obtain ⟨h0, hsym, hcard, hgap⟩ := familySet_good hN
  have hn : (familySet N).Nonempty := by
    apply card_pos.mp
    rw [hcard]
    have hq := (parameters_bounds hN).1
    have hL := large_log hN
    have hq0 : 0 < sampleSize N := by
      by_contra he
      have hz : sampleSize N = 0 := by omega
      rw [hz] at hq
      norm_num at hq
      linarith
    omega
  have hu0 : phaseSpectrum N 0 = 1 := phase_anchor 0 (by simp [anchors])
  have htol := tolerance_bounds hN
  refine ⟨h0, hsym, hcard, hn, gap_generating _ (by linarith), hgap,
    (fun k => congr_fun source_dft k), target_dft, ?_, hu0, ?_, ?_, ?_, ?_, ?_,
    htol.1, htol.2.1, htol.2.2, source_energy, translation_bounds hN,
    coefficient_necessary hN⟩
  · intro k
    rw [source_dft, target_dft]
    exact ⟨norm_one, phase_unit k⟩
  · intro s hs
    exact phase_anchor s (mem_insert_of_mem hs)
  · rw [source_dft]
  · rw [target_dft, hu0]
  · intro k
    rw [source_dft, target_dft]
    simp only [bispectrum, add_zero, hu0, mul_one, map_one]
    exact unit_mul_conj _ (phase_unit k)
  · intro s hs k
    rw [source_dft, target_dft]
    simpa [bispectrum] using phase_row hN k s hs

def claim : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)),
    S.Nonempty → 0 ∉ S → generating S → 0 < ordinaryGap S →
    ∀ (f g : ZMod N → ℂ) (m ε : ℝ),
      0 < m → 0 ≤ ε → ε ≤ m ^ 3 / 4 → ZMod.dft f 0 = ZMod.dft g 0 →
      (∀ k, m ≤ ‖ZMod.dft f k‖) →
      (∀ k, ‖bispectrum (ZMod.dft g) k 0 - bispectrum (ZMod.dft f) k 0‖ ≤ ε) →
      (∀ s ∈ S, ∀ k,
        ‖bispectrum (ZMod.dft g) k s - bispectrum (ZMod.dft f) k s‖ ≤ ε) →
      ∃ t, countingError f g t ≤
        C * ε ^ 2 * GeneratorRowStability.sourceEnergy f / (m ^ 6 * ordinaryGap S)

private lemma phase_real_nonnegative {N : ℕ} [NeZero N] (k : ZMod N) :
    0 ≤ (phaseSpectrum N k).re := by
  have h := angle_bounds k
  unfold phaseSpectrum
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h.2⟩

private lemma sum_correlation {N : ℕ} [NeZero N] :
    ∑ t : ZMod N, correlation t = (N : ℂ) := by
  classical
  unfold correlation
  rw [sum_comm]
  have he (k : ZMod N) :
      ∑ t : ZMod N, phaseSpectrum N k * conj (ZMod.stdAddChar (-(k * t))) =
        if k = 0 then (N : ℂ) else 0 := by
    rw [← mul_sum, ← map_sum]
    have hc : ∑ t : ZMod N, ZMod.stdAddChar (-(k * t)) =
        if k = 0 then (N : ℂ) else 0 := by simpa [neg_mul] using char_sum (-k)
    rw [hc]
    by_cases hk : k = 0
    · rw [if_pos hk, hk, phase_anchor 0 (by simp [anchors])]
      simp
    · rw [if_neg hk]
      simp
  simp_rw [he]
  simp

private lemma sum_errors {N : ℕ} [NeZero N] :
    ∑ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t = 2 * (N : ℝ) - 2 := by
  classical
  simp_rw [translation_error]
  rw [sum_sub_distrib, ← sum_div, ← mul_sum, ← Complex.re_sum, sum_correlation]
  simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card, Complex.natCast_re]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hn]

private lemma error_zero_lt_average {N : ℕ} [NeZero N] (hN : familyDomain N) :
    countingError (sourceSignal N) (targetSignal N) 0 < 2 - 2 / (N : ℝ) := by
  classical
  have hn : 0 < (N : ℝ) := by exact_mod_cast large_order_pos hN
  have he : (correlation (0 : ZMod N)).re = ∑ k : ZMod N, (phaseSpectrum N k).re := by
    simp [correlation, Complex.re_sum]
  have hA : ((anchors N).card : ℝ) ≤ (correlation (0 : ZMod N)).re := by
    rw [he]
    calc
      _ = ∑ a ∈ anchors N, (phaseSpectrum N a).re := by
        have hh : ∑ a ∈ anchors N, (phaseSpectrum N a).re =
            ∑ _a ∈ anchors N, (1 : ℝ) := sum_congr rfl (fun a ha => by rw [phase_anchor a ha]; rfl)
        rw [hh]
        simp
      _ ≤ ∑ k : ZMod N, (phaseSpectrum N k).re :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun k _ _ => phase_real_nonnegative k)
  have hcard : 1 < (anchors N).card := by
    rw [anchors, card_insert_of_notMem (familySet_good hN).1, (familySet_good hN).2.2.1]
    have hq := (parameters_bounds hN).1
    have hL := large_log hN
    have hqpos : 0 < sampleSize N := by
      by_contra hh
      have hz : sampleSize N = 0 := by omega
      rw [hz] at hq
      norm_num at hq
      linarith
    omega
  have hc : (1 : ℝ) < (correlation (0 : ZMod N)).re :=
    lt_of_lt_of_le (by exact_mod_cast hcard) hA
  rw [translation_error]
  have hd := div_lt_div_of_pos_right (show (2 : ℝ) < 2 * (correlation (0 : ZMod N)).re by
    linarith) hn
  linarith

private lemma translation_dependence {N : ℕ} [NeZero N] (hN : familyDomain N) :
    ∃ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t ≠
      countingError (sourceSignal N) (targetSignal N) 0 := by
  classical
  by_contra hh
  have he (t : ZMod N) : countingError (sourceSignal N) (targetSignal N) t =
      countingError (sourceSignal N) (targetSignal N) 0 := by
    by_contra ht
    exact hh ⟨t, ht⟩
  have hsum := sum_errors (N := N)
  simp_rw [he] at hsum
  simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card] at hsum
  have hn : 0 < (N : ℝ) := by exact_mod_cast large_order_pos hN
  have hlt := mul_lt_mul_of_pos_left (error_zero_lt_average hN) hn
  have heavg : (N : ℝ) * (2 - 2 / (N : ℝ)) = 2 * (N : ℝ) - 2 := by
    field_simp
  rw [heavg, hsum] at hlt
  exact lt_irrefl _ hlt

theorem result : ¬ claim := by
  rintro ⟨C, hC, hclaim⟩
  let B : ℝ := 128 + 16 * Real.pi * (C + 1)
  let N := Nat.ceil (Real.exp B)
  have hB : 128 ≤ B := by
    dsimp [B]
    have : 0 ≤ 16 * Real.pi * (C + 1) := by positivity
    linarith
  have hN : familyDomain N := Nat.ceil_mono (Real.exp_le_exp.mpr hB)
  haveI : NeZero N := ⟨Nat.ne_of_gt (large_order_pos hN)⟩
  have hlog : B ≤ logOrder N := by
    apply (Real.le_log_iff_exp_le (show 0 < (N : ℝ) by exact_mod_cast large_order_pos hN)).2
    exact Nat.le_ceil _
  obtain ⟨h0, _hsym, _hcard, hne, hgen, hgap, hF, _hG, _hunit, _hcal0, _hcalS,
      hDCf, hDCg, hzero, hrows, heps0, heps16, hpi, _henergy, _herr, hK⟩ :=
    parameter_family N hN
  have hbound := hclaim N (familySet N) hne h0 hgen (by linarith)
    (sourceSignal N) (targetSignal N) 1 (observationTolerance N)
    zero_lt_one heps0.le (by norm_num; linarith)
    (hDCf.trans hDCg.symm) (fun k => by rw [hF k]; simp)
    (fun k => by rw [hzero k]; simp; exact heps0.le) hrows
  have hKbound : logOrder N ^ 2 / (256 * Real.pi ^ 2) ≤ C :=
    hK C (by simpa only [one_pow, one_mul] using hbound)
  have hden : 0 < 256 * Real.pi ^ 2 := by positivity
  have hKM := (div_le_iff₀ hden).mp hKbound
  have hL := large_log hN
  have hlen : 16 * Real.pi * (C + 1) ≤ logOrder N := by dsimp [B] at hlog; linarith
  have hsq : (16 * Real.pi * (C + 1)) ^ 2 ≤ logOrder N ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).2 hlen
  have hcs : C < (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have hp := mul_pos (sub_pos.mpr hcs) hden
  nlinarith

end
end D5.S3.Fourier.SparseGeneratorGapObstruction
