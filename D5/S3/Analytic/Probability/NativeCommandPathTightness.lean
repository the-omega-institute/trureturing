/- GID: D5/S3/Analytic/Probability/NativeCommandPathTightness
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NativeCommandPathTightness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-time oscillation estimates for the actual stopped native command triples. -/

import D5.S3.Analytic.Probability.NativeCommandLifetime

/-! Oscillation bounds retain the original stopped chords and chronological area. -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Probability.NativeCommandPathTightness
open NativeCommandLifetime

theorem raw_coefficient_bounds (B : Model) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Triple, q 0 ∈ Icc B.l B.u →
      ∀ i : Fin 2, |drift B q i| ≤ M ∧ |B.A q i i| ≤ M := by
  let p := 2 * Real.pi
  have hp : 0 < p := by dsimp [p]; positivity
  let K : Set Triple := Icc ![B.l,0,0] ![B.u,p,p]
  have hK : IsCompact K := isCompact_Icc
  have hsub : K ⊆ B.neighbourhood := by
    intro q hq
    exact B.contains_cylinder q ⟨hq.1 0,hq.2 0⟩
  let f : Triple → ℝ := fun q => ∑ i : Fin 2, (|drift B q i| + |B.A q i i|)
  have hf : ContinuousOn f K := by
    apply continuousOn_finsetSum
    intro i _
    exact ((drift_continuous B i).abs.add (B.smooth_A i i).continuousOn.abs).mono hsub
  obtain ⟨M,hM⟩ := (hK.image_of_continuousOn hf).bddAbove
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro q hq i
  let q' : Triple := ![q 0,p * Int.fract (q 1/p),p * Int.fract (q 2/p)]
  have hq' : q' ∈ K := by
    constructor
    · intro j
      fin_cases j
      · exact hq.1
      · exact mul_nonneg hp.le (Int.fract_nonneg _)
      · exact mul_nonneg hp.le (Int.fract_nonneg _)
    · intro j
      fin_cases j
      · exact hq.2
      · exact (mul_lt_of_lt_one_right hp (Int.fract_lt_one _)).le
      · exact (mul_lt_of_lt_one_right hp (Int.fract_lt_one _)).le
  have hshift : q' = q + ![0,(-⌊q 1/p⌋:ℤ)*(2*Real.pi),
      (-⌊q 2/p⌋:ℤ)*(2*Real.pi)] := by
    ext j
    fin_cases j
    · simp [q']
    · change p * Int.fract (q 1/p) = q 1 + (-⌊q 1/p⌋:ℤ)*p
      have hh := Int.fract_div_mul_self_add_zsmul_eq p (q 1) (ne_of_gt hp)
      simp only [zsmul_eq_mul,Int.cast_neg] at *
      nlinarith
    · change p * Int.fract (q 2/p) = q 2 + (-⌊q 2/p⌋:ℤ)*p
      have hh := Int.fract_div_mul_self_add_zsmul_eq p (q 2) (ne_of_gt hp)
      simp only [zsmul_eq_mul,Int.cast_neg] at *
      nlinarith
  have hsum : |drift B q' i| + |B.A q' i i| ≤ f q' :=
    Finset.single_le_sum (f := fun j : Fin 2 => |drift B q' j| + |B.A q' j j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hb := hsum.trans ((hM (mem_image_of_mem f hq')).trans (le_max_right 0 M))
  have hd : drift B q' i = drift B q i := by rw [hshift,drift_periodic B i q hq]
  have hA : B.A q' = B.A q := by rw [hshift,B.periodic_A]
  rw [hd,hA] at hb
  exact ⟨by linarith [abs_nonneg (B.A q i i)], by linarith [abs_nonneg (drift B q i)]⟩

private theorem sigma_entry_sq_le (B : Model) (q : Triple)
    (hq : q 0 ∈ Icc B.l B.u) (i j : Fin 2) :
    (sigma B q i j)^2 ≤ B.A q i i := by
  obtain ⟨_,hs,hp⟩ := D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot_spec
    (B.A q) (B.positive_A q (B.contains_cylinder q hq))
  have hsym (k : Fin 2) : sigma B q k i = sigma B q i k := by
    simpa [sigma,Matrix.conjTranspose_apply] using
      congrArg (fun S : Covariance => S i k) hs
  have he := congrArg (fun S : Covariance => S i i) hp
  change (sigma B q * sigma B q) i i = _ at he
  simp only [Matrix.mul_apply,hsym,←pow_two] at he
  rw [←he]
  exact Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)

theorem increment_sqrt_bound (B : Model) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ z : Triple, Alive B z → ∀ e : SignPair, ∀ i : Fin 2,
        |increment B δ z e i| ≤ L * Real.sqrt δ := by
  obtain ⟨M,hM,hraw⟩ := raw_coefficient_bounds B
  refine ⟨M + 4*(M+1),by positivity,?_⟩
  intro δ hδ hδ1 z hz e i
  let q := sourceMap B z
  have hq : q 0 ∈ Icc B.l B.u := ⟨hz.1.le,hz.2.le⟩
  have hroot (j : Fin 2) : |sigma B q i j| ≤ M+1 := by
    have hh := (sigma_entry_sq_le B q hq i j).trans (le_abs_self _)
    have hb := (hraw q hq i).2
    nlinarith [sq_abs (sigma B q i j),abs_nonneg (sigma B q i j),sq_nonneg M]
  have hsign (b : Bool) : |if b then (1 : ℝ) else -1| = 1 := by cases b <;> norm_num
  have hnoise : |sigma B q i 0 * (if e.1 then 1 else -1) +
      sigma B q i 1 * (if e.2 then 1 else -1)| ≤ 2*(M+1) := by
    have hh := abs_add_le (sigma B q i 0 * (if e.1 then 1 else -1))
      (sigma B q i 1 * (if e.2 then 1 else -1))
    simp only [abs_mul,hsign,mul_one] at hh
    linarith [hroot 0,hroot 1]
  have hsδ : δ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ]
  have hs2 : Real.sqrt (2*δ) ≤ 2*Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le,Real.sq_sqrt (show 0 ≤ 2*δ by positivity),
      Real.sqrt_nonneg (2*δ),Real.sqrt_nonneg δ]
  have hdrift : |drift B q i*δ| ≤ M*Real.sqrt δ := by
    rw [abs_mul,abs_of_pos hδ]
    exact (mul_le_mul_of_nonneg_right (hraw q hq i).1 hδ.le).trans
      (mul_le_mul_of_nonneg_left hsδ hM)
  have hn : |Real.sqrt (2*δ) * (sigma B q i 0 * (if e.1 then 1 else -1) +
      sigma B q i 1 * (if e.2 then 1 else -1))| ≤ 4*(M+1)*Real.sqrt δ := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul hs2 hnoise (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hh := (abs_add_le (drift B q i*δ) _).trans (add_le_add hdrift hn)
  change |drift B q i*δ + Real.sqrt (2*δ) *
    (sigma B q i 0 * (if e.1 then 1 else -1) + sigma B q i 1 * (if e.2 then 1 else -1))| ≤ _
  exact hh.trans_eq (by ring)

theorem alive_height_abs (B : Model) (z : Triple) (hz : Alive B z) :
    |z 0| ≤ |B.source 0| + |B.l| + |B.u| := by
  have hl : B.l < B.source 0 + z 0 := hz.1
  have hu : B.source 0 + z 0 < B.u := hz.2
  apply abs_le.mpr
  constructor
  · linarith [le_abs_self (B.source 0),neg_abs_le (B.l),abs_nonneg (B.u)]
  · linarith [neg_abs_le (B.source 0),le_abs_self (B.u),abs_nonneg (B.l)]

theorem chord_dist_bound (z : Triple) (v : Fin 2 → ℝ)
    (H V : ℝ) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hz : |z 0| ≤ H) (hv : ∀ i, |v i| ≤ V)
    (θ φ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (hφ : φ ∈ Icc (0 : ℝ) 1) :
    ‖chord z v θ - chord z v φ‖ ≤ V * (H+V+1) * |θ-φ| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |(chord z v θ - chord z v φ) 0| ≤ _
    have he : (chord z v θ - chord z v φ) 0 = (θ-φ)*v 0 := by
      simp [chord]; ring
    rw [he,abs_mul]
    have hh := mul_le_mul_of_nonneg_left (hv 0) (abs_nonneg (θ-φ))
    nlinarith [mul_nonneg hV (abs_nonneg (θ-φ))]
  · change |(chord z v θ - chord z v φ) 1| ≤ _
    have he : (chord z v θ - chord z v φ) 1 = (θ-φ)*v 1 := by
      simp [chord]; ring
    rw [he,abs_mul]
    have hh := mul_le_mul_of_nonneg_left (hv 1) (abs_nonneg (θ-φ))
    nlinarith [mul_nonneg hV (abs_nonneg (θ-φ))]
  · change |(chord z v θ - chord z v φ) 2| ≤ _
    have he : (chord z v θ - chord z v φ) 2 =
        (θ-φ) * (z 0 + ((θ+φ)/2)*v 0) * v 1 := by
      simp [chord]; ring
    have hθφ : |(θ+φ)/2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hθ.1,hφ.1])]
      linarith [hθ.2,hφ.2]
    have hmid : |z 0 + ((θ+φ)/2)*v 0| ≤ H+V := by
      calc
        _ ≤ |z 0| + |(θ+φ)/2| * |v 0| := by simpa [abs_mul] using abs_add_le (z 0) (((θ+φ)/2)*v 0)
        _ ≤ H + 1*V := add_le_add hz (mul_le_mul hθφ (hv 0) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    rw [he,abs_mul,abs_mul]
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hmid (abs_nonneg (θ-φ))) (hv 1)
      (abs_nonneg _) (by positivity)
    exact hh.trans (by nlinarith only [mul_nonneg hV (abs_nonneg (θ-φ))])

private theorem cut_chord_dist_bound (δ cap : ℝ) (z : Triple) (v : Fin 2 → ℝ)
    (hδ : 0 < δ) (hcap : cap ∈ Icc (0 : ℝ) 1)
    (H V : ℝ) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hz : |z 0| ≤ H) (hv : ∀ i, |v i| ≤ V) (s t : ℝ) :
    ‖cutChord δ cap z v t - cutChord δ cap z v s‖ ≤
      (V*(H+V+1)/δ) * |t-s| := by
  have hc (x : ℝ) : cutParameter δ cap x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (le_max_right _ _) hcap.1,(min_le_right _ _).trans hcap.2⟩
  have hparam := (cutParameter_lipschitz δ cap).dist_le_mul t s
  simp only [Real.dist_eq,coe_nnnorm,Real.norm_eq_abs,
    abs_inv,abs_of_pos hδ] at hparam
  have hh := chord_dist_bound z v H V hH hV hz hv _ _ (hc t) (hc s)
  exact hh.trans ((mul_le_mul_of_nonneg_left hparam (by positivity)).trans_eq (by ring))

private theorem trajectory_dist_bound (B : Model) (δ L : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 ≤ L)
    (hinc : ∀ z : Triple, Alive B z → ∀ e : SignPair, ∀ i : Fin 2,
      |increment B δ z e i| ≤ L*Real.sqrt δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ (w.length:ℝ)*δ →
      ‖trajectory B δ z w t - trajectory B δ z w s‖ ≤
        ((L*Real.sqrt δ) * (|B.source 0|+|B.l|+|B.u|+L+1)/δ) * (t-s) := by
  let H := |B.source 0|+|B.l|+|B.u|
  let V := L*Real.sqrt δ
  let K := V*(H+L+1)/δ
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hVL : V ≤ L := by
    have hs : Real.sqrt δ ≤ 1 := (Real.sqrt_le_one).mpr hδ1
    exact (mul_le_mul_of_nonneg_left hs hL).trans_eq (mul_one _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut (z : Triple) (hz : Alive B z) (e : SignPair)
      (cap : ℝ) (hcap : cap ∈ Icc (0 : ℝ) 1) (s t : ℝ) :
      ‖cutChord δ cap z (increment B δ z e) t -
        cutChord δ cap z (increment B δ z e) s‖ ≤ K*|t-s| := by
    have hh := cut_chord_dist_bound δ cap z (increment B δ z e) hδ hcap H V hH hV
      (alive_height_abs B z hz) (hinc z hz e) s t
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply div_le_div_of_nonneg_right _ hδ.le
    exact mul_le_mul_of_nonneg_left (by linarith) hV
  change ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ (w.length:ℝ)*δ →
    ‖trajectory B δ z w t - trajectory B δ z w s‖ ≤ K*(t-s)
  induction w generalizing z with
  | nil =>
    intro s t hs hst ht
    have ht0 : t ≤ 0 := by simpa using ht
    have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0,ht0]
  | cons e w ih =>
    intro s t hs hst ht
    by_cases hn : Alive B (next B δ z e)
    · have hshort (x : ℝ) (hx : x ≤ δ) :
          trajectory B δ z (e::w) x = cutChord δ 1 z (increment B δ z e) x := by
        have hp : max (x/δ) 0 ≤ 1 := max_le ((div_le_one hδ).mpr hx) (by norm_num)
        simp [trajectory,hn,hx,cutChord,cutParameter,min_eq_left hp]
      have hlong (x : ℝ) (hx : δ < x) :
          trajectory B δ z (e::w) x = trajectory B δ (next B δ z e) w (x-δ) := by
        simp [trajectory,hn,not_le.mpr hx]
      have hj : cutChord δ 1 z (increment B δ z e) δ = next B δ z e := by
        simp [cutChord,cutParameter,next,ne_of_gt hδ]
      have hlen : t-δ ≤ (w.length:ℝ)*δ := by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at ht
        nlinarith
      by_cases htδ : t ≤ δ
      · rw [hshort t htδ,hshort s (hst.trans htδ)]
        simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hcut z hz e 1 (by norm_num) s t
      · by_cases hsδ : s ≤ δ
        · rw [hlong t (lt_of_not_ge htδ),hshort s hsδ]
          have htail := ih (next B δ z e) hn 0 (t-δ) (by norm_num)
            (by linarith) hlen
          rw [trajectory_zero B δ hδ w _ hn] at htail
          have hhead := hcut z hz e 1 (by norm_num) s δ
          rw [hj,abs_of_nonneg (sub_nonneg.mpr hsδ)] at hhead
          have htri : ‖trajectory B δ (next B δ z e) w (t-δ) -
              cutChord δ 1 z (increment B δ z e) s‖ ≤
              ‖trajectory B δ (next B δ z e) w (t-δ)-next B δ z e‖ +
              ‖next B δ z e-cutChord δ 1 z (increment B δ z e) s‖ := by
            simpa only [dist_eq_norm] using dist_triangle
              (trajectory B δ (next B δ z e) w (t-δ)) (next B δ z e)
              (cutChord δ 1 z (increment B δ z e) s)
          nlinarith
        · rw [hlong t (lt_of_not_ge htδ),hlong s (lt_of_not_ge hsδ)]
          have hh := ih (next B δ z e) hn (s-δ) (t-δ) (by linarith) (by linarith) hlen
          convert hh using 1; ring
    · have he (x : ℝ) : trajectory B δ z (e::w) x =
          cutChord δ (hitFraction B z (increment B δ z e)) z (increment B δ z e) x := by
        simp [trajectory,hn,cutChord,cutParameter]
      rw [he t,he s]
      simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using
        hcut z hz e _ ⟨(fraction_bounds B z _ hz).1.le,(fraction_bounds B z _ hz).2⟩ s t

private theorem command_dist_bound (B : Model) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin (n ^ 3) → SignPair, ∀ s t : ℝ,
      0 ≤ s → s ≤ t → t ≤ (n:ℝ) →
      ‖command B n w t - command B n w s‖ ≤
        K*Real.sqrt (mesh n)/mesh n*(t-s) := by
  obtain ⟨L,hL,hinc⟩ := increment_sqrt_bound B
  refine ⟨L*(|B.source 0|+|B.l|+|B.u|+L+1),by positivity,?_⟩
  intro n hn w s t hs hst ht
  have hnc : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 < mesh n := by dsimp [mesh]; positivity
  have hδ1 : mesh n ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hnc)).mpr
    nlinarith
  have htime : ((n^3:ℕ):ℝ)*mesh n = n := by
    simp only [mesh,Nat.cast_pow]
    field_simp
  have hh := trajectory_dist_bound B (mesh n) L hδ hδ1 hL
    (hinc (mesh n) hδ hδ1) (List.ofFn w) 0
    (by simpa [Alive,sourceMap] using B.source_height) s t hs hst
    (by simpa only [List.length_ofFn,htime] using ht)
  change ‖command B n w t-command B n w s‖ ≤ _ at hh
  convert hh using 1; ring

/-- The supremum of the fourth power of the joint triple oscillation on one anchored block. -/
def blockFourthOscillation (B : Model) (n : ℕ) (w : Fin (n ^ 3) → SignPair)
    (R a h : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ s ∈ Icc a (min R (a+h)), ∃ t ∈ Icc a (min R (a+h)),
    x = ‖command B n w t-command B n w s‖^4}

/-- All complete sign words retain their common original mass, including unused suffixes. -/
def blockFourthExpectation (B : Model) (n : ℕ) (R a h : ℝ) : ℝ :=
  (1/4:ℝ)^(n ^ 3) * ∑ w : Fin (n ^ 3) → SignPair, blockFourthOscillation B n w R a h

private theorem short_block_pointwise (B : Model) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ R a h : ℝ,
      0 ≤ a → R ≤ n → 0 < h → h ≤ mesh n →
      ∀ w : Fin (n ^ 3) → SignPair,
      ∀ s ∈ Icc a (min R (a+h)), ∀ t ∈ Icc a (min R (a+h)),
        ‖command B n w t-command B n w s‖^4 ≤ C*h^2 := by
  obtain ⟨K,hK,hbound⟩ := command_dist_bound B
  refine ⟨K^4,by positivity,?_⟩
  intro n hn R a h ha hRn hh hhδ w s hs t ht
  have hδ : 0 < mesh n := by dsimp [mesh]; positivity
  have hnorm : ‖command B n w t-command B n w s‖ ≤
      K*Real.sqrt (mesh n)/mesh n*h := by
    rcases le_total s t with hst | hts
    · have hb := hbound n hn w s t (ha.trans hs.1) hst
        ((ht.2.trans (min_le_left _ _)).trans hRn)
      exact hb.trans (mul_le_mul_of_nonneg_left
        (by linarith [hs.1,ht.2.trans (min_le_right _ _)]) (by positivity))
    · rw [norm_sub_rev]
      have hb := hbound n hn w t s (ha.trans ht.1) hts
        ((hs.2.trans (min_le_left _ _)).trans hRn)
      exact hb.trans (mul_le_mul_of_nonneg_left
        (by linarith [ht.1,hs.2.trans (min_le_right _ _)]) (by positivity))
  have hsqrt : (Real.sqrt (mesh n))^4 = (mesh n)^2 := by
    rw [show 4 = 2*2 by norm_num,pow_mul,Real.sq_sqrt hδ.le]
  have hfour : (K*Real.sqrt (mesh n)/mesh n*h)^4 = K^4*h^4/(mesh n)^2 := by
    field_simp
    rw [hsqrt]
  have hhpow : h^2 ≤ (mesh n)^2 := pow_le_pow_left₀ hh.le hhδ 2
  calc
    _ ≤ (K*Real.sqrt (mesh n)/mesh n*h)^4 := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    _ = K^4*h^4/(mesh n)^2 := hfour
    _ ≤ K^4*h^2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
      have hmul := mul_le_mul_of_nonneg_left hhpow (show 0 ≤ K^4*h^2 by positivity)
      nlinarith

/-- Blocks shorter than a mesh cell have a fourth oscillation bound under the actual joint law.
The assertion includes blocks crossing a node and the first wall contact. -/
theorem actual_short_block_estimate (B : Model) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ n : ℕ, R+1 < n →
      ∀ a h : ℝ, 0 ≤ a → a ≤ R → 0 < h → h ≤ mesh n →
        blockFourthExpectation B n R a h ≤ C*h^2 ∧
        ∀ (w : Fin (n ^ 3) → SignPair) (t : ℝ), 0 ≤ t →
          commandArea B n w t = command B n w t 2 := by
  obtain ⟨C,hC,hpoint⟩ := short_block_pointwise B
  refine ⟨C,hC,?_⟩
  intro R hR n hn a h ha haR hh hhδ
  have hnc : (0 : ℝ) < n := by linarith
  have hn' : 0 < n := by exact_mod_cast hnc
  have hδ : 0 < mesh n := by dsimp [mesh]; positivity
  have hblock : a ≤ min R (a+h) := le_min haR (by linarith)
  have hsup (w : Fin (n ^ 3) → SignPair) : blockFourthOscillation B n w R a h ≤ C*h^2 := by
    apply csSup_le
    · refine ⟨0,a,⟨le_rfl,hblock⟩,a,⟨le_rfl,hblock⟩,?_⟩
      simp
    · rintro x ⟨s,hs,t,ht,rfl⟩
      exact hpoint n hn' R a h ha (by linarith) hh hhδ w s hs t ht
  constructor
  · calc
      _ ≤ (1/4:ℝ)^(n ^ 3) * ∑ _w : Fin (n ^ 3) → SignPair, C*h^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ => hsup w)) (by positivity)
      _ = C*h^2 := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
          Fintype.card_prod,Fintype.card_bool,nsmul_eq_mul,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
        have he : (1/4:ℝ)^(n ^ 3) * (4:ℝ)^(n ^ 3) = 1 := by
          rw [←mul_pow]
          norm_num
        norm_num only [show (2 : ℝ)*2 = 4 by norm_num]
        rw [←mul_assoc,he,one_mul]
  · intro w t ht
    exact (actual_state_bridge B n hδ w t ht).1

end D5.S3.Analytic.Probability.NativeCommandPathTightness
