/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalNonunitShortest
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalNonunitShortest
   mirror-E: none(waiver:original-nonunit-shortest-chart-count)
   anchors: []
   utility: none
   digest: Nonunit shortest-vector charts count actual original parameters and endpoints. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalChartPieces

/-! All normalized nonunit shortest vectors lie in one anisotropic ball of
squared radius 2p. Counting this whole ball avoids a separate scale sum. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem primeCube_reduction_fiber_count {p : ℕ} (hp : p.Prime)
    (s : Finset (ZMod (p ^ 3))) (v : ZMod (p ^ 2))
    (he : ∀ a ∈ s, (ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3))
      (ZMod (p ^ 2))) a = v) : s.card ≤ p := by
  classical
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ρ : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) _
  suffices hs : s.card ≤ (Finset.range p).card by simpa only [Finset.card_range] using hs
  apply Finset.card_le_card_of_injOn (fun a : ZMod (p ^ 3) => a.val/(p ^ 2))
  · intro a ha
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul (pow_pos hp.pos 2)).mpr
    convert a.val_lt using 1 <;> ring
  · intro a ha b hb hab
    change a.val/(p ^ 2) = b.val/(p ^ 2) at hab
    have hcast (a : ZMod (p ^ 3)) : (a.val : ZMod (p ^ 2)) = ρ a := by
      simpa only [map_natCast] using congrArg ρ (ZMod.natCast_zmod_val a)
    have hmod : a.val % (p ^ 2) = b.val % (p ^ 2) := by
      have hh : (a.val : ZMod (p ^ 2)) = (b.val : ZMod (p ^ 2)) :=
        (hcast a).trans ((he a ha).trans ((he b hb).symm.trans (hcast b).symm))
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hh
    apply ZMod.val_injective (p ^ 3)
    have h₁ := Nat.mod_add_div a.val (p ^ 2)
    have h₂ := Nat.mod_add_div b.val (p ^ 2)
    rw [hab, hmod] at h₁
    omega

private theorem middle_mem_slope {c : ℕ} {t w : ℤ}
    (hw : IsUnit (w : ZMod c)) (slope : ZMod c)
    (hslope : slope*(w : ZMod c) = t) (z : Coordinate) :
    z ∈ middleLattice c t w ↔ (z.2 : ZMod c) = slope*(z.1 : ZMod c) := by
  have hm : z ∈ middleLattice c t w ↔
      (w : ZMod c)*(z.2 : ZMod c) = (t : ZMod c)*(z.1 : ZMod c) := by
    rw [middleLattice, Set.mem_ofPred_eq, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, sub_eq_zero]
  rw [hm, ← hslope]
  constructor
  · intro hz
    apply hw.mul_left_cancel
    convert hz using 1 <;> ring
  · intro hz
    rw [hz]
    ring

private theorem nonunit_shortest_normalization {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hYsmall : Y < (p : ℝ) ^ 2)
    (ht : IsUnit (t : ZMod (p ^ 3))) (hw : IsUnit (w : ZMod (p ^ 3)))
    (hanchor : (-w, -t) ∈ literalBox X Y)
    (B : ReducedMiddleBasis (p ^ 3) t w X Y)
    (hdiv : (p : ℤ) ∣ B.R.1) :
    let U : Coordinate := (B.R.1 / p, B.R.2 / p)
    B.R = (p : ℤ) • U ∧ U ∈ middleLattice (p ^ 2) t w ∧ U.1 ≠ 0 ∧ U.2 ≠ 0 ∧
      IsUnit (U.1 : ZMod (p ^ 2)) ∧ IsUnit (U.2 : ZMod (p ^ 2)) ∧
      weightedSq X Y U ≤ 2*(p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact (1 < p ^ 3) := ⟨one_lt_pow₀ hp.one_lt (by decide : 3 ≠ 0)⟩
  let ρ : ZMod (p ^ 3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) _
  have hwp : IsUnit (w : ZMod p) := by simpa only [map_intCast] using hw.map ρ
  have htp : IsUnit (t : ZMod p) := by simpa only [map_intCast] using ht.map ρ
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hR0 := B.first_ne_zero (pow_pos hp.pos _)
  have hanchor0 : (-w, -t) ≠ (0 : Coordinate) := by
    intro hz
    have hw0 : w = 0 := by have := congrArg Prod.fst hz; simpa using this
    exact hw.ne_zero (by simp only [hw0, Int.cast_zero])
  have hshort := B.shortest (-w, -t) (anchor_mem_middleLattice _ _ _) hanchor0
  have hbox := literalBox_weightedSq hX hY hanchor
  have hRbox : weightedSq X Y B.R ≤ 2*(X*Y) := hshort.trans hbox
  have hRupper : weightedSq X Y B.R ≤ 2*(p : ℝ) ^ 3 := by
    have h := (B.reduction_bounds (pow_pos hp.pos _) hX hY).2.1.le
    simpa only [Nat.cast_pow] using h
  have haxis (a b : ℤ) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
      (hCsmall : C < (p : ℝ) ^ 2) (hb : b ≠ 0)
      (hd : ((p ^ 3 : ℕ) : ℤ) ∣ b)
      (hineq : A/C*(b : ℝ) ^ 2 ≤ 2*(A*C)) : False := by
    have habs : (p : ℝ) ^ 3 ≤ |(b : ℝ)| := by
      exact_mod_cast Int.le_abs_of_dvd hb hd
    have hsq : (p : ℝ) ^ 6 ≤ (b : ℝ) ^ 2 := by
      have h := (sq_le_sq₀ (by positivity) (abs_nonneg (b : ℝ))).mpr habs
      nlinarith [sq_abs (b : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hineq hC.le
    have he : A/C*(b : ℝ) ^ 2*C = A*(b : ℝ) ^ 2 := by field_simp
    rw [he] at hmul
    have hbound : (b : ℝ) ^ 2 ≤ 2*C ^ 2 := by
      apply (mul_le_mul_iff_left₀ hA).mp
      convert hmul using 1 <;> ring
    have hCsq : C ^ 2 < (p : ℝ) ^ 4 := by
      have h := (sq_lt_sq₀ hC.le (by positivity)).mpr hCsmall
      nlinarith
    have hp4 : (2 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
    have hh := mul_lt_mul_of_pos_right hp4 (by positivity : 0 < (p : ℝ) ^ 4)
    nlinarith
  have hRfirst : B.R.1 ≠ 0 := by
    intro hz
    have hn : B.R.2 ≠ 0 := by
      intro hy
      exact hR0 (Prod.ext hz hy)
    have hd : ((p ^ 3 : ℕ) : ℤ) ∣ w*B.R.2 := by
      simpa only [middleLattice, Set.mem_ofPred_eq, hz, mul_zero, sub_zero] using B.memR
    apply haxis B.R.1 B.R.2 X Y hX hY hYsmall hn
      (integer_unit_cancel_dvd hw hd)
    simpa [weightedSq, hz] using hRbox
  have hRsecond : B.R.2 ≠ 0 := by
    intro hz
    have hd : ((p ^ 3 : ℕ) : ℤ) ∣ t*B.R.1 := by
      have hh : ((p ^ 3 : ℕ) : ℤ) ∣ -(t*B.R.1) := by
        simpa only [middleLattice, Set.mem_ofPred_eq, hz, mul_zero, zero_sub] using B.memR
      exact dvd_neg.mp hh
    apply haxis B.R.2 B.R.1 Y X hY hX (hXY.trans_lt hYsmall) hRfirst
      (integer_unit_cancel_dvd ht hd)
    simpa [weightedSq, hz, mul_comm] using hRbox
  have hpc : (p : ℤ) ∣ ((p ^ 3 : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p (by decide : 3 ≠ 0)
  have hrel : (w : ZMod p)*(B.R.2 : ZMod p) = (t : ZMod p)*(B.R.1 : ZMod p) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans hpc B.memR)
    simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using h
  have hdiv' : (p : ℤ) ∣ B.R.2 := by
    have hz : (B.R.1 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    have hz' : (B.R.2 : ZMod p) = 0 := hwp.mul_left_cancel
      (by simpa only [hz, mul_zero] using hrel)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz'
  let U : Coordinate := (B.R.1 / p, B.R.2 / p)
  have hscale : B.R = (p : ℤ) • U := by
    apply Prod.ext
    · simpa only [U, Prod.smul_fst, smul_eq_mul, mul_comm] using
        (Int.ediv_mul_cancel hdiv).symm
    · simpa only [U, Prod.smul_snd, smul_eq_mul, mul_comm] using
        (Int.ediv_mul_cancel hdiv').symm
  have hUfirst : U.1 ≠ 0 := by
    intro hz
    have h := congrArg Prod.fst hscale
    simp only [Prod.smul_fst, smul_eq_mul, hz, mul_zero] at h
    exact hRfirst h
  have hUsecond : U.2 ≠ 0 := by
    intro hz
    have h := congrArg Prod.snd hscale
    simp only [Prod.smul_snd, smul_eq_mul, hz, mul_zero] at h
    exact hRsecond h
  have hQscale : weightedSq X Y B.R = (p : ℝ) ^ 2*weightedSq X Y U := by
    rw [hscale, weightedSq_zsmul]
    norm_cast
  have hQ : weightedSq X Y U ≤ 2*(p : ℝ) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hpR)).mp
    calc
      weightedSq X Y U*(p : ℝ) ^ 2 = weightedSq X Y B.R := by
        rw [mul_comm]
        exact hQscale.symm
      _ ≤ 2*(p : ℝ) ^ 3 := hRupper
      _ = (2*(p : ℝ))*(p : ℝ) ^ 2 := by ring
  have hnotboth : ¬ ((p : ℤ) ∣ U.1 ∧ (p : ℤ) ∣ U.2) := by
    rintro ⟨hu, hv⟩
    have ha : (p : ℝ) ≤ |(U.1 : ℝ)| := by exact_mod_cast Int.le_abs_of_dvd hUfirst hu
    have hb : (p : ℝ) ≤ |(U.2 : ℝ)| := by exact_mod_cast Int.le_abs_of_dvd hUsecond hv
    have hh := mul_le_mul ha hb hpR.le (abs_nonneg _)
    have hmetric := two_abs_product_le_weightedSq hX hY U
    nlinarith
  have hUmem : U ∈ middleLattice (p ^ 2) t w := by
    have hm := B.memR
    rw [hscale] at hm
    change ((p ^ 3 : ℕ) : ℤ) ∣ w*((p : ℤ)*U.2)-t*((p : ℤ)*U.1) at hm
    have hm' : (p : ℤ)*(p : ℤ) ^ 2 ∣ (p : ℤ)*(w*U.2-t*U.1) := by
      convert hm using 1 <;> push_cast <;> ring
    change ((p ^ 2 : ℕ) : ℤ) ∣ w*U.2-t*U.1
    simpa only [Nat.cast_pow] using
      (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp hm'
  have hUrel : (w : ZMod p)*(U.2 : ZMod p) = (t : ZMod p)*(U.1 : ZMod p) := by
    have hp2div : (p : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast dvd_pow_self p (by decide : 2 ≠ 0)
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans hp2div hUmem)
    simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using h
  have hun : ¬ (p : ℤ) ∣ U.1 := by
    intro hu
    have hz : (U.1 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hu
    have hz' : (U.2 : ZMod p) = 0 := hwp.mul_left_cancel
      (by simpa only [hz, mul_zero] using hUrel)
    exact hnotboth ⟨hu, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz'⟩
  have hvn : ¬ (p : ℤ) ∣ U.2 := by
    intro hv
    have hz : (U.2 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hv
    have hz' : (U.1 : ZMod p) = 0 := htp.mul_left_cancel
      (by simpa only [hz, mul_zero] using hUrel.symm)
    exact hnotboth ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz', hv⟩
  exact ⟨hscale, hUmem, hUfirst, hUsecond,
    primeSquare_int_unit hp hun, primeSquare_int_unit hp hvn, hQ⟩

private def normalizedShortest {p : ℕ} {X Y : ℝ} {T : Finset ReturnRows}
    (B : ∀ h ∈ T, ReducedMiddleBasis (p ^ 3) (h.2 2) (h.1 2) X Y)
    (h : ReturnRows) : Coordinate :=
  if hh : h ∈ T then ((B h hh).R.1/p, (B h hh).R.2/p) else 0

private def middleSlope (p : ℕ) (h : ReturnRows) : ZMod (p ^ 3) :=
  (h.2 2 : ZMod (p ^ 3))*(h.1 2 : ZMod (p ^ 3))⁻¹

private theorem middleSlope_spec {p : ℕ} {h : ReturnRows}
    (hw : IsUnit (h.1 2 : ZMod (p ^ 3))) :
    middleSlope p h*(h.1 2 : ZMod (p ^ 3)) = h.2 2 := by
  rw [middleSlope, mul_assoc, ZMod.inv_mul_of_unit _ hw, mul_one]

private theorem nonunit_shortest_label_count {p : ℕ} (hp : p.Prime)
    {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hH : 0 < H) (hHsq : H ^ 2 = X*Y) (hYsmall : Y < (p : ℝ) ^ 2)
    (T : Finset ReturnRows)
    (hbox : ∀ h ∈ T, |(h.1 2 : ℝ)| ≤ X ∧ |(h.2 2 : ℝ)| ≤ Y)
    (hunit : ∀ h ∈ T, IsUnit (h.1 2 : ZMod (p ^ 3)) ∧ IsUnit (h.2 2 : ZMod (p ^ 3)))
    (B : ∀ h ∈ T, ReducedMiddleBasis (p ^ 3) (h.2 2) (h.1 2) X Y)
    (hdiv : ∀ h (hh : h ∈ T), (p : ℤ) ∣ (B h hh).R.1) :
    ((T.image fun h => (normalizedShortest B h, middleSlope p h)).card : ℝ) ≤
      8*(p : ℝ) ^ 2 := by
  classical
  let K := T.image fun h => (normalizedShortest B h, middleSlope p h)
  let V := K.image Prod.fst
  let ρ : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) _
  have hdata (h : ReturnRows) (hh : h ∈ T) :
      normalizedShortest B h ∈ middleLattice (p ^ 2) (h.2 2) (h.1 2) ∧
      (normalizedShortest B h).1 ≠ 0 ∧ (normalizedShortest B h).2 ≠ 0 ∧
      IsUnit ((normalizedShortest B h).1 : ZMod (p ^ 2)) ∧
      IsUnit ((normalizedShortest B h).2 : ZMod (p ^ 2)) ∧
      weightedSq X Y (normalizedShortest B h) ≤ 2*(p : ℝ) := by
    have ha : (-(h.1 2), -(h.2 2)) ∈ literalBox X Y := by
      exact anchor_mem_literalBox (hbox h hh).1 (hbox h hh).2
    have hd := nonunit_shortest_normalization hp hX hY hXY hYsmall
      (hunit h hh).2 (hunit h hh).1 ha (B h hh) (hdiv h hh)
    simpa only [normalizedShortest, dite_eq_left hh] using hd.2
  have hV (u : Coordinate) (hu : u ∈ V) : ∃ h ∈ T, normalizedShortest B h = u := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨h, hh, rfl⟩
  have hVcount : (V.card : ℝ) ≤ 8*(p : ℝ) := by
    have hpR : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    have hsq : (Real.sqrt (2*(p : ℝ))) ^ 2 = 2*(p : ℝ) := Real.sq_sqrt (by positivity)
    have h := nonaxis_short_vector_candidates_count hX hY hH hHsq
      (Real.sqrt_nonneg (2*(p : ℝ))) V (by
        intro u hu
        obtain ⟨h, hh, rfl⟩ := hV u hu
        exact ⟨(hdata h hh).2.1, (hdata h hh).2.2.1⟩) (by
        intro u hu
        obtain ⟨h, hh, rfl⟩ := hV u hu
        simpa only [hsq] using (hdata h hh).2.2.2.2.2)
    nlinarith
  have hroot (h : ReturnRows) (hh : h ∈ T) :
      ρ (middleSlope p h)*((normalizedShortest B h).1 : ZMod (p ^ 2)) =
        (normalizedShortest B h).2 := by
    have hw : IsUnit (h.1 2 : ZMod (p ^ 2)) := by
      simpa only [map_intCast] using (hunit h hh).1.map ρ
    have hs := congrArg ρ (middleSlope_spec (hunit h hh).1)
    simp only [map_mul, map_intCast] at hs
    exact ((middle_mem_slope hw _ hs _).mp (hdata h hh).1).symm
  have hfiber (u : Coordinate) (hu : u ∈ V) :
      (K.filter (fun k => k.1=u)).card ≤ p := by
    obtain ⟨h₀, hh₀, hu₀⟩ := hV u hu
    let L := (K.filter (fun k => k.1=u)).image Prod.snd
    have hinj : Set.InjOn (Prod.snd : Coordinate × ZMod (p ^ 3) → ZMod (p ^ 3))
        ((K.filter (fun k => k.1=u)) : Set (Coordinate × ZMod (p ^ 3))) := by
      intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
    have hL : L.card ≤ p := by
      apply primeCube_reduction_fiber_count hp L (ρ (middleSlope p h₀))
      intro slope hslope
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hslope
      obtain ⟨h, hh, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hk).1
      have huf : normalizedShortest B h = u :=
        (congrArg Prod.fst he).trans (Finset.mem_filter.mp hk).2
      have hslopef : middleSlope p h = k.2 := congrArg Prod.snd he
      have huunit : IsUnit (u.1 : ZMod (p ^ 2)) := by
        simpa only [hu₀] using (hdata h₀ hh₀).2.2.2.1
      apply huunit.mul_right_cancel
      have h₁ := hroot h hh
      have h₂ := hroot h₀ hh₀
      simp only [huf, hu₀, hslopef] at h₁ h₂
      exact h₁.trans h₂.symm
    simpa only [L, Finset.card_image_of_injOn hinj] using hL
  have hcount : (K.card : ℝ) = ∑ u ∈ V, ((K.filter (fun k => k.1=u)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (Prod.fst : Coordinate × ZMod (p ^ 3) → Coordinate) K
  calc
    (K.card : ℝ) = ∑ u ∈ V, ((K.filter (fun k => k.1=u)).card : ℝ) := hcount
    _ ≤ ∑ _u ∈ V, (p : ℝ) := Finset.sum_le_sum (by
      intro u hu
      exact_mod_cast hfiber u hu)
    _ = (V.card : ℝ)*p := by simp
    _ ≤ (8*(p : ℝ))*p := mul_le_mul_of_nonneg_right hVcount (Nat.cast_nonneg _)
    _ = 8*(p : ℝ) ^ 2 := by ring

private theorem nonunit_shortest_box_section_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H ^ 2 = X*Y) (harea : (p : ℝ) ^ 3 ≤ X*Y)
    (hw : IsUnit (w : ZMod (p ^ 3))) (hanchor : (-w, -t) ∈ literalBox X Y)
    (B : ReducedMiddleBasis (p ^ 3) t w X Y) (hdiv : (p : ℤ) ∣ B.R.1)
    (F : Finset Coordinate)
    (hmem : ∀ z ∈ F, z ∈ middleLattice (p ^ 3) t w)
    (hbox : ∀ z ∈ F, z ∈ literalBox X Y) :
    (F.card : ℝ) ≤ 64*(X*Y)/(p : ℝ) ^ 3 := by
  letI : Fact p.Prime := ⟨hp⟩
  let D : ℤ := B.R.1*(-t)-(-w)*B.R.2
  obtain ⟨i, j, hij⟩ := B.decompose (-w, -t) (anchor_mem_middleLattice _ _ _)
  have h₁ : i*B.R.1+j*B.V.1 = -w := congrArg Prod.fst hij
  have h₂ : i*B.R.2+j*B.V.2 = -t := congrArg Prod.snd hij
  have hjD : j*((p ^ 3 : ℕ) : ℤ) = D := by
    dsimp [D]
    have hd := B.det
    push_cast at hd ⊢
    linear_combination B.R.1*h₂-B.R.2*h₁-j*hd
  have hD0 : D ≠ 0 := by
    intro hz
    have hj : j = 0 := by
      have hc : ((p ^ 3 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hp.ne_zero
      rw [hz] at hjD
      exact (mul_eq_zero.mp hjD).resolve_right hc
    have hd : (p : ℤ) ∣ w := by
      have hh : (p : ℤ) ∣ -w := by
        rw [← h₁, hj, zero_mul, add_zero]
        exact dvd_mul_of_dvd_right hdiv i
      exact dvd_neg.mp hh
    let ρ : ZMod (p ^ 3) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) _
    have hwp : IsUnit (w : ZMod p) := by simpa only [map_intCast] using hw.map ρ
    exact hwp.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)
  have hDc : ((p ^ 3 : ℕ) : ℤ) ∣ D := ⟨j, by simpa only [mul_comm] using hjD.symm⟩
  have hDabs : (p : ℝ) ^ 3 ≤ |(D : ℝ)| := by
    exact_mod_cast Int.le_abs_of_dvd hD0 hDc
  have hDsq : (p : ℝ) ^ 6 ≤ (D : ℝ) ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity) (abs_nonneg (D : ℝ))).mpr hDabs
    nlinarith [sq_abs (D : ℝ)]
  have hdet := weighted_det_sq_le hX hY B.R (-w, -t)
  change (D : ℝ) ^ 2 ≤ weightedSq X Y B.R*weightedSq X Y (-w, -t) at hdet
  have hanchorQ := literalBox_weightedSq hX hY hanchor
  have hQ : (p : ℝ) ^ 6 ≤ 2*(X*Y)*weightedSq X Y B.R := by
    have hh := mul_le_mul_of_nonneg_left hanchorQ (weightedSq_nonneg hX hY B.R)
    nlinarith
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hσ : 0 < σ := Real.sqrt_pos.mpr
    (weightedSq_pos hX hY (B.first_ne_zero (pow_pos hp.pos _)))
  have hσsq : σ ^ 2 = weightedSq X Y B.R := Real.sq_sqrt (weightedSq_nonneg hX hY _)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hgeom : (p : ℝ) ^ 3 ≤ 2*H*σ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      ((p : ℝ) ^ 3) ^ 2 = (p : ℝ) ^ 6 := by ring
      _ ≤ 2*(X*Y)*weightedSq X Y B.R := hQ
      _ ≤ (2*H*σ) ^ 2 := by
        rw [← hHsq, ← hσsq]
        nlinarith [sq_nonneg (H*σ)]
  have hboundary : H/σ ≤ 2*(X*Y)/(p : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ hσ (by positivity : 0 < (p : ℝ) ^ 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hgeom hH.le]
  have hboundary' : H/σ ≤ 2*((X*Y)/(p : ℝ) ^ 3) := by
    convert hboundary using 1 <;> ring
  have hvolume : 1 ≤ (X*Y)/(p : ℝ) ^ 3 :=
    (le_div_iff₀ (by positivity : 0 < (p : ℝ) ^ 3)).mpr (by simpa using harea)
  have hF := actual_middle_box_section_count B (pow_pos hp.pos _) hX hY H hH hHsq F hmem hbox
  dsimp only at hF
  push_cast at hF
  change (F.card : ℝ) ≤ 16*(1+H/σ+(X*Y)/(p : ℝ) ^ 3) at hF
  calc
    (F.card : ℝ) ≤ 64*((X*Y)/(p : ℝ) ^ 3) := by linarith
    _ = 64*(X*Y)/(p : ℝ) ^ 3 := by ring

private theorem common_nonunit_shortest_rows_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H ^ 2 = X*Y) (harea : (p : ℝ) ^ 3 ≤ X*Y)
    (hXsmall : 2*X < (p ^ 2 : ℕ)) (hYsmall : 2*Y < (p ^ 3 : ℕ))
    (hw : IsUnit (w : ZMod (p ^ 3))) (hanchor : (-w, -t) ∈ literalBox X Y)
    (B : ReducedMiddleBasis (p ^ 3) t w X Y) (hdiv : (p : ℤ) ∣ B.R.1)
    (a₁ a₂ : ZMod (p ^ 3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (S : Finset ReturnRows)
    (hbox : ∀ h ∈ S, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ S, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ S, IsUnit (h.1 2 : ZMod (p ^ 3)) ∧ IsUnit (h.2 2 : ZMod (p ^ 3)))
    (hshared : ∀ h ∈ S, middleLattice (p ^ 3) (h.2 2) (h.1 2) =
      middleLattice (p ^ 3) t w) :
    (S.card : ℝ) ≤ 8256*((X*Y)/(p : ℝ) ^ 3) ^ 2 := by
  classical
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let points (h : ReturnRows) : Finset Coordinate :=
    {originalMiddle h, (originalEndpoints h).1, (originalEndpoints h).2}
  let F := S.biUnion points
  let P := S.image originalMiddle
  have hpnt (h : ReturnRows) (hh : h ∈ S) (z : Coordinate) (hz : z ∈ points h) :
      z ∈ middleLattice (p ^ 3) t w ∧ z ∈ literalBox X Y := by
    have heq := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp (hword h hh)
    have hmid : originalMiddle h ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      simp only [originalMiddle, middleLattice, Set.mem_ofPred_eq, Prod.fst, Prod.snd,
        mul_comm, sub_self, dvd_zero]
    have hfirst : (originalEndpoints h).1 ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [originalEndpoints, Int.cast_sub, Int.cast_mul] using
        sub_eq_zero.mpr heq.2.2.1
    have hsecond : (originalEndpoints h).2 ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [originalEndpoints, Int.cast_sub, Int.cast_mul] using
        sub_eq_zero.mpr heq.2.2.2
    simp only [points, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨hshared h hh ▸ hmid, hbox h hh 2⟩
    · exact ⟨hshared h hh ▸ hfirst, hbox h hh 0⟩
    · exact ⟨hshared h hh ▸ hsecond, hbox h hh 1⟩
  have hF (z : Coordinate) (hz : z ∈ F) :
      z ∈ middleLattice (p ^ 3) t w ∧ z ∈ literalBox X Y := by
    obtain ⟨h, hh, hz⟩ := Finset.mem_biUnion.mp hz
    exact hpnt h hh z hz
  have hFin (h : ReturnRows) (hh : h ∈ S) :
      originalMiddle h ∈ F ∧ (originalEndpoints h).1 ∈ F ∧ (originalEndpoints h).2 ∈ F := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp only [points, Finset.mem_insert, true_or]⟩
    constructor
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp [points]⟩
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp [points]⟩
  have hFcount : (F.card : ℝ) ≤ 64*(X*Y)/(p : ℝ) ^ 3 :=
    nonunit_shortest_box_section_count hp hX hY hH hHsq harea hw hanchor B hdiv F
      (fun z hz => (hF z hz).1) (fun z hz => (hF z hz).2)
  have hPcount : P.card ≤ F.card := Finset.card_le_card (by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    exact (hFin h hh).1)
  have hfiber (wt : Coordinate) (hwt : wt ∈ P) :
      (S.filter (fun h => originalMiddle h = wt)).card ≤ 2*F.card+1 := by
    obtain ⟨h₀, hh₀, he₀⟩ := Finset.mem_image.mp hwt
    let A := S.filter fun h => originalMiddle h = wt
    let E := A.image originalEndpoints
    have hm (h : ReturnRows) (hh : h ∈ A) : h ∈ S ∧
        h.1 2 = h₀.1 2 ∧ h.2 2 = h₀.2 2 := by
      have ha := Finset.mem_filter.mp hh
      exact ⟨ha.1, (congrArg Prod.fst ha.2).trans (congrArg Prod.fst he₀).symm,
        (congrArg Prod.snd ha.2).trans (congrArg Prod.snd he₀).symm⟩
    have hinj : Set.InjOn originalEndpoints (A : Set ReturnRows) := by
      intro h hh h' hh' he
      have hb := hm h hh
      have hb' := hm h' hh'
      apply Prod.ext <;> funext i <;> fin_cases i
      · exact congrArg (fun e : Endpoint => e.1.1) he
      · exact congrArg (fun e : Endpoint => e.2.1) he
      · exact hb.2.1.trans hb'.2.1.symm
      · exact congrArg (fun e : Endpoint => e.1.2) he
      · exact congrArg (fun e : Endpoint => e.2.2) he
      · exact hb.2.2.trans hb'.2.2.symm
    have hsub : E ⊆ (F.product F).filter fun e => sixReturnWord a₁ a₂
        (e.1.1 : ZMod (p ^ 3)) (h₀.2 2) e.2.1 e.1.2 (h₀.1 2) e.2.2 =
          scalarReturn (-1) := by
      intro e he
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hs, hwm, htm⟩ := hm h hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hFin h hs).2.1, (hFin h hs).2.2⟩, ?_⟩
      simpa only [originalEndpoints, hwm, htm] using hword h hs
    have helem := actual_endpoint_pair_elementary_count hp hXsmall hYsmall
      a₁ a₂ ha₁ ha₂ (hunit h₀ hh₀).2 (hunit h₀ hh₀).1 F (by
        intro z hz
        rw [hshared h₀ hh₀]
        exact (hF z hz).1) (fun z hz => (hF z hz).2)
    calc
      A.card = E.card := by simp only [E, Finset.card_image_of_injOn hinj]
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ 2*F.card+1 := helem
  have hcount : (S.card : ℝ) =
      ∑ wt ∈ P, ((S.filter (fun h => originalMiddle h = wt)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image originalMiddle S
  have hA : 1 ≤ (X*Y)/(p : ℝ) ^ 3 :=
    (le_div_iff₀ (by exact_mod_cast pow_pos hp.pos 3 : 0 < (p : ℝ) ^ 3)).mpr
      (by simpa using harea)
  have hpc : (P.card : ℝ) ≤ 64*((X*Y)/(p : ℝ) ^ 3) := by
    have hpc' : (P.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hPcount
    exact hpc'.trans (by simpa only [mul_div_assoc] using hFcount)
  have hec : 2*(F.card : ℝ)+1 ≤ 129*((X*Y)/(p : ℝ) ^ 3) := by
    have hf : (F.card : ℝ) ≤ 64*((X*Y)/(p : ℝ) ^ 3) := by
      simpa only [mul_div_assoc] using hFcount
    linarith
  calc
    (S.card : ℝ) = ∑ wt ∈ P, ((S.filter (fun h => originalMiddle h = wt)).card : ℝ) := hcount
    _ ≤ ∑ _wt ∈ P, (2*(F.card : ℝ)+1) := Finset.sum_le_sum (by
      intro wt hwt
      exact_mod_cast hfiber wt hwt)
    _ = (P.card : ℝ)*(2*(F.card : ℝ)+1) := by simp; ring
    _ ≤ (64*((X*Y)/(p : ℝ) ^ 3))*(129*((X*Y)/(p : ℝ) ^ 3)) :=
      mul_le_mul hpc hec (by positivity) (by positivity)
    _ = 8256*((X*Y)/(p : ℝ) ^ 3) ^ 2 := by ring

/- All actual original words whose chosen reduced shortest vector is nonunit
have the prime-cube error bound. The finite label set and every label fiber
are constructed from the original rows themselves. -/
theorem actual_nonunit_shortest_tuple_count {p : ℕ} (hp : p.Prime)
    {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hH : 0 < H) (hHsq : H ^ 2 = X*Y) (harea : (p : ℝ) ^ 3 ≤ X*Y)
    (hXsmall : 2*X < (p ^ 2 : ℕ)) (hYsmall : 2*Y < (p ^ 3 : ℕ))
    (hYsquare : Y < (p : ℝ) ^ 2)
    (a₁ a₂ : ZMod (p ^ 3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (T : Finset ReturnRows)
    (hbox : ∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ T, IsUnit (h.1 2 : ZMod (p ^ 3)) ∧ IsUnit (h.2 2 : ZMod (p ^ 3)))
    (B : ∀ h ∈ T, ReducedMiddleBasis (p ^ 3) (h.2 2) (h.1 2) X Y)
    (hdiv : ∀ h (hh : h ∈ T), (p : ℤ) ∣ (B h hh).R.1) :
    (T.card : ℝ) ≤ 66048*(X*Y) ^ 2/(p : ℝ) ^ 4 := by
  classical
  let K := T.image fun h => (normalizedShortest B h, middleSlope p h)
  have hK : (K.card : ℝ) ≤ 8*(p : ℝ) ^ 2 :=
    nonunit_shortest_label_count hp hX hY hXY hH hHsq hYsquare T
      (fun h hh => hbox h hh 2) hunit B hdiv
  have hfiber (k : Coordinate × ZMod (p ^ 3)) (hk : k ∈ K) :
      ((T.filter (fun h => (normalizedShortest B h, middleSlope p h) = k)).card : ℝ) ≤
        8256*((X*Y)/(p : ℝ) ^ 3) ^ 2 := by
    obtain ⟨h₀, hh₀, he₀⟩ := Finset.mem_image.mp hk
    let S := T.filter fun h => (normalizedShortest B h, middleSlope p h) = k
    have hS (h : ReturnRows) (hh : h ∈ S) : h ∈ T ∧ middleSlope p h = middleSlope p h₀ := by
      have hs := Finset.mem_filter.mp hh
      exact ⟨hs.1, (congrArg Prod.snd hs.2).trans (congrArg Prod.snd he₀).symm⟩
    have hanchor : (-(h₀.1 2), -(h₀.2 2)) ∈ literalBox X Y := by
      exact anchor_mem_literalBox (hbox h₀ hh₀ 2).1 (hbox h₀ hh₀ 2).2
    apply common_nonunit_shortest_rows_count hp hX hY hH hHsq harea
      hXsmall hYsmall (hunit h₀ hh₀).1 hanchor (B h₀ hh₀) (hdiv h₀ hh₀)
      a₁ a₂ ha₁ ha₂ S
      (fun h hh => hbox h (hS h hh).1)
      (fun h hh => hword h (hS h hh).1)
      (fun h hh => hunit h (hS h hh).1)
    intro h hh
    apply Set.ext
    intro z
    rw [middle_mem_slope (hunit h (hS h hh).1).1 _
      (middleSlope_spec (hunit h (hS h hh).1).1),
      middle_mem_slope (hunit h₀ hh₀).1 _ (middleSlope_spec (hunit h₀ hh₀).1),
      (hS h hh).2]
  have hcount : (T.card : ℝ) = ∑ k ∈ K,
      ((T.filter (fun h => (normalizedShortest B h, middleSlope p h) = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image
      (fun h => (normalizedShortest B h, middleSlope p h)) T
  calc
    (T.card : ℝ) = ∑ k ∈ K,
        ((T.filter (fun h => (normalizedShortest B h, middleSlope p h) = k)).card : ℝ) := hcount
    _ ≤ ∑ _k ∈ K, 8256*((X*Y)/(p : ℝ) ^ 3) ^ 2 := Finset.sum_le_sum hfiber
    _ = (K.card : ℝ)*(8256*((X*Y)/(p : ℝ) ^ 3) ^ 2) := by simp
    _ ≤ (8*(p : ℝ) ^ 2)*(8256*((X*Y)/(p : ℝ) ^ 3) ^ 2) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = 66048*(X*Y) ^ 2/(p : ℝ) ^ 4 := by
      field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
      <;> ring

end

end D5.S3.Arith.CharacterSums.Original
