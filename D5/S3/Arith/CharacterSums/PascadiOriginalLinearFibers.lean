/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalLinearFibers
   mirror-E: none(waiver:original-physical-linear-fibers)
   anchors: []
   utility: none
   digest: Actual physical multiplicity of a relevant primitive linear factor. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalLattice
import Mathlib.Data.Int.Interval

/-! The rational-factor direction is counted in the actual physical box.
Relevance forces its primitive physical step into p times the index-p² lattice. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem primitive_linear_parameter (a b : ℤ) (hab : Int.gcd a b = 1)
    {z z₀ : Coordinate} (h : a * z.1 - b * z.2 = a * z₀.1 - b * z₀.2) :
    z - z₀ = (Int.gcdA a b * (z.2 - z₀.2) +
      Int.gcdB a b * (z.1 - z₀.1)) • (b, a) := by
  have hg : a * Int.gcdA a b + b * Int.gcdB a b = 1 := by
    simpa only [hab, Nat.cast_one] using (Int.gcd_eq_gcd_ab a b).symm
  apply Prod.ext
  · change z.1 - z₀.1 = _ * b
    linear_combination -(z.1 - z₀.1) * hg + Int.gcdA a b * h
  · change z.2 - z₀.2 = _ * a
    linear_combination -(z.2 - z₀.2) * hg - Int.gcdB a b * h

theorem weightedSq_zsmul (X Y : ℝ) (n : ℤ) (z : Coordinate) :
    weightedSq X Y (n • z) = (n : ℝ)^2 * weightedSq X Y z := by
  simp only [weightedSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Int.cast_mul]
  ring

private theorem physical_sub (R V z z₀ : Coordinate) :
    physical R V (z - z₀) = physical R V z - physical R V z₀ := by
  apply Prod.ext <;> simp [physical] <;> ring

private theorem physical_zsmul (R V z : Coordinate) (n : ℤ) :
    physical R V (n • z) = n • physical R V z := by
  apply Prod.ext <;> simp [physical] <;> ring

/-- The physical step associated to a relevant linear factor is divisible by p;
after dividing by p it lies in the original index-p² congruence lattice. -/
theorem relevant_linear_physical_step {p : ℕ} (hp : p.Prime) {t w : ℤ}
    (B : MiddleBasis (p^3) t w) (a b : ℤ) (hab : Int.gcd a b = 1)
    (hw : IsUnit (w : ZMod p))
    (hroot : ((a * B.V.1 + b * B.R.1 : ℤ) : ZMod p) = 0) :
    ∃ U : Coordinate, U ≠ 0 ∧ U ∈ middleLattice (p^2) t w ∧
      physical B.R B.V (b, a) = (p : ℤ) • U := by
  let W := physical B.R B.V (b, a)
  have hc : 0 < p^3 := pow_pos hp.pos _
  have hW0 : W ≠ 0 := by
    intro hW
    have hz : (b, a) = (0 : Coordinate) :=
      B.coordinates_unique hc (by simpa [W, physical] using hW)
    have hb : b = 0 := congrArg Prod.fst hz
    have ha : a = 0 := congrArg Prod.snd hz
    simp [ha, hb] at hab
  have hx : (p : ℤ) ∣ W.1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [W, physical, add_comm] using hroot
  have hmem : W ∈ middleLattice (p^3) t w := B.physical_mem (b, a)
  have hpc : (p : ℤ) ∣ ((p^3 : ℕ) : ℤ) := by
    exact ⟨(p : ℤ)^2, by push_cast; ring⟩
  have hwm : (p : ℤ) ∣ w * W.2 := by
    have hh := dvd_add (dvd_trans hpc hmem) (dvd_mul_of_dvd_right hx t)
    convert hh using 1 <;> ring
  have hy : (p : ℤ) ∣ W.2 := by
    have hh : (w : ZMod p) * (W.2 : ZMod p) = 0 := by
      simpa only [Int.cast_mul] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hwm
    have hwcancel := hw.mul_right_injective
    have hh' : (W.2 : ZMod p) = 0 := hwcancel (by simpa using hh)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh'
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  let U : Coordinate := (u, v)
  have hWU : W = (p : ℤ) • U := Prod.ext hu hv
  have hU0 : U ≠ 0 := by
    intro hU
    exact hW0 (by simpa [hU] using hWU)
  refine ⟨U, hU0, ?_, hWU⟩
  obtain ⟨k, hk⟩ := hmem
  change ∃ k : ℤ, w * v - t * u = ((p^2 : ℕ) : ℤ) * k
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
  push_cast at hk ⊢
  rw [hu, hv] at hk
  linear_combination hk

private theorem box_difference_weightedSq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {z z₀ : Coordinate} (hz : z ∈ literalBox X Y) (hz₀ : z₀ ∈ literalBox X Y) :
    weightedSq X Y (z - z₀) ≤ 8 * (X * Y) := by
  have hx : |((z - z₀).1 : ℝ)| ≤ 2 * X := by
    simpa only [Prod.fst_sub, Int.cast_sub] using
      (abs_sub (z.1 : ℝ) (z₀.1 : ℝ)).trans (by linarith [hz.1, hz₀.1])
  have hy : |((z - z₀).2 : ℝ)| ≤ 2 * Y := by
    simpa only [Prod.snd_sub, Int.cast_sub] using
      (abs_sub (z.2 : ℝ) (z₀.2 : ℝ)).trans (by linarith [hz.2, hz₀.2])
  have hh := literalBox_weightedSq (X := 2*X) (Y := 2*Y)
    (by positivity) (by positivity) (z := z-z₀) ⟨hx,hy⟩
  have he : weightedSq (2*X) (2*Y) (z-z₀) = weightedSq X Y (z-z₀) := by
    unfold weightedSq
    field_simp
  rw [he] at hh
  nlinarith

/-- A relevant primitive linear factor has the physical multiplicity dictated
by the shortest vector of the index-p² lattice. The count is of the actual
integer coordinate vectors whose physical images lie in the original box. -/
theorem actual_linear_factor_fiber_count {p : ℕ} (hp : p.Prime) {t w : ℤ}
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
    (H : ℝ) (hH : 0 < H) (hHsq : H^2 = X*Y)
    (a b value : ℤ) (hab : Int.gcd a b = 1)
    (hw : IsUnit (w : ZMod p))
    (hroot : ((a * B.V.1 + b * B.R.1 : ℤ) : ZMod p) = 0)
    (s : Finset Coordinate)
    (hbox : ∀ z ∈ s, physical B.R B.V z ∈ literalBox X Y)
    (hvalue : ∀ z ∈ s, a * z.1 - b * z.2 = value) :
    (s.card : ℝ) ≤ 1 + 6 * H /
      ((p : ℝ) * Real.sqrt (weightedSq X Y B₂.R)) := by
  classical
  let σ := Real.sqrt (weightedSq X Y B₂.R)
  have hσ : 0 < σ := Real.sqrt_pos.mpr
    (weightedSq_pos hX hY (B₂.first_ne_zero (pow_pos hp.pos _)))
  have hσsq : σ^2 = weightedSq X Y B₂.R :=
    Real.sq_sqrt (weightedSq_nonneg hX hY _)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpσ : 0 < (p : ℝ) * σ := mul_pos hpR hσ
  obtain ⟨U, hU0, hUm, hW⟩ := relevant_linear_physical_step hp B a b hab hw hroot
  have hshort := B₂.shortest U hUm hU0
  have hstep : ((p : ℝ)*σ)^2 ≤ weightedSq X Y (physical B.R B.V (b,a)) := by
    rw [hW, weightedSq_zsmul]
    rw [mul_pow, hσsq]
    exact mul_le_mul_of_nonneg_left hshort (sq_nonneg _)
  by_cases hs : s.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hs
    let n : Coordinate → ℤ := fun z =>
      Int.gcdA a b * (z.2-z₀.2) + Int.gcdB a b * (z.1-z₀.1)
    have hn (z : Coordinate) (hz : z ∈ s) : z-z₀ = n z • (b,a) :=
      primitive_linear_parameter a b hab ((hvalue z hz).trans (hvalue z₀ hz₀).symm)
    have hinj : Set.InjOn n (s : Set Coordinate) := by
      intro z hz z' hz' he
      have hh : z-z₀ = z'-z₀ := by rw [hn z hz, hn z' hz', he]
      exact sub_left_inj.mp hh
    let T : ℝ := 3 * H / ((p : ℝ)*σ)
    have hT : 0 ≤ T := le_of_lt (div_pos (by positivity) hpσ)
    have hnbound (z : Coordinate) (hz : z ∈ s) : |(n z : ℝ)| ≤ T := by
      have hdiff : physical B.R B.V z - physical B.R B.V z₀ =
          n z • physical B.R B.V (b,a) := by
        rw [← physical_sub, hn z hz, physical_zsmul]
      have hupper := box_difference_weightedSq hX hY (hbox z hz) (hbox z₀ hz₀)
      rw [hdiff, weightedSq_zsmul] at hupper
      have hmul := mul_le_mul_of_nonneg_left hstep (sq_nonneg (n z : ℝ))
      have hsq : (|(n z : ℝ)| * ((p : ℝ)*σ))^2 ≤ (3*H)^2 := by
        rw [mul_pow, sq_abs]
        nlinarith [sq_pos_of_pos hH]
      have hh := (sq_le_sq₀
        (mul_nonneg (abs_nonneg _) hpσ.le) (by positivity : 0 ≤ 3*H)).mp hsq
      exact (le_div_iff₀ hpσ).mpr hh
    let N : ℤ := ⌊T⌋
    have hN : 0 ≤ N := Int.floor_nonneg.mpr hT
    have hsub : s.image n ⊆ Finset.Icc (-N) N := by
      intro k hk
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
      have hbnd := abs_le.mp (hnbound z hz)
      have hu : n z ≤ N := Int.le_floor.mpr hbnd.2
      have hl : -n z ≤ N := Int.le_floor.mpr (by push_cast; linarith [hbnd.1])
      exact Finset.mem_Icc.mpr ⟨by omega, hu⟩
    have hcard : s.card ≤ (Finset.Icc (-N) N).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have hc : ((Finset.Icc (-N) N).card : ℝ) = 2*(N : ℝ)+1 := by
      have hh := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
      have hh' : ((Finset.Icc (-N) N).card : ℝ) = (N : ℝ)+1-(-N) := by
        exact_mod_cast hh
      linarith
    calc
      (s.card : ℝ) ≤ ((Finset.Icc (-N) N).card : ℝ) := by exact_mod_cast hcard
      _ = 2*(N : ℝ)+1 := hc
      _ ≤ 2*T+1 := by linarith [Int.floor_le T]
      _ = 1 + 6*H/((p : ℝ)*σ) := by dsimp [T]; ring
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    positivity

theorem integer_eq_of_box_residue {c : ℕ} {X : ℝ} {u v : ℤ}
    (hu : |(u : ℝ)| ≤ X) (hv : |(v : ℝ)| ≤ X)
    (hsmall : 2 * X < c) (hmod : (u : ZMod c) = v) : u = v := by
  have hm : ((u - v : ℤ) : ZMod c) = 0 := by
    simpa only [Int.cast_sub] using sub_eq_zero.mpr hmod
  have hdvd : (c : ℤ) ∣ u - v :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hm
  have hbound : |((u - v : ℤ) : ℝ)| < c := by
    push_cast
    exact (abs_sub (u : ℝ) (v : ℝ)).trans_lt (by linarith)
  apply sub_eq_zero.mp
  by_contra hne
  have hle := Int.le_abs_of_dvd hne hdvd
  have hleR : (c : ℝ) ≤ |((u - v : ℤ) : ℝ)| := by exact_mod_cast hle
  exact (not_le_of_gt hbound) hleR

theorem middle_box_first_projection_unique {c : ℕ} {t w : ℤ}
    {X Y : ℝ} (hYsmall : 2 * Y < c) (hw : IsUnit (w : ZMod c))
    {z z' : Coordinate} (hz : z ∈ middleLattice c t w)
    (hz' : z' ∈ middleLattice c t w)
    (hb : z ∈ literalBox X Y) (hb' : z' ∈ literalBox X Y)
    (hfirst : z.1 = z'.1) : z = z' := by
  have hm : (w : ZMod c) * (z.2 : ZMod c) =
      (w : ZMod c) * (z'.2 : ZMod c) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz'
    push_cast at h h'
    rw [hfirst] at h
    linear_combination h - h'
  exact Prod.ext hfirst
    (integer_eq_of_box_residue hb.2 hb'.2 hYsmall (hw.mul_left_cancel hm))

theorem unit_right_side_second_residue {A : Type*} [CommRing A]
    {g a t b d w v b' d' v' : A}
    (h : MinusEquations g a t b d w v)
    (h' : MinusEquations g a t b' d' w v')
    (hk : IsUnit (1 + g * t * w)) : b = b' := by
  have hproduct : (1 - g * t * a) * (1 - g * t * b) = 1 + g * t * w := by
    linear_combination -g * t * h.1
  have hfactor : IsUnit (1 - g * t * a) := by
    exact (IsUnit.mul_iff.mp (hproduct.symm ▸ hk)).1
  apply hfactor.mul_left_cancel
  linear_combination h.1 - h'.1

/-- In the retained original unit chart, fixing the first actual point fixes
the second. Residue uniqueness comes from the original word equation and its
unit right side; the two small physical widths lift it to an actual point. -/
theorem actual_first_endpoint_determines_second {c : ℕ} [NeZero c] {t w : ℤ}
    {X Y : ℝ} (hXsmall : 2 * X < c) (hYsmall : 2 * Y < c)
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (B : MiddleBasis c t w) (q : Coordinate)
    (hq : physical B.R B.V q = (-w, -t))
    (ht : IsUnit (t : ZMod c)) (hw : IsUnit (w : ZMod c))
    (hk : IsUnit (1 - a₁ * a₂ * (ht.unit : ZMod c) *
      ((physical B.R B.V q).1 : ZMod c)))
    (x y y' : Coordinate)
    (he : WordSolution c a₁ a₂ B.R B.V q (x, y))
    (he' : WordSolution c a₁ a₂ B.R B.V q (x, y'))
    (hy : physical B.R B.V y ∈ literalBox X Y)
    (hy' : physical B.R B.V y' ∈ literalBox X Y) : y = y' := by
  have hword : MinusEquations (a₁ * a₂)
      ((physical B.R B.V x).1 : ZMod c) (t : ZMod c)
      ((physical B.R B.V y).1 : ZMod c) ((physical B.R B.V x).2 : ZMod c)
      (w : ZMod c) ((physical B.R B.V y).2 : ZMod c) := by
    have h := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp he
    simpa [originalRows, hq] using h
  have hword' : MinusEquations (a₁ * a₂)
      ((physical B.R B.V x).1 : ZMod c) (t : ZMod c)
      ((physical B.R B.V y').1 : ZMod c) ((physical B.R B.V x).2 : ZMod c)
      (w : ZMod c) ((physical B.R B.V y').2 : ZMod c) := by
    have h := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp he'
    simpa [originalRows, hq] using h
  have hku : IsUnit (1 + (a₁ * a₂) * (t : ZMod c) * (w : ZMod c)) := by
    simpa only [ht.unit_spec, hq, Prod.fst, Int.cast_neg, mul_neg,
      sub_neg_eq_add] using hk
  have hmod : ((physical B.R B.V y).1 : ZMod c) =
      ((physical B.R B.V y').1 : ZMod c) :=
    unit_right_side_second_residue hword hword' hku
  have hfirst : (physical B.R B.V y).1 = (physical B.R B.V y').1 :=
    integer_eq_of_box_residue hy.1 hy'.1 hXsmall hmod
  apply B.coordinates_unique (Nat.pos_of_ne_zero (NeZero.ne c))
  exact middle_box_first_projection_unique hYsmall hw
    (B.physical_mem y) (B.physical_mem y') hy hy' hfirst

/-- A fixed first linear value costs its physical fiber weight only once in
the actual ordered partner count. The second endpoint is recovered from the
original word, rather than counted through an independent linear fiber. -/
theorem actual_linear_factor_partner_count {p : ℕ} (hp : p.Prime) {t w : ℤ}
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hXsmall : 2 * X < (p^3 : ℕ)) (hYsmall : 2 * Y < (p^3 : ℕ))
    (B : MiddleBasis (p^3) t w) (B₂ : ReducedMiddleBasis (p^2) t w X Y)
    (H : ℝ) (hH : 0 < H) (hHsq : H^2 = X*Y)
    (a b value : ℤ) (hab : Int.gcd a b = 1)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (q : Coordinate) (hq : physical B.R B.V q = (-w, -t))
    (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3)))
    (hk : IsUnit (1 - a₁ * a₂ * (ht.unit : ZMod (p^3)) *
      ((physical B.R B.V q).1 : ZMod (p^3))))
    (hroot : ((a * B.V.1 + b * B.R.1 : ℤ) : ZMod p) = 0)
    (s : Finset Endpoint)
    (hword : ∀ e ∈ s, WordSolution (p^3) a₁ a₂ B.R B.V q e)
    (hbox : ∀ e ∈ s, physical B.R B.V e.1 ∈ literalBox X Y ∧
      physical B.R B.V e.2 ∈ literalBox X Y)
    (hvalue : ∀ e ∈ s, a * e.1.1 - b * e.1.2 = value) :
    (s.card : ℝ) ≤ 1 + 6 * H /
      ((p : ℝ) * Real.sqrt (weightedSq X Y B₂.R)) := by
  classical
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hinj : Set.InjOn (Prod.fst : Endpoint → Coordinate) (s : Set Endpoint) := by
    intro e he e' he' hfirst
    apply Prod.ext hfirst
    apply actual_first_endpoint_determines_second hXsmall hYsmall
      a₁ a₂ ha₁ ha₂ B q hq ht hw hk e.1 e.2 e'.2 (hword e he)
    · simpa only [hfirst] using hword e' he'
    · exact (hbox e he).2
    · exact (hbox e' he').2
  let reduction : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hwp : IsUnit (w : ZMod p) := by
    simpa only [map_intCast] using hw.map reduction
  have hcount := actual_linear_factor_fiber_count hp hX hY B B₂ H hH hHsq
    a b value hab hwp hroot (s.image Prod.fst) (by
      intro z hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact (hbox e he).1) (by
      intro z hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact hvalue e he)
  simpa only [Finset.card_image_of_injOn hinj] using hcount

end

end D5.S3.Arith.CharacterSums.Original
