/- GID: D5/S3/Observer/CubicGain/JMJRootPair
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/JMJRootPair
   mirror-E: none(waiver:native-jmj-quadratic-root-worlds)
   anchors: [mathlib/module/Mathlib.Algebra.QuadraticDiscriminant]
   utility: none
   digest: Complete native JMJJ losing pairs are exactly the legal quadratic-root pair; every distinct actual JMJM pair fails three-step losing. -/
import D5.S3.Observer.CubicGain.JMJPairLosing
import Mathlib.Algebra.QuadraticDiscriminant
/-! Complete native pair classification at both actual fourth children of JMJ. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.CubicGain.JMJRootPair
open D5.S3.Observer.Linear.GainRay
open D5.S3.Observer.CubicGain.MixedTripleExclusion
open D5.S3.Observer.CubicGain.JMJPairLosing

def q (a B : ℝ) : ℝ := B^2 - (a+4/5)*B + 6/5*a-a^2
def discriminant (a : ℝ) : ℝ := 5*a^2-16/5*a+16/25
def lowerRoot (a : ℝ) : ℝ := (a+4/5-Real.sqrt (discriminant a))/2
def upperRoot (a : ℝ) : ℝ := (a+4/5+Real.sqrt (discriminant a))/2
def rootMatrix (a B : ℝ) : Mat := !![a, B;4/5-B, 6/5-a-B]
def rootScale (B : ℝ) : ℝ := 6/5-B

def RootData (a B : ℝ) : Prop := 0 < B ∧ B < 4/5 ∧ q a B = 0

private theorem root_eq_iff (a B : ℝ) : q a B = 0 ↔ B = upperRoot a ∨ B = lowerRoot a := by
  have hd : 0 < discriminant a := by
    dsimp [discriminant]
    nlinarith [sq_nonneg (a-8/25)]
  have hs := Real.sq_sqrt hd.le
  have hh := quadratic_eq_zero_iff (a := (1:ℝ)) (b := -(a+4/5))
    (c := 6/5*a-a^2) (by norm_num)
    (s := Real.sqrt (discriminant a)) (by
      dsimp [discrim, discriminant] at *
      nlinarith [hs]) B
  convert hh using 2 <;> dsimp [q, upperRoot, lowerRoot] <;> ring

private theorem root_bounds (a : ℝ) (ha : 0 < a ∧ a < 2/5) :
    RootData a (lowerRoot a) ∧ RootData a (upperRoot a) ∧ lowerRoot a < upperRoot a := by
  have hd : 0 < discriminant a := by
    dsimp [discriminant]
    nlinarith [sq_nonneg (a-8/25)]
  have hs := Real.sq_sqrt hd.le
  have hp := Real.sqrt_pos.2 hd
  have hs0 := Real.sqrt_nonneg (discriminant a)
  have hprod : 0 < a*(6/5-a) := mul_pos ha.1 (by linarith [ha.2])
  have hend : 0 < a*(2/5-a) := mul_pos ha.1 (by linarith [ha.2])
  have hl : Real.sqrt (discriminant a) < a+4/5 := by
    apply (Real.sqrt_lt' (by linarith [ha.1] : 0 < a+4/5)).2
    dsimp [discriminant]
    nlinarith
  have hu : Real.sqrt (discriminant a) < 4/5-a := by
    apply (Real.sqrt_lt' (by linarith [ha.2] : 0 < 4/5-a)).2
    dsimp [discriminant]
    nlinarith
  have hr := root_eq_iff a
  refine ⟨⟨?_, ?_, (hr _).2 (Or.inr rfl)⟩, ⟨?_, ?_, (hr _).2 (Or.inl rfl)⟩, ?_⟩
  all_goals dsimp [lowerRoot, upperRoot]; linarith

private theorem root_legal (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) :
    LegalSource ((rootScale B)⁻¹ • rootMatrix a B) := by
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have hs : 0 < rootScale B := by dsimp [rootScale]; linarith [hB.2.1]
  have hc : 0 < 4/5-B := by linarith [hB.2.1]
  have hq := hB.2.2
  dsimp [q] at hq
  have hden : 1 + ((4/5-B)/a)*(B/a) = rootScale B / a := by
    field_simp
    dsimp [rootScale]
    nlinarith
  have he : (rootScale B)⁻¹ • rootMatrix a B = sourceChart ((4/5-B)/a) (B/a) := by
    rw [sourceChart, hden]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootMatrix, Matrix.smul_apply, smul_eq_mul]
    all_goals field_simp
    all_goals dsimp [rootScale] at *; nlinarith
  rw [he]
  exact source_chart_legal _ _ (div_pos hc ha.1) (div_pos hB.1 ha.1)

/-- The whole coefficient vector is s times the coefficients of t(t-6)(t-7). -/
def rootWorld (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) : World3 where
  source := (rootScale B)⁻¹ • rootMatrix a B
  legal := root_legal a B ha hB
  coeff := ![0, 42*rootScale B, -13*rootScale B, rootScale B]
  nonzero := by
    intro h
    have hh := congrFun h 3
    have hs : 0 < rootScale B := by dsimp [rootScale]; linarith [hB.2.1]
    norm_num at hh
    linarith
  drift := 0

def lowerWorld (a : ℝ) (ha : 0 < a ∧ a < 2/5) : World3 :=
  rootWorld a (lowerRoot a) ha (root_bounds a ha).1

def upperWorld (a : ℝ) (ha : 0 < a ∧ a < 2/5) : World3 :=
  rootWorld a (upperRoot a) ha (root_bounds a ha).2.1

private theorem root_gain (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) (t : ℝ) :
    (gain 3 (rootWorld a B ha hB).coeff).eval t = rootScale B * (t*(t-6)*(t-7)) := by
  norm_num [gain, rootWorld, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ]
  ring

private theorem root_read (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B)
    (u : List Bool) (i : ℕ) :
    readAt (rootWorld a B ha hB) u i =
      ((i:ℝ)*((i:ℝ)-6)*((i:ℝ)-7))*Matrix.trace (acquisition (u.take i)*rootMatrix a B) := by
  have hs : rootScale B ≠ 0 := ne_of_gt (by dsimp [rootScale]; linarith [hB.2.1])
  rw [readAt, root_gain]
  simp only [rootWorld, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, add_zero]
  field_simp

private theorem root_history (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) :
    readings (rootWorld a B ha hB) [true, false, true, true] =
      ![0, 24, 48, 36*(a+4/5), 144/5] := by
  ext i
  change readAt (rootWorld a B ha hB) [true, false, true, true] i = _
  rw [root_read]
  fin_cases i <;>
    norm_num [acquisition, Raw, rootMatrix,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] <;> ring

private theorem root_fifth (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) (F : Bool) :
    readAt (rootWorld a B ha hB) [true, false, true, true, F] 5 =
      if F then 10*(a+4/5) else 20 := by
  rw [root_read]
  cases F <;>
    norm_num [acquisition, Raw, rootMatrix,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] <;> ring

/-- Both quadratic-root worlds are legal native worlds, realize the same actual
JMJJ child, remain distinct, and lose for three further original-clock actions. -/
theorem canonical_pair_losing (a : ℝ) (ha : 0 < a ∧ a < 2/5) :
    lowerWorld a ha ≠ upperWorld a ha ∧
    readings (lowerWorld a ha) [true, false, true, true] = ![0, 24, 48, 36*(a+4/5), 144/5] ∧
    readings (upperWorld a ha) [true, false, true, true] = ![0, 24, 48, 36*(a+4/5), 144/5] ∧
    Losing 3 {lowerWorld a ha, upperWorld a ha} [true, false, true, true] := by
  have hne : lowerWorld a ha ≠ upperWorld a ha := by
    intro h
    have hh := congrArg (fun W : World3 => W.coeff 3) h
    change rootScale (lowerRoot a) = rootScale (upperRoot a) at hh
    have hl := (root_bounds a ha).2.2
    dsimp [rootScale] at hh
    linarith
  have hl := root_history a (lowerRoot a) ha (root_bounds a ha).1
  have hu := root_history a (upperRoot a) ha (root_bounds a ha).2.1
  refine ⟨hne, hl, hu, ?_⟩
  apply (jmj_pair_losing_iff 3 (by omega) true (36*(a+4/5)) (144/5) _ _ hne hl hu).2
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj hjn
    interval_cases j <;> simp [lowerWorld, upperWorld, root_gain]
  · intro F
    simp only [lowerWorld, upperWorld, root_fifth]

private def g (W : World3) (t : ℝ) : ℝ := (gain 3 W.coeff).eval t
private def j (W : World3) : ℝ := W.source 0 1 + W.source 1 0
private def ell (W : World3) : ℝ := 1 + W.source 0 1
private def tor (W : World3) : ℝ := W.source 0 0 + j W

private theorem trace_one (W : World3) : W.source 0 0 + W.source 1 1 = 1 := by
  simpa [Matrix.trace, Fin.sum_univ_two] using W.legal.2.2

private theorem source_positive (W : World3) : 0 < j W ∧ 0 < ell W ∧ 0 < tor W := by
  have h00 := W.legal.1 0 0
  have h01 := W.legal.1 0 1
  have h10 := W.legal.1 1 0
  dsimp [j, ell, tor]
  exact ⟨by positivity, by positivity, by positivity⟩

private theorem history_rows (W : World3) (E : Bool) (z v : ℝ)
    (hW : readings W [true, false, true, E] = ![0, 24, 48, z, v]) :
    g W 0 + W.drift = 0 ∧ g W 1 * j W + W.drift = 24 ∧
    g W 2 * ell W + W.drift = 48 ∧ g W 3 * tor W + W.drift = z ∧
    g W 4 * (if E then ell W else 2*ell W-1) + W.drift = v := by
  have ht := trace_one W
  have ht1 : W.source 1 1 = 1-W.source 0 0 := by linarith
  have h0 := congrFun hW (0:Fin 5)
  have h1 := congrFun hW (1:Fin 5)
  have h2 := congrFun hW (2:Fin 5)
  have h3 := congrFun hW (3:Fin 5)
  have h4 := congrFun hW (4:Fin 5)
  cases E <;>
    norm_num [readings, readAt, acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] at h0 h1 h2 h3 h4
  all_goals
    simp only [ht1] at h0 h1 h2 h3 h4
    dsimp [g, j, ell, tor]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

private theorem fifth_read (W : World3) (E F : Bool) :
    readAt W [true, false, true, E, F] 5 = g W 5 *
      (if E then (if F then tor W else j W+ell W)
       else (if F then 2*tor W-j W else tor W+2*ell W-1)) + W.drift := by
  have ht := trace_one W
  have ht1 : W.source 1 1 = 1-W.source 0 0 := by linarith
  cases E <;> cases F <;>
    norm_num [readAt, acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, g, j, ell, tor] <;> (try simp only [ht1]) <;> (first | (left; ring) | ring)

private theorem eval_coeff (W : World3) (t : ℝ) :
    g W t = W.coeff 0 + W.coeff 1*t+W.coeff 2*t^2+W.coeff 3*t^3 := by
  norm_num [g, gain, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ]
  ring

private theorem gain_form (W : World3) (h0 : g W 0 + W.drift = 0)
    (h6 : g W 6 = 0) (h7 : g W 7 = 0) (t : ℝ) :
    g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42) := by
  rw [eval_coeff] at h0 h6 h7 ⊢
  norm_num at h0 h6 h7
  have hc1 : W.coeff 1 = 42*W.coeff 3+13*W.drift/42 := by linarith
  have hc2 : W.coeff 2 = -13*W.coeff 3-W.drift/42 := by linarith
  rw [hc1, hc2]
  have hc0 : W.coeff 0 = -W.drift := by linarith
  rw [hc0]
  ring

private theorem coeff_eq (W Z : World3) (hd : W.drift = Z.drift)
    (hβ : W.coeff 3 = Z.coeff 3)
    (hfW : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42))
    (hfZ : ∀ t : ℝ, g Z t = (t-6)*(t-7)*(Z.coeff 3*t-Z.drift/42)) :
    W.coeff = Z.coeff := by
  apply four_evaluations W.coeff Z.coeff (fun i : Fin 4 => (i.val:ℝ))
  · intro i k h
    exact Fin.ext (Nat.cast_injective h)
  · intro i
    change g W _ = g Z _
    rw [hfW, hfZ, hd, hβ]

private theorem world_eq (W Z : World3) (hp : W.source = Z.source)
    (hc : W.coeff = Z.coeff) (hd : W.drift = Z.drift) : W = Z := by
  cases W
  cases Z
  cases hp
  cases hc
  cases hd
  rfl

private theorem source_eq (W Z : World3) (hj : j W = j Z) (hl : ell W = ell Z)
    (ht : tor W = tor Z) : W.source = Z.source := by
  have hW := trace_one W
  have hZ := trace_one Z
  dsimp [j, ell, tor] at hj hl ht
  ext i k
  fin_cases i <;> fin_cases k <;> dsimp <;> linarith

private theorem leading_distinct (W Z : World3) (E : Bool) (z v : ℝ)
    (hne : W ≠ Z) (hd : W.drift = Z.drift)
    (hW : readings W [true, false, true, E] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, E] = ![0, 24, 48, z, v])
    (hfW : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42))
    (hfZ : ∀ t : ℝ, g Z t = (t-6)*(t-7)*(Z.coeff 3*t-Z.drift/42))
    (he : ∀ F : Bool, readAt W [true, false, true, E, F] 5 = readAt Z [true, false, true, E, F] 5) :
    W.coeff 3 ≠ Z.coeff 3 := by
  intro hβ
  have hc := coeff_eq W Z hd hβ hfW hfZ
  have hg (t : ℝ) : g W t = g Z t := by simp [g, hc]
  obtain ⟨hW0, hW1, hW2, hW3, hW4⟩ := history_rows W E z v hW
  obtain ⟨hZ0, hZ1, hZ2, hZ3, hZ4⟩ := history_rows Z E z v hZ
  have hnon : ∀ (t u : ℝ), t ≠ u → t ≠ 6 → t ≠ 7 → u ≠ 6 → u ≠ 7 →
      ¬ (g W t = 0 ∧ g W u = 0) := by
    intro t u htu ht6 ht7 hu6 hu7 ⟨ht, hu⟩
    rw [hfW] at ht hu
    have htβ : W.coeff 3*t-W.drift/42 = 0 :=
      (mul_eq_zero.mp ht).resolve_left (mul_ne_zero (sub_ne_zero.mpr ht6) (sub_ne_zero.mpr ht7))
    have huβ : W.coeff 3*u-W.drift/42 = 0 :=
      (mul_eq_zero.mp hu).resolve_left (mul_ne_zero (sub_ne_zero.mpr hu6) (sub_ne_zero.mpr hu7))
    have hh : W.coeff 3*(t-u) = 0 := by nlinarith
    have hβ0 : W.coeff 3 = 0 := (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr htu)
    have hd0 : W.drift = 0 := by rw [hβ0] at htβ; linarith
    apply W.nonzero
    apply four_evaluations W.coeff 0 (fun i : Fin 4 => (i.val:ℝ))
    · intro i k h
      exact Fin.ext (Nat.cast_injective h)
    · intro i
      change g W _ = (gain 3 0).eval _
      rw [hfW, hβ0, hd0]
      simp [gain, Polynomial.ofFn_eq_sum_monomial]
  have hl : ell W = ell Z := by
    by_cases h2 : g W 2 = 0
    · have h4 : g W 4 ≠ 0 := by
        intro hh
        exact hnon 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨h2, hh⟩
      have hh : g W 4*(if E then ell W else 2*ell W-1) =
          g W 4*(if E then ell Z else 2*ell Z-1) := by rw [← hg 4, ← hd] at hZ4; linarith
      have hh := mul_left_cancel₀ h4 hh
      cases E <;> simp at hh <;> linarith
    · have hh : g W 2*ell W = g W 2*ell Z := by rw [← hg 2, ← hd] at hZ2; linarith
      exact mul_left_cancel₀ h2 hh
  have hjt : j W = j Z ∧ tor W = tor Z := by
    by_cases h5 : g W 5 = 0
    · have h1 : g W 1 ≠ 0 := by
        intro hh
        exact hnon 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh, h5⟩
      have h3 : g W 3 ≠ 0 := by
        intro hh
        exact hnon 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨hh, h5⟩
      rw [← hg 1, ← hd] at hZ1
      rw [← hg 3, ← hd] at hZ3
      exact ⟨mul_left_cancel₀ h1 (by linarith), mul_left_cancel₀ h3 (by linarith)⟩
    · have hJ := he true
      have hM := he false
      simp only [fifth_read, ← hg 5, ← hd] at hJ hM
      have hJ := mul_left_cancel₀ h5 (add_right_cancel hJ)
      have hM := mul_left_cancel₀ h5 (add_right_cancel hM)
      cases E <;> simp at hJ hM <;> constructor <;> linarith
  exact hne (world_eq W Z (source_eq W Z hjt.1 hl hjt.2) hc hd)

private theorem losing_constraints (W Z : World3) (E : Bool) (z v : ℝ)
    (hne : W ≠ Z)
    (hW : readings W [true, false, true, E] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, E] = ![0, 24, 48, z, v])
    (hl : Losing 3 {W, Z} [true, false, true, E]) :
    W.drift = Z.drift ∧ W.coeff 3 ≠ Z.coeff 3 ∧
    (∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42)) ∧
    (∀ t : ℝ, g Z t = (t-6)*(t-7)*(Z.coeff 3*t-Z.drift/42)) ∧
    (∀ F : Bool, readAt W [true, false, true, E, F] 5 = readAt Z [true, false, true, E, F] 5) := by
  obtain ⟨hd, hroots, he⟩ := (jmj_pair_losing_iff 3 (by omega) E z v W Z hne hW hZ).1 hl
  have h6 := hroots 2 (by omega) (by omega)
  have h7 := hroots 3 (by omega) (by omega)
  have hfW := gain_form W (history_rows W E z v hW).1 h6.1 h7.1
  have hfZ := gain_form Z (history_rows Z E z v hZ).1 h6.2 h7.2
  exact ⟨hd, leading_distinct W Z E z v hne hd hW hZ hfW hfZ he, hfW, hfZ, he⟩

private theorem early_nonzero (W Z : World3) (E : Bool) (z v : ℝ)
    (hd : W.drift = Z.drift) (hb : W.coeff 3 ≠ Z.coeff 3)
    (hW : readings W [true, false, true, E] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, E] = ![0, 24, 48, z, v])
    (hfW : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42))
    (hfZ : ∀ t : ℝ, g Z t = (t-6)*(t-7)*(Z.coeff 3*t-Z.drift/42)) :
    g W 1 ≠ 0 ∧ g W 2 ≠ 0 ∧ g W 3 ≠ 0 := by
  obtain ⟨_, hW1, hW2, hW3, _⟩ := history_rows W E z v hW
  obtain ⟨_, hZ1, hZ2, hZ3, _⟩ := history_rows Z E z v hZ
  obtain ⟨hj, hl, ht⟩ := source_positive Z
  rw [← hd] at hZ1 hZ2 hZ3
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h] at hW1
    have hz : g Z 1 = 0 := (mul_eq_zero.mp (by nlinarith : g Z 1*j Z=0)).resolve_right (ne_of_gt hj)
    have hwf := hfW 1
    have hzf := hfZ 1
    rw [h] at hwf
    rw [hz, ← hd] at hzf
    apply hb
    nlinarith
  · intro h
    rw [h] at hW2
    have hz : g Z 2 = 0 := (mul_eq_zero.mp (by nlinarith : g Z 2*ell Z=0)).resolve_right (ne_of_gt hl)
    have hwf := hfW 2
    have hzf := hfZ 2
    rw [h] at hwf
    rw [hz, ← hd] at hzf
    apply hb
    nlinarith
  · intro h
    rw [h] at hW3
    have hz : g Z 3 = 0 := (mul_eq_zero.mp (by nlinarith : g Z 3*tor Z=0)).resolve_right (ne_of_gt ht)
    have hwf := hfW 3
    have hzf := hfZ 3
    rw [h] at hwf
    rw [hz, ← hd] at hzf
    apply hb
    nlinarith

private theorem j_drift_zero (W Z : World3) (z v : ℝ)
    (hd : W.drift = Z.drift) (hb : W.coeff 3 ≠ Z.coeff 3)
    (hW : readings W [true, false, true, true] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, true] = ![0, 24, 48, z, v])
    (hfW : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42))
    (hfZ : ∀ t : ℝ, g Z t = (t-6)*(t-7)*(Z.coeff 3*t-Z.drift/42)) : W.drift = 0 := by
  have hnW := early_nonzero W Z true z v hd hb hW hZ hfW hfZ
  have hnZ := early_nonzero Z W true z v hd.symm (Ne.symm hb) hZ hW hfZ hfW
  obtain ⟨_, _, hW2, _, hW4⟩ := history_rows W true z v hW
  obtain ⟨_, _, hZ2, _, hZ4⟩ := history_rows Z true z v hZ
  simp only [ite_true] at hW4 hZ4
  rw [← hd] at hZ2 hZ4
  have hD : 48-W.drift ≠ 0 := by
    intro h
    have hh : g W 2*ell W=0 := by linarith
    exact (mul_ne_zero hnW.2.1 (ne_of_gt (source_positive W).2.1)) hh
  have hrW : g W 4/g W 2 = (v-W.drift)/(48-W.drift) := by
    apply (div_eq_div_iff hnW.2.1 hD).2
    linear_combination g W 2*hW4-g W 4*hW2
  have hrZ : g Z 4/g Z 2 = (v-W.drift)/(48-W.drift) := by
    apply (div_eq_div_iff hnZ.2.1 hD).2
    linear_combination g Z 2*hZ4-g Z 4*hZ2
  have hc := (div_eq_div_iff hnW.2.1 hnZ.2.1).1 (hrW.trans hrZ.symm)
  rw [hfW, hfZ, hfW, hfZ, ← hd] at hc
  have hh : W.drift*(W.coeff 3-Z.coeff 3)=0 := by nlinarith
  exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hb)

private theorem j_world_shape (W : World3) (z v : ℝ)
    (hW : readings W [true, false, true, true] = ![0, 24, 48, z, v])
    (hd : W.drift = 0)
    (hf : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42)) :
    0 < W.coeff 3 ∧ v = 144/5 ∧
    W.coeff 3 • W.source = rootMatrix (z/36-4/5) (W.coeff 3*W.source 0 1) ∧
    W.coeff 3 = rootScale (W.coeff 3*W.source 0 1) ∧
    q (z/36-4/5) (W.coeff 3*W.source 0 1) = 0 := by
  obtain ⟨_, h1, h2, h3, h4⟩ := history_rows W true z v hW
  simp only [ite_true] at h4
  rw [hf, hd] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  have hj := (source_positive W).1
  have hb : 0 < W.coeff 3 := by nlinarith
  have ht := trace_one W
  dsimp [j, ell, tor] at h1 h2 h3 h4
  have he : W.coeff 3 • W.source = rootMatrix (z/36-4/5) (W.coeff 3*W.source 0 1) := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [rootMatrix, Matrix.smul_apply, smul_eq_mul] <;> nlinarith [ht]
  have hs : W.coeff 3 = rootScale (W.coeff 3*W.source 0 1) := by
    dsimp [rootScale]
    nlinarith
  have hdet : W.source.det = 0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    rw [W.legal.2.1] at hr
    norm_num at hr
  have hdR : (W.coeff 3 • W.source).det = 0 := by rw [Matrix.det_smul, hdet, mul_zero]
  rw [he] at hdR
  have hq : q (z/36-4/5) (W.coeff 3*W.source 0 1)=0 := by
    simp [rootMatrix, Matrix.det_fin_two] at hdR
    dsimp [q]
    nlinarith [hdR]
  exact ⟨hb, by nlinarith, he, hs, hq⟩

private theorem positive_coordinates (W : World3) (a B β : ℝ) (hb : 0 < β)
    (he : β • W.source = rootMatrix a B) : 0 < a ∧ 0 < B ∧ B < 4/5 := by
  have h00 := congrFun (congrFun he 0) 0
  have h01 := congrFun (congrFun he 0) 1
  have h10 := congrFun (congrFun he 1) 0
  simp [rootMatrix, Matrix.smul_apply, smul_eq_mul] at h00 h01 h10
  exact ⟨by nlinarith [mul_pos hb (W.legal.1 0 0)],
    by nlinarith [mul_pos hb (W.legal.1 0 1)],
    by nlinarith [mul_pos hb (W.legal.1 1 0)]⟩

private theorem two_roots_interval (a B C : ℝ) (ha : 0 < a)
    (hB : B < 4/5) (hC : C < 4/5) (hne : B ≠ C) (hqB : q a B=0) (hqC : q a C=0) :
    a < 2/5 := by
  dsimp [q] at hqB hqC
  have hsum0 : (B-C)*(B+C-a-4/5)=0 := by nlinarith
  have hsum : B+C=a+4/5 := by
    have hh := (mul_eq_zero.mp hsum0).resolve_left (sub_ne_zero.mpr hne)
    linarith
  have hprod : B*C=6/5*a-a^2 := by nlinarith
  have hend := mul_pos (show 0 < 4/5-B by linarith) (show 0 < 4/5-C by linarith)
  nlinarith

private theorem shape_world (W : World3) (a B : ℝ) (ha : 0 < a ∧ a < 2/5)
    (hB : RootData a B) (hb : 0 < W.coeff 3)
    (he : W.coeff 3 • W.source = rootMatrix a B)
    (hs : W.coeff 3 = rootScale B) (hd : W.drift = 0)
    (hf : ∀ t : ℝ, g W t = (t-6)*(t-7)*(W.coeff 3*t-W.drift/42)) :
    W = rootWorld a B ha hB := by
  apply world_eq
  · change W.source = (rootScale B)⁻¹ • rootMatrix a B
    rw [← he, ← hs, smul_smul, inv_mul_cancel₀ (ne_of_gt hb), one_smul]
  · apply four_evaluations W.coeff (rootWorld a B ha hB).coeff (fun i : Fin 4 => (i.val:ℝ))
    · intro i k h
      exact Fin.ext (Nat.cast_injective h)
    · intro i
      change g W _ = _
      rw [hf, root_gain, hd, hs]
      ring
  · exact hd

private theorem interval_parameter (z : ℝ) (hz : 144/5 < z ∧ z < 216/5) :
    0 < z/36-4/5 ∧ z/36-4/5 < 2/5 := by constructor <;> linarith [hz.1, hz.2]

/-- The unordered pair from the two roots in (20.6), indexed by the original third reading. -/
def canonicalPair (z : ℝ) (hz : 144/5 < z ∧ z < 216/5) : Finset World3 :=
  {lowerWorld (z/36-4/5) (interval_parameter z hz), upperWorld (z/36-4/5) (interval_parameter z hz)}

/-- All distinct complete worlds in the actual JMJJ child are classified;
source distinction, zero drift and the gain ray are conclusions. -/
theorem jmjj_pair_losing_iff (z v : ℝ) (W Z : World3) (hne : W ≠ Z)
    (hW : readings W [true, false, true, true] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, true] = ![0, 24, 48, z, v]) :
    Losing 3 {W, Z} [true, false, true, true] ↔
      ∃ hz : 144/5 < z ∧ z < 216/5, v = 144/5 ∧ {W, Z} = canonicalPair z hz := by
  constructor
  · intro hl
    obtain ⟨hd, hb, hfW, hfZ, _⟩ := losing_constraints W Z true z v hne hW hZ hl
    have hdW := j_drift_zero W Z z v hd hb hW hZ hfW hfZ
    have hdZ : Z.drift=0 := hd.symm.trans hdW
    obtain ⟨hbW, hv, heW, hsW, hqW⟩ := j_world_shape W z v hW hdW hfW
    obtain ⟨hbZ, _, heZ, hsZ, hqZ⟩ := j_world_shape Z z v hZ hdZ hfZ
    obtain ⟨ha, hB, hBu⟩ := positive_coordinates W _ _ _ hbW heW
    obtain ⟨_, hC, hCu⟩ := positive_coordinates Z _ _ _ hbZ heZ
    have hBC : W.coeff 3*W.source 0 1 ≠ Z.coeff 3*Z.source 0 1 := by
      intro hh
      rw [hh] at hsW
      exact hb (hsW.trans hsZ.symm)
    have hau := two_roots_interval _ _ _ ha hBu hCu hBC hqW hqZ
    have hz : 144/5 < z ∧ z < 216/5 := by constructor <;> linarith
    let haI := interval_parameter z hz
    have hw : W = lowerWorld (z/36-4/5) haI ∨ W = upperWorld (z/36-4/5) haI := by
      have hh := shape_world W _ _ haI ⟨hB, hBu, hqW⟩ hbW heW hsW hdW hfW
      rcases (root_eq_iff _ _).1 hqW with h | h
      · exact Or.inr (by simpa [upperWorld, h] using hh)
      · exact Or.inl (by simpa [lowerWorld, h] using hh)
    have hzW : Z = lowerWorld (z/36-4/5) haI ∨ Z = upperWorld (z/36-4/5) haI := by
      have hh := shape_world Z _ _ haI ⟨hC, hCu, hqZ⟩ hbZ heZ hsZ hdZ hfZ
      rcases (root_eq_iff _ _).1 hqZ with h | h
      · exact Or.inr (by simpa [upperWorld, h] using hh)
      · exact Or.inl (by simpa [lowerWorld, h] using hh)
    refine ⟨hz, hv, ?_⟩
    rcases hw with hw | hw <;> rcases hzW with hzW | hzW
    · exact (hne (hw.trans hzW.symm)).elim
    · simp [canonicalPair, hw, hzW, haI]
    · simp [canonicalPair, hw, hzW, haI, Finset.pair_comm]
    · exact (hne (hw.trans hzW.symm)).elim
  · rintro ⟨hz, _, he⟩
    rw [he]
    exact (canonical_pair_losing _ (interval_parameter z hz)).2.2.2

private theorem common_positive_product (x y A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hx : x ≠ 0) (hxA : x*A=C) (hyB : y*B=C) : 0 < x*y := by
  have hC : C ≠ 0 := by rw [← hxA]; exact mul_ne_zero hx (ne_of_gt hA)
  apply (mul_pos_iff_of_pos_right (mul_pos hA hB)).1
  calc
    0 < C*C := mul_self_pos.mpr hC
    _ = (x*A)*(y*B) := congrArg₂ (·*·) hxA.symm hyB.symm
    _ = (x*y)*(A*B) := by ring

private theorem m_numeric_impossible (d z x y : ℝ) (hne : x ≠ y)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h1x : 3/4*x-5*d/14 ≠ 0) (h1y : 3/4*y-5*d/14 ≠ 0)
    (h3x : 9/10*x+d/7 ≠ 0) (h3y : 9/10*y+d/7 ≠ 0)
    (hp : 0 < x*y) (hT : 0 < (3/4*x-5*d/14)*(3/4*y-5*d/14))
    (h4 : (3/5*x+d/7)*(2*(48-d)/x-1) = (3/5*y+d/7)*(2*(48-d)/y-1))
    (hJ : (x/4+d/14)*(2*(z-d)/(9/10*x+d/7)-(24-d)/(3/4*x-5*d/14)) =
      (y/4+d/14)*(2*(z-d)/(9/10*y+d/7)-(24-d)/(3/4*y-5*d/14)))
    (hM : (x/4+d/14)*((z-d)/(9/10*x+d/7)+2*(48-d)/x-1) =
      (y/4+d/14)*((z-d)/(9/10*y+d/7)+2*(48-d)/y-1)) : False := by
  have hxy : x-y ≠ 0 := sub_ne_zero.mpr hne
  have e4 : (3/5*x+d/7)*(2*(48-d)/x-1)-(3/5*y+d/7)*(2*(48-d)/y-1) =
      (x-y)*(-3/5-2*(d*(48-d)/(7*(x*y)))) := by field_simp [hx,hy]; ring
  have eJ : (x/4+d/14)*(2*(z-d)/(9/10*x+d/7)-(24-d)/(3/4*x-5*d/14)) -
      (y/4+d/14)*(2*(z-d)/(9/10*y+d/7)-(24-d)/(3/4*y-5*d/14)) =
      (x-y)*(-2*(d*(z-d)/(35*((9/10*x+d/7)*(9/10*y+d/7))))+
        d*(24-d)/(7*((3/4*x-5*d/14)*(3/4*y-5*d/14)))) := by
    generalize hA : (3/4*x-5*d/14)=A at h1x ⊢
    generalize hB : (3/4*y-5*d/14)=B at h1y ⊢
    generalize hC : (9/10*x+d/7)=C at h3x ⊢
    generalize hD : (9/10*y+d/7)=D at h3y ⊢
    field_simp [h1x,h1y,h3x,h3y]
    simp only [← hA,← hB,← hC,← hD]
    ring
  have eM : (x/4+d/14)*((z-d)/(9/10*x+d/7)+2*(48-d)/x-1) -
      (y/4+d/14)*((z-d)/(9/10*y+d/7)+2*(48-d)/y-1) =
      (x-y)*(-d*(z-d)/(35*((9/10*x+d/7)*(9/10*y+d/7)))-
        d*(48-d)/(7*(x*y))-1/4) := by
    generalize hC : (9/10*x+d/7)=C at h3x ⊢
    generalize hD : (9/10*y+d/7)=D at h3y ⊢
    field_simp [hx,hy,h3x,h3y]
    simp only [← hC,← hD]
    ring
  rw [sub_eq_zero.mpr h4] at e4
  rw [sub_eq_zero.mpr hJ] at eJ
  rw [sub_eq_zero.mpr hM] at eM
  have c4 := (mul_eq_zero.mp e4.symm).resolve_left hxy
  have cJ := (mul_eq_zero.mp eJ.symm).resolve_left hxy
  have cM := (mul_eq_zero.mp eM.symm).resolve_left hxy
  simp only [neg_mul,neg_div] at cM
  have hV : d*(48-d)/(7*(x*y)) = -3/10 := by linarith
  have hU : d*(z-d)/(35*((9/10*x+d/7)*(9/10*y+d/7)))=1/20 := by linarith
  have hR : d*(24-d)/(7*((3/4*x-5*d/14)*(3/4*y-5*d/14)))=1/10 := by linarith
  have hπ := (div_eq_iff (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<7) hp))).1 hV
  have hT1 := (div_eq_iff (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<7) hT))).1 hR
  have hdcase : d < 0 ∨ 48 < d := by
    by_cases hd : d < 0
    · exact Or.inl hd
    · right
      have hd0 : 0 ≤ d := le_of_not_gt hd
      by_contra hh
      have hd48 : d ≤ 48 := le_of_not_gt hh
      have hn := mul_nonneg hd0 (show 0 ≤ 48-d by linarith)
      nlinarith
  have hsign : d*(24-d)<0 := by
    rcases hdcase with hd | hd
    · exact mul_neg_of_neg_of_pos hd (by linarith)
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  nlinarith

set_option maxHeartbeats 800000 in
/-- No distinct complete native pair in an actual fourth M child of JMJ loses
for three additional actions, including arbitrary drift, signs and zero samples. -/
theorem jmjm_pair_not_losing (z v : ℝ) (W Z : World3) (hne : W ≠ Z)
    (hW : readings W [true, false, true, false] = ![0, 24, 48, z, v])
    (hZ : readings Z [true, false, true, false] = ![0, 24, 48, z, v]) :
    ¬ Losing 3 {W, Z} [true, false, true, false] := by
  intro hl
  obtain ⟨hd, hb, hfW, hfZ, he⟩ := losing_constraints W Z false z v hne hW hZ hl
  have hnW := early_nonzero W Z false z v hd hb hW hZ hfW hfZ
  have hnZ := early_nonzero Z W false z v hd.symm (Ne.symm hb) hZ hW hfZ hfW
  obtain ⟨_, hW1, hW2, hW3, hW4⟩ := history_rows W false z v hW
  obtain ⟨_, hZ1, hZ2, hZ3, hZ4⟩ := history_rows Z false z v hZ
  rw [← hd] at hZ1 hZ2 hZ3 hZ4
  have fW1 : g W 1=3/4*g W 2-5*W.drift/14 := by have h1:=hfW 1; have h2:=hfW 2; nlinarith only [h1,h2]
  have fW3 : g W 3=9/10*g W 2+W.drift/7 := by have h3:=hfW 3; have h2:=hfW 2; nlinarith only [h3,h2]
  have fW4 : g W 4=3/5*g W 2+W.drift/7 := by have h4:=hfW 4; have h2:=hfW 2; nlinarith only [h4,h2]
  have fW5 : g W 5=g W 2/4+W.drift/14 := by have h5:=hfW 5; have h2:=hfW 2; nlinarith only [h5,h2]
  have fZ1 : g Z 1=3/4*g Z 2-5*W.drift/14 := by have h1:=hfZ 1; have h2:=hfZ 2; rw [← hd] at h1 h2; nlinarith only [h1,h2]
  have fZ3 : g Z 3=9/10*g Z 2+W.drift/7 := by have h3:=hfZ 3; have h2:=hfZ 2; rw [← hd] at h3 h2; nlinarith only [h3,h2]
  have fZ4 : g Z 4=3/5*g Z 2+W.drift/7 := by have h4:=hfZ 4; have h2:=hfZ 2; rw [← hd] at h4 h2; nlinarith only [h4,h2]
  have fZ5 : g Z 5=g Z 2/4+W.drift/14 := by have h5:=hfZ 5; have h2:=hfZ 2; rw [← hd] at h5 h2; nlinarith only [h5,h2]
  have hxy : g W 2 ≠ g Z 2 := by
    intro hh
    have hw := hfW 2
    have hz := hfZ 2
    rw [← hd, ← hh] at hz
    apply hb
    nlinarith only [hw,hz]
  have jW : j W=(24-W.drift)/g W 1 := (eq_div_iff hnW.1).2 (by linarith only [hW1])
  have lW : ell W=(48-W.drift)/g W 2 := (eq_div_iff hnW.2.1).2 (by linarith only [hW2])
  have tW : tor W=(z-W.drift)/g W 3 := (eq_div_iff hnW.2.2).2 (by linarith only [hW3])
  have jZ : j Z=(24-W.drift)/g Z 1 := (eq_div_iff hnZ.1).2 (by linarith only [hZ1])
  have lZ : ell Z=(48-W.drift)/g Z 2 := (eq_div_iff hnZ.2.1).2 (by linarith only [hZ2])
  have tZ : tor Z=(z-W.drift)/g Z 3 := (eq_div_iff hnZ.2.2).2 (by linarith only [hZ3])
  have hp := common_positive_product _ _ _ _ _ (source_positive W).2.1 (source_positive Z).2.1 hnW.2.1
    (show g W 2*ell W=48-W.drift by linarith only [hW2]) (show g Z 2*ell Z=48-W.drift by linarith only [hZ2])
  have hT := common_positive_product _ _ _ _ _ (source_positive W).1 (source_positive Z).1 hnW.1
    (show g W 1*j W=24-W.drift by linarith only [hW1]) (show g Z 1*j Z=24-W.drift by linarith only [hZ1])
  have hJ := he true
  have hM := he false
  simp only [fifth_read, Bool.false_eq_true, if_false, if_true, ← hd] at hJ hM
  simp only [Bool.false_eq_true, if_false] at hW4 hZ4
  have h4 : g W 4*(2*ell W-1)=g Z 4*(2*ell Z-1) := by linarith only [hW4,hZ4]
  rw [fW4, fZ4, lW, lZ] at h4
  have hJ0 := add_right_cancel hJ
  have hM0 := add_right_cancel hM
  rw [fW5, fZ5, tW, tZ, jW, jZ, fW3, fZ3, fW1, fZ1] at hJ0
  rw [fW5, fZ5, tW, tZ, lW, lZ, fW3, fZ3] at hM0
  apply m_numeric_impossible W.drift z (g W 2) (g Z 2) hxy hnW.2.1 hnZ.2.1
    (by simpa only [← fW1] using hnW.1) (by simpa only [← fZ1] using hnZ.1)
    (by simpa only [← fW3] using hnW.2.2) (by simpa only [← fZ3] using hnZ.2.2) hp
    (by simpa only [← fW1, ← fZ1] using hT) (by convert h4 using 1 <;> ring)
  · convert hJ0 using 1 <;> ring
  · convert hM0 using 1 <;> ring

end D5.S3.Observer.CubicGain.JMJRootPair
