/- GID: D5/S3/Entropy/ProductAbsorptionLogKernel
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductAbsorptionLogKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single crossing of the exact logarithmic kernel for binary product absorption. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Entropy.ProductAbsorptionLogKernel
open Set Filter
open scoped Topology

/-- The five-term logarithmic kernel, with the two quadratic roots kept explicitly.
The later entropy integral uses this kernel with a decreasing positive weight. -/
def productLogKernel (u v s : ℝ) : ℝ :=
  let A := u + v
  let B := u * v
  let L := A - B
  let q := Real.sqrt (B * (1 - A + B))
  Real.log (1 + u / s) + Real.log (1 + v / s) - 2 * Real.log (1 + L / s) +
    (Real.log (1 + (A - 2 * B + 2 * q) / s) +
      Real.log (1 + (A - 2 * B - 2 * q) / s)) / 2

private def c4 (A B : ℝ) : ℝ := 2 * B * (2 * A - 3 * B - 1)
private def c3 (A B : ℝ) : ℝ := 2 * B * (4 * A ^ 2 - 6 * A * B - A + 2 * B ^ 2 - 4 * B)
private def c2 (A B : ℝ) : ℝ :=
  B * (4 * A ^ 3 - 6 * A ^ 2 * B + 2 * A ^ 2 + 4 * A * B ^ 2 -
    8 * A * B - B ^ 3 - 7 * B)
private def c1 (A B : ℝ) : ℝ := 2 * B * (A ^ 3 - 3 * A * B - 2 * B ^ 2)
private def c0 (A B : ℝ) : ℝ := B ^ 2 * (A ^ 2 - 4 * B)
private def poly (A B s : ℝ) : ℝ :=
  c4 A B * s ^ 4 + c3 A B * s ^ 3 + c2 A B * s ^ 2 + c1 A B * s + c0 A B

private lemma expansion (A B s : ℝ) :
    (s ^ 2 + A * s + B) ^ 2 * (s ^ 2 + 2 * (A - 2 * B) * s + A ^ 2 - 4 * B) -
      s ^ 2 * (s + A - B) ^ 4 = poly A B s := by
  dsimp [poly, c4, c3, c2, c1, c0]
  ring

private lemma coefficient_signs {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ c0 (u + v) (u * v) ∧ 0 < c1 (u + v) (u * v) ∧
    0 < c2 (u + v) (u * v) ∧
    (0 ≤ c4 (u + v) (u * v) → 0 ≤ c3 (u + v) (u * v)) := by
  let A := u + v
  let B := u * v
  let w := Real.sqrt B
  have hB : 0 < B := mul_pos hu.1 hv.1
  have hB1 : B < 1 := by
    exact (mul_lt_mul_of_pos_left hv.2 hu.1).trans (by simpa using hu.2)
  have hw : 0 < w := Real.sqrt_pos.mpr hB
  have hw1 : w < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hB1)
  have hw2 : w ^ 2 = B := Real.sq_sqrt hB.le
  have hw_square : w ^ 2 ≤ w := by
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hw1.le)]
  have hA : 2 * w ≤ A := by
    have hsq : 4 * B ≤ A ^ 2 := by dsimp [A, B]; nlinarith [sq_nonneg (u - v)]
    have hAp : 0 < A := add_pos hu.1 hv.1
    nlinarith
  have hAB : 2 * B < A := by
    have h := add_pos (mul_pos hu.1 (sub_pos.mpr hv.2))
      (mul_pos hv.1 (sub_pos.mpr hu.2))
    dsimp [A, B]
    nlinarith
  have hzero : 0 ≤ c0 A B := by
    apply mul_nonneg (sq_nonneg B)
    dsimp [A, B]
    nlinarith [sq_nonneg (u - v)]
  have hone : 0 < c1 A B := by
    have hsum : 0 ≤ (u - v) ^ 2 * (u + v) := mul_nonneg (sq_nonneg _) (by linarith [hu.1, hv.1])
    have hstrict := mul_pos hB (sub_pos.mpr hAB)
    apply mul_pos (by positivity)
    have hid : A ^ 3 - 3 * A * B - 2 * B ^ 2 =
        (u - v) ^ 2 * (u + v) + B * (A - 2 * B) := by dsimp [A, B]; ring
    rw [hid]
    exact add_pos_of_nonneg_of_pos hsum hstrict
  have htwo : 0 < c2 A B := by
    have hfactor : 0 < w ^ 2 * (1 - w) * (w ^ 3 - 7 * w ^ 2 + 17 * w + 1) := by
      have hlast : 0 < w ^ 3 - 7 * w ^ 2 + 17 * w + 1 := by
        nlinarith [hw_square, pow_pos hw 3]
      exact mul_pos (mul_pos (sq_pos_of_pos hw) (sub_pos.mpr hw1)) hlast
    have hdiff : 0 ≤ (A - 2 * w) *
        (4 * (A ^ 2 + 2 * A * w + 4 * w ^ 2) - 6 * B * (A + 2 * w) +
          2 * (A + 2 * w) + 4 * B ^ 2 - 8 * B) := by
      apply mul_nonneg (sub_nonneg.mpr hA)
      have h1 : 0 ≤ A * (4 * A - 6 * B) := mul_nonneg (by linarith [hw]) (by linarith)
      have h2 : 0 ≤ w * (8 * A - 12 * B) := mul_nonneg hw.le (by linarith)
      nlinarith [sq_nonneg B]
    apply mul_pos hB
    have hid : 4 * A ^ 3 - 6 * A ^ 2 * B + 2 * A ^ 2 + 4 * A * B ^ 2 -
        8 * A * B - B ^ 3 - 7 * B =
        w ^ 2 * (1 - w) * (w ^ 3 - 7 * w ^ 2 + 17 * w + 1) +
        (A - 2 * w) * (4 * (A ^ 2 + 2 * A * w + 4 * w ^ 2) -
          6 * B * (A + 2 * w) + 2 * (A + 2 * w) + 4 * B ^ 2 - 8 * B) := by
      rw [← hw2]
      ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg hfactor hdiff
  refine ⟨hzero, hone, htwo, ?_⟩
  intro hfour
  have hthresh : (1 + 3 * B) / 2 ≤ A := by
    dsimp [c4] at hfour
    have hinner : 0 ≤ 2 * A - 3 * B - 1 :=
      nonneg_of_mul_nonneg_right hfour (by positivity : 0 < 2 * B)
    linarith
  apply mul_nonneg (by positivity)
  by_cases hsmall : w ≤ 1 / 3
  · have hlow : 0 ≤ (1 - B) * (1 - 4 * B) / 2 := by
      have hBsmall : B ≤ 1 / 9 := by nlinarith
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    have hdiff : 0 ≤ (A - (1 + 3 * B) / 2) *
        (4 * (A + (1 + 3 * B) / 2) - 6 * B - 1) := by
      apply mul_nonneg (sub_nonneg.mpr hthresh)
      linarith
    have hid : 4 * A ^ 2 - 6 * A * B - A + 2 * B ^ 2 - 4 * B =
        (1 - B) * (1 - 4 * B) / 2 + (A - (1 + 3 * B) / 2) *
          (4 * (A + (1 + 3 * B) / 2) - 6 * B - 1) := by ring
    rw [hid]
    exact add_nonneg hlow hdiff
  · have hthird : 1 / 3 ≤ w := (lt_of_not_ge hsmall).le
    have hlast : 0 ≤ -w ^ 2 + 5 * w - 1 := by nlinarith [hw_square]
    have hlow := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * w)
      (sub_nonneg.mpr hw1.le)) hlast
    have hdiff : 0 ≤ (A - 2 * w) * (4 * (A + 2 * w) - 6 * B - 1) := by
      apply mul_nonneg (sub_nonneg.mpr hA)
      nlinarith [hw_square]
    have hid : 4 * A ^ 2 - 6 * A * B - A + 2 * B ^ 2 - 4 * B =
        2 * w * (1 - w) * (-w ^ 2 + 5 * w - 1) +
          (A - 2 * w) * (4 * (A + 2 * w) - 6 * B - 1) := by
      rw [← hw2]
      ring
    rw [hid]
    exact add_nonneg hlow hdiff

private lemma normalized_four (A B s : ℝ) (hs : s ≠ 0) :
    poly A B s / s ^ 4 = c4 A B + c3 A B / s + c2 A B / s ^ 2 +
      c1 A B / s ^ 3 + c0 A B / s ^ 4 := by
  dsimp [poly]
  field_simp [hs]
  <;> ring

private lemma normalized_three (A B s : ℝ) (hs : s ≠ 0) :
    poly A B s / s ^ 3 = c4 A B * s + c3 A B + c2 A B / s +
      c1 A B / s ^ 2 + c0 A B / s ^ 3 := by
  dsimp [poly]
  field_simp [hs]
  <;> ring

private lemma ratio_strictAnti {A B : ℝ}
    (h0 : 0 ≤ c0 A B) (h1 : 0 < c1 A B) (h2 : 0 < c2 A B)
    (h4 : c4 A B < 0) :
    ∃ n : ℕ, StrictAntiOn (fun s => poly A B s / s ^ n) (Ioi 0) := by
  by_cases h3 : 0 ≤ c3 A B
  · refine ⟨4, ?_⟩
    intro s hs t ht hst
    change 0 < s at hs
    change 0 < t at ht
    change poly A B t / t ^ 4 < poly A B s / s ^ 4
    rw [normalized_four A B s hs.ne', normalized_four A B t ht.ne']
    have hthree : c3 A B / t ≤ c3 A B / s := by gcongr
    have htwo : c2 A B / t ^ 2 ≤ c2 A B / s ^ 2 := by gcongr <;> positivity
    have hone : c1 A B / t ^ 3 < c1 A B / s ^ 3 :=
      div_lt_div_of_pos_left h1 (pow_pos hs 3) (pow_lt_pow_left₀ hst hs.le (by decide))
    have hzero : c0 A B / t ^ 4 ≤ c0 A B / s ^ 4 := by gcongr <;> positivity
    linarith
  · refine ⟨3, ?_⟩
    intro s hs t ht hst
    change 0 < s at hs
    change 0 < t at ht
    change poly A B t / t ^ 3 < poly A B s / s ^ 3
    rw [normalized_three A B s hs.ne', normalized_three A B t ht.ne']
    have hfour : c4 A B * t < c4 A B * s := mul_lt_mul_of_neg_left hst h4
    have htwo : c2 A B / t ≤ c2 A B / s := by gcongr
    have hone : c1 A B / t ^ 2 ≤ c1 A B / s ^ 2 := by gcongr <;> positivity
    have hzero : c0 A B / t ^ 3 ≤ c0 A B / s ^ 3 := by gcongr <;> positivity
    linarith

private lemma polynomial_crossing {A B : ℝ}
    (h0 : 0 ≤ c0 A B) (h1 : 0 < c1 A B) (h2 : 0 < c2 A B)
    (h43 : 0 ≤ c4 A B → 0 ≤ c3 A B) :
    (∀ s ∈ Ioi (0 : ℝ), 0 ≤ poly A B s) ∨
      ∃ r ∈ Ioi (0 : ℝ), poly A B r = 0 ∧
        (∀ s ∈ Ioo (0 : ℝ) r, 0 < poly A B s) ∧
        (∀ s ∈ Ioi r, poly A B s < 0) := by
  by_cases h4 : 0 ≤ c4 A B
  · left
    intro s hs
    dsimp [poly]
    have h3 := h43 h4
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg h4 (pow_nonneg hs.le 4))
      (mul_nonneg h3 (pow_nonneg hs.le 3)))
      (mul_nonneg h2.le (pow_nonneg hs.le 2))) (mul_nonneg h1.le hs.le)) h0
  · have h4' : c4 A B < 0 := lt_of_not_ge h4
    obtain ⟨n, hanti⟩ := ratio_strictAnti h0 h1 h2 h4'
    have hpos : ∃ a > (0 : ℝ), 0 < poly A B a := by
      let g := fun s : ℝ => c4 A B * s ^ 3 + c3 A B * s ^ 2 + c2 A B * s + c1 A B
      have hg : Continuous g := by fun_prop
      have hlim : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < g s :=
        (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
          (eventually_gt_nhds (by simpa [g] using h1))
      have hmem : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      obtain ⟨a, ha, hga⟩ := (hmem.and hlim).exists
      refine ⟨a, ha, ?_⟩
      have hid : poly A B a = a * g a + c0 A B := by dsimp [poly, g]; ring
      rw [hid]
      exact add_pos_of_pos_of_nonneg (mul_pos ha hga) h0
    obtain ⟨a, ha, hpa⟩ := hpos
    have hneg : ∃ b > a, poly A B b < 0 := by
      have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have hlim : Tendsto
          (fun s : ℝ => c4 A B + c3 A B / s + c2 A B / s ^ 2 +
            c1 A B / s ^ 3 + c0 A B / s ^ 4) atTop (𝓝 (c4 A B)) := by
        simpa [div_eq_mul_inv, inv_pow] using
          (((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add
            (tendsto_const_nhds.mul (hinv.pow 2))).add
            (tendsto_const_nhds.mul (hinv.pow 3))).add
            (tendsto_const_nhds.mul (hinv.pow 4))
      obtain ⟨b, hb, hpb⟩ := ((eventually_gt_atTop a).and
        (hlim.eventually (eventually_lt_nhds h4'))).exists
      refine ⟨b, hb, ?_⟩
      rw [← normalized_four A B b (by linarith)] at hpb
      simpa only [zero_mul] using (div_lt_iff₀ (pow_pos (ha.trans hb) 4)).mp hpb
    obtain ⟨b, hab, hpb⟩ := hneg
    have hcont : Continuous (poly A B) := by unfold poly; fun_prop
    obtain ⟨r, hr, hpr⟩ := intermediate_value_Icc' hab.le hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (poly A B b) (poly A B a) from ⟨hpb.le, hpa.le⟩)
    right
    have hrapos : 0 < r := ha.trans_le hr.1
    refine ⟨r, hrapos, hpr, ?_, ?_⟩
    · intro s hs
      have hh := hanti hs.1 hrapos hs.2
      dsimp only at hh
      rw [hpr, zero_div] at hh
      exact (div_pos_iff_of_pos_right (pow_pos hs.1 n)).mp hh
    · intro s hs
      have hh := hanti hrapos (hrapos.trans hs) hs
      dsimp only at hh
      rw [hpr, zero_div] at hh
      simpa only [zero_mul] using (div_lt_iff₀ (pow_pos (hrapos.trans hs) n)).mp hh

private lemma kernel_sign {u v s : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) :
    (0 ≤ productLogKernel u v s ↔ 0 ≤ poly (u + v) (u * v) s) ∧
    (0 < productLogKernel u v s ↔ 0 < poly (u + v) (u * v) s) ∧
    (productLogKernel u v s < 0 ↔ poly (u + v) (u * v) s < 0) := by
  let A := u + v
  let B := u * v
  let L := A - B
  let q := Real.sqrt (B * (1 - A + B))
  let mp := A - 2 * B + 2 * q
  let mm := A - 2 * B - 2 * q
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := hv.1
  have hB : 0 < B := mul_pos hu.1 hv.1
  have hAB : 0 < A - 2 * B := by
    dsimp [A, B]
    nlinarith [mul_pos hu.1 (sub_pos.mpr hv.2), mul_pos hv.1 (sub_pos.mpr hu.2)]
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = B * (1 - A + B) := by
    apply Real.sq_sqrt
    have hh := mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr hv.2)
    apply mul_nonneg hB.le
    dsimp [A, B]
    nlinarith
  have hm : 0 ≤ mm := by
    have hd : (A - 2 * B) ^ 2 - 4 * q ^ 2 = (u - v) ^ 2 := by
      rw [hq2]
      dsimp [A, B]
      ring
    dsimp [mm]
    nlinarith [sq_nonneg (u - v)]
  have hp : 0 ≤ mp := by dsimp [mp]; linarith
  have hL : 0 < L := by dsimp [L]; linarith
  let N := ((s + u) * (s + v)) ^ 2 * ((s + mp) * (s + mm))
  let D := s ^ 2 * (s + L) ^ 4
  have hNp : 0 < N := by dsimp [N]; positivity
  have hDp : 0 < D := by dsimp [D]; positivity
  have hN : Real.log N =
      2 * (Real.log (s + u) + Real.log (s + v)) +
        Real.log (s + mp) + Real.log (s + mm) := by
    dsimp only [N]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    ring
  have hD : Real.log D = 2 * Real.log s + 4 * Real.log (s + L) := by
    dsimp only [D]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have hlog (x : ℝ) (hx : 0 ≤ x) :
      Real.log (1 + x / s) = Real.log (s + x) - Real.log s := by
    rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']]
    exact Real.log_div (by positivity) hs.ne'
  have he : 2 * productLogKernel u v s = Real.log N - Real.log D := by
    rw [hN, hD]
    change 2 * (Real.log (1 + u / s) + Real.log (1 + v / s) -
      2 * Real.log (1 + L / s) +
      (Real.log (1 + mp / s) + Real.log (1 + mm / s)) / 2) = _
    rw [hlog u hu.1.le, hlog v hv.1.le, hlog L hL.le, hlog mp hp, hlog mm hm]
    ring
  have hpoly : N - D = poly A B s := by
    have hfirst : (s + u) * (s + v) = s ^ 2 + A * s + B := by dsimp [A, B]; ring
    have hsecond : (s + mp) * (s + mm) =
        s ^ 2 + 2 * (A - 2 * B) * s + A ^ 2 - 4 * B := by
      dsimp [mp, mm]
      nlinarith [hq2]
    dsimp only [N, D]
    rw [hfirst, hsecond]
    simpa only [L, add_sub_assoc] using expansion A B s
  have hn := Real.log_le_log_iff hDp hNp
  have hp' := Real.log_lt_log_iff hDp hNp
  have hm' := Real.log_lt_log_iff hNp hDp
  change (0 ≤ productLogKernel u v s ↔ 0 ≤ poly A B s) ∧
    (0 < productLogKernel u v s ↔ 0 < poly A B s) ∧
    (productLogKernel u v s < 0 ↔ poly A B s < 0)
  constructor
  · constructor <;> intro h
    · have hl : Real.log D ≤ Real.log N := by linarith
      have hh := hn.mp hl
      linarith
    · have hl := hn.mpr (show D ≤ N by linarith)
      linarith
  constructor
  · constructor <;> intro h
    · have hl : Real.log D < Real.log N := by linarith
      have hh := hp'.mp hl
      linarith
    · have hl := hp'.mpr (show D < N by linarith)
      linarith
  · constructor <;> intro h
    · have hl : Real.log N < Real.log D := by linarith
      have hh := hm'.mp hl
      linarith
    · have hl := hm'.mpr (show N < D by linarith)
      linarith

private theorem interior_single_crossing {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∀ s ∈ Ioi (0 : ℝ), 0 ≤ productLogKernel u v s) ∨
      ∃ r ∈ Ioi (0 : ℝ), productLogKernel u v r = 0 ∧
        (∀ s ∈ Ioo (0 : ℝ) r, 0 < productLogKernel u v s) ∧
        (∀ s ∈ Ioi r, productLogKernel u v s < 0) := by
  obtain ⟨h0, h1, h2, h43⟩ := coefficient_signs hu hv
  rcases polynomial_crossing h0 h1 h2 h43 with h | ⟨r, hr, he, hp, hn⟩
  · exact Or.inl (fun s hs => (kernel_sign hu hv hs).1.mpr (h s hs))
  · right
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · have hnonneg := (kernel_sign hu hv hr).1.mpr he.ge
      have hnotpos : ¬0 < productLogKernel u v r := by
        intro hh
        have hh' := (kernel_sign hu hv hr).2.1.mp hh
        linarith
      linarith
    · intro s hs
      exact (kernel_sign hu hv hs.1).2.1.mpr (hp s hs)
    · intro s hs
      exact (kernel_sign hu hv (hr.trans hs)).2.2.mpr (hn s hs)

private lemma kernel_symm (u v s : ℝ) :
    productLogKernel u v s = productLogKernel v u s := by
  unfold productLogKernel
  rw [show v + u = u + v by ring, show v * u = u * v by ring]
  ring

private lemma kernel_zero_left (v s : ℝ) : productLogKernel 0 v s = 0 := by
  simp only [productLogKernel, zero_add, zero_mul, Real.sqrt_zero, mul_zero,
    add_zero, sub_zero, zero_div, Real.log_one]
  ring

private lemma kernel_one_left (v s : ℝ) :
    productLogKernel 1 v s = Real.log (1 + v / s) +
      Real.log (1 + (1 - v) / s) - Real.log (1 + 1 / s) := by
  simp only [productLogKernel, one_mul,
    show v * (1 - (1 + v) + v) = 0 by ring,
    Real.sqrt_zero, mul_zero, add_zero, sub_zero,
    show 1 + v - v = 1 by ring, show 1 + v - 2 * v = 1 - v by ring]
  ring

private lemma log_partition_nonneg {v s : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hs : 0 < s) : 0 ≤ Real.log (1 + v / s) +
      Real.log (1 + (1 - v) / s) - Real.log (1 + 1 / s) := by
  have hv0 : 0 ≤ v := hv.1
  have hv1 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hfirst : 0 < 1 + v / s := by positivity
  have hsecond : 0 < 1 + (1 - v) / s := by positivity
  have hbase : 0 < 1 + 1 / s := by positivity
  have hid : (1 + v / s) * (1 + (1 - v) / s) - (1 + 1 / s) =
      v * (1 - v) / s ^ 2 := by
    field_simp [hs.ne']
    <;> ring
  have hprod : 1 + 1 / s ≤ (1 + v / s) * (1 + (1 - v) / s) := by
    have hnonneg := div_nonneg (mul_nonneg hv0 hv1) (sq_nonneg s)
    linarith
  rw [← Real.log_mul hfirst.ne' hsecond.ne']
  exact sub_nonneg.mpr (Real.log_le_log hbase hprod)

/-- On the whole closed parameter square, the actual logarithmic kernel is either
nonnegative everywhere or has exactly one positive zero, positive before it and
negative after it. The diagonal and all zero-root boundary cases are included. -/
theorem product_log_kernel_single_crossing {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    (∀ s ∈ Ioi (0 : ℝ), 0 ≤ productLogKernel u v s) ∨
      ∃ r ∈ Ioi (0 : ℝ), productLogKernel u v r = 0 ∧
        (∀ s ∈ Ioo (0 : ℝ) r, 0 < productLogKernel u v s) ∧
        (∀ s ∈ Ioi r, productLogKernel u v s < 0) := by
  by_cases hu0 : u = 0
  · subst u
    exact Or.inl (fun s _ => by rw [kernel_zero_left])
  by_cases hu1 : u = 1
  · subst u
    exact Or.inl (fun s hs => by rw [kernel_one_left]; exact log_partition_nonneg hv hs)
  by_cases hv0 : v = 0
  · subst v
    exact Or.inl (fun s _ => by rw [kernel_symm, kernel_zero_left])
  by_cases hv1 : v = 1
  · subst v
    exact Or.inl (fun s hs => by
      rw [kernel_symm, kernel_one_left]
      exact log_partition_nonneg hu hs)
  exact interior_single_crossing
    ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩
    ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩

#print axioms product_log_kernel_single_crossing
end D5.S3.Entropy.ProductAbsorptionLogKernel
