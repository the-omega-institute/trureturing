/- GID: D5/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/AffineCongruenceRectangleCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A missed affine rectangle forces a unique primitive label and a phase obstruction. -/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.GCD
import D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Start with the joint square bound from the finite rectangle inverse.
The affine construction uses integer Bézout, nearest-residue rounding, and the
interval image of a real rectangle.
-/

@[expose] public section

namespace D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover

/-- Joint primitiveness; no pairwise coprimality is required. -/
def Primitive (h : ℕ) (p3 p5 : ℤ) : Prop :=
  Int.gcd (h : ℤ) (Int.gcd p3 p5 : ℤ) = 1

def delta (h : ℕ) (theta : ℝ) (p : ℤ) : ℝ := (h : ℝ) * theta - (p : ℝ)

def errorSum (h : ℕ) (p3 p5 : ℤ) (theta phi : ℝ) : ℝ :=
  |delta h theta p3| + |delta h phi p5|

/-- The original target phase, with real division and signed errors. -/
noncomputable def phase (N M h : ℕ) (p3 p5 : ℤ) (theta phi t w : ℝ) : ℝ :=
  (h : ℝ) * (t + w / 2) - (3 * (N : ℝ) / 2) * delta h theta p3 -
    (3 * (M : ℝ) / 2) * delta h phi p5

noncomputable def radius (N M h : ℕ) (p3 p5 : ℤ) (theta phi w : ℝ) : ℝ :=
  ((h : ℝ) * w + (N : ℝ) * |delta h theta p3| +
    (M : ℝ) * |delta h phi p5|) / 2

def RectangleHit (N M : ℕ) (theta phi t w : ℝ) : Prop :=
  ∃ a : ℤ, ∃ b d : ℕ, N ≤ b ∧ b ≤ 2 * N ∧ M ≤ d ∧ d ≤ 2 * M ∧
    t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) ∧
    (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w

/-- The squared norm of the three jointly scaled coordinates. -/
def jointSquare (N M h : ℕ) (p3 p5 : ℤ) (theta phi w : ℝ) : ℝ :=
  ((N : ℝ) * delta h theta p3) ^ 2 + ((M : ℝ) * delta h phi p5) ^ 2 +
    (w * (h : ℝ)) ^ 2

/-- A positive jointly primitive label with signed numerators and a joint square bound. -/
structure ShortLabel (N M : ℕ) (theta phi w : ℝ) where
  h : ℕ
  p3 : ℤ
  p5 : ℤ
  positive : 1 ≤ h
  joint_bound : jointSquare N M h p3 p5 theta phi w ≤ (11 : ℝ) / 3
  primitive : Primitive h p3 p5

/-- Factor out the positive joint gcd, preserving the joint square upper bound. -/
private theorem joint_gcd_reduction {N M : ℕ} {h p3 p5 : ℤ} {theta phi w : ℝ}
    (hh : 1 ≤ h)
    (hsq : ((N : ℝ) * ((h : ℝ) * theta - (p3 : ℝ))) ^ 2 +
      ((M : ℝ) * ((h : ℝ) * phi - (p5 : ℝ))) ^ 2 + (w * (h : ℝ)) ^ 2 ≤
        (11 : ℝ) / 3) :
    ∃ L : ShortLabel N M theta phi w,
      let g := Int.gcd h (Int.gcd p3 p5 : ℤ)
      0 < g ∧ h = (g : ℤ) * (L.h : ℤ) ∧ p3 = (g : ℤ) * L.p3 ∧ p5 = (g : ℤ) * L.p5 := by
  let g := Int.gcd h (Int.gcd p3 p5 : ℤ)
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left _ (by omega : h ≠ 0)
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hgInner : (g : ℤ) ∣ (Int.gcd p3 p5 : ℤ) :=
    Int.gcd_dvd_right h (Int.gcd p3 p5 : ℤ)
  obtain ⟨h', hfactor⟩ := Int.gcd_dvd_left h (Int.gcd p3 p5 : ℤ)
  obtain ⟨p3', hp3factor⟩ := Int.dvd_trans hgInner (Int.gcd_dvd_left p3 p5)
  obtain ⟨p5', hp5factor⟩ := Int.dvd_trans hgInner (Int.gcd_dvd_right p3 p5)
  change h = (g : ℤ) * h' at hfactor
  have hprod : 0 < (g : ℤ) * h' := by rw [← hfactor]; omega
  have hh' : 0 < h' := (mul_pos_iff_of_pos_left hgZ).mp hprod
  let d := h'.toNat
  have hdZ : (d : ℤ) = h' := Int.toNat_of_nonneg hh'.le
  have hd : 1 ≤ d := by
    have hdOne : (1 : ℤ) ≤ (d : ℤ) := by rw [hdZ]; omega
    exact_mod_cast hdOne
  have hfactorNat : h = (g : ℤ) * (d : ℤ) := by rwa [hdZ]
  have hInner : Int.gcd p3 p5 = g * Int.gcd p3' p5' := by
    rw [hp3factor, hp5factor, Int.gcd_mul_left, Int.natAbs_natCast]
  have hgcd : g = g * Int.gcd h' (Int.gcd p3' p5' : ℤ) := calc
    g = Int.gcd h (Int.gcd p3 p5 : ℤ) := rfl
    _ = g * Int.gcd h' (Int.gcd p3' p5' : ℤ) := by
      rw [hfactor, hInner, Int.natCast_mul, Int.gcd_mul_left, Int.natAbs_natCast]
  have hprimitive : Primitive d p3' p5' := by
    unfold Primitive
    rw [hdZ]
    exact mul_left_cancel₀ hg.ne' (by simpa only [mul_one] using hgcd.symm)
  have hhR : (h : ℝ) = (g : ℝ) * (d : ℝ) := by exact_mod_cast hfactorNat
  have hp3R : (p3 : ℝ) = (g : ℝ) * (p3' : ℝ) := by exact_mod_cast hp3factor
  have hp5R : (p5 : ℝ) = (g : ℝ) * (p5' : ℝ) := by exact_mod_cast hp5factor
  have hscale : (g : ℝ) ^ 2 * jointSquare N M d p3' p5' theta phi w =
      ((N : ℝ) * ((h : ℝ) * theta - (p3 : ℝ))) ^ 2 +
        ((M : ℝ) * ((h : ℝ) * phi - (p5 : ℝ))) ^ 2 + (w * (h : ℝ)) ^ 2 := by
    rw [hhR, hp3R, hp5R]
    unfold jointSquare delta
    ring
  have hgOne : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (show 1 ≤ g from hg)
  have hgSq : (1 : ℝ) ≤ (g : ℝ) ^ 2 := by
    simpa only [one_pow] using
      (sq_le_sq₀ zero_le_one (Nat.cast_nonneg g : (0 : ℝ) ≤ g)).mpr hgOne
  have hdSq : 0 ≤ jointSquare N M d p3' p5' theta phi w := by
    unfold jointSquare
    positivity
  have hbound : jointSquare N M d p3' p5' theta phi w ≤ (11 : ℝ) / 3 := calc
    _ ≤ (g : ℝ) ^ 2 * jointSquare N M d p3' p5' theta phi w :=
      le_mul_of_one_le_left hdSq hgSq
    _ ≤ (11 : ℝ) / 3 := by rw [hscale]; exact hsq
  exact ⟨⟨d, p3', p5', hd, hbound, hprimitive⟩, hg, hfactorNat, hp3factor, hp5factor⟩

private theorem primitive_bezout {h : ℕ} {p q : ℤ} (hp : Primitive h p q) :
    ∃ u v z : ℤ, (h : ℤ) * u + p * v + q * z = 1 := by
  have h₁ := Int.gcd_eq_gcd_ab (h : ℤ) (Int.gcd p q : ℤ)
  rw [show Int.gcd (h : ℤ) (Int.gcd p q : ℤ) = 1 from hp] at h₁
  have h₂ := Int.gcd_eq_gcd_ab p q
  refine ⟨Int.gcdA (h : ℤ) (Int.gcd p q : ℤ),
    Int.gcdA p q * Int.gcdB (h : ℤ) (Int.gcd p q : ℤ),
    Int.gcdB p q * Int.gcdB (h : ℤ) (Int.gcd p q : ℤ), ?_⟩
  calc
    _ = (h : ℤ) * Int.gcdA (h : ℤ) (Int.gcd p q : ℤ) +
        (p * Int.gcdA p q + q * Int.gcdB p q) *
          Int.gcdB (h : ℤ) (Int.gcd p q : ℤ) := by ring
    _ = 1 := by rw [← h₂]; exact h₁.symm

private theorem weighted_abs_sum {u v x y U V : ℝ}
    (hu : |u| ≤ U) (hv : |v| ≤ V) :
    |u * x + v * y| ≤ U * |x| + V * |y| := by
  calc
    _ ≤ |u * x| + |v * y| := abs_add_le _ _
    _ = |u| * |x| + |v| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hv (abs_nonneg _))

private theorem nearest_residue (h : ℕ) (hh : 0 < h) (r : ℤ) (x : ℝ) :
    ∃ b k : ℤ, b = r + (h : ℤ) * k ∧ |(b : ℝ) - x| ≤ (h : ℝ) / 2 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  let k : ℤ := round ((x - (r : ℝ)) / (h : ℝ))
  refine ⟨r + (h : ℤ) * k, k, rfl, ?_⟩
  have he : ((r + (h : ℤ) * k : ℤ) : ℝ) - x =
      (h : ℝ) * ((k : ℝ) - (x - (r : ℝ)) / (h : ℝ)) := by
    push_cast
    rw [mul_sub, mul_div_cancel₀ _ hhR.ne']
    ring
  rw [he, abs_mul, abs_of_pos hhR, abs_sub_comm]
  calc
    _ ≤ (h : ℝ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (abs_sub_round _) hhR.le
    _ = (h : ℝ) / 2 := by ring

private theorem closed_open_overlap {c r T A : ℝ} (hr : 0 ≤ r) (hA : 0 < A)
    (hc : |c - T| < r + A) : ∃ y : ℝ, |y - c| ≤ r ∧ |y - T| < A := by
  obtain ⟨hc₁, hc₂⟩ := abs_lt.mp hc
  by_cases hleft : T < c - r
  · refine ⟨c - r, ?_, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    rw [show c - r - c = -r by ring, abs_neg, abs_of_nonneg hr]
  · by_cases hright : c + r < T
    · refine ⟨c + r, ?_, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
      rw [show c + r - c = r by ring, abs_of_nonneg hr]
    · refine ⟨T, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      simpa using hA

private theorem axis_extremes (c r x : ℝ) (hr : 0 ≤ r) :
    ∃ lo hi : ℝ, c - r ≤ lo ∧ lo ≤ c + r ∧ c - r ≤ hi ∧ hi ≤ c + r ∧
      lo * x = c * x - r * |x| ∧ hi * x = c * x + r * |x| := by
  by_cases hx : 0 ≤ x
  · refine ⟨c - r, c + r, le_rfl, by linarith, by linarith, le_rfl, ?_, ?_⟩
    all_goals rw [abs_of_nonneg hx]; ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    refine ⟨c + r, c - r, by linarith, le_rfl, le_rfl, by linarith, ?_, ?_⟩
    all_goals rw [abs_of_nonpos hx']; ring

private theorem linear_box_image (o cb rb cd rd x z y : ℝ)
    (hb : 0 ≤ rb) (hd : 0 ≤ rd)
    (hy : |y - (o + cb * x + cd * z)| ≤ rb * |x| + rd * |z|) :
    ∃ b d : ℝ, |b - cb| ≤ rb ∧ |d - cd| ≤ rd ∧ o + b * x + d * z = y := by
  obtain ⟨bl, bu, hbl₁, hbl₂, hbu₁, hbu₂, hbl, hbu⟩ := axis_extremes cb rb x hb
  obtain ⟨dl, du, hdl₁, hdl₂, hdu₁, hdu₂, hdl, hdu⟩ := axis_extremes cd rd z hd
  let f : ℝ → ℝ := fun s => o + ((1 - s) * bl + s * bu) * x +
    ((1 - s) * dl + s * du) * z
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    fun_prop
  have hf0 : f 0 = o + cb * x + cd * z - (rb * |x| + rd * |z|) := by
    simp only [f, sub_zero, one_mul, zero_mul, add_zero]
    rw [hbl, hdl]
    ring
  have hf1 : f 1 = o + cb * x + cd * z + (rb * |x| + rd * |z|) := by
    simp only [f, sub_self, zero_mul, one_mul, zero_add]
    rw [hbu, hdu]
    ring
  have hy' : y ∈ Set.Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    obtain ⟨hy₁, hy₂⟩ := abs_le.mp hy
    constructor <;> linarith
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hy'
  refine ⟨(1 - s) * bl + s * bu, (1 - s) * dl + s * du, ?_, ?_, hfs⟩
  · apply abs_le.mpr
    have h₁ := mul_le_mul_of_nonneg_left hbl₁ (sub_nonneg.mpr hs.2)
    have h₂ := mul_le_mul_of_nonneg_left hbu₁ hs.1
    have h₃ := mul_le_mul_of_nonneg_left hbl₂ (sub_nonneg.mpr hs.2)
    have h₄ := mul_le_mul_of_nonneg_left hbu₂ hs.1
    constructor <;> nlinarith
  · apply abs_le.mpr
    have h₁ := mul_le_mul_of_nonneg_left hdl₁ (sub_nonneg.mpr hs.2)
    have h₂ := mul_le_mul_of_nonneg_left hdu₁ hs.1
    have h₃ := mul_le_mul_of_nonneg_left hdl₂ (sub_nonneg.mpr hs.2)
    have h₄ := mul_le_mul_of_nonneg_left hdu₂ hs.1
    constructor <;> nlinarith

/-- Each specified integer in the inner phase band constructs legal natural
rectangle indices and an integer edit, realizing that very congruence label. -/
private theorem affine_hit_sufficient {N M h : ℕ} {p3 p5 : ℤ} {theta phi t w : ℝ}
    (hh : 1 ≤ h) (hhN : h ≤ N) (hhM : h ≤ M)
    (hp : Primitive h p3 p5) (hw : 0 < w)
    (hS : errorSum h p3 p5 theta phi < w) (n : ℤ)
    (hn : |(n : ℝ) - phase N M h p3 p5 theta phi t w| <
      radius N M h p3 p5 theta phi w - (h : ℝ) * errorSum h p3 p5 theta phi) :
    ∃ a : ℤ, ∃ b d : ℕ, N ≤ b ∧ b ≤ 2 * N ∧ M ≤ d ∧ d ≤ 2 * M ∧
      n = (b : ℤ) * p3 + (d : ℤ) * p5 - (h : ℤ) * a ∧
      t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) ∧
      (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w := by
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh0
  have hhNR : (h : ℝ) ≤ N := by exact_mod_cast hhN
  have hhMR : (h : ℝ) ≤ M := by exact_mod_cast hhM
  have hNr : 0 ≤ (N : ℝ) - (h : ℝ) := sub_nonneg.mpr hhNR
  have hMr : 0 ≤ (M : ℝ) - (h : ℝ) := sub_nonneg.mpr hhMR
  let x := delta h theta p3
  let z := delta h phi p5
  let S := |x| + |z|
  let c := (n : ℝ) + 3 * (N : ℝ) / 2 * x + 3 * (M : ℝ) / 2 * z
  let r := (((N : ℝ) - h) * |x| + ((M : ℝ) - h) * |z|) / 2
  let T := (h : ℝ) * (t + w / 2)
  let A := (h : ℝ) * (w - S) / 2
  have hr : 0 ≤ r := by
    exact div_nonneg (add_nonneg (mul_nonneg hNr (abs_nonneg x))
      (mul_nonneg hMr (abs_nonneg z))) (by norm_num)
  have hA : 0 < A := by
    have hS' : S < w := hS
    dsimp [A]
    exact div_pos (mul_pos hhR (sub_pos.mpr hS')) (by norm_num)
  have hc : |c - T| < r + A := by
    have hc' : c - T = (n : ℝ) - phase N M h p3 p5 theta phi t w := by
      dsimp [c, T, x, z, phase]
      ring
    have hrA : r + A = radius N M h p3 p5 theta phi w -
        (h : ℝ) * errorSum h p3 p5 theta phi := by
      dsimp [r, A, S, x, z, radius, errorSum]
      ring
    rw [hc', hrA]
    exact hn
  obtain ⟨y, hyc, hyT⟩ := closed_open_overlap hr hA hc
  have himage : |y - ((n : ℝ) + 3 * (N : ℝ) / 2 * x + 3 * (M : ℝ) / 2 * z)| ≤
      (((N : ℝ) - h) / 2) * |x| + (((M : ℝ) - h) / 2) * |z| := calc
    |y - c| ≤ r := hyc
    _ = _ := by
      dsimp only [r]
      ring
  obtain ⟨bs, ds, hbs, hds, hy⟩ := linear_box_image (n : ℝ)
    (3 * (N : ℝ) / 2) (((N : ℝ) - h) / 2)
    (3 * (M : ℝ) / 2) (((M : ℝ) - h) / 2) x z y
    (div_nonneg hNr (by norm_num)) (div_nonneg hMr (by norm_num)) himage
  obtain ⟨u, v, q, hbez⟩ := primitive_bezout hp
  obtain ⟨b, k, hbdef, hbround⟩ := nearest_residue h hh0 (n * v) bs
  obtain ⟨d, l, hddef, hdround⟩ := nearest_residue h hh0 (n * q) ds
  let a : ℤ := -n * u + k * p3 + l * p5
  have hcong : b * p3 + d * p5 - (h : ℤ) * a = n := by
    rw [hbdef, hddef]
    dsimp [a]
    linear_combination n * hbez
  -- The same integer is the exact quotient in the ordinary construction.
  have hquotient : a = (b * p3 + d * p5 - n) / (h : ℤ) := by
    have heq : b * p3 + d * p5 - n = a * (h : ℤ) := by
      linear_combination hcong
    rw [heq, Int.mul_ediv_cancel _ (by exact_mod_cast (ne_of_gt hh0))]
  have hb₀ := (abs_le.mp hbround).1
  have hb₁ := (abs_le.mp hbround).2
  have hd₀ := (abs_le.mp hdround).1
  have hd₁ := (abs_le.mp hdround).2
  obtain ⟨hbs₀, hbs₁⟩ := abs_le.mp hbs
  obtain ⟨hds₀, hds₁⟩ := abs_le.mp hds
  have hbN : (N : ℝ) ≤ b := by linarith only [hb₀, hbs₀]
  have hb2N : (b : ℝ) ≤ 2 * (N : ℝ) := by linarith only [hb₁, hbs₁]
  have hdM : (M : ℝ) ≤ d := by linarith only [hd₀, hds₀]
  have hd2M : (d : ℝ) ≤ 2 * (M : ℝ) := by linarith only [hd₁, hds₁]
  have hbnonneg : (0 : ℤ) ≤ b := by
    have : (0 : ℝ) ≤ b := le_trans (Nat.cast_nonneg N) hbN
    exact_mod_cast this
  have hdnonneg : (0 : ℤ) ≤ d := by
    have : (0 : ℝ) ≤ d := le_trans (Nat.cast_nonneg M) hdM
    exact_mod_cast this
  have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hbnonneg
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hdnonneg
  have hbcastR : (b.toNat : ℝ) = b := by exact_mod_cast hbcast
  have hdcastR : (d.toNat : ℝ) = d := by exact_mod_cast hdcast
  have hround : |((b : ℝ) - bs) * x + ((d : ℝ) - ds) * z| ≤ (h : ℝ) * S / 2 := calc
    _ ≤ (h : ℝ) / 2 * |x| + (h : ℝ) / 2 * |z| :=
      weighted_abs_sum (x := x) (y := z) hbround hdround
    _ = _ := by
      dsimp only [S]
      ring
  obtain ⟨her₀, her₁⟩ := abs_le.mp hround
  obtain ⟨hyt₀, hyt₁⟩ := abs_lt.mp hyT
  have hlinear : (h : ℝ) * ((b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ)) =
      y + (((b : ℝ) - bs) * x + ((d : ℝ) - ds) * z) := by
    have hcR : (b : ℝ) * (p3 : ℝ) + (d : ℝ) * (p5 : ℝ) -
        (h : ℝ) * (a : ℝ) = (n : ℝ) := by exact_mod_cast hcong
    dsimp only [x, z, delta] at hy ⊢
    linear_combination hy + hcR
  have hhit₀ : t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hhR).mp
    dsimp only [T, A] at hyt₀
    linarith only [hyt₀, her₀, hlinear]
  have hhit₁ : (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w := by
    apply (mul_lt_mul_iff_right₀ hhR).mp
    dsimp only [T, A] at hyt₁
    linarith only [hyt₁, her₁, hlinear]
  refine ⟨(b * p3 + d * p5 - n) / (h : ℤ), b.toNat, d.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (N : ℝ) ≤ (b.toNat : ℝ) by rwa [hbcastR])
  · exact_mod_cast (show (b.toNat : ℝ) ≤ 2 * (N : ℝ) by rwa [hbcastR])
  · exact_mod_cast (show (M : ℝ) ≤ (d.toNat : ℝ) by rwa [hdcastR])
  · exact_mod_cast (show (d.toNat : ℝ) ≤ 2 * (M : ℝ) by rwa [hdcastR])
  · rw [← hquotient, hbcast, hdcast]
    exact hcong.symm
  · rw [← hquotient, hbcastR, hdcastR]
    exact hhit₀
  · rw [← hquotient, hbcastR, hdcastR]
    exact hhit₁

private theorem joint_coordinate_bounds {x y z : ℝ}
    (hsq : x ^ 2 + y ^ 2 + z ^ 2 ≤ (11 : ℝ) / 3) :
    |x| < 2 ∧ |y| < 2 ∧ |z| < 2 := by
  refine ⟨abs_lt_of_sq_lt_sq ?_ (by norm_num), abs_lt_of_sq_lt_sq ?_ (by norm_num),
    abs_lt_of_sq_lt_sq ?_ (by norm_num)⟩
  · linarith only [hsq, sq_nonneg y, sq_nonneg z]
  · linarith only [hsq, sq_nonneg x, sq_nonneg z]
  · linarith only [hsq, sq_nonneg x, sq_nonneg y]

private theorem short_scale_bounds {N M : ℕ} {theta phi w : ℝ}
    (hw : 0 < w) (hNw : (4 : ℝ) ≤ (N : ℝ) * w) (hMw : (4 : ℝ) ≤ (M : ℝ) * w)
    (L : ShortLabel N M theta phi w) :
    2 * (L.h : ℝ) < N ∧ 2 * (L.h : ℝ) < M ∧ errorSum L.h L.p3 L.p5 theta phi < w := by
  have hNR : (0 : ℝ) < N :=
    pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 4).trans_le hNw) hw.le
  have hMR : (0 : ℝ) < M :=
    pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 4).trans_le hMw) hw.le
  have hsq := L.joint_bound
  unfold jointSquare at hsq
  obtain ⟨hX, hY, hZ⟩ := joint_coordinate_bounds hsq
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)] at hX
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M)] at hY
  rw [abs_of_nonneg (mul_nonneg hw.le (Nat.cast_nonneg L.h))] at hZ
  have hdenom : (2 * (L.h : ℝ)) * w < 4 := by linarith only [hZ]
  have herr3 : |delta L.h theta L.p3| < w / 2 := by
    apply (mul_lt_mul_iff_right₀ hNR).mp
    linarith only [hX, hNw]
  have herr5 : |delta L.h phi L.p5| < w / 2 := by
    apply (mul_lt_mul_iff_right₀ hMR).mp
    linarith only [hY, hMw]
  refine ⟨(mul_lt_mul_iff_left₀ hw).mp (hdenom.trans_le hNw),
    (mul_lt_mul_iff_left₀ hw).mp (hdenom.trans_le hMw), ?_⟩
  unfold errorSum
  linarith only [herr3, herr5]

private theorem abs_two_row_det_le {x z x' z' C : ℝ}
    (hx : x ^ 2 + z ^ 2 ≤ C) (hx' : x' ^ 2 + z' ^ 2 ≤ C) :
    |x * z' - x' * z| ≤ C := by
  have hC : 0 ≤ C := (add_nonneg (sq_nonneg x) (sq_nonneg z)).trans hx
  have hprod : (x ^ 2 + z ^ 2) * (x' ^ 2 + z' ^ 2) ≤ C ^ 2 := by
    rw [pow_two C]
    exact mul_le_mul hx hx' (add_nonneg (sq_nonneg x') (sq_nonneg z')) hC
  have hdet : (x * z' - x' * z) ^ 2 ≤ C ^ 2 := calc
    _ ≤ (x * z' - x' * z) ^ 2 + (x * x' + z * z') ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = (x ^ 2 + z ^ 2) * (x' ^ 2 + z' ^ 2) := by ring
    _ ≤ _ := hprod
  simpa only [abs_of_nonneg hC] using sq_le_sq.mp hdet

private theorem cross_minor_zero {A h₁ h₂ : ℕ} {p₁ p₂ : ℤ} {theta w : ℝ}
    (hAw : (4 : ℝ) ≤ (A : ℝ) * w)
    (hsq₁ : ((A : ℝ) * delta h₁ theta p₁) ^ 2 + (w * (h₁ : ℝ)) ^ 2 ≤ (11 : ℝ) / 3)
    (hsq₂ : ((A : ℝ) * delta h₂ theta p₂) ^ 2 + (w * (h₂ : ℝ)) ^ 2 ≤ (11 : ℝ) / 3) :
    (h₁ : ℤ) * p₂ = (h₂ : ℤ) * p₁ := by
  let m : ℤ := (h₁ : ℤ) * p₂ - (h₂ : ℤ) * p₁
  have hdet := abs_two_row_det_le hsq₁ hsq₂
  have hfactor : ((A : ℝ) * delta h₁ theta p₁) * (w * (h₂ : ℝ)) -
      ((A : ℝ) * delta h₂ theta p₂) * (w * (h₁ : ℝ)) = ((A : ℝ) * w) * (m : ℝ) := by
    dsimp [m, delta]
    push_cast
    ring
  have hAw₀ : 0 ≤ (A : ℝ) * w := (by norm_num : (0 : ℝ) ≤ 4).trans hAw
  rw [hfactor, abs_mul, abs_of_nonneg hAw₀] at hdet
  have h4 : (4 : ℝ) * |(m : ℝ)| ≤ (11 : ℝ) / 3 :=
    (mul_le_mul_of_nonneg_right hAw (abs_nonneg _)).trans hdet
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (show |(m : ℝ)| < 1 by linarith only [h4])
  have hloZ : (-1 : ℤ) < m := by exact_mod_cast hlo
  have hhiZ : m < (1 : ℤ) := by exact_mod_cast hhi
  exact sub_eq_zero.mp (show m = 0 by omega)

private theorem primitive_equal_of_minors {h₁ h₂ : ℕ} {p₁ q₁ p₂ q₂ : ℤ}
    (hh₁ : 1 ≤ h₁) (hp₁ : Primitive h₁ p₁ q₁) (hp₂ : Primitive h₂ p₂ q₂)
    (hc₃ : (h₁ : ℤ) * p₂ = (h₂ : ℤ) * p₁)
    (hc₅ : (h₁ : ℤ) * q₂ = (h₂ : ℤ) * q₁) : h₁ = h₂ ∧ p₁ = p₂ ∧ q₁ = q₂ := by
  obtain ⟨u₁, v₁, z₁, hb₁⟩ := primitive_bezout hp₁
  obtain ⟨u₂, v₂, z₂, hb₂⟩ := primitive_bezout hp₂
  have hd₁ : (h₁ : ℤ) ∣ (h₂ : ℤ) := by
    refine ⟨(h₂ : ℤ) * u₁ + p₂ * v₁ + q₂ * z₁, ?_⟩
    linear_combination -(h₂ : ℤ) * hb₁ - v₁ * hc₃ - z₁ * hc₅
  have hd₂ : (h₂ : ℤ) ∣ (h₁ : ℤ) := by
    refine ⟨(h₁ : ℤ) * u₂ + p₁ * v₂ + q₁ * z₂, ?_⟩
    linear_combination -(h₁ : ℤ) * hb₂ + v₂ * hc₃ + z₂ * hc₅
  have hh : h₁ = h₂ := Nat.dvd_antisymm (by exact_mod_cast hd₁) (by exact_mod_cast hd₂)
  have hhZ : (h₁ : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hh₁))
  rw [← hh] at hc₃ hc₅
  exact ⟨hh, (mul_left_cancel₀ hhZ hc₃).symm, (mul_left_cancel₀ hhZ hc₅).symm⟩

/-- At side-width products at least four, the joint square bound fixes the
positive primitive triple. -/
private theorem short_label_unique {N M : ℕ} {theta phi w : ℝ}
    (hNw : (4 : ℝ) ≤ (N : ℝ) * w) (hMw : (4 : ℝ) ≤ (M : ℝ) * w)
    (L₁ L₂ : ShortLabel N M theta phi w) : L₁ = L₂ := by
  have hsq₁ := L₁.joint_bound
  have hsq₂ := L₂.joint_bound
  unfold jointSquare at hsq₁ hsq₂
  have hc₃ : (L₁.h : ℤ) * L₂.p3 = (L₂.h : ℤ) * L₁.p3 := by
    apply cross_minor_zero (theta := theta) hNw
    · linarith only [hsq₁, sq_nonneg ((M : ℝ) * delta L₁.h phi L₁.p5)]
    · linarith only [hsq₂, sq_nonneg ((M : ℝ) * delta L₂.h phi L₂.p5)]
  have hc₅ : (L₁.h : ℤ) * L₂.p5 = (L₂.h : ℤ) * L₁.p5 := by
    apply cross_minor_zero (theta := phi) hMw
    · linarith only [hsq₁, sq_nonneg ((N : ℝ) * delta L₁.h theta L₁.p3)]
    · linarith only [hsq₂, sq_nonneg ((N : ℝ) * delta L₂.h theta L₂.p3)]
  obtain ⟨hh, hp, hq⟩ := primitive_equal_of_minors L₁.positive L₁.primitive L₂.primitive hc₃ hc₅
  cases L₁ with
  | mk h₁ p₁ q₁ hh₁ hs₁ hp₁ =>
    cases L₂ with
    | mk h₂ p₂ q₂ hh₂ hs₂ hp₂ =>
      change h₁ = h₂ at hh
      change p₁ = p₂ at hp
      change q₁ = q₂ at hq
      subst h₂
      subst p₂
      subst q₂
      rfl

/-- An actual rectangle miss forces the unique positive primitive label in the
joint square bound, excludes every integer in the inner phase band, and bounds
the weighted width by one. -/
theorem short_label_miss_obstruction {N M : ℕ} {theta phi t w : ℝ}
    (hw : 0 < w ∧ w < 1)
    (hNw : (4 : ℝ) ≤ (N : ℝ) * w) (hMw : (4 : ℝ) ≤ (M : ℝ) * w)
    (hmiss : ¬ RectangleHit N M theta phi t w) :
    ∃ L : ShortLabel N M theta phi w,
      (∀ L' : ShortLabel N M theta phi w, L' = L) ∧
      (∀ n : ℤ, radius N M L.h L.p3 L.p5 theta phi w -
        (L.h : ℝ) * errorSum L.h L.p3 L.p5 theta phi ≤
        |(n : ℝ) - phase N M L.h L.p3 L.p5 theta phi t w|) ∧
      ((L.h : ℝ) * w + ((N : ℝ) - 2 * (L.h : ℝ)) * |delta L.h theta L.p3| +
        ((M : ℝ) - 2 * (L.h : ℝ)) * |delta L.h phi L.p5| ≤ 1) ∧
      (L.h : ℝ) ≤ 1 / w := by
  have side_ge_two (A : ℕ) (hAw : (4 : ℝ) ≤ (A : ℝ) * w) : 2 ≤ A := by
    by_contra hA
    have hAR : (A : ℝ) ≤ 1 := by exact_mod_cast (show A ≤ 1 by omega)
    have hprod := mul_le_mul_of_nonneg_right hAR hw.1.le
    linarith only [hprod, hAw, hw.2]
  have hmiss' : ¬ ∃ b d : ℕ, ∃ a : ℤ, N ≤ b ∧ b ≤ 2 * N ∧ M ≤ d ∧ d ≤ 2 * M ∧
      t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) ∧
      (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w := by
    rintro ⟨b, d, a, hb₁, hb₂, hd₁, hd₂, ht₁, ht₂⟩
    exact hmiss ⟨a, b, d, hb₁, hb₂, hd₁, hd₂, ht₁, ht₂⟩
  obtain ⟨h, p3, p5, hh, hsq⟩ :=
    D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover.finite_rectangle_inverse
      N M (side_ge_two N hNw) (side_ge_two M hMw) theta phi t w hw hmiss'
  obtain ⟨L, _⟩ := joint_gcd_reduction
    (N := N) (M := M) (theta := theta) (phi := phi) (w := w) hh
      (by simpa only [mul_pow] using hsq)
  obtain ⟨hhN, hhM, hS⟩ := short_scale_bounds hw.1 hNw hMw L
  have hh₀ : (0 : ℝ) ≤ (L.h : ℝ) := Nat.cast_nonneg L.h
  have hhN' : L.h ≤ N := (Nat.cast_le (α := ℝ)).mp (by linarith only [hhN, hh₀])
  have hhM' : L.h ≤ M := (Nat.cast_le (α := ℝ)).mp (by linarith only [hhM, hh₀])
  have hphase : ∀ n : ℤ, radius N M L.h L.p3 L.p5 theta phi w -
      (L.h : ℝ) * errorSum L.h L.p3 L.p5 theta phi ≤
      |(n : ℝ) - phase N M L.h L.p3 L.p5 theta phi t w| := by
    intro n
    apply le_of_not_gt
    intro hn
    obtain ⟨a, b, d, hb₁, hb₂, hd₁, hd₂, _, ht₁, ht₂⟩ :=
      affine_hit_sufficient L.positive hhN' hhM' L.primitive hw.1 hS n hn
    exact hmiss ⟨a, b, d, hb₁, hb₂, hd₁, hd₂, ht₁, ht₂⟩
  let Xi := phase N M L.h L.p3 L.p5 theta phi t w
  have hn : |((round Xi : ℤ) : ℝ) - Xi| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round Xi
  have hR : radius N M L.h L.p3 L.p5 theta phi w -
      (L.h : ℝ) * errorSum L.h L.p3 L.p5 theta phi ≤ 1 / 2 :=
    (hphase (round Xi)).trans hn
  have hwidth : (L.h : ℝ) * w + ((N : ℝ) - 2 * (L.h : ℝ)) * |delta L.h theta L.p3| +
      ((M : ℝ) - 2 * (L.h : ℝ)) * |delta L.h phi L.p5| ≤ 1 := by
    unfold radius errorSum at hR
    linarith only [hR]
  have hcoefN : 0 ≤ (N : ℝ) - 2 * (L.h : ℝ) := sub_nonneg.mpr hhN.le
  have hcoefM : 0 ≤ (M : ℝ) - 2 * (L.h : ℝ) := sub_nonneg.mpr hhM.le
  refine ⟨L, fun L' => short_label_unique hNw hMw L' L, hphase, hwidth, ?_⟩
  apply (le_div_iff₀ hw.1).mpr
  linarith only [hwidth, mul_nonneg hcoefN (abs_nonneg (delta L.h theta L.p3)),
    mul_nonneg hcoefM (abs_nonneg (delta L.h phi L.p5))]


namespace Shared

theorem nearest_residue (h : ℕ) (hh : 0 < h) (r : ℤ) (x : ℝ) :
    ∃ b k : ℤ, b = r + (h : ℤ) * k ∧ |(b : ℝ) - x| ≤ (h : ℝ) / 2 :=
  D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.nearest_residue h hh r x

theorem closed_open_overlap {c r T A : ℝ} (hr : 0 ≤ r) (hA : 0 < A)
    (hc : |c - T| < r + A) : ∃ y : ℝ, |y - c| ≤ r ∧ |y - T| < A :=
  D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.closed_open_overlap hr hA hc

theorem axis_extremes (c r x : ℝ) (hr : 0 ≤ r) :
    ∃ lo hi : ℝ, c - r ≤ lo ∧ lo ≤ c + r ∧ c - r ≤ hi ∧ hi ≤ c + r ∧
      lo * x = c * x - r * |x| ∧ hi * x = c * x + r * |x| :=
  D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.axis_extremes c r x hr

theorem abs_two_row_det_le {x z x' z' C : ℝ}
    (hx : x ^ 2 + z ^ 2 ≤ C) (hx' : x' ^ 2 + z' ^ 2 ≤ C) :
    |x * z' - x' * z| ≤ C :=
  D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover.abs_two_row_det_le hx hx'

end Shared

end D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
