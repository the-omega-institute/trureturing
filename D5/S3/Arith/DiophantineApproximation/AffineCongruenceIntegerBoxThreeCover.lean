/- GID: D5/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/AffineCongruenceIntegerBoxThreeCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A three-axis box miss forces a unique primitive label and a signed phase obstruction. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Basic
import D5.S3.Arith.DiophantineApproximation.AffineCongruenceRectangleCover
import D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! A joint resonance becomes an affine obstruction by rounding in its Bézout residues. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover

open AffineCongruenceRectangleCover (nearest_residue closed_open_overlap axis_extremes
  abs_two_row_det_le)
open FiniteIntegerBoxThreeCircleCover (finite_integer_box_inverse_three)

@[expose] public section

/-- Joint primitiveness expressed by an integer Bézout identity. -/
def Primitive (h : ℤ) (p : Fin 3 → ℤ) : Prop :=
  ∃ (u : ℤ) (v : Fin 3 → ℤ), h * u + (∑ i, p i * v i) = 1

def delta (h : ℤ) (p : Fin 3 → ℤ) (θ : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (h : ℝ) * θ i - (p i : ℝ)

def errorSum (h : ℤ) (p : Fin 3 → ℤ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ i, |delta h p θ i|

noncomputable def phase (N : Fin 3 → ℤ) (h : ℤ) (p : Fin 3 → ℤ)
    (θ : Fin 3 → ℝ) (t w : ℝ) : ℝ :=
  (h : ℝ) * (t + w / 2) - ∑ i, (3 * (N i : ℝ) / 2) * delta h p θ i

noncomputable def radius (N : Fin 3 → ℤ) (h : ℤ) (p : Fin 3 → ℤ)
    (θ : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  ((h : ℝ) * w + ∑ i, (N i : ℝ) * |delta h p θ i|) / 2

def jointSquare (N : Fin 3 → ℤ) (h : ℤ) (p : Fin 3 → ℤ)
    (θ : Fin 3 → ℝ) (w : ℝ) : ℝ :=
  (∑ i, (((N i : ℝ) + 2) * delta h p θ i) ^ 2) + (w * (h : ℝ)) ^ 2

/-- A positive jointly primitive label in the padded squared bound. -/
structure ShortLabel (N : Fin 3 → ℤ) (θ : Fin 3 → ℝ) (w : ℝ) where
  h : ℤ
  p : Fin 3 → ℤ
  positive : 1 ≤ h
  joint_bound : jointSquare N h p θ w ≤ (43 : ℝ) / 9
  primitive : Primitive h p

end

private theorem joint_gcd_reduction {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {w : ℝ}
    {h : ℤ} {p : Fin 3 → ℤ} (hh : 1 ≤ h)
    (hsq : jointSquare N h p θ w ≤ (43 : ℝ) / 9) :
    Nonempty (ShortLabel N θ w) := by
  classical
  let x : Fin 4 → ℤ := Fin.snoc (α := fun _ => ℤ) p h
  let g : ℤ := Finset.univ.gcd x
  have hdvd (j : Fin 4) : g ∣ x j := Finset.gcd_dvd (Finset.mem_univ j)
  have hgh : g ∣ h := by simpa only [x, Fin.snoc_last] using hdvd (Fin.last 3)
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, zero_dvd_iff] at hgh
    omega
  have hgn : 0 ≤ g := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  have hg : 0 < g := lt_of_le_of_ne hgn hg0.symm
  obtain ⟨d, hd⟩ := hgh
  have hdpos : 1 ≤ d := by
    have hprod : 0 < g * d := by rw [← hd]; omega
    have := (mul_pos_iff_of_pos_left hg).mp hprod
    omega
  have hgp (i : Fin 3) : g ∣ p i := by
    simpa only [x, Fin.snoc_castSucc] using hdvd i.castSucc
  choose q hq using hgp
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul Finset.univ x
  change g = ∑ j, x j * a j at ha
  have hprimitive : Primitive d q := by
    refine ⟨a (Fin.last 3), fun i => a i.castSucc, mul_left_cancel₀ hg0 ?_⟩
    calc
      g * (d * a (Fin.last 3) + ∑ i, q i * a i.castSucc) = ∑ j, x j * a j := by
        rw [Fin.sum_univ_castSucc (fun j : Fin 4 => x j * a j)]
        simp only [x, Fin.snoc_castSucc, Fin.snoc_last, mul_add, Finset.mul_sum]
        rw [add_comm]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [hq i, mul_assoc]
        · rw [hd, mul_assoc]
      _ = g * 1 := by rw [mul_one]; exact ha.symm
  have hdR : (h : ℝ) = (g : ℝ) * (d : ℝ) := by exact_mod_cast hd
  have hqR (i : Fin 3) : (p i : ℝ) = (g : ℝ) * (q i : ℝ) := by exact_mod_cast hq i
  have hscale : jointSquare N h p θ w = (g : ℝ) ^ 2 * jointSquare N d q θ w := by
    unfold jointSquare
    rw [mul_add, Finset.mul_sum, hdR]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [delta, delta, hdR, hqR i]
      ring
    · ring
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (show 1 ≤ g by omega)
  have hgSq : (1 : ℝ) ≤ (g : ℝ) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hg1 2
  have hnonneg : 0 ≤ jointSquare N d q θ w := by
    unfold jointSquare
    positivity
  rw [hscale] at hsq
  exact ⟨⟨d, q, hdpos, (le_mul_of_one_le_left hnonneg hgSq).trans hsq, hprimitive⟩⟩

private theorem unpadded_bound {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {w : ℝ}
    (hN : ∀ i, 0 ≤ (N i : ℝ)) (L : ShortLabel N θ w) :
    (∑ i, ((N i : ℝ) * |delta L.h L.p θ i|) ^ 2) + (w * (L.h : ℝ)) ^ 2 ≤
      (43 : ℝ) / 9 := by
  have hpad := L.joint_bound
  unfold jointSquare at hpad
  refine (add_le_add (Finset.sum_le_sum ?_) le_rfl).trans hpad
  intro i _
  rw [← sq_abs (((N i : ℝ) + 2) * delta L.h L.p θ i), abs_mul,
    abs_of_nonneg (by linarith [hN i] : 0 ≤ (N i : ℝ) + 2)]
  exact pow_le_pow_left₀ (mul_nonneg (hN i) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)) 2

private theorem short_scale_bounds {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {w : ℝ}
    (hw : 0 < w) (hN : ∀ i, 0 ≤ (N i : ℝ))
    (hNw : ∀ i, (43 : ℝ) / 9 < (N i : ℝ) * w) (L : ShortLabel N θ w) :
    (∀ i, 2 * (L.h : ℝ) < (N i : ℝ)) ∧ errorSum L.h L.p θ < w := by
  let a (i : Fin 3) := (N i : ℝ) * |delta L.h L.p θ i|
  have hsq : (∑ i, a i ^ 2) + (w * (L.h : ℝ)) ^ 2 ≤ 43 / 9 := unpadded_bound hN L
  have hhsmall : w * (L.h : ℝ) < 9 / 4 := by
    by_contra! hlarge
    have hlargeSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 4) hlarge 2
    linarith only [hsq, hlargeSq, show 0 ≤ ∑ i, a i ^ 2 by positivity]
  refine ⟨fun i => (mul_lt_mul_iff_left₀ hw).mp ?_, ?_⟩
  · linarith only [hhsmall, hNw i]
  · have hcs : (∑ i, a i) ^ 2 ≤ 3 * ∑ i, a i ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a))
    have hsmall : (∑ i, a i) < (43 : ℝ) / 9 := by
      by_contra! hlarge
      have hlargeSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 43 / 9) hlarge 2
      linarith only [hcs, hsq, hlargeSq, sq_nonneg (w * (L.h : ℝ))]
    have hcompare : ((43 : ℝ) / 9) * errorSum L.h L.p θ ≤ w * ∑ i, a i := by
      simp only [errorSum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ((N i : ℝ) * w) * |delta L.h L.p θ i| :=
          mul_le_mul_of_nonneg_right (hNw i).le (abs_nonneg _)
        _ = _ := by dsimp [a]; ring
    have hscaled := mul_lt_mul_of_pos_left hsmall hw
    linarith only [hcompare, hscaled]

private theorem short_label_unique {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {w : ℝ}
    (hN : ∀ i, 0 ≤ (N i : ℝ))
    (hNw : ∀ i, (43 : ℝ) / 9 < (N i : ℝ) * w) (L K : ShortLabel N θ w) : L = K := by
  have hrow (J : ShortLabel N θ w) (i : Fin 3) :
      ((N i : ℝ) * delta J.h J.p θ i) ^ 2 + (w * (J.h : ℝ)) ^ 2 ≤ (43 : ℝ) / 9 := by
    have hi : ((N i : ℝ) * delta J.h J.p θ i) ^ 2 ≤
        ∑ j, ((N j : ℝ) * |delta J.h J.p θ j|) ^ 2 := by
      rw [mul_pow, ← sq_abs (delta J.h J.p θ i), ← mul_pow]
      exact Finset.single_le_sum (fun j _ => sq_nonneg ((N j : ℝ) * |delta J.h J.p θ j|))
        (Finset.mem_univ i)
    exact (add_le_add hi (le_refl ((w * (J.h : ℝ)) ^ 2))).trans (unpadded_bound hN J)
  have hminor (i : Fin 3) : L.h * K.p i = K.h * L.p i := by
    let m : ℤ := L.h * K.p i - K.h * L.p i
    have hdet := abs_two_row_det_le (hrow L i) (hrow K i)
    have hfactor :
        ((N i : ℝ) * delta L.h L.p θ i) * (w * (K.h : ℝ)) -
        ((N i : ℝ) * delta K.h K.p θ i) * (w * (L.h : ℝ)) =
        ((N i : ℝ) * w) * (m : ℝ) := by
      dsimp [m, delta]
      push_cast
      ring
    have hmargin : 0 ≤ (N i : ℝ) * w := by linarith only [hNw i]
    rw [hfactor, abs_mul, abs_of_nonneg hmargin] at hdet
    have hsmall : |(m : ℝ)| < 1 := by
      by_contra! hlarge
      have := mul_le_mul_of_nonneg_left hlarge hmargin
      linarith only [this, hdet, hNw i]
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp (by exact_mod_cast hsmall) : m = 0)
  have hdiv (J J' : ShortLabel N θ w)
      (hcross : ∀ i, J.h * J'.p i = J'.h * J.p i) : J.h ∣ J'.h := by
    obtain ⟨u, v, hbez⟩ := J.primitive
    refine ⟨J'.h * u + ∑ i, J'.p i * v i, ?_⟩
    have hsum : J.h * (∑ i, J'.p i * v i) = J'.h * (∑ i, J.p i * v i) := by
      simp only [Finset.mul_sum, ← mul_assoc, hcross]
    calc
      J'.h = J'.h * (J.h * u + ∑ i, J.p i * v i) := by rw [hbez, mul_one]
      _ = J.h * (J'.h * u + ∑ i, J'.p i * v i) := by
        rw [mul_add, mul_add, hsum]
        ring
  have hLK := hdiv L K hminor
  have hKL := hdiv K L (fun i => (hminor i).symm)
  have hh : L.h = K.h :=
    le_antisymm (Int.le_of_dvd (by have := K.positive; omega) hLK)
      (Int.le_of_dvd (by have := L.positive; omega) hKL)
  have hp : L.p = K.p := by
    funext i
    have hi := hminor i
    rw [← hh] at hi
    exact (mul_left_cancel₀ (by have := L.positive; omega) hi).symm
  cases L
  cases K
  cases hh
  cases hp
  rfl

private theorem linear_box_image (c r x : Fin 3 → ℝ) (o y : ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hy : |y - (o + ∑ i, c i * x i)| ≤ ∑ i, r i * |x i|) :
    ∃ z : Fin 3 → ℝ, (∀ i, |z i - c i| ≤ r i) ∧ o + (∑ i, z i * x i) = y := by
  choose lo hi hlo₀ hlo₁ hhi₀ hhi₁ hlo hhi using
    fun i => axis_extremes (c i) (r i) (x i) (hr i)
  let z (s : ℝ) (i : Fin 3) := (1 - s) * lo i + s * hi i
  let f (s : ℝ) := o + ∑ i, z s i * x i
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f, z]
    fun_prop
  have hf₀ : f 0 = o + (∑ i, c i * x i) - ∑ i, r i * |x i| := by
    simp only [f, z, sub_zero, one_mul, zero_mul, add_zero, hlo, Finset.sum_sub_distrib]
    ring
  have hf₁ : f 1 = o + (∑ i, c i * x i) + ∑ i, r i * |x i| := by
    simp only [f, z, sub_self, zero_mul, one_mul, zero_add, hhi, Finset.sum_add_distrib]
    ring
  have hy' : y ∈ Set.Icc (f 0) (f 1) := by
    rw [hf₀, hf₁]
    obtain ⟨hy₀, hy₁⟩ := abs_le.mp hy
    exact ⟨by linarith only [hy₀], by linarith only [hy₁]⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hy'
  refine ⟨z s, fun i => abs_le.mpr ⟨?_, ?_⟩, hfs⟩
  · have hl := mul_le_mul_of_nonneg_left (hlo₀ i) (sub_nonneg.mpr hs.2)
    have hh := mul_le_mul_of_nonneg_left (hhi₀ i) hs.1
    dsimp only [z]
    linarith only [hl, hh]
  · have hl := mul_le_mul_of_nonneg_left (hlo₁ i) (sub_nonneg.mpr hs.2)
    have hh := mul_le_mul_of_nonneg_left (hhi₁ i) hs.1
    dsimp only [z]
    linarith only [hl, hh]

/-- A strict phase hit in the inset box survives rounding in its Bézout residues. -/
private theorem affine_hit_sufficient {N : Fin 3 → ℤ} {θ : Fin 3 → ℝ} {t w : ℝ}
    {L : ShortLabel N θ w} (hN : ∀ i, 2 * (L.h : ℝ) < (N i : ℝ))
    (hE : errorSum L.h L.p θ < w) (n : ℤ)
    (hn : |(n : ℝ) - phase N L.h L.p θ t w| <
      radius N L.h L.p θ w - (L.h : ℝ) * errorSum L.h L.p θ) :
    ∃ (b : Fin 3 → ℤ) (a : ℤ), (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      t < (∑ i, (b i : ℝ) * θ i) - (a : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (a : ℝ) < t + w := by
  have hh : 0 < L.h := by have := L.positive; omega
  let H : ℝ := L.h
  have hH : 0 < H := by
    change (0 : ℝ) < (L.h : ℝ)
    exact_mod_cast hh
  let x := delta L.h L.p θ
  let E := errorSum L.h L.p θ
  let c (i : Fin 3) := 3 * (N i : ℝ) / 2
  let r (i : Fin 3) := ((N i : ℝ) - H) / 2
  let T := H * (t + w / 2)
  let A := H * (w - E) / 2
  have hr (i : Fin 3) : 0 ≤ r i := by
    have hi : 2 * H < (N i : ℝ) := hN i
    dsimp only [r]
    linarith only [hi, hH]
  have hA : 0 < A := div_pos (mul_pos hH (sub_pos.mpr hE)) (by norm_num)
  have hband : (∑ i, r i * |x i|) + A = radius N L.h L.p θ w - H * E := by
    have hsum : (∑ i, r i * |x i|) = ((∑ i, (N i : ℝ) * |x i|) - H * E) / 2 := by
      calc
        _ = ∑ i, (1 / 2) * ((N i : ℝ) * |x i| - H * |x i|) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [r]
          ring
        _ = _ := by
          change _ = ((∑ i, (N i : ℝ) * |x i|) - H * (∑ i, |x i|)) / 2
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
    rw [hsum]
    change _ = (H * w + ∑ i, (N i : ℝ) * |x i|) / 2 - H * E
    dsimp only [A]
    ring
  have hclose : |((n : ℝ) + ∑ i, c i * x i) - T| < (∑ i, r i * |x i|) + A := by
    rw [hband]
    have hcenter : ((n : ℝ) + ∑ i, c i * x i) - T =
        (n : ℝ) - phase N L.h L.p θ t w := by
      change ((n : ℝ) + ∑ i, c i * x i) - T = (n : ℝ) - (T - ∑ i, c i * x i)
      ring
    rwa [hcenter]
  have hrad : 0 ≤ ∑ i, r i * |x i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (abs_nonneg _))
  obtain ⟨y, hyc, hyT⟩ := closed_open_overlap hrad hA hclose
  obtain ⟨z, hz, hy⟩ := linear_box_image c r x (n : ℝ) y hr hyc
  obtain ⟨u, v, hbez⟩ := L.primitive
  let d := L.h.toNat
  have hd : (d : ℤ) = L.h := Int.toNat_of_nonneg hh.le
  have hdpos : 0 < d := by
    exact_mod_cast (show (0 : ℤ) < (d : ℤ) by rwa [hd])
  have hdR : (d : ℝ) = H := by
    change (d : ℝ) = (L.h : ℝ)
    exact_mod_cast hd
  have hnearest (i : Fin 3) : ∃ b k : ℤ, b = n * v i + L.h * k ∧
      |(b : ℝ) - z i| ≤ H / 2 := by
    simpa only [hd, hdR] using nearest_residue d hdpos (n * v i) (z i)
  choose b k hb hbround using hnearest
  let a : ℤ := (∑ i, k i * L.p i) - n * u
  have hcong : (∑ i, b i * L.p i) - L.h * a = n := by
    have hsum : (∑ i, b i * L.p i) =
        n * (∑ i, L.p i * v i) + L.h * (∑ i, k i * L.p i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i]
      ring
    rw [hsum]
    dsimp only [a]
    linear_combination n * hbez
  have hbox (i : Fin 3) : N i ≤ b i ∧ b i ≤ 2 * N i := by
    obtain ⟨hz₀, hz₁⟩ := abs_le.mp (hz i)
    obtain ⟨hb₀, hb₁⟩ := abs_le.mp (hbround i)
    dsimp only [c, r] at hz₀ hz₁
    constructor
    · exact_mod_cast (show (N i : ℝ) ≤ (b i : ℝ) by linarith only [hz₀, hb₀])
    · exact_mod_cast (show (b i : ℝ) ≤ 2 * (N i : ℝ) by linarith only [hz₁, hb₁])
  let e := ∑ i, ((b i : ℝ) - z i) * x i
  have he : |e| ≤ H * E / 2 := calc
    |e| ≤ ∑ i, |((b i : ℝ) - z i) * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (H / 2) * |x i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hbround i) (abs_nonneg _)
    _ = H * E / 2 := by
      rw [← Finset.mul_sum]
      change H / 2 * E = H * E / 2
      ring
  have hlinear : H * ((∑ i, (b i : ℝ) * θ i) - (a : ℝ)) = y + e := by
    have hcongR : (∑ i, (b i : ℝ) * (L.p i : ℝ)) - H * (a : ℝ) = (n : ℝ) := by
      dsimp only [H]
      exact_mod_cast hcong
    have hsplit : H * (∑ i, (b i : ℝ) * θ i) =
        (∑ i, (b i : ℝ) * (L.p i : ℝ)) + ∑ i, (b i : ℝ) * x i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [x, delta, H]
      ring
    have hshift : (∑ i, (b i : ℝ) * x i) = (∑ i, z i * x i) + e := by
      dsimp only [e]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [mul_sub, hsplit, hshift]
    linarith only [hy, hcongR]
  obtain ⟨hy₀, hy₁⟩ := abs_lt.mp hyT
  obtain ⟨he₀, he₁⟩ := abs_le.mp he
  dsimp only [T, A] at hy₀ hy₁
  refine ⟨b, a, hbox, (mul_lt_mul_iff_right₀ hH).mp ?_, (mul_lt_mul_iff_right₀ hH).mp ?_⟩
  · linarith only [hy₀, he₀, hlinear]
  · linarith only [hy₁, he₁, hlinear]

public section

/-- A strict phase miss on the closed integer box gives the unique padded
primitive label, the exclusion of every integer in its inner phase band, and
the weighted width and denominator bounds. -/
theorem short_label_miss_obstruction
    (N : Fin 3 → ℤ) (θ : Fin 3 → ℝ) (t w : ℝ)
    (hw : 0 < w) (hNw : ∀ i, (43 : ℝ) / 9 < (N i : ℝ) * w)
    (hmiss : ¬ ∃ (b : Fin 3 → ℤ) (a : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      t < (∑ i, (b i : ℝ) * θ i) - (a : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (a : ℝ) < t + w) :
    ∃ L : ShortLabel N θ w,
      (∀ L' : ShortLabel N θ w, L' = L) ∧
      (∀ n : ℤ, radius N L.h L.p θ w - (L.h : ℝ) * errorSum L.h L.p θ ≤
        |(n : ℝ) - phase N L.h L.p θ t w|) ∧
      ((L.h : ℝ) * w + ∑ i, ((N i : ℝ) - 2 * (L.h : ℝ)) * |delta L.h L.p θ i|) ≤ 1 ∧
      (L.h : ℝ) ≤ 1 / w := by
  have hNpos (i : Fin 3) : 0 < (N i : ℝ) :=
    pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 43 / 9).trans (hNw i)) hw.le
  have hNint (i : Fin 3) : 1 ≤ N i := by
    have : 0 < N i := by exact_mod_cast hNpos i
    omega
  obtain ⟨h, p, hh, hsq⟩ := finite_integer_box_inverse_three N hNint θ t w hw hmiss
  obtain ⟨L⟩ := joint_gcd_reduction hh (show jointSquare N h p θ w ≤ 43 / 9 by
    simpa only [jointSquare, delta, mul_pow] using hsq)
  have hN (i : Fin 3) := (hNpos i).le
  obtain ⟨hscale, hE⟩ := short_scale_bounds hw hN hNw L
  have hphase (n : ℤ) : radius N L.h L.p θ w - (L.h : ℝ) * errorSum L.h L.p θ ≤
      |(n : ℝ) - phase N L.h L.p θ t w| :=
    le_of_not_gt (fun hn => hmiss (affine_hit_sufficient hscale hE n hn))
  let Xi := phase N L.h L.p θ t w
  have hnear : |((round Xi : ℤ) : ℝ) - Xi| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round Xi
  have hband : radius N L.h L.p θ w - (L.h : ℝ) * errorSum L.h L.p θ ≤ 1 / 2 :=
    (hphase (round Xi)).trans hnear
  have hweight : (∑ i, ((N i : ℝ) - 2 * (L.h : ℝ)) * |delta L.h L.p θ i|) =
      (∑ i, (N i : ℝ) * |delta L.h L.p θ i|) - 2 * (L.h : ℝ) * errorSum L.h L.p θ := by
    simp only [sub_mul, Finset.sum_sub_distrib, errorSum, ← Finset.mul_sum]
  have hwidth : (L.h : ℝ) * w +
      (∑ i, ((N i : ℝ) - 2 * (L.h : ℝ)) * |delta L.h L.p θ i|) ≤ 1 := by
    rw [hweight]
    unfold radius at hband
    linarith only [hband]
  have hnonneg : 0 ≤ ∑ i, ((N i : ℝ) - 2 * (L.h : ℝ)) * |delta L.h L.p θ i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hscale i).le) (abs_nonneg _))
  refine ⟨L, fun L' => short_label_unique hN hNw L' L, hphase, hwidth, (le_div_iff₀ hw).mpr ?_⟩
  linarith only [hwidth, hnonneg]

end

end D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover
