/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentDisks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A closed-form choice of the unobserved coupling for coherent Fibonacci marginals. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
/-! Closed-form selection for the residual disks of coherent Fibonacci marginals. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder Matrix
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks

private noncomputable def diskWeight (d r s : ℝ) : ℝ :=
  min 1 (max 0 ((d + r - s) / (2 * d)))

private noncomputable def diskPoint (p q : ℂ) (r s : ℝ) : ℂ :=
  let t := diskWeight (normSq (q - p)) r s
  p + (t : ℂ) * (q - p)

private theorem disk_identity (p q z : ℂ) (t : ℝ) :
    (1-t) * normSq (z-p) + t * normSq (z-q) =
      normSq (z-(p+(t : ℂ)*(q-p))) + t*(1-t)*normSq (q-p) := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, zero_mul, sub_zero]
  ring

private theorem disk_distances (p q : ℂ) (t : ℝ) :
    normSq (p + (t : ℂ)*(q-p) - p) = t^2 * normSq (q-p) ∧
    normSq (p + (t : ℂ)*(q-p) - q) = (1-t)^2 * normSq (q-p) := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, zero_mul, sub_zero]
  constructor <;> ring

private theorem diskPoint_iff (p q : ℂ) (r s : ℝ) :
    (∃ z : ℂ, normSq (z-p) ≤ r ∧ normSq (z-q) ≤ s) ↔
      normSq (diskPoint p q r s-p) ≤ r ∧ normSq (diskPoint p q r s-q) ≤ s := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨z, hr, hs⟩
  by_cases he : p = q
  · subst q
    simpa [diskPoint] using
      And.intro ((normSq_nonneg _).trans hr) ((normSq_nonneg _).trans hs)
  let d := normSq (q-p)
  have hd : 0 < d := normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm he))
  have hden : 0 < 2*d := by positivity
  let u := (d+r-s)/(2*d)
  let t := diskWeight d r s
  have hrad : 0 ≤ r := (normSq_nonneg _).trans hr
  have hsad : 0 ≤ s := (normSq_nonneg _).trans hs
  change normSq (p+(t : ℂ)*(q-p)-p) ≤ r ∧ normSq (p+(t : ℂ)*(q-p)-q) ≤ s
  obtain ⟨h₁, h₂⟩ := disk_distances p q t
  rw [h₁, h₂]
  by_cases hlo : u ≤ 0
  · have ht : t = 0 := by
      change min 1 (max 0 u) = 0
      rw [max_eq_left hlo, min_eq_right (by norm_num)]
    have h : d+r-s ≤ 0 := (div_le_iff₀ hden).mp hlo |>.trans_eq (zero_mul _)
    change t^2*d ≤ r ∧ (1-t)^2*d ≤ s
    rw [ht]
    constructor <;> nlinarith
  by_cases hhi : 1 ≤ u
  · have ht : t = 1 := by
      change min 1 (max 0 u) = 1
      exact min_eq_left (hhi.trans (le_max_right _ _))
    have h : 1 * (2*d) ≤ d+r-s := (le_div_iff₀ hden).mp hhi
    change t^2*d ≤ r ∧ (1-t)^2*d ≤ s
    rw [ht]
    constructor <;> nlinarith
  have htp : 0 ≤ t := by
    change 0 ≤ min 1 (max 0 u)
    exact le_min (by norm_num) (le_max_left _ _)
  have htq : t ≤ 1 := min_le_left _ _
  have ht : t = u := by
    change min 1 (max 0 u) = u
    rw [max_eq_right (le_of_not_ge hlo), min_eq_right (le_of_not_ge hhi)]
  have heq : t * (2*d) = d+r-s := by
    rw [ht]
    exact div_mul_cancel₀ _ hden.ne'
  have hbalance : t^2*d-r = (1-t)^2*d-s := by nlinarith only [heq]
  have hsum : t*(1-t)*d ≤ (1-t)*r+t*s := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr htq))
      (mul_le_mul_of_nonneg_left hs htp)
    rw [disk_identity] at h
    exact (le_add_of_nonneg_left (normSq_nonneg _)).trans h
  change t^2*d ≤ r ∧ (1-t)^2*d ≤ s
  constructor <;> nlinarith only [hsum, heq, hbalance, congrArg (fun a => t*a) heq]


private def block (a d : ℝ) (x : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑a, x; conj x, ↑d]

private def scalarBlock (a : ℝ) : Matrix Unit Unit ℂ := fun _ _ => a

private abbrev split : Unit ⊕ Unit ≃ Fin 2 :=
  (Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv

private theorem scalar_psd (a : ℝ) : (scalarBlock a).PosSemidef ↔ 0 ≤ a := by
  have hm : scalarBlock a = diagonal (fun _ => (a : ℂ)) := by
    ext i j
    cases i
    cases j
    simp [scalarBlock]
  rw [hm, posSemidef_diagonal_iff]
  simp [Complex.nonneg_iff]

private theorem block_criterion (a d : ℝ) (x : ℂ) :
    (block a d x).PosSemidef ↔ 0 ≤ a ∧ (a = 0 → x = 0) ∧ 0 ≤ d - normSq x / a := by
  rw [← Matrix.posSemidef_submatrix_equiv split]
  have hm : (block a d x).submatrix split split =
      assemble a (fun _ : Unit => x) (scalarBlock d) := by
    ext i j
    cases i <;> cases j <;> rfl
  have hc : scalarBlock d - correction a (fun _ : Unit => x) =
      scalarBlock (d - normSq x / a) := by
    ext i j
    simp [scalarBlock, correction, Matrix.vecMulVec_apply, Complex.ofReal_div,
      ← Complex.mul_conj]
    ring
  rw [hm, block_psd, hc, scalar_psd]
  simp [funext_iff]

private theorem completing_square (a e : ℝ) (c k z : ℂ) :
    let h := a + normSq k
    let p := k * c / (h : ℂ)
    h ≠ 0 →
      a * (e - normSq z) - normSq (c - conj k * z) =
        a*e - normSq c + h * normSq p - h * normSq (z-p) := by
  dsimp only
  intro hh
  have hdiv : ((a + normSq k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh
  set t : ℝ := (a + normSq k)⁻¹
  have hscale : (a + normSq k) * t = 1 := mul_inv_cancel₀ hh
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  change a * (e - normSq z) - normSq (c - conj k * z) =
    a*e - normSq c + (a + normSq k) * normSq (k*c*(t : ℂ)) -
      (a + normSq k) * normSq (z-k*c*(t : ℂ))
  rw [normSq_sub z]
  have hnorm : normSq (conj k * z) = normSq k * normSq z := by
    rw [normSq_mul, normSq_conj]
  have hcross : (a + normSq k) * (z * conj (k*c*(t : ℂ))).re =
      (c * conj (conj k * z)).re := by
    have hcscale : (↑(a + normSq k) : ℂ) * (t : ℂ) = 1 := by exact_mod_cast hscale
    rw [← Complex.re_ofReal_mul]
    rw [← Complex.conj_re (c * conj (conj k * z))]
    apply congrArg Complex.re
    simp only [map_mul, conj_ofReal, conj_conj]
    calc
      (↑(a + normSq k) : ℂ) * (z * (conj k * conj c * ↑t)) =
          (↑(a + normSq k) * ↑t) * (z * conj k * conj c) := by ring
      _ = conj c * (conj k * z) := by rw [hcscale, one_mul]; ring
  rw [normSq_sub c, hnorm]
  linarith only [hcross]


noncomputable def disk (a e : ℝ) (c k : ℂ) : ℂ × ℝ :=
  let h := a + normSq k
  let p := k * c / (h : ℂ)
  if 0 < a then
    (p, (a*e - normSq c + h * normSq p) / h)
  else if a = 0 then
    if k = 0 then (0, if c = 0 then e else -1)
    else (p, if normSq p ≤ e then 0 else -1)
  else (0, -1)

private theorem disk_spec (a e : ℝ) (c k z : ℂ) :
    (block a (e-normSq z) (c-conj k*z)).PosSemidef ↔
      normSq (z-(disk a e c k).1) ≤ (disk a e c k).2 := by
  by_cases ha : 0 < a
  · simp only [disk, ite_eq_left ha]
    rw [block_criterion, and_iff_right ha.le,
      and_iff_right (fun h => (ha.ne' h).elim), sub_nonneg, div_le_iff₀ ha,
      mul_comm (e - normSq z) a]
    let h := a + normSq k
    let p := k*c / (h : ℂ)
    have hh : 0 < h := add_pos_of_pos_of_nonneg ha (normSq_nonneg _)
    change normSq (c-conj k*z) ≤ a*(e-normSq z) ↔
      normSq (z-p) ≤ (a*e - normSq c + h*normSq p)/h
    rw [le_div_iff₀ hh]
    have he := completing_square a e c k z hh.ne'
    change a*(e-normSq z) - normSq (c-conj k*z) =
      a*e-normSq c+h*normSq p-h*normSq (z-p) at he
    constructor <;> intro ht <;> linarith only [he, ht]
  by_cases hz : a = 0
  · subst a
    simp only [block_criterion, le_refl, true_and, true_implies, div_zero, sub_zero]
    by_cases hk : k = 0
    · subst k
      by_cases hc : c = 0
      · subst c
        simp [disk, sub_nonneg]
      · simp [disk, hc, show ¬ normSq z ≤ -1 by linarith [normSq_nonneg z]]
    · have hkn : normSq k ≠ 0 := fun h => hk (normSq_eq_zero.mp h)
      have hkn' : (↑(normSq k) : ℂ) ≠ 0 := by exact_mod_cast hkn
      have hkc : conj k ≠ 0 := by
        intro h
        exact hk (by simpa using congrArg conj h)
      let p := k*c / (normSq k : ℂ)
      have hp : conj k * p = c := by
        dsimp [p]
        rw [mul_div_assoc, ← mul_assoc, mul_comm (conj k) k, mul_conj]
        rw [← mul_div_assoc]; exact mul_div_cancel_left₀ c hkn'
      have hz : c - conj k*z = 0 ↔ z = p := by
        rw [sub_eq_zero, ← hp]
        exact ⟨fun h => mul_left_cancel₀ hkc h.symm, fun h => congrArg (conj k * ·) h.symm⟩
      simp only [disk, lt_irrefl, ↓reduceIte, hk, zero_add]
      change (c - conj k*z = 0 ∧ 0 ≤ e-normSq z) ↔
        normSq (z-p) ≤ if normSq p ≤ e then 0 else -1
      rw [hz, sub_nonneg]
      by_cases hpe : normSq p ≤ e
      · rw [ite_eq_left hpe]
        have heq : normSq (z-p) ≤ 0 ↔ z = p := by
          rw [← sub_eq_zero (a := z)]
          exact ⟨fun ht => normSq_eq_zero.mp (le_antisymm ht (normSq_nonneg _)),
            fun ht => by simp [ht]⟩
        rw [heq]
        exact ⟨And.left, fun h => ⟨h, h.symm ▸ hpe⟩⟩
      · rw [ite_eq_right hpe]
        constructor
        · rintro ⟨rfl, h⟩
          exact (hpe h).elim
        · intro h
          linarith [normSq_nonneg (z-p)]
  · simp only [disk, ite_eq_right ha, ite_eq_right hz]
    constructor
    · intro h
      have hn := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
      change 0 ≤ (a : ℂ).re at hn
      rw [ofReal_re] at hn
      exact (ha (lt_of_le_of_ne hn (Ne.symm hz))).elim
    · intro h
      linarith [normSq_nonneg (z-0)]


noncomputable def edgeDisk (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w : ℂ) : ℂ × ℝ :=
  disk (b*(L false false).re - normSq u - normSq w)
    (b*(L true true).re - normSq v)
    ((b : ℂ)*L false true - conj u*v) w

theorem edgeDisk_spec (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (hb : 0 < b) (hL : L.IsHermitian) :
    (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef ↔
      normSq (z-(edgeDisk b L u v w).1) ≤ (edgeDisk b L u v w).2 := by
  let G := L - partialTraceRight (correction b (middleRow u v w z))
  have hb' : (0 : ℂ) < (b : ℂ) := by exact_mod_cast hb
  have hpos : G.PosSemidef ↔ ((b : ℂ) • G).PosSemidef := by
    refine ⟨fun h => h.smul hb'.le, fun h => ?_⟩
    have hinv : (0 : ℂ) ≤ (b⁻¹ : ℝ) := by exact_mod_cast (inv_nonneg.mpr hb.le)
    have hnz : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hs := h.smul hinv
    change ((↑(b⁻¹) : ℂ) • ((b : ℂ) • G)).PosSemidef at hs
    rwa [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hnz, one_smul] at hs
  have hdiag (i : Bool) : (↑(L i i).re : ℂ) = L i i := by
    apply Complex.ext
    · simp
    · have hh := congrArg Complex.im (hL.apply i i)
      simp at hh ⊢
      linarith
  have hc : conj (L false true) = L true false := hL.apply _ _
  rw [hpos, ← Matrix.posSemidef_submatrix_equiv finTwoEquiv]
  have hm : ((b : ℂ) • G).submatrix finTwoEquiv finTwoEquiv =
      block (b*(L false false).re - normSq u - normSq w)
        (b*(L true true).re - normSq v - normSq z)
        ((b : ℂ)*L false true - conj u * v - conj w * z) := by
    ext i j
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    fin_cases i <;> fin_cases j <;>
      simp [G, block, finTwoEquiv, Matrix.vecMulVec_apply, correction, partialTraceRight,
        middleRow, Complex.ofReal_mul, Complex.ofReal_inv, hdiag, hc,
        ← Complex.mul_conj, Complex.ofReal_sub] <;>
      field_simp <;> ring
  rw [hm]
  exact disk_spec _ _ _ _ _

theorem swapped_trace (b : ℝ) (u v w z : ℂ) :
    partialTraceLeft (correction b (middleRow u v w z)) =
      partialTraceRight (correction b (middleRow u w v z)) := by
  ext i j
  cases i <;> cases j <;>
    simp [partialTraceLeft, partialTraceRight, correction, middleRow, Matrix.vecMulVec_apply]

/-- The coupling given by the two residual disks. -/
noncomputable def selectedCoupling (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) : ℂ :=
  if b = 0 then 0
  else
    let left := edgeDisk b L u v w
    let right := edgeDisk b R u w v
    diskPoint left.1 right.1 left.2 right.2

/-- Testing the selected coupling decides common extension, including zero middle weight. -/
theorem extendible_iff_selected (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) :
    CoherentExtendible b L R u v w ↔
      0 ≤ b ∧ L.trace + (b : ℂ) = 1 ∧ R.trace = L.trace ∧
      (b = 0 → middleRow u v w (selectedCoupling b L R u v w) = 0) ∧
      (L - partialTraceRight
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef ∧
      (R - partialTraceLeft
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef := by
  rw [coherent_extendible_iff]
  constructor
  · rintro ⟨hb, hn, ht, z, hzero, hl, hr⟩
    rcases hb.eq_or_lt with heq | hb
    · subst b
      have hz : z = 0 := congrFun (hzero rfl) (true, true)
      subst z
      simpa [selectedCoupling] using
        And.intro (le_refl (0 : ℝ)) (And.intro hn (And.intro ht ⟨hzero rfl, hl, hr⟩))
    refine ⟨hb.le, hn, ht, (fun heq => (hb.ne' heq).elim), ?_⟩
    have hc : (correction b (middleRow u v w z)).PosSemidef := by
      unfold correction
      exact (posSemidef_vecMulVec_star_self _).smul (inv_nonneg.mpr hb.le)
    have hL : L.IsHermitian := by
      simpa using (hl.add (partialTraceRight_posSemidef hc)).isHermitian
    have hR : R.IsHermitian := by
      simpa using (hr.add (partialTraceLeft_posSemidef hc)).isHermitian
    rw [swapped_trace] at hr ⊢
    have hd := (diskPoint_iff (edgeDisk b L u v w).1 (edgeDisk b R u w v).1
      (edgeDisk b L u v w).2 (edgeDisk b R u w v).2).mp
      ⟨z, (edgeDisk_spec _ _ _ _ _ _ hb hL).mp hl, (edgeDisk_spec _ _ _ _ _ _ hb hR).mp hr⟩
    simpa only [selectedCoupling, ite_eq_right hb.ne'] using
      And.intro ((edgeDisk_spec _ _ _ _ _ _ hb hL).mpr hd.1)
        ((edgeDisk_spec _ _ _ _ _ _ hb hR).mpr hd.2)
  · rintro ⟨hb, hn, ht, hzero, hl, hr⟩
    exact ⟨hb, hn, ht, _, hzero, hl, hr⟩

open FibRationalPureExtension

def RationalReal (x : ℝ) : Prop := ∃ a : ℚ, (a : ℝ) = x

theorem realMk {x : ℝ} (h : RationalReal x) : RationalEntry (x : ℂ) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, 0, hq, by simp⟩

private theorem rnormSq {z : ℂ} (hz : RationalEntry z) : RationalReal (normSq z) := by
  obtain ⟨a, b, ha, hb⟩ := hz
  exact ⟨a*a + b*b, by simp [ha, hb, Complex.normSq_apply]⟩

private theorem clipping {x : ℝ} (hx : RationalReal x) :
    RationalReal (min 1 (max 0 x)) := by
  by_cases h0 : x ≤ 0
  · rw [max_eq_left h0, min_eq_right (by norm_num)]
    exact ⟨0, by simp⟩
  by_cases h1 : 1 ≤ x
  · rw [max_eq_right (le_of_not_ge h0), min_eq_left h1]
    exact ⟨1, by simp⟩
  rwa [max_eq_right (le_of_not_ge h0), min_eq_right (le_of_not_ge h1)]

private theorem rational_selected (p q : ℂ) (r s : ℝ)
    (hp : RationalEntry p) (hq : RationalEntry q) (hr : RationalReal r) (hs : RationalReal s) :
    RationalEntry (diskPoint p q r s) := by
  unfold diskPoint diskWeight
  dsimp only
  apply rationalComplex.add_mem hp
  apply rationalComplex.mul_mem (realMk (clipping ?_)) (rationalComplex.sub_mem hq hp)
  obtain ⟨u, hu⟩ := rnormSq (rationalComplex.sub_mem hq hp)
  obtain ⟨v, hv⟩ := hr
  obtain ⟨w, hw⟩ := hs
  exact ⟨(u+v-w)/(2*u), by simp [hu, hv, hw]⟩

theorem rreal {z : ℂ} (h : RationalEntry z) : RationalReal z.re := by
  obtain ⟨a, _, ha, _⟩ := h
  exact ⟨a, ha⟩

private theorem rradd {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) :
    RationalReal (x+y) := by
  obtain ⟨xq, hxq⟩ := hx
  obtain ⟨yq, hyq⟩ := hy
  exact ⟨xq+yq, by simp [hxq, hyq]⟩

theorem rrsub {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) :
    RationalReal (x-y) := by
  obtain ⟨xq, hxq⟩ := hx
  obtain ⟨yq, hyq⟩ := hy
  exact ⟨xq-yq, by simp [hxq, hyq]⟩

theorem rrmul {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) :
    RationalReal (x*y) := by
  obtain ⟨xq, hxq⟩ := hx
  obtain ⟨yq, hyq⟩ := hy
  exact ⟨xq*yq, by simp [hxq, hyq]⟩

private theorem rrdiv {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) :
    RationalReal (x/y) := by
  obtain ⟨xq, hxq⟩ := hx
  obtain ⟨yq, hyq⟩ := hy
  exact ⟨xq/yq, by simp [hxq, hyq]⟩

private theorem diskRational (a e : ℝ) (c k : ℂ) (ha : RationalReal a)
    (he : RationalReal e) (hc : RationalEntry c) (hk : RationalEntry k) :
    RationalEntry (disk a e c k).1 ∧ RationalReal (disk a e c k).2 := by
  have hd := rradd ha (rnormSq hk)
  have hp := rationalComplex.div_mem (rationalComplex.mul_mem hk hc) (realMk hd)
  unfold disk
  split
  · exact ⟨hp, rrdiv (rradd (rrsub (rrmul ha he) (rnormSq hc))
      (rrmul hd (rnormSq hp))) hd⟩
  · split
    · split
      · refine ⟨rationalComplex.zero_mem, ?_⟩
        split
        · exact he
        · exact ⟨-1, by simp⟩
      · refine ⟨hp, ?_⟩
        dsimp only
        split
        · exact ⟨0, by simp⟩
        · exact ⟨-1, by simp⟩
    · exact ⟨rationalComplex.zero_mem, ⟨-1, by simp⟩⟩

theorem edgeDiskRational (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : RationalReal b) (hl : ∀ i j, RationalEntry (L i j))
    (hu : RationalEntry u) (hv : RationalEntry v) (hw : RationalEntry w) :
    RationalEntry (edgeDisk b L u v w).1 ∧ RationalReal (edgeDisk b L u v w).2 :=
  diskRational _ _ _ _
    (rrsub (rrsub (rrmul hb (rreal (hl false false))) (rnormSq hu)) (rnormSq hw))
    (rrsub (rrmul hb (rreal (hl true true))) (rnormSq hv))
    (rationalComplex.sub_mem (rationalComplex.mul_mem (realMk hb) (hl false true))
      (rationalComplex.mul_mem (rationalConjugate ⟨u, hu⟩).property hv)) hw

private theorem selected_rational (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : RationalReal b)
    (hl : ∀ i j, RationalEntry (L i j)) (hr : ∀ i j, RationalEntry (R i j))
    (hu : RationalEntry u) (hv : RationalEntry v) (hw : RationalEntry w) :
    RationalEntry (selectedCoupling b L R u v w) := by
  unfold selectedCoupling
  split
  · exact rationalComplex.zero_mem
  · obtain ⟨hlp, hlr⟩ := edgeDiskRational b L u v w hb hl hu hv hw
    obtain ⟨hrp, hrr⟩ := edgeDiskRational b R u w v hb hr hu hw hv
    exact rational_selected _ _ _ _ hlp hrp hlr hrr

open FibMarginalExtension (Word edgeTrace)

/-- Compatible rational edge data have a rational common extension at the selected coupling. -/
theorem rational_coherent_extendible_iff (b : ℝ) (L R : Matrix Bool Bool ℂ)
    (u v w : ℂ)
    (hl : ∀ i j, RationalEntry (L i j)) (hr : ∀ i j, RationalEntry (R i j))
    (hu : RationalEntry u) (hv : RationalEntry v) (hw : RationalEntry w) :
    CoherentExtendible b L R u v w ↔
      ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧
        ρ.trace = 1 ∧ edgeTrace ρ 1 2 = coherentEdge b L u v ∧
        edgeTrace ρ 2 1 = coherentEdge b R u w ∧
        ρ (.inl 0) (.inr true) = selectedCoupling b L R u v w ∧
        ∀ i j, RationalEntry (ρ i j) := by
  constructor
  · intro h
    obtain ⟨hb', ht, hr', hzero, hleft, hright⟩ :=
      (extendible_iff_selected b L R u v w).mp h
    have htq : RationalEntry L.trace := rationalComplex.sum_mem fun i _ => hl i i
    have hb : RationalReal b := by
      obtain ⟨q, hq⟩ := rreal htq
      have he := congrArg Complex.re ht
      simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at he
      refine ⟨1-q, ?_⟩
      push_cast
      rw [hq]
      linarith
    obtain ⟨ρ, hp, ⟨hn, hL, hR, hz⟩, hq⟩ :=
      rational_extension_at b L R u v w _ hb' ht hr' hzero hleft hright
        hl hr hu hv hw (selected_rational b L R u v w hb hl hr hu hv hw)
    exact ⟨ρ, hp, hn, hL, hR, hz, hq⟩
  · rintro ⟨ρ, hp, ht, hleft, hright, _, _⟩
    exact ⟨ρ, hp, ht, hleft, hright⟩

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
