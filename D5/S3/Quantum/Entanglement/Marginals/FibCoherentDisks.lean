/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentDisks
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentDisks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A closed-form choice of the unobserved coupling for coherent Fibonacci marginals. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
import Mathlib.Analysis.Complex.Norm

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

private def coupling (x : ℂ) : Matrix Unit Unit ℂ := fun _ _ => x

private def split : Unit ⊕ Unit ≃ Fin 2 where
  toFun
    | .inl _ => 0
    | .inr _ => 1
  invFun i := if i = 0 then .inl () else .inr ()
  left_inv := by rintro (i | i) <;> cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem scalar_matrix (a : ℝ) : scalarBlock a = diagonal (fun _ => (a : ℂ)) := by
  ext i j
  cases i
  cases j
  simp [scalarBlock]

private theorem scalar_psd (a : ℝ) : (scalarBlock a).PosSemidef ↔ 0 ≤ a := by
  rw [scalar_matrix, posSemidef_diagonal_iff]
  simp [Complex.nonneg_iff]

private theorem block_schur (a d : ℝ) (x : ℂ) (ha : 0 < a) :
    (block a d x).PosSemidef ↔ normSq x ≤ a*d := by
  rw [← Matrix.posSemidef_submatrix_equiv split]
  have hblock : (block a d x).submatrix split split =
      fromBlocks (scalarBlock a) (coupling x) (coupling x)ᴴ (scalarBlock d) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [hblock]
  have hA : (scalarBlock a).PosDef := by
    rw [scalar_matrix, posDef_diagonal_iff]
    intro i
    simpa [Complex.lt_def] using ha
  let := hA.isUnit.invertible
  rw [Matrix.PosDef.fromBlocks₁₁ _ _ hA]
  have hr : scalarBlock d - (coupling x)ᴴ * (scalarBlock a)⁻¹ * coupling x =
      scalarBlock (d - normSq x / a) := by
    ext i j
    cases i
    cases j
    have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hi : (scalarBlock a)⁻¹ = diagonal (fun _ : Unit => (a : ℂ)⁻¹) := by
      apply Matrix.inv_eq_right_inv
      ext i j
      cases i
      cases j
      simp [scalarBlock, Matrix.mul_apply, hne]
    rw [hi]
    simp [scalarBlock, coupling, Matrix.mul_apply, Complex.ofReal_div]
    rw [← Complex.mul_conj]
    ring
  rw [hr, scalar_psd, sub_nonneg, div_le_iff₀ ha]
  rw [mul_comm]

private theorem block_zero (d : ℝ) (x : ℂ) :
    (block 0 d x).PosSemidef ↔ x = 0 ∧ 0 ≤ d := by
  constructor
  · intro h
    have hz := h.det_nonneg
    rw [block, Matrix.det_fin_two] at hz
    change 0 ≤ (0 : ℂ) * (d : ℂ) - x * conj x at hz
    rw [zero_mul, Complex.mul_conj] at hz
    have hx : normSq x = 0 := by
      have hn := (Complex.nonneg_iff.mp hz).1
      simp at hn
      exact le_antisymm hn (normSq_nonneg _)
    exact ⟨normSq_eq_zero.mp hx, by simpa [block, Complex.nonneg_iff] using h.diag_nonneg (i := 1)⟩
  · rintro ⟨rfl, hd⟩
    have hm : block 0 d 0 = diagonal ![0, (d : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [block]
    rw [hm]
    exact .diagonal (by intro i; fin_cases i <;> simp [Complex.nonneg_iff, hd])

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


private noncomputable def disk (a e : ℝ) (c k : ℂ) : ℂ × ℝ :=
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
    rw [block_schur _ _ _ ha]
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
    rw [block_zero]
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


private def boolIndex : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro b; cases b <;> decide

private noncomputable def edgeDisk (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w : ℂ) : ℂ × ℝ :=
  disk (b*(L false false).re - normSq u - normSq w)
    (b*(L true true).re - normSq v)
    ((b : ℂ)*L false true - conj u*v) w

private theorem edgeDisk_spec (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w z : ℂ)
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
  rw [hpos, ← Matrix.posSemidef_submatrix_equiv boolIndex]
  have hm : ((b : ℂ) • G).submatrix boolIndex boolIndex =
      block (b*(L false false).re - normSq u - normSq w)
        (b*(L true true).re - normSq v - normSq z)
        ((b : ℂ)*L false true - conj u * v - conj w * z) := by
    ext i j
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    fin_cases i <;> fin_cases j <;>
      simp [G, block, boolIndex, Matrix.vecMulVec_apply, correction, partialTraceRight,
        middleRow, Complex.ofReal_mul, Complex.ofReal_inv, hdiag, hc,
        ← Complex.mul_conj, Complex.ofReal_sub] <;>
      field_simp <;> ring
  rw [hm]
  exact disk_spec _ _ _ _ _

private theorem swapped_trace (b : ℝ) (u v w z : ℂ) :
    partialTraceLeft (correction b (middleRow u v w z)) =
      partialTraceRight (correction b (middleRow u w v z)) := by
  ext i j
  cases i <;> cases j <;>
    simp [partialTraceLeft, partialTraceRight, correction, middleRow, Matrix.vecMulVec_apply]

/-- The coupling given by the two residual disks. -/
noncomputable def selectedCoupling (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) : ℂ :=
  let left := edgeDisk b L u v w
  let right := edgeDisk b R u w v
  diskPoint left.1 right.1 left.2 right.2

/-- For positive middle weight, testing the selected coupling decides common extension. -/
theorem extendible_iff_selected (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : 0 < b) (hL : L.IsHermitian) (hR : R.IsHermitian) :
    CoherentExtendible b L R u v w ↔
      L.trace + (b : ℂ) = 1 ∧ R.trace = L.trace ∧
      (L - partialTraceRight
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef ∧
      (R - partialTraceLeft
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef := by
  rw [coherent_extendible_iff]
  constructor
  · rintro ⟨_, hn, ht, z, _, hl, hr⟩
    rw [swapped_trace] at hr ⊢
    have hd := (diskPoint_iff (edgeDisk b L u v w).1 (edgeDisk b R u w v).1
      (edgeDisk b L u v w).2 (edgeDisk b R u w v).2).mp
      ⟨z, (edgeDisk_spec _ _ _ _ _ _ hb hL).mp hl, (edgeDisk_spec _ _ _ _ _ _ hb hR).mp hr⟩
    exact ⟨hn, ht, (edgeDisk_spec _ _ _ _ _ _ hb hL).mpr hd.1,
      (edgeDisk_spec _ _ _ _ _ _ hb hR).mpr hd.2⟩
  · rintro ⟨hn, ht, hl, hr⟩
    exact ⟨hb.le, hn, ht, _, fun h => (hb.ne' h).elim, hl, hr⟩

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
