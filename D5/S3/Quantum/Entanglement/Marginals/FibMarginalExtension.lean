/- GID: D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibMarginalExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact common positive extensions of two Fibonacci edge marginals. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt

/-! Common positive extensions of the two nearest-neighbor marginals of three Fibonacci sites. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder
open Matrix

namespace D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension

abbrev Site := Fin 3

private def blockData (M : Matrix Site Site ℂ) (a b c : ℝ) (α β : ℂ) : Prop :=
  M 0 0 = (b : ℂ) ∧ M 1 1 = (a : ℂ) ∧ M 2 2 = (c : ℂ) ∧
    M 1 0 = α ∧ M 2 0 = β

private theorem bound {M : Matrix Site Site ℂ} (hM : M.PosSemidef)
    {i : Site} {a b : ℝ} {z : ℂ}
    (ha : M i i = (a : ℂ)) (hb : M 0 0 = (b : ℂ)) (hz : M i 0 = z) :
    Complex.normSq z ≤ b * a := by
  let e : Fin 2 → Site := ![0, i]
  have h := (hM.submatrix e).det_nonneg
  have hz' : M 0 i = star z := by
    rw [← hz]
    exact (hM.isHermitian.apply 0 i).symm
  have hdet : (M.submatrix e e).det = (b : ℂ) * (a : ℂ) - z * star z := by
    rw [Matrix.det_fin_two]
    change M 0 0 * M i i - M 0 i * M i 0 = _
    rw [hb, ha, hz', hz, mul_comm (star z)]
  rw [hdet] at h
  change 0 ≤ (b : ℂ) * (a : ℂ) - z * (starRingEnd ℂ) z at h
  rw [Complex.mul_conj] at h
  exact sub_nonneg.mp (by simpa using (Complex.nonneg_iff.mp h).1)

private theorem exists_block_iff (a b c : ℝ) (α β : ℂ) :
    (∃ M : Matrix Site Site ℂ, M.PosSemidef ∧ blockData M a b c α β) ↔
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ Complex.normSq α ≤ b*a ∧ Complex.normSq β ≤ b*c := by
  constructor
  · rintro ⟨M, h, ha0, ha1, ha2, hα, hβ⟩
    have db := h.diag_nonneg (i := 0)
    have da := h.diag_nonneg (i := 1)
    have dc := h.diag_nonneg (i := 2)
    rw [ha0] at db
    rw [ha1] at da
    rw [ha2] at dc
    exact ⟨(Complex.nonneg_iff.mp da).1, (Complex.nonneg_iff.mp db).1,
      (Complex.nonneg_iff.mp dc).1, bound h ha1 ha0 hα, bound h ha2 ha0 hβ⟩
  · rintro ⟨ha, hb, hc, hα, hβ⟩
    rcases hb.eq_or_lt with hb0 | hbpos
    · cases hb0
      have hα0 : α = 0 := Complex.normSq_eq_zero.mp
        (le_antisymm (by simpa using hα) (Complex.normSq_nonneg _))
      have hβ0 : β = 0 := Complex.normSq_eq_zero.mp
        (le_antisymm (by simpa using hβ) (Complex.normSq_nonneg _))
      let d : Site → ℝ := ![0, a, c]
      refine ⟨diagonal (fun i => (d i : ℂ)), .diagonal ?_, ?_⟩
      · intro i
        apply Complex.nonneg_iff.mpr
        fin_cases i <;> simp [d, ha, hc]
      · simp [blockData, d, hα0, hβ0]
    · let s := Real.sqrt b
      have hs : 0 < s := Real.sqrt_pos.2 hbpos
      have hs2 : s * s = b := Real.mul_self_sqrt hb
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      let u : Site → ℂ := ![(s : ℂ), α / (s : ℂ), β / (s : ℂ)]
      let d : Site → ℝ := ![0, a - Complex.normSq α / b, c - Complex.normSq β / b]
      have ha' : Complex.normSq α / b ≤ a :=
        (div_le_iff₀ hbpos).mpr (by rw [mul_comm]; exact hα)
      have hc' : Complex.normSq β / b ≤ c :=
        (div_le_iff₀ hbpos).mpr (by rw [mul_comm]; exact hβ)
      have hd : (0 : Site → ℂ) ≤ fun i => (d i : ℂ) := by
        intro i
        apply Complex.nonneg_iff.mpr
        fin_cases i <;> simp [d, ha', hc']
      refine ⟨vecMulVec u (star u) + diagonal (fun i => (d i : ℂ)),
        (posSemidef_vecMulVec_self_star u).add (.diagonal hd), ?_⟩
      have hbs : (s : ℂ) * (s : ℂ) = (b : ℂ) := by exact_mod_cast hs2
      have normTerm (z : ℂ) : (z / (s : ℂ)) * star (z / (s : ℂ)) =
          ((Complex.normSq z / b : ℝ) : ℂ) := by
        change (z / (s : ℂ)) * (starRingEnd ℂ) (z / (s : ℂ)) = _
        rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hbs,
          Complex.mul_conj, Complex.ofReal_div]
      have starS : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
      have entry (i j : Site) :
          (vecMulVec u (star u) + diagonal (fun i => (d i : ℂ))) i j =
            u i * star (u j) + if i = j then (d i : ℂ) else 0 := by
        simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.diagonal_apply]
      unfold blockData
      simp only [entry]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change (s : ℂ) * star (s : ℂ) + 0 = _
        rw [starS, add_zero, hbs]
      · change (α / (s : ℂ)) * star (α / (s : ℂ)) + (↑(a - Complex.normSq α / b) : ℂ) = _
        rw [normTerm, Complex.ofReal_sub]
        ring
      · change (β / (s : ℂ)) * star (β / (s : ℂ)) + (↑(c - Complex.normSq β / b) : ℂ) = _
        rw [normTerm, Complex.ofReal_sub]
        ring
      · change α / (s : ℂ) * star (s : ℂ) + 0 = _
        rw [starS, add_zero, div_mul_cancel₀ _ hsc]
      · change β / (s : ℂ) * star (s : ℂ) + 0 = _
        rw [starS, add_zero, div_mul_cancel₀ _ hsc]

private def BlockExtendible (pA pB pC : ℝ) (α β : ℂ) : Prop :=
  ∃ q : ℝ, 0 ≤ q ∧ 0 ≤ 1 - pA - pB - pC + q ∧
    ∃ M : Matrix Site Site ℂ, M.PosSemidef ∧
      blockData M (pA - q) pB (pC - q) α β

private theorem block_extendible_iff (pA pB pC : ℝ) (α β : ℂ) :
    let q₀ := max 0 (pA + pB + pC - 1)
    BlockExtendible pA pB pC α β ↔
      q₀ ≤ pA ∧ 0 ≤ pB ∧ q₀ ≤ pC ∧
      Complex.normSq α ≤ pB * (pA - q₀) ∧
      Complex.normSq β ≤ pB * (pC - q₀) := by
  dsimp only
  unfold BlockExtendible
  simp only [exists_block_iff]
  constructor
  · rintro ⟨q, hq, hw, ha, hb, hc, hα, hβ⟩
    have hmin : max 0 (pA + pB + pC - 1) ≤ q := max_le hq (by linarith)
    exact ⟨by linarith, hb, by linarith,
      hα.trans (mul_le_mul_of_nonneg_left (by linarith) hb),
      hβ.trans (mul_le_mul_of_nonneg_left (by linarith) hb)⟩
  · rintro ⟨ha, hb, hc, hα, hβ⟩
    refine ⟨_, le_max_left _ _, ?_, sub_nonneg.mpr ha, hb, sub_nonneg.mpr hc, hα, hβ⟩
    linarith [le_max_right 0 (pA + pB + pC - 1)]


/-- The three singleton words, followed by the empty word and the occupied endpoint pair. -/
abbrev Word := Site ⊕ Bool

private def vacuum : Word := .inr false
private def endpoints : Word := .inr true

/-- Partial trace over the outside site. Local order is empty, middle, measured endpoint. -/
def edgeTrace (ρ : Matrix Word Word ℂ) (endpoint outside : Site) :
    Matrix Site Site ℂ := fun i j =>
  let empty : Site → Word := ![vacuum, .inl 0, .inl endpoint]
  let occupied : Site → Option Word := ![some (.inl outside), none, some endpoints]
  ρ (empty i) (empty j) + match occupied i, occupied j with
  | some u, some v => ρ u v
  | _, _ => 0

/-- A two-site state with no adjacent occupations and no inter-sector entries. -/
def edgeState (p b : ℝ) (z : ℂ) : Matrix Site Site ℂ :=
  !![↑(1 - p - b : ℝ), 0, 0; 0, ↑b, star z; 0, z, ↑p]

/-- Both edge states are traces of one positive semidefinite, trace-one chain state. -/
def Extendible (pA pB pC : ℝ) (α β : ℂ) : Prop :=
  ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
    edgeTrace ρ 1 2 = edgeState pA pB α ∧ edgeTrace ρ 2 1 = edgeState pC pB β

private theorem completion_psd (M : Matrix Site Site ℂ) (hM : M.PosSemidef)
    (w q : ℝ) (hw : 0 ≤ w) (hq : 0 ≤ q) :
    (fromBlocks M 0 0 (diagonal (fun b : Bool => (if b then q else w : ℂ)))).PosSemidef := by
  have hD : (diagonal (fun b : Bool => (if b then q else w : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro b
    cases b <;> simp [Complex.nonneg_iff, hw, hq]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.fromBlocks
    · exact hM.isHermitian
    · simp
    · exact hD.isHermitian
  · intro x
    have h₁ := hM.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h₂ := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    change 0 ≤ star x ⬝ᵥ (_ *ᵥ x)
    simpa only [dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add, Pi.star_apply, Function.comp_apply] using
      add_nonneg h₁ h₂

private theorem extendible_iff_block (pA pB pC : ℝ) (α β : ℂ) :
    Extendible pA pB pC α β ↔ BlockExtendible pA pB pC α β := by
  constructor
  · rintro ⟨ρ, hρ, hTr, hL, hR⟩
    let q := (ρ endpoints endpoints).re
    have hq' := Complex.nonneg_iff.mp (hρ.diag_nonneg (i := endpoints))
    have hw' := Complex.nonneg_iff.mp (hρ.diag_nonneg (i := vacuum))
    have hq : ρ endpoints endpoints = (q : ℂ) := by
      apply Complex.ext <;> simp [q, hq'.2]
    have hb := congrFun (congrFun hL 1) 1
    have ha := congrFun (congrFun hL 2) 2
    have hc := congrFun (congrFun hR 2) 2
    have hz₁ := congrFun (congrFun hL 2) 1
    have hz₂ := congrFun (congrFun hR 2) 1
    simp [edgeTrace, edgeState] at hb ha hc hz₁ hz₂
    have ha' : ρ (.inl 1) (.inl 1) = (↑(pA - q) : ℂ) := by
      rw [hq] at ha
      rw [Complex.ofReal_sub, eq_sub_iff_add_eq]
      exact ha
    have hc' : ρ (.inl 2) (.inl 2) = (↑(pC - q) : ℂ) := by
      rw [hq] at hc
      rw [Complex.ofReal_sub, eq_sub_iff_add_eq]
      exact hc
    refine ⟨q, hq'.1, ?_, ρ.submatrix Sum.inl Sum.inl, hρ.submatrix Sum.inl,
      hb, ha', hc', hz₁, hz₂⟩
    have ht := congrArg Complex.re hTr
    change (ρ.trace).re = 1 at ht
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, Fintype.sum_bool, hb, ha', hc'] at ht
    change (↑pB + ↑(pA - q) + ↑(pC - q) +
      (ρ endpoints endpoints + ρ vacuum vacuum)).re = 1 at ht
    rw [hq] at ht
    simp only [Complex.add_re, Complex.ofReal_re] at ht
    linarith [hw'.1]
  · rintro ⟨q, hq, hw, M, hM, hb, ha, hc, hα, hβ⟩
    let w := 1 - pA - pB - pC + q
    let ρ : Matrix Word Word ℂ :=
      fromBlocks M 0 0 (diagonal fun b : Bool => (if b then (q : ℂ) else (w : ℂ)))
    have hρ : ρ.PosSemidef := completion_psd M hM w q hw hq
    have hα' : M 0 1 = star α := by
      rw [← hα]
      exact (hM.isHermitian.apply 0 1).symm
    have hβ' : M 0 2 = star β := by
      rw [← hβ]
      exact (hM.isHermitian.apply 0 2).symm
    refine ⟨ρ, hρ, ?_, ?_, ?_⟩
    · simp [ρ, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_three,
        ha, hb, hc, w]
      ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ρ, edgeTrace, edgeState, vacuum, endpoints, ha, hb, hc, hα, hα', w]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ρ, edgeTrace, edgeState, vacuum, endpoints, ha, hb, hc, hβ, hβ', w]
      ring

/-- The minimum weight of the word with both endpoints occupied. -/
def minDouble (pA pB pC : ℝ) : ℝ := max 0 (pA + pB + pC - 1)

/-- A pair of particle-number-invariant Fibonacci edge states has a common extension exactly
when the minimum possible double-occupation weight leaves enough mass for both coherences. -/
theorem extendible_iff (pA pB pC : ℝ) (α β : ℂ) :
    Extendible pA pB pC α β ↔
      minDouble pA pB pC ≤ pA ∧ 0 ≤ pB ∧ minDouble pA pB pC ≤ pC ∧
      Complex.normSq α ≤ pB * (pA - minDouble pA pB pC) ∧
      Complex.normSq β ≤ pB * (pC - minDouble pA pB pC) :=
  (extendible_iff_block pA pB pC α β).trans (block_extendible_iff pA pB pC α β)

end D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
