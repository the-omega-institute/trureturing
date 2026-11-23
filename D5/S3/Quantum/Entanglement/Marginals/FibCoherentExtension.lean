/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A scalar coherence criterion for common positive Fibonacci marginal extensions. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension

/-! Common extensions of adjacent Fibonacci marginals with arbitrary coherences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder Kronecker Matrix
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension

private def pivot (b : ℝ) : Matrix Unit Unit ℂ := diagonal fun _ => (b : ℂ)

private def cross {n : Type*} (v : n → ℂ) : Matrix Unit n ℂ := fun _ i => v i

private def assemble {n : Type*} (b : ℝ) (v : n → ℂ) (T : Matrix n n ℂ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  fromBlocks (pivot b) (cross v) (cross v)ᴴ T

/-- The term subtracted from the endpoint density by eliminating the middle singleton. -/
noncomputable def correction {n : Type*} (b : ℝ) (v : n → ℂ) : Matrix n n ℂ :=
  (b⁻¹ : ℝ) • vecMulVec (star v) v

private theorem pivot_isUnit {b : ℝ} (hb : b ≠ 0) : IsUnit (pivot b) := by
  apply Matrix.isUnit_diagonal.mpr
  exact Pi.isUnit_iff.mpr fun _ => isUnit_iff_ne_zero.mpr (by exact_mod_cast hb)

private theorem block_psd_iff {n : Type*} [Fintype n]
    (b : ℝ) (hb : 0 < b) (v : n → ℂ) (T : Matrix n n ℂ) :
    (assemble b v T).PosSemidef ↔ (T - correction b v).PosSemidef := by
  have hp : (pivot b).PosDef := Matrix.PosDef.diagonal fun _ => by
    change (0 : ℂ) < (b : ℂ)
    exact_mod_cast hb
  let := (pivot_isUnit hb.ne').invertible
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hinv : (pivot b)⁻¹ = diagonal (fun _ : Unit => (b : ℂ)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    ext i j
    cases i
    cases j
    simp [pivot, Matrix.mul_apply, hbc]
  have hc : (cross v)ᴴ * (pivot b)⁻¹ * cross v = correction b v := by
    ext i j
    rw [hinv]
    simp [Matrix.mul_apply, correction, cross, Matrix.vecMulVec_apply]
    ring
  unfold assemble
  rw [Matrix.PosDef.fromBlocks₁₁ _ _ hp, hc]

private theorem zero_cross {n : Type*} [Fintype n] {v : n → ℂ} {T : Matrix n n ℂ}
    (h : (assemble 0 v T).PosSemidef) : v = 0 := by
  funext j
  let e : Fin 2 → Unit ⊕ n := ![.inl (), .inr j]
  have hd := (h.submatrix e).det_nonneg
  rw [Matrix.det_fin_two] at hd
  change 0 ≤ (0 : ℂ) * T j j - v j * (starRingEnd ℂ) (v j) at hd
  rw [Complex.mul_conj] at hd
  have hd' := (Complex.nonneg_iff.mp hd).1
  simp at hd'
  exact Complex.normSq_eq_zero.mp (le_antisymm (by linarith) (Complex.normSq_nonneg _))

private theorem block_zero_psd {n : Type*} [Fintype n] {T : Matrix n n ℂ}
    (hT : T.PosSemidef) : (assemble 0 (0 : n → ℂ) T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.fromBlocks
    · simp [pivot]
    · rfl
    · exact hT.isHermitian
  · intro x
    simpa [assemble, pivot, cross, dotProduct, mulVec, Fintype.sum_sum_type] using
      hT.dotProduct_mulVec_nonneg (x ∘ Sum.inr)

private theorem block_psd {n : Type*} [Fintype n] (b : ℝ) (v : n → ℂ)
    (T : Matrix n n ℂ) :
    (assemble b v T).PosSemidef ↔
      0 ≤ b ∧ (b = 0 → v = 0) ∧ (T - correction b v).PosSemidef := by
  constructor
  · intro h
    have hd := h.diag_nonneg (i := Sum.inl ())
    have hb : 0 ≤ b := by simpa [assemble, pivot] using (Complex.nonneg_iff.mp hd).1
    refine ⟨hb, ?_, ?_⟩
    · rintro rfl
      exact zero_cross h
    · rcases hb.eq_or_lt with h0 | hp
      · subst b
        have hT : T.PosSemidef := h.submatrix Sum.inr
        simpa [correction] using hT
      · exact (block_psd_iff b hp v T).mp h
  · rintro ⟨hb, h0, hT⟩
    rcases hb.eq_or_lt with hz | hp
    · subst b
      rw [h0 rfl]
      exact block_zero_psd (by simpa [correction] using hT)
    · exact (block_psd_iff b hp v T).mpr hT

private theorem partialTraceRight_sub {A C : Type*} [Fintype C]
    (X Y : Matrix (A × C) (A × C) ℂ) :
    partialTraceRight (X - Y) = partialTraceRight X - partialTraceRight Y := by
  ext i j
  simp [partialTraceRight, Finset.sum_sub_distrib]

private theorem partialTraceLeft_sub {A C : Type*} [Fintype A]
    (X Y : Matrix (A × C) (A × C) ℂ) :
    partialTraceLeft (X - Y) = partialTraceLeft X - partialTraceLeft Y := by
  ext i j
  simp [partialTraceLeft, Finset.sum_sub_distrib]

private theorem product_completion {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (L : Matrix A A ℂ) (R : Matrix C C ℂ) (hL : L.PosSemidef) (hR : R.PosSemidef)
    (htr : L.trace = R.trace) :
    ∃ S : Matrix (A × C) (A × C) ℂ, S.PosSemidef ∧
      partialTraceRight S = L ∧ partialTraceLeft S = R := by
  by_cases hz : L.trace = 0
  · rw [(hL.trace_eq_zero_iff).mp hz, (hR.trace_eq_zero_iff).mp (htr.symm.trans hz)]
    exact ⟨0, .zero, by ext; simp [partialTraceRight], by ext; simp [partialTraceLeft]⟩
  have hlo := hL.trace_nonneg
  have ht : 0 ≤ L.trace⁻¹ := by
    rw [Complex.nonneg_iff] at hlo ⊢
    simp [Complex.inv_re, Complex.inv_im, ← hlo.2, div_nonneg hlo.1 (Complex.normSq_nonneg _)]
  refine ⟨L.trace⁻¹ • kronecker L R, (hL.kronecker hR).smul ht, ?_, ?_⟩
  · have hm : partialTraceRight (L.trace⁻¹ • kronecker L R) =
        L.trace⁻¹ • partialTraceRight (kronecker L R) := by
      ext i j
      simp [partialTraceRight, Finset.mul_sum]
    rw [hm, partialTraceRight_kronecker, ← htr, smul_smul, inv_mul_cancel₀ hz, one_smul]
  · have hm : partialTraceLeft (L.trace⁻¹ • kronecker L R) =
        L.trace⁻¹ • partialTraceLeft (kronecker L R) := by
      ext i j
      simp [partialTraceLeft, Finset.mul_sum]
    rw [hm, partialTraceLeft_kronecker, smul_smul, inv_mul_cancel₀ hz, one_smul]

private theorem block_marginals_iff {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (b : ℝ) (v : A × C → ℂ)
    (L : Matrix A A ℂ) (R : Matrix C C ℂ) (htr : L.trace = R.trace) :
    (∃ T : Matrix (A × C) (A × C) ℂ, (assemble b v T).PosSemidef ∧
      partialTraceRight T = L ∧ partialTraceLeft T = R) ↔
      0 ≤ b ∧ (b = 0 → v = 0) ∧
      (L - partialTraceRight (correction b v)).PosSemidef ∧
      (R - partialTraceLeft (correction b v)).PosSemidef := by
  constructor
  · rintro ⟨T, hT, rfl, rfl⟩
    obtain ⟨hb, hz, hS⟩ := (block_psd b v T).mp hT
    exact ⟨hb, hz, by simpa [partialTraceRight_sub] using partialTraceRight_posSemidef hS,
      by simpa [partialTraceLeft_sub] using partialTraceLeft_posSemidef hS⟩
  · rintro ⟨hb, hv, hL, hR⟩
    obtain ⟨S, hS, hsL, hsR⟩ := product_completion _ _ hL hR (by
      simp [Matrix.trace_sub, htr, trace_partialTraceRight, trace_partialTraceLeft])
    refine ⟨S + correction b v, (block_psd _ _ _).mpr ⟨hb, hv, ?_⟩, ?_, ?_⟩
    · simpa using hS
    · simp [partialTraceRight_add, hsL]
    · simp [partialTraceLeft_add, hsR]


open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word Site edgeTrace)
open private vacuum endpoints from D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension

private def wordEquiv : Unit ⊕ (Bool × Bool) ≃ Word where
  toFun
    | .inl _ => .inl 0
    | .inr (false, false) => .inr false
    | .inr (true, false) => .inl 1
    | .inr (false, true) => .inl 2
    | .inr (true, true) => .inr true
  invFun
    | .inl i => ![.inl (), .inr (true, false), .inr (false, true)] i
    | .inr b => .inr (b, b)
  left_inv := by
    rintro (_ | ⟨a, c⟩)
    · rfl
    · cases a <;> cases c <;> rfl
  right_inv := by
    rintro (i | b)
    · fin_cases i <;> rfl
    · cases b <;> rfl

/-- The middle row of the full endpoint-coherent chain, in left-right occupation order. -/
def middleRow (empty left right both : ℂ) : Bool × Bool → ℂ
  | (false, false) => empty
  | (true, false) => left
  | (false, true) => right
  | (true, true) => both

/-- Measured edge in the order vacuum, occupied middle, occupied endpoint. -/
def coherentEdge (b : ℝ) (L : Matrix Bool Bool ℂ) (u v : ℂ) : Matrix Site Site ℂ :=
  !![L false false, star u, L false true;
      u, ↑b, v;
      L true false, star v, L true true]

/-- Two coherent edge matrices are reductions of the same legal trace-one state. -/
def CoherentExtendible (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) : Prop :=
  ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
    edgeTrace ρ 1 2 = coherentEdge b L u v ∧ edgeTrace ρ 2 1 = coherentEdge b R u w

private def original (M : Matrix (Unit ⊕ (Bool × Bool)) (Unit ⊕ (Bool × Bool)) ℂ) :
    Matrix Word Word ℂ := M.submatrix wordEquiv.symm wordEquiv.symm

private theorem trace_original
    (M : Matrix (Unit ⊕ (Bool × Bool)) (Unit ⊕ (Bool × Bool)) ℂ) :
    (original M).trace = M.trace := by
  unfold original
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply] using
    Fintype.sum_equiv wordEquiv.symm (fun x => M (wordEquiv.symm x) (wordEquiv.symm x))
      (fun i => M i i) (fun _ => rfl)

private theorem trace_assemble (b : ℝ) (row : Bool × Bool → ℂ)
    (T : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (assemble b row T).trace = T.trace + (b : ℂ) := by
  simp [Matrix.trace, Fintype.sum_sum_type, assemble, pivot, add_comm]

private theorem left_read (b : ℝ) (row : Bool × Bool → ℂ)
    (T : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    edgeTrace (original (assemble b row T)) 1 2 =
      coherentEdge b (partialTraceRight T) (row (false, false)) (row (true, false)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeTrace, original, assemble,
    wordEquiv, cross, pivot, coherentEdge, partialTraceRight, vacuum, endpoints, add_comm]

private theorem right_read (b : ℝ) (row : Bool × Bool → ℂ)
    (T : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    edgeTrace (original (assemble b row T)) 2 1 =
      coherentEdge b (partialTraceLeft T) (row (false, false)) (row (false, true)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeTrace, original, assemble,
    wordEquiv, cross, pivot, coherentEdge, partialTraceLeft, vacuum, endpoints, add_comm]

private theorem split_state (ρ : Matrix Word Word ℂ) (hρ : ρ.IsHermitian) :
    let b := (ρ (.inl 0) (.inl 0)).re
    let v := fun i => ρ (.inl 0) (wordEquiv (.inr i))
    let T := ρ.submatrix (fun i => wordEquiv (.inr i)) (fun i => wordEquiv (.inr i))
    original (assemble b v T) = ρ := by
  dsimp only
  ext i j
  have hd : ρ (.inl 0) (.inl 0) = (↑(ρ (.inl 0) (.inl 0)).re : ℂ) := by
    have he := hρ.apply (.inl 0) (.inl 0)
    have hi := congrArg Complex.im he
    simp at hi
    apply Complex.ext
    · simp
    · simp
      linarith
  obtain ⟨k, rfl⟩ := wordEquiv.surjective i
  obtain ⟨l, rfl⟩ := wordEquiv.surjective j
  simp only [original, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases k <;> cases l
  · cases ‹Unit›
    cases ‹Unit›
    exact hd.symm
  · rfl
  · exact hρ.apply _ _
  · rfl

/-- Common extensions are determined by the consistency of the two reduced residuals after
one chooses the unobserved coupling from the middle singleton to double occupation. -/
theorem coherent_extendible_iff (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) :
    CoherentExtendible b L R u v w ↔
      0 ≤ b ∧ L.trace + (b : ℂ) = 1 ∧ R.trace = L.trace ∧
      ∃ z : ℂ, (b = 0 → middleRow u v w z = 0) ∧
        (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef ∧
        (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef := by
  constructor
  · rintro ⟨ρ, hρ, htrace, hleft, hright⟩
    let b' := (ρ (.inl 0) (.inl 0)).re
    let row := fun i => ρ (.inl 0) (wordEquiv (.inr i))
    let T := ρ.submatrix (fun i => wordEquiv (.inr i)) (fun i => wordEquiv (.inr i))
    have hsplit : original (assemble b' row T) = ρ := split_state ρ hρ.isHermitian
    have hPSD : (assemble b' row T).PosSemidef := by
      apply (Matrix.posSemidef_submatrix_equiv wordEquiv.symm).mp
      change (original (assemble b' row T)).PosSemidef
      rwa [hsplit]
    rw [← hsplit, left_read] at hleft
    rw [← hsplit, right_read] at hright
    have hb : b' = b := by
      have e := congrFun (congrFun hleft 1) 1
      change (b' : ℂ) = (b : ℂ) at e
      exact_mod_cast e
    have hL : partialTraceRight T = L := by
      ext i j
      cases i <;> cases j
      · exact congrFun (congrFun hleft 0) 0
      · exact congrFun (congrFun hleft 0) 2
      · exact congrFun (congrFun hleft 2) 0
      · exact congrFun (congrFun hleft 2) 2
    have hR : partialTraceLeft T = R := by
      ext i j
      cases i <;> cases j
      · exact congrFun (congrFun hright 0) 0
      · exact congrFun (congrFun hright 0) 2
      · exact congrFun (congrFun hright 2) 0
      · exact congrFun (congrFun hright 2) 2
    have hrow : row = middleRow u v w (row (true, true)) := by
      funext i
      obtain ⟨a, c⟩ := i
      cases a <;> cases c
      · exact congrFun (congrFun hleft 1) 0
      · exact congrFun (congrFun hright 1) 2
      · exact congrFun (congrFun hleft 1) 2
      · rfl
    have htrL : L.trace = T.trace := hL ▸ trace_partialTraceRight T
    have htrR : R.trace = T.trace := hR ▸ trace_partialTraceLeft T
    have htr : L.trace = R.trace := htrL.trans htrR.symm
    have ht : L.trace + (b : ℂ) = 1 := by
      rw [← hsplit, trace_original, trace_assemble, hb, ← htrL] at htrace
      exact htrace
    rw [hb, hrow] at hPSD
    obtain ⟨hn, hz, hL', hR'⟩ := (block_marginals_iff b _ L R htr).mp ⟨T, hPSD, hL, hR⟩
    exact ⟨hn, ht, htr.symm, row (true, true), hz, hL', hR'⟩
  · rintro ⟨hb, htr, hr, z, hz, hL, hR⟩
    let row := middleRow u v w z
    obtain ⟨T, hPSD, hLT, hRT⟩ :=
      (block_marginals_iff b row L R hr.symm).mpr ⟨hb, hz, hL, hR⟩
    refine ⟨original (assemble b row T), hPSD.submatrix _, ?_, ?_, ?_⟩
    · rw [trace_original, trace_assemble, ← trace_partialTraceRight T, hLT]
      exact htr
    · rw [left_read, hLT]
      rfl
    · rw [right_read, hRT]
      rfl

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
