/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A scalar coherence criterion for common positive Fibonacci marginal extensions. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
import D5.S3.Quantum.Decoherence.LabelResetSupport
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

/-! Common extensions of adjacent Fibonacci marginals with arbitrary coherences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder Kronecker Matrix
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension

private def pivot (b : ℝ) : Matrix Unit Unit ℂ := diagonal fun _ => (b : ℂ)

private def cross {n : Type*} (v : n → ℂ) : Matrix Unit n ℂ := fun _ i => v i

/-- Assemble a Hermitian scalar pivot with its coupling row and residual block. -/
def assemble {n : Type*} (b : ℝ) (v : n → ℂ) (T : Matrix n n ℂ) :
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

/-- Positivity of a scalar pivot, including its zero case. -/
theorem block_psd {n : Type*} [Fintype n] (b : ℝ) (v : n → ℂ)
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

private theorem product_completion_formula {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (L : Matrix A A ℂ) (R : Matrix C C ℂ) (hL : L.PosSemidef) (hR : R.PosSemidef)
    (htr : L.trace = R.trace) :
    let S := kronecker (L.trace⁻¹ • L) R
    S.PosSemidef ∧ partialTraceRight S = L ∧ partialTraceLeft S = R := by
  dsimp only
  by_cases hz : L.trace = 0
  · rw [(hL.trace_eq_zero_iff).mp hz, (hR.trace_eq_zero_iff).mp (htr.symm.trans hz)]
    have hk : kronecker (((0 : Matrix A A ℂ).trace)⁻¹ • (0 : Matrix A A ℂ))
        (0 : Matrix C C ℂ) = 0 := by
      ext i j
      simp
    rw [hk]
    exact ⟨.zero, by ext; simp [partialTraceRight], by ext; simp [partialTraceLeft]⟩
  have hlo := hL.trace_nonneg
  have ht : 0 ≤ L.trace⁻¹ := by
    rw [Complex.nonneg_iff] at hlo ⊢
    simp [Complex.inv_re, Complex.inv_im, ← hlo.2, div_nonneg hlo.1 (Complex.normSq_nonneg _)]
  refine ⟨(hL.smul ht).kronecker hR, ?_, ?_⟩
  · rw [partialTraceRight_kronecker, ← htr, smul_smul, mul_inv_cancel₀ hz, one_smul]
  · rw [partialTraceLeft_kronecker, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hz, one_smul]


private theorem product_completion {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (L : Matrix A A ℂ) (R : Matrix C C ℂ) (hL : L.PosSemidef) (hR : R.PosSemidef)
    (htr : L.trace = R.trace) :
    ∃ S : Matrix (A × C) (A × C) ℂ, S.PosSemidef ∧
      partialTraceRight S = L ∧ partialTraceLeft S = R := by
  let S := kronecker (L.trace⁻¹ • L) R
  obtain ⟨hS, hleft, hright⟩ := product_completion_formula L R hL hR htr
  exact ⟨S, hS, hleft, hright⟩

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
    wordEquiv, cross, pivot, coherentEdge, partialTraceRight, add_comm]
  all_goals first | rfl | exact add_comm _ _

private theorem right_read (b : ℝ) (row : Bool × Bool → ℂ)
    (T : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    edgeTrace (original (assemble b row T)) 2 1 =
      coherentEdge b (partialTraceLeft T) (row (false, false)) (row (false, true)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [edgeTrace, original, assemble,
    wordEquiv, cross, pivot, coherentEdge, partialTraceLeft, add_comm]
  all_goals first | rfl | exact add_comm _ _

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

private theorem recover_edge_data (b d : ℝ) (L R : Matrix Bool Bool ℂ)
    (u v w : ℂ) (row : Bool × Bool → ℂ) (T : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hleft : coherentEdge d (partialTraceRight T) (row (false, false))
      (row (true, false)) = coherentEdge b L u v)
    (hright : coherentEdge d (partialTraceLeft T) (row (false, false))
      (row (false, true)) = coherentEdge b R u w) :
    partialTraceRight T = L ∧ partialTraceLeft T = R ∧
      row = middleRow u v w (row (true, true)) := by
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
  exact ⟨hL, hR, hrow⟩

/-- The two residual endpoint marginals determine whether a common extension exists
for a choice of the unobserved coupling from the middle singleton to double occupation. -/
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
    obtain ⟨hL, hR, hrow⟩ := recover_edge_data b b' L R u v w row T hleft hright
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

open D5.S3.Quantum.PureState.PureStateHandshake
open scoped ComplexConjugate

private theorem pure_correction {n : Type*} (x : ℂ) (y : n → ℂ)
    (hx : 0 < Complex.normSq x) :
    correction (Complex.normSq x) (fun i => x * star (y i)) = rankOneDensity y := by
  ext i j
  change (((Complex.normSq x)⁻¹ : ℝ) : ℂ) *
      (star (x * star (y i)) * (x * star (y j))) = y i * star (y j)
  have hmul : star x * x = ((Complex.normSq x : ℝ) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj x
  calc
    _ = (((Complex.normSq x)⁻¹ : ℝ) : ℂ) * (star x * x) * (y i * star (y j)) := by
      simp only [star_mul, star_star]
      ring
    _ = _ := by
      rw [hmul, ← Complex.ofReal_mul, inv_mul_cancel₀ hx.ne', Complex.ofReal_one, one_mul]

private theorem pure_from_positive_pivot {n : Type*} (b : ℝ) (v : n → ℂ) (hb : 0 < b) :
    ∃ ψ : Unit ⊕ n → ℂ, assemble b v (correction b v) = rankOneDensity ψ := by
  let x := Real.sqrt b
  let z : ℂ := x
  have hnorm : Complex.normSq z = b := by
    rw [show z = (x : ℂ) from rfl, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt hb.le
  have hx : z ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hnorm
    exact hb.ne' hnorm.symm
  let y : n → ℂ := fun i => star (v i / z)
  have hv (i : n) : z * star (y i) = v i := by
    simp only [y, star_star]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hx]
  have hrow : (fun i => z * star (y i)) = v := funext hv
  have hcor := pure_correction z y (hnorm ▸ hb)
  rw [hnorm, hrow] at hcor
  refine ⟨Sum.elim (fun _ => z) y, ?_⟩
  rw [hcor]
  ext i j
  rcases i with (_ | i) <;> rcases j with (_ | j)
  · change (b : ℂ) = z * (conj z)
    rw [Complex.mul_conj, hnorm]
  · exact (hv j).symm
  · change star (v i) = y i * star z
    rw [← hv i, star_mul, star_star]
  · rfl


/-- Trace normalization and agreement with the specified edge marginals and coupling. -/
def MatchesCoherentData (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (ρ : Matrix Word Word ℂ) : Prop :=
  ρ.trace = 1 ∧ edgeTrace ρ 1 2 = coherentEdge b L u v ∧
    edgeTrace ρ 2 1 = coherentEdge b R u w ∧ ρ (.inl 0) (.inr true) = z

private theorem extension_blocks {b : ℝ} {L R : Matrix Bool Bool ℂ} {u v w z : ℂ}
    {ρ : Matrix Word Word ℂ} (hρ : ρ.PosSemidef)
    (hdata : MatchesCoherentData b L R u v w z ρ) :
    ∃ T : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      original (assemble b (middleRow u v w z) T) = ρ ∧
      (T - correction b (middleRow u v w z)).PosSemidef ∧
      partialTraceRight T = L ∧ partialTraceLeft T = R := by
  obtain ⟨_, hl, hr, hz⟩ := hdata
  let d := (ρ (.inl 0) (.inl 0)).re
  let row := fun i => ρ (.inl 0) (wordEquiv (.inr i))
  let T := ρ.submatrix (fun i => wordEquiv (.inr i)) (fun i => wordEquiv (.inr i))
  have hsplit : original (assemble d row T) = ρ := split_state ρ hρ.isHermitian
  rw [← hsplit, left_read] at hl
  rw [← hsplit, right_read] at hr
  have hd : d = b := by
    have e := congrFun (congrFun hl 1) 1
    change (d : ℂ) = (b : ℂ) at e
    exact_mod_cast e
  obtain ⟨hL, hR, hrow⟩ := recover_edge_data b d L R u v w row T hl hr
  have hz' : row (true, true) = z := hz
  rw [hd, hrow, hz'] at hsplit
  have hblock : (assemble b (middleRow u v w z) T).PosSemidef := by
    apply (Matrix.posSemidef_submatrix_equiv wordEquiv.symm).mp
    change (original (assemble b (middleRow u v w z) T)).PosSemidef
    rwa [hsplit]
  exact ⟨T, hsplit, ((block_psd _ _ _).mp hblock).2.2, hL, hR⟩

/-- At nonzero middle occupation, a pure extension exists exactly when the normalization
and both zero-residual equations hold. If it exists, every positive extension with the
same data equals it. -/
theorem pure_coherent_iff (b : ℝ) (L R : Matrix Bool Bool ℂ)
    (u v w z : ℂ) (hb : b ≠ 0) :
    ((∃ ρ : Matrix Word Word ℂ,
      (∃ ψ : Word → ℂ, ρ = rankOneDensity ψ) ∧ MatchesCoherentData b L R u v w z ρ) ↔
      L.trace + (b : ℂ) = 1 ∧
        L = partialTraceRight (correction b (middleRow u v w z)) ∧
        R = partialTraceLeft (correction b (middleRow u v w z))) ∧
    (∀ (ψ : Word → ℂ) (ρ : Matrix Word Word ℂ),
      MatchesCoherentData b L R u v w z (rankOneDensity ψ) →
      ρ.PosSemidef → MatchesCoherentData b L R u v w z ρ → ρ = rankOneDensity ψ) := by
  let row₀ := middleRow u v w z
  let T₀ := correction b row₀
  let ρ₀ := original (assemble b row₀ T₀)
  have recover (ψ : Word → ℂ) (hψ : MatchesCoherentData b L R u v w z (rankOneDensity ψ)) :
      rankOneDensity ψ = ρ₀ ∧ L = partialTraceRight T₀ ∧ R = partialTraceLeft T₀ := by
    obtain ⟨_, hl, hr, hz⟩ := hψ
    let x := ψ (.inl 0)
    let y := fun i : Bool × Bool => ψ (wordEquiv (.inr i))
    let row := fun i => x * star (y i)
    let T := rankOneDensity y
    have hb' : Complex.normSq x = b := by
      have obs := congrFun (congrFun hl 1) 1
      change x * conj x + 0 = (b : ℂ) at obs
      rw [add_zero, Complex.mul_conj] at obs
      exact Complex.ofReal_injective obs
    have hsplit : original (assemble b row T) = rankOneDensity ψ := by
      have hp : (rankOneDensity ψ).PosSemidef :=
        Matrix.posSemidef_vecMulVec_self_star ψ
      have hh := split_state (rankOneDensity ψ) hp.isHermitian
      change original (assemble (x * conj x).re row T) = rankOneDensity ψ at hh
      rw [Complex.mul_conj, Complex.ofReal_re, hb'] at hh
      exact hh
    rw [← hsplit, left_read] at hl
    rw [← hsplit, right_read] at hr
    obtain ⟨hL, hR, hrow⟩ := recover_edge_data b b L R u v w row T hl hr
    have hz' : row (true, true) = z := hz
    rw [hz'] at hrow
    have hx : 0 < Complex.normSq x :=
      lt_of_le_of_ne (Complex.normSq_nonneg x) (by rw [hb']; exact Ne.symm hb)
    have hcor := pure_correction x y hx
    change correction (Complex.normSq x) row = T at hcor
    rw [hb', hrow] at hcor
    change T₀ = T at hcor
    refine ⟨?_, hcor.symm ▸ hL.symm, hcor.symm ▸ hR.symm⟩
    rw [← hsplit, hrow, ← hcor]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨ρ, ⟨ψ, rfl⟩, hψ⟩
      obtain ⟨he, hL, hR⟩ := recover ψ hψ
      refine ⟨?_, hL, hR⟩
      obtain ⟨htrace, _, _, _⟩ := hψ
      rw [he] at htrace
      change (original (assemble b row₀ T₀)).trace = 1 at htrace
      rwa [trace_original, trace_assemble, ← trace_partialTraceRight T₀, ← hL] at htrace
    · rintro ⟨htrace, hL, hR⟩
      have htraceT : T₀.trace + (b : ℂ) = 1 := by
        rwa [← trace_partialTraceRight T₀, ← hL]
      have hbpos : 0 < b := by
        by_contra! hn
        have hprod : T₀.trace = ((b⁻¹ * ∑ i, Complex.normSq (row₀ i) : ℝ) : ℂ) := by
          dsimp only [T₀, correction]
          rw [Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct, Complex.ofReal_mul,
            Complex.ofReal_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm]
          exact Complex.mul_conj _
        have hnonpos : (T₀.trace).re ≤ 0 := by
          rw [hprod, Complex.ofReal_re]
          exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hn)
            (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (row₀ i))
        have ht := congrArg Complex.re htraceT
        simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at ht
        linarith
      obtain ⟨ψ, hψ⟩ := pure_from_positive_pivot b row₀ hbpos
      have he : rankOneDensity (ψ ∘ wordEquiv.symm) = ρ₀ := by
        change _ = original (assemble b row₀ (correction b row₀))
        rw [hψ]
        rfl
      have ht : ρ₀.trace = 1 := by
        change (original (assemble b row₀ T₀)).trace = 1
        rwa [trace_original, trace_assemble]
      refine ⟨ρ₀, ⟨ψ ∘ wordEquiv.symm, he.symm⟩, ht, ?_, ?_, rfl⟩
      · change edgeTrace (original (assemble b row₀ T₀)) 1 2 = _
        rw [left_read, ← hL]
        rfl
      · change edgeTrace (original (assemble b row₀ T₀)) 2 1 = _
        rw [right_read, ← hR]
        rfl
  · intro ψ ρ hψ hρ hdata
    obtain ⟨hψeq, hL, _⟩ := recover ψ hψ
    obtain ⟨T, hsplit, hres, hLT, _⟩ := extension_blocks hρ hdata
    change (T - T₀).PosSemidef at hres
    have hzero : (T - T₀).trace = 0 := by
      rw [← trace_partialTraceRight (T - T₀), partialTraceRight_sub, hLT, ← hL, sub_self,
        Matrix.trace_zero]
    have hT : T = T₀ := sub_eq_zero.mp (hres.trace_eq_zero_iff.mp hzero)
    rw [hψeq, ← hsplit, hT]

open FibRationalPureExtension Complex

/-- The prescribed rational coupling and positive Schur residuals give a rational extension. -/
theorem rational_extension_at (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (hb : 0 ≤ b) (htr : L.trace + (b : ℂ) = 1) (hr : R.trace = L.trace)
    (hzero : b = 0 → middleRow u v w z = 0)
    (hL : (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef)
    (hR : (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef)
    (qL : ∀ i j, RationalEntry (L i j))
    (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w) (qz : RationalEntry z) :
    ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ∀ i j, RationalEntry (ρ i j) := by
  let row := middleRow u v w z
  let K := correction b row
  let X := L - partialTraceRight K
  let Y := R - partialTraceLeft K
  let S := kronecker (X.trace⁻¹ • X) Y
  let T := S + K
  have ht : X.trace = Y.trace := by
    simp [X, Y, Matrix.trace_sub, hr, trace_partialTraceRight, trace_partialTraceLeft]
  obtain ⟨hS, hsL, hsR⟩ := product_completion_formula X Y hL hR ht
  change S.PosSemidef at hS
  change partialTraceRight S = X at hsL
  change partialTraceLeft S = Y at hsR
  have hT := (block_psd b row T).mpr ⟨hb, hzero, by simpa [T, K] using hS⟩
  have htL : partialTraceRight T = L := by simp [T, partialTraceRight_add, hsL, X]
  have htR : partialTraceLeft T = R := by simp [T, partialTraceLeft_add, hsR, Y]
  refine ⟨original (assemble b row T), hT.submatrix _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · rw [trace_original, trace_assemble, ← trace_partialTraceRight T, htL, htr]
  · rw [left_read, htL]
    rfl
  · rw [right_read, htR]
    rfl
  · have rr (i : Bool × Bool) : RationalEntry (row i) := by
      rcases i with ⟨i,j⟩
      cases i <;> cases j
      · exact qu
      · exact qw
      · exact qv
      · exact qz
    have qpivot : RationalEntry (b : ℂ) := by
      have htq : RationalEntry L.trace := rationalComplex.sum_mem fun i _ => qL i i
      have hpivot : (b : ℂ) = 1 - L.trace := by
        rw [← htr]
        ring
      rw [hpivot]
      exact rationalComplex.sub_mem rationalComplex.one_mem htq
    have qK (i j) : RationalEntry (K i j) := by
      change RationalEntry ((↑b⁻¹ : ℂ) * (conj (row i) * row j))
      rw [Complex.ofReal_inv]
      exact rationalComplex.mul_mem (rationalComplex.inv_mem qpivot)
        (rationalComplex.mul_mem (rationalConjugate ⟨row i, rr i⟩).property (rr j))
    have qX (i j) : RationalEntry (X i j) :=
      rationalComplex.sub_mem (qL i j) (rationalComplex.sum_mem fun k _ => qK (i, k) (j, k))
    have qY (i j) : RationalEntry (Y i j) :=
      rationalComplex.sub_mem (qR i j) (rationalComplex.sum_mem fun k _ => qK (k, i) (k, j))
    have qtr : RationalEntry X.trace := rationalComplex.sum_mem fun i _ => qX i i
    have qT (i j) : RationalEntry (T i j) :=
      rationalComplex.add_mem (rationalComplex.mul_mem
        (rationalComplex.mul_mem (rationalComplex.inv_mem qtr) (qX i.1 j.1)) (qY i.2 j.2)) (qK i j)
    intro i j
    change RationalEntry (assemble b row T (wordEquiv.symm i) (wordEquiv.symm j))
    cases wordEquiv.symm i <;> cases wordEquiv.symm j
    · exact qpivot
    · apply rr
    · exact (rationalConjugate ⟨_, rr _⟩).property
    · apply qT

open LabelResetBandwidth (pure_marginal_factors)

private theorem pure_of_singular (L : Matrix Bool Bool ℂ) (hL : L.PosSemidef)
    (hdet : L.det = 0) (ht : L.trace = 1) :
    ∃ x : Bool → ℂ, star x ⬝ᵥ x = 1 ∧ L = LabelResetBandwidth.pure x := by
  classical
  let h := hL.isHermitian
  let U : Matrix Bool Bool ℂ := h.eigenvectorUnitary
  have he₀ : (h.eigenvalues false : ℂ) * (h.eigenvalues true : ℂ) = 0 := by
    have hh := h.det_eq_prod_eigenvalues
    rw [Fintype.prod_bool] at hh
    rw [mul_comm]
    exact hh.symm.trans hdet
  have he₁ : (h.eigenvalues false : ℂ) + (h.eigenvalues true : ℂ) = 1 := by
    simpa [h.trace_eq_sum_eigenvalues, Fintype.sum_bool, add_comm] using ht
  obtain ⟨j, hj⟩ : ∃ j : Bool, ∀ i : Bool, (h.eigenvalues i : ℂ) =
      if i = j then 1 else 0 := by
    rcases mul_eq_zero.mp he₀ with hf | ht'
    · refine ⟨true, fun i => ?_⟩
      cases i
      · simp [hf]
      · simpa [hf] using he₁
    · refine ⟨false, fun i => ?_⟩
      cases i
      · simpa [ht'] using he₁
      · simp [ht']
  let x : Bool → ℂ := fun i => U i j
  refine ⟨x, ?_, ?_⟩
  · have hu : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
    have h := congrFun (congrFun hu j) j
    simpa [x, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  · have hd : diagonal (RCLike.ofReal ∘ h.eigenvalues : Bool → ℂ) =
        diagonal (fun i => if i = j then (1 : ℂ) else 0) := by
      congr 1
      funext i
      exact hj i
    rw [h.spectral_theorem, hd, Unitary.conjStarAlgAut_apply]
    change U * diagonal (fun i => if i = j then (1 : ℂ) else 0) * Uᴴ = LabelResetBandwidth.pure x
    ext i k
    cases j <;> simp [x, LabelResetBandwidth.pure, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply]

private theorem singular_left_unique {S T : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hL : partialTraceRight S = partialTraceRight T)
    (hR : partialTraceLeft S = partialTraceLeft T)
    (hd : (partialTraceRight S).det = 0) : S = T := by
  let t := S.trace
  have htT : T.trace = t := by
    rw [← trace_partialTraceRight T, ← hL, trace_partialTraceRight]
  by_cases hz : t = 0
  · exact ((hS.trace_eq_zero_iff).mp hz).trans
      ((hT.trace_eq_zero_iff).mp (htT.trans hz)).symm
  have hi : 0 ≤ t⁻¹ := by
    have hlo := hS.trace_nonneg
    change 0 ≤ S.trace⁻¹
    rw [Complex.nonneg_iff] at hlo ⊢
    simp [Complex.inv_re, Complex.inv_im, ← hlo.2,
      div_nonneg hlo.1 (Complex.normSq_nonneg _)]
  let A := t⁻¹ • S
  let B := t⁻¹ • T
  have left_smul (K : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
      partialTraceRight (t⁻¹ • K) = t⁻¹ • partialTraceRight K := by
    ext i j
    simp [partialTraceRight, mul_add]
  have right_smul (K : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
      partialTraceLeft (t⁻¹ • K) = t⁻¹ • partialTraceLeft K := by
    ext i j
    simp [partialTraceLeft, mul_add]
  have ha : (partialTraceRight A).trace = 1 := by
    rw [trace_partialTraceRight, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hz]
  have had : (partialTraceRight A).det = 0 := by
    rw [left_smul, Matrix.det_smul, hd, mul_zero]
  obtain ⟨x, hx, hAx⟩ := pure_of_singular _ (partialTraceRight_posSemidef (hS.smul hi)) had ha
  have hBx : partialTraceRight B = LabelResetBandwidth.pure x := by
    change partialTraceRight (t⁻¹ • T) = _
    rwa [left_smul, ← hL, ← left_smul]
  have hrAB : partialTraceLeft A = partialTraceLeft B := by
    change partialTraceLeft (t⁻¹ • S) = partialTraceLeft (t⁻¹ • T)
    rw [right_smul, right_smul, hR]
  have hAp : A.PosSemidef := hS.smul hi
  have hBp : B.PosSemidef := hT.smul hi
  have hab : A = B :=
    (pure_marginal_factors x hx hAp hAx).trans
      ((congrArg (kronecker (LabelResetBandwidth.pure x)) hrAB).trans
        (pure_marginal_factors x hx hBp hBx).symm)
  have eq := congrArg (fun K : Matrix (Bool × Bool) (Bool × Bool) ℂ => t • K) hab
  simpa only [A, B, smul_smul, mul_inv_cancel₀ hz, one_smul] using eq

private theorem singular_right_unique {S T : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hL : partialTraceRight S = partialTraceRight T)
    (hR : partialTraceLeft S = partialTraceLeft T)
    (hd : (partialTraceLeft S).det = 0) : S = T := by
  let e := Equiv.prodComm Bool Bool
  have h := singular_left_unique (hS.submatrix e) (hT.submatrix e) hR hL hd
  ext i j
  exact congrFun (congrFun h (e i)) (e j)

private theorem psd_of_trace_det_pos {K : Matrix Bool Bool ℂ} (h : K.IsHermitian)
    (ht : 0 < K.trace.re) (hd : 0 < K.det.re) : K.PosSemidef := by
  have ht' : 0 < h.eigenvalues true + h.eigenvalues false := by
    simpa [h.trace_eq_sum_eigenvalues, Fintype.sum_bool, Complex.add_re] using ht
  have hd' : 0 < h.eigenvalues true * h.eigenvalues false := by
    have hdet := h.det_eq_prod_eigenvalues
    rw [Fintype.prod_bool] at hdet
    rw [hdet] at hd
    exact_mod_cast hd
  apply h.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  rcases mul_pos_iff.mp hd' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · cases i
    · exact hb.le
    · exact ha.le
  · linarith

private theorem locally_feasible {F : ℂ → Matrix Bool Bool ℂ} (hF : Continuous F)
    (hH : ∀ z, (F z).IsHermitian) {z : ℂ} (hp : (F z).PosSemidef)
    (hd : (F z).det ≠ 0) : ∀ᶠ y in nhds z, (F y).PosSemidef := by
  have hpos := hp.posDef_iff_det_ne_zero.mpr hd
  have ht : ∀ᶠ y in nhds z, 0 < (F y).trace.re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hF.matrix_trace)).mem_nhds
      ((Complex.pos_iff.mp hpos.trace_pos).1)
  have he : ∀ᶠ y in nhds z, 0 < (F y).det.re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hF.matrix_det)).mem_nhds
      ((Complex.pos_iff.mp hpos.det_pos).1)
  filter_upwards [ht, he] with y hy hd'
  exact psd_of_trace_det_pos (hH y) hy hd'

private theorem extension_from_residuals {b : ℝ} {L R : Matrix Bool Bool ℂ} {u v w z : ℂ}
    (hb : 0 < b) (ht : L.trace + (b : ℂ) = 1) (hr : R.trace = L.trace)
    (hL : (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef)
    (hR : (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef) :
    ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ := by
  obtain ⟨T, hT, hTL, hTR⟩ := (block_marginals_iff b _ L R hr.symm).mpr
    ⟨hb.le, fun h => (hb.ne' h).elim, hL, hR⟩
  refine ⟨original (assemble b (middleRow u v w z) T), hT.submatrix _, ?_, ?_, ?_, rfl⟩
  · rwa [trace_original, trace_assemble, ← trace_partialTraceRight T, hTL]
  · rw [left_read, hTL]
    rfl
  · rw [right_read, hTR]
    rfl

private theorem residual_continuous (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ) :
    Continuous (fun z : ℂ => L - partialTraceRight (correction b (middleRow u v w z))) ∧
    Continuous (fun z : ℂ => R - partialTraceLeft (correction b (middleRow u v w z))) := by
  have hrow (i : Bool × Bool) : Continuous (fun z : ℂ => middleRow u v w z i) := by
    obtain ⟨i, j⟩ := i
    cases i <;> cases j
    all_goals first | exact continuous_const | exact continuous_id
  have h (i j : Bool × Bool) : Continuous (fun z : ℂ =>
      correction b (middleRow u v w z) i j) := by
    simp only [correction, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.real_smul]
    exact continuous_const.mul ((continuous_star.comp (hrow i)).mul (hrow j))
  constructor
  · apply continuous_matrix
    intro i j
    simp only [Matrix.sub_apply, partialTraceRight, Fintype.sum_bool]
    exact continuous_const.sub ((h _ _).add (h _ _))
  · apply continuous_matrix
    intro i j
    simp only [Matrix.sub_apply, partialTraceLeft, Fintype.sum_bool]
    exact continuous_const.sub ((h _ _).add (h _ _))

private theorem residuals_hermitian {b : ℝ} {L R : Matrix Bool Bool ℂ} {u v w z : ℂ}
    (hb : 0 < b) (hL : L.IsHermitian) (hR : R.IsHermitian) :
    (L - partialTraceRight (correction b (middleRow u v w z))).IsHermitian ∧
    (R - partialTraceLeft (correction b (middleRow u v w z))).IsHermitian := by
  obtain ⟨ψ, hψ⟩ := pure_from_positive_pivot b (middleRow u v w z) hb
  have hp : (assemble b (middleRow u v w z) (correction b (middleRow u v w z))).PosSemidef := by
    rw [hψ]
    exact Matrix.posSemidef_vecMulVec_self_star ψ
  have hc : (correction b (middleRow u v w z)).PosSemidef := hp.submatrix Sum.inr
  exact ⟨hL.sub (partialTraceRight_posSemidef hc).isHermitian,
    hR.sub (partialTraceLeft_posSemidef hc).isHermitian⟩

/-- At positive middle occupation, a compatible pair of edge marginals determines exactly
one global state if and only if there is exactly one feasible hidden coupling. -/
theorem unique_coherent_extension_iff (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : 0 < b) :
    (∃! ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      edgeTrace ρ 1 2 = coherentEdge b L u v ∧ edgeTrace ρ 2 1 = coherentEdge b R u w) ↔
    L.trace + (b : ℂ) = 1 ∧ R.trace = L.trace ∧
    ∃! z : ℂ, (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef ∧
      (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef := by
  let coupling (ρ : Matrix Word Word ℂ) := ρ (.inl 0) (.inr true)
  let A (z : ℂ) := L - partialTraceRight (correction b (middleRow u v w z))
  let C (z : ℂ) := R - partialTraceLeft (correction b (middleRow u v w z))
  have residuals (ρ : Matrix Word Word ℂ) (hp : ρ.PosSemidef)
      (hdata : MatchesCoherentData b L R u v w (coupling ρ) ρ) :
      (A (coupling ρ)).PosSemidef ∧ (C (coupling ρ)).PosSemidef := by
    obtain ⟨T, _, hT, hL, hR⟩ := extension_blocks hp hdata
    exact ⟨by simpa [A, partialTraceRight_sub, hL] using partialTraceRight_posSemidef hT,
      by simpa [C, partialTraceLeft_sub, hR] using partialTraceLeft_posSemidef hT⟩
  constructor
  · rintro ⟨ρ, hρ, huniq⟩
    obtain ⟨_, ht, hr, _⟩ := (coherent_extendible_iff b L R u v w).mp ⟨ρ, hρ⟩
    obtain ⟨hp, htρ, hLρ, hRρ⟩ := hρ
    refine ⟨ht, hr, coupling ρ, residuals ρ hp ⟨htρ, hLρ, hRρ, rfl⟩, ?_⟩
    rintro z ⟨ha, hc⟩
    obtain ⟨σ, hs, htσ, hLσ, hRσ, hz⟩ := extension_from_residuals hb ht hr ha hc
    exact hz.symm.trans (congrArg coupling (huniq σ ⟨hs, htσ, hLσ, hRσ⟩))
  · rintro ⟨ht, hr, z, ⟨hA, hC⟩, huniq⟩
    obtain ⟨ρ, hp, hdata⟩ := extension_from_residuals hb ht hr hA hC
    obtain ⟨T, hρ, hT, hLT, hRT⟩ := extension_blocks hp hdata
    have hsing : (A z).det = 0 ∨ (C z).det = 0 := by
      by_contra! hn
      have hblock : T.PosSemidef := by
        have h := hp.submatrix (fun i : Bool × Bool => wordEquiv (.inr i))
        rw [← hρ] at h
        convert h using 1
        ext i j
        simp [original, assemble]
      have hLH : L.IsHermitian := hLT ▸ (partialTraceRight_posSemidef hblock).isHermitian
      have hRH : R.IsHermitian := hRT ▸ (partialTraceLeft_posSemidef hblock).isHermitian
      obtain ⟨ha, hc⟩ := residual_continuous b L R u v w
      let U : Set ℂ := {y | (A y).PosSemidef ∧ (C y).PosSemidef}
      have hU : U ∈ nhds z :=
        (locally_feasible ha (fun y => (residuals_hermitian hb hLH hRH (z := y)).1)
          hA hn.1).and
        (locally_feasible hc (fun y => (residuals_hermitian hb hLH hRH (z := y)).2)
          hC hn.2)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
      let y := (↑(ε / 2) : ℂ) + z
      have hy : y ∈ Metric.ball z ε := by
        change dist y z < ε
        rw [dist_eq_norm, show y - z = (↑(ε / 2) : ℂ) by simp [y],
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      have hne : y ≠ z := by
        intro he
        have hm : (↑(ε / 2) : ℂ) = 0 := add_right_cancel (he.trans (zero_add z).symm)
        exact (by positivity : 0 < ε / 2).ne' (Complex.ofReal_eq_zero.mp hm)
      exact hne (huniq y (hball hy))
    obtain ⟨htρ, hLρ, hRρ, _⟩ := hdata
    refine ⟨ρ, ⟨hp, htρ, hLρ, hRρ⟩, ?_⟩
    rintro σ ⟨hs, htσ, hLσ, hRσ⟩
    have hdσ : MatchesCoherentData b L R u v w (coupling σ) σ := ⟨htσ, hLσ, hRσ, rfl⟩
    have hz : coupling σ = z := huniq _ (residuals σ hs hdσ)
    rw [hz] at hdσ
    obtain ⟨W, hσ, hW, hLW, hRW⟩ := extension_blocks hs hdσ
    let Q := correction b (middleRow u v w z)
    have heL : partialTraceRight (T - Q) = partialTraceRight (W - Q) := by
      rw [partialTraceRight_sub, partialTraceRight_sub, hLT, hLW]
    have heR : partialTraceLeft (T - Q) = partialTraceLeft (W - Q) := by
      rw [partialTraceLeft_sub, partialTraceLeft_sub, hRT, hRW]
    have he : T - Q = W - Q := by
      rcases hsing with hl | hr
      · apply singular_left_unique hT hW heL heR
        rwa [partialTraceRight_sub, hLT]
      · apply singular_right_unique hT hW heL heR
        rwa [partialTraceLeft_sub, hRT]
    rw [← hρ, ← hσ, sub_left_inj.mp he]

private theorem leftGram (M : Matrix Bool Bool ℂ) :
    partialTraceRight (rankOneDensity (fun p : Bool × Bool => M p.1 p.2)) = M * Mᴴ := by
  ext i j : 1
  simp [partialTraceRight, rankOneDensity, Matrix.vecMulVec_apply, Matrix.mul_apply]

private theorem rightGram (M : Matrix Bool Bool ℂ) :
    partialTraceLeft (rankOneDensity (fun p : Bool × Bool => M p.1 p.2)) = (Mᴴ * M)ᵀ := by
  ext i j : 1
  simp [partialTraceLeft, rankOneDensity, Matrix.vecMulVec_apply, Matrix.mul_apply, mul_comm]

private theorem endpoint_purity_iff (L R : Matrix Bool Bool ℂ) :
    (∃ ψ : Bool × Bool → ℂ, partialTraceRight (rankOneDensity ψ) = L ∧
      partialTraceLeft (rankOneDensity ψ) = R) ↔
      L.PosSemidef ∧ R.PosSemidef ∧ L.charpoly = R.charpoly := by
  constructor
  · rintro ⟨ψ, rfl, rfl⟩
    have hp : (rankOneDensity ψ).PosSemidef := Matrix.posSemidef_vecMulVec_self_star ψ
    refine ⟨partialTraceRight_posSemidef hp, partialTraceLeft_posSemidef hp, ?_⟩
    let M : Matrix Bool Bool ℂ := fun i j => ψ (i,j)
    rw [show ψ = (fun p => M p.1 p.2) from rfl, leftGram, rightGram,
      Matrix.charpoly_transpose, Matrix.charpoly_mul_comm]
  · rintro ⟨hL, hR, hc⟩
    let hLH := hL.isHermitian
    let hRH := hR.isHermitian
    have he := (hLH.eigenvalues_eq_eigenvalues_iff hRH).mpr hc
    let U : Matrix Bool Bool ℂ := hLH.eigenvectorUnitary
    let V : Matrix Bool Bool ℂ := hRH.eigenvectorUnitary
    let D : Matrix Bool Bool ℂ := diagonal (fun i => (Real.sqrt (hLH.eigenvalues i) : ℂ))
    let Ω : Matrix Bool Bool ℂ := diagonal (fun i => (hLH.eigenvalues i : ℂ))
    have hu : Uᴴ * U = 1 := by
      exact Unitary.coe_star_mul_self hLH.eigenvectorUnitary
    have hv : Vᴴ * V = 1 := by
      exact Unitary.coe_star_mul_self hRH.eigenvectorUnitary
    have hvt : Vᵀ * (Vᵀ)ᴴ = 1 := by
      rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hv, transpose_one]
    have hd : Dᴴ = D := by simp [D]
    have hdd : D * D = Ω := by
      simp [D, Ω, diagonal_mul_diagonal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hL.eigenvalues_nonneg _)]
    have hLdiag : L = U * Ω * Uᴴ := by
      simpa only [U, Ω, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hLH.spectral_theorem
    have hRdiag : R = V * Ω * Vᴴ := by
      rw [show Ω = diagonal (fun i => (hRH.eigenvalues i : ℂ)) by rw [← he]]
      simpa only [V, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hRH.spectral_theorem
    let M := U * D * Vᵀ
    refine ⟨fun p => M p.1 p.2, ?_, ?_⟩
    · rw [leftGram, hLdiag]
      dsimp only [M]
      rw [conjTranspose_mul, conjTranspose_mul, hd]
      calc
        _ = U * (D * (Vᵀ * (Vᵀ)ᴴ) * D) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hvt, mul_one, hdd]
    · rw [rightGram, hRdiag]
      dsimp only [M]
      rw [conjTranspose_mul, conjTranspose_mul, hd]
      calc
        _ = ((Vᵀ)ᴴ * (D * (Uᴴ * U) * D) * Vᵀ)ᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hu, mul_one, hdd, transpose_mul, transpose_mul, transpose_transpose,
            conjTranspose_transpose_eq_transpose_conjTranspose, transpose_transpose]
          simp [Ω, Matrix.mul_assoc]

/-- At zero middle occupation, pure extensions exist exactly for zero coupling and
positive trace-one endpoint marginals with equal determinants. -/
theorem pure_coherent_zero_iff (L R : Matrix Bool Bool ℂ) (u v w z : ℂ) :
    (∃ ψ : Word → ℂ, MatchesCoherentData 0 L R u v w z (rankOneDensity ψ)) ↔
      u = 0 ∧ v = 0 ∧ w = 0 ∧ z = 0 ∧
        L.PosSemidef ∧ R.PosSemidef ∧ L.trace = 1 ∧ R.trace = 1 ∧ L.det = R.det := by
  constructor
  · rintro ⟨ψ, ht, hl, hr, hz⟩
    let y := fun i : Bool × Bool => ψ (wordEquiv (.inr i))
    let T := rankOneDensity y
    have hxnorm : Complex.normSq (ψ (.inl 0)) = 0 := by
      have obs := congrFun (congrFun hl 1) 1
      change ψ (.inl 0) * conj (ψ (.inl 0)) + 0 = (0 : ℂ) at obs
      rw [add_zero, Complex.mul_conj] at obs
      exact_mod_cast obs
    have hx := Complex.normSq_eq_zero.mp hxnorm
    have hp : (rankOneDensity ψ).PosSemidef := Matrix.posSemidef_vecMulVec_self_star ψ
    have hsplit : original (assemble 0 0 T) = rankOneDensity ψ := by
      have hh := split_state (rankOneDensity ψ) hp.isHermitian
      change original (assemble ((ψ (.inl 0) * conj (ψ (.inl 0))).re)
        (fun i => ψ (.inl 0) * conj (y i)) T) = rankOneDensity ψ at hh
      simpa only [hx, zero_mul, Complex.zero_re, Pi.zero_def] using hh
    rw [← hsplit, left_read] at hl
    rw [← hsplit, right_read] at hr
    have hu : u = 0 := (congrFun (congrFun hl 1) 0).symm
    have hv : v = 0 := (congrFun (congrFun hl 1) 2).symm
    have hw : w = 0 := (congrFun (congrFun hr 1) 2).symm
    have hz0 : z = 0 := by
      simpa [rankOneDensity, Matrix.vecMulVec_apply, hx] using hz.symm
    obtain ⟨hL, hR, _⟩ := recover_edge_data 0 0 L R u v w 0 T hl hr
    obtain ⟨hLP, hRP, hc⟩ := (endpoint_purity_iff L R).mp ⟨y, hL, hR⟩
    have htT : T.trace = 1 := by
      simpa only [← hsplit, trace_original, trace_assemble, Complex.ofReal_zero, add_zero] using ht
    have htL : L.trace = 1 := by rw [← hL, trace_partialTraceRight, htT]
    have htR : R.trace = 1 := by rw [← hR, trace_partialTraceLeft, htT]
    have hd := congrArg (fun p : Polynomial ℂ => p.coeff 0) hc
    rw [L.charpoly_of_card_eq_two (by decide), R.charpoly_of_card_eq_two (by decide)] at hd
    exact ⟨hu, hv, hw, hz0, hLP, hRP, htL, htR, by simpa using hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hLP, hRP, htL, htR, hd⟩
    have hc : L.charpoly = R.charpoly := by
      rw [L.charpoly_of_card_eq_two (by decide), R.charpoly_of_card_eq_two (by decide), htL, htR, hd]
    obtain ⟨y, hL, hR⟩ := (endpoint_purity_iff L R).mpr ⟨hLP, hRP, hc⟩
    let x : Unit ⊕ (Bool × Bool) → ℂ := Sum.elim (fun _ => 0) y
    let T := rankOneDensity y
    let ψ := x ∘ wordEquiv.symm
    have hsplit : original (assemble 0 0 T) = rankOneDensity ψ := by
      unfold original ψ
      suffices h : assemble 0 0 T = rankOneDensity x by
        rw [h]
        rfl
      ext i j
      rcases i with (_ | i) <;> rcases j with (_ | j) <;>
        simp [assemble, pivot, cross, rankOneDensity, x, T, Matrix.vecMulVec_apply]
    refine ⟨ψ, ?_, ?_, ?_, ?_⟩ <;> rw [← hsplit]
    · rw [trace_original, trace_assemble, ← trace_partialTraceRight T, hL, Complex.ofReal_zero, add_zero]
      exact htL
    · simpa only [Pi.zero_apply, show partialTraceRight T = L from hL] using left_read 0 0 T
    · simpa only [Pi.zero_apply, show partialTraceLeft T = R from hR] using right_read 0 0 T
    · rfl

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
