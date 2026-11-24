/- GID: D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibCoherentExtension
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A scalar coherence criterion for common positive Fibonacci marginal extensions. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
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
    obtain ⟨hLT, _, hrow⟩ := recover_edge_data b d L R u v w row T hl hr
    have hz' : row (true, true) = z := hz
    rw [hd, hrow, hz'] at hsplit
    change original (assemble b row₀ T) = ρ at hsplit
    have hblock : (assemble b row₀ T).PosSemidef := by
      apply (Matrix.posSemidef_submatrix_equiv wordEquiv.symm).mp
      change (original (assemble b row₀ T)).PosSemidef
      rwa [hsplit]
    have hres := ((block_psd b row₀ T).mp hblock).2.2
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


open D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
  (pureCoupling ptrace2_pure ptrace1_pure)

private theorem leftGram {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    partialTraceRight (rankOneDensity (fun p : n × n => M p.1 p.2)) = M * Mᴴ := by
  let e := (Fintype.equivFin n).symm
  let N := M.submatrix e e
  let T := rankOneDensity (fun p : n × n => M p.1 p.2)
  have ht : (partialTraceRight T).submatrix e e = partialTraceRight (pureCoupling N) := by
    ext i j : 1
    change (∑ k : n, T (e i, k) (e j, k)) =
      ∑ k : Fin (Fintype.card n), T (e i, e k) (e j, e k)
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hm : (M * Mᴴ).submatrix e e = N * Nᴴ := by
    exact (submatrix_mul_equiv M Mᴴ e e e).symm
  have h := ht.trans ((ptrace2_pure N).trans hm.symm)
  ext i j : 1
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨c, rfl⟩ := e.surjective j
  exact congrFun (congrFun h a) c

private theorem rightGram {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    partialTraceLeft (rankOneDensity (fun p : n × n => M p.1 p.2)) = (Mᴴ * M)ᵀ := by
  let e := (Fintype.equivFin n).symm
  let N := M.submatrix e e
  let T := rankOneDensity (fun p : n × n => M p.1 p.2)
  have ht : (partialTraceLeft T).submatrix e e = partialTraceLeft (pureCoupling N) := by
    ext i j : 1
    change (∑ k : n, T (k, e i) (k, e j)) =
      ∑ k : Fin (Fintype.card n), T (e k, e i) (e k, e j)
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hm : ((Mᴴ * M)ᵀ).submatrix e e = (Nᴴ * N)ᵀ := by
    change ((Mᴴ * M).submatrix e e)ᵀ = _
    exact congrArg Matrix.transpose (submatrix_mul_equiv Mᴴ M e e e).symm
  have h := ht.trans ((ptrace1_pure N).trans hm.symm)
  ext i j : 1
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨c, rfl⟩ := e.surjective j
  exact congrFun (congrFun h a) c

private theorem endpoint_purity_iff {n : Type*} [Fintype n] [DecidableEq n]
    (L R : Matrix n n ℂ) :
    (∃ ψ : n × n → ℂ, partialTraceRight (rankOneDensity ψ) = L ∧
      partialTraceLeft (rankOneDensity ψ) = R) ↔
      L.PosSemidef ∧ R.PosSemidef ∧ L.charpoly = R.charpoly := by
  constructor
  · rintro ⟨ψ, rfl, rfl⟩
    have hp : (rankOneDensity ψ).PosSemidef := Matrix.posSemidef_vecMulVec_self_star ψ
    refine ⟨partialTraceRight_posSemidef hp, partialTraceLeft_posSemidef hp, ?_⟩
    let M : Matrix n n ℂ := fun i j => ψ (i,j)
    change (partialTraceRight (rankOneDensity (fun p : n × n => M p.1 p.2))).charpoly = _
    rw [leftGram]
    change _ = (partialTraceLeft (rankOneDensity (fun p : n × n => M p.1 p.2))).charpoly
    rw [rightGram, Matrix.charpoly_transpose, Matrix.charpoly_mul_comm]
  · rintro ⟨hL, hR, hc⟩
    let hLH := hL.isHermitian
    let hRH := hR.isHermitian
    have he := (hLH.eigenvalues_eq_eigenvalues_iff hRH).mpr hc
    let U : Matrix n n ℂ := hLH.eigenvectorUnitary
    let V : Matrix n n ℂ := hRH.eigenvectorUnitary
    let D : Matrix n n ℂ := diagonal (fun i => (Real.sqrt (hLH.eigenvalues i) : ℂ))
    let Ω : Matrix n n ℂ := diagonal (fun i => (hLH.eigenvalues i : ℂ))
    have hu : Uᴴ * U = 1 := by
      exact Unitary.coe_star_mul_self hLH.eigenvectorUnitary
    have hv : Vᴴ * V = 1 := by
      exact Unitary.coe_star_mul_self hRH.eigenvectorUnitary
    have hvt : Vᵀ * (Vᵀ)ᴴ = 1 := by
      rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hv, transpose_one]
    have hd : Dᴴ = D := by simp [D]
    have hdd : D * D = Ω := by
      rw [show D = diagonal (fun i => (Real.sqrt (hLH.eigenvalues i) : ℂ)) from rfl,
        diagonal_mul_diagonal]
      refine congrArg diagonal (funext fun i => ?_)
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hL.eigenvalues_nonneg i)]
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

private theorem charpoly_bool_iff (L R : Matrix Bool Bool ℂ) :
    L.charpoly = R.charpoly ↔ L.trace = R.trace ∧ L.det = R.det := by
  have hcard : Fintype.card Bool = 2 := by decide
  rw [Matrix.charpoly_of_card_eq_two L hcard, Matrix.charpoly_of_card_eq_two R hcard]
  constructor
  · intro h
    have yt := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    have yd := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
    simp at yt yd
    exact ⟨yt, yd⟩
  · rintro ⟨ht,hd⟩
    rw [ht,hd]

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
      change ψ (.inl 0) * conj (ψ (.inr true)) = z at hz
      simpa [hx] using hz.symm
    obtain ⟨hL, hR, _⟩ := recover_edge_data 0 0 L R u v w 0 T hl hr
    obtain ⟨hLP, hRP, hc⟩ := (endpoint_purity_iff L R).mp ⟨y, hL, hR⟩
    have htT : T.trace = 1 := by
      rw [← hsplit, trace_original, trace_assemble, Complex.ofReal_zero, add_zero] at ht
      exact ht
    have htL : L.trace = 1 := by rw [← hL, trace_partialTraceRight, htT]
    have htR : R.trace = 1 := by rw [← hR, trace_partialTraceLeft, htT]
    exact ⟨hu, hv, hw, hz0, hLP, hRP, htL, htR, ((charpoly_bool_iff L R).mp hc).2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hLP, hRP, htL, htR, hd⟩
    obtain ⟨y, hL, hR⟩ := (endpoint_purity_iff L R).mpr
      ⟨hLP, hRP, (charpoly_bool_iff L R).mpr ⟨htL.trans htR.symm, hd⟩⟩
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
    · rw [left_read, hL]
      rfl
    · rw [right_read, hR]
      rfl
    · rfl

end D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
