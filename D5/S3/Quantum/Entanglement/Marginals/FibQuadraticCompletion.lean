/- GID: D5/S3/Quantum/Entanglement/Marginals/FibQuadraticCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibQuadraticCompletion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rank-three Fibonacci completion with one real square root. -/

import D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
import D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
/-! Low-rank completion of coherent Fibonacci marginals at a residual disk boundary. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder Matrix Kronecker
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.Marginals.FibQuadraticCompletion

open FibRationalPureExtension
open FibMarginalExtension (Word)

private theorem edge_singular_at_boundary (b : ℝ) (L : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (hb : 0 < b) (hL : L.IsHermitian)
    (hz : normSq (z - (edgeDisk b L u v w).1) = (edgeDisk b L u v w).2) :
    (L - partialTraceRight (correction b (middleRow u v w z))).det = 0 := by
  let F := fun y => L - partialTraceRight (correction b (middleRow u v w y))
  let p := (edgeDisk b L u v w).1
  let r := (edgeDisk b L u v w).2
  change normSq (z - p) = r at hz
  have hF : Continuous F := (residual_continuous b L 0 u v w).1
  have hH (y : ℂ) : (F y).IsHermitian :=
    (residuals_hermitian (z := y) hb hL Matrix.isHermitian_zero).1
  have hp : (F z).PosSemidef := (edgeDisk_spec b L u v w z hb hL).mpr hz.le
  change (F z).det = 0
  by_contra hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (locally_feasible hF hH hp hd)
  let s := if z.re < p.re then -(ε / 2) else ε / 2
  let y := z + (s : ℂ)
  have habs : |s| = ε / 2 := by
    by_cases h : z.re < p.re <;> simp [s, h, abs_of_nonneg (show 0 ≤ ε / 2 by positivity)]
  have hy : y ∈ Metric.ball z ε := by
    change dist y z < ε
    rw [dist_eq_norm, show y - z = (s : ℂ) by dsimp [y]; ring,
      Complex.norm_real, Real.norm_eq_abs, habs]
    linarith
  have hin : normSq (y - p) ≤ r := (edgeDisk_spec b L u v w y hb hL).mp (hball hy)
  have hn : s ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    linarith
  have hsq : 0 < s * s := mul_self_pos.mpr hn
  have hs : 0 ≤ (z.re - p.re) * s := by
    by_cases h : z.re < p.re
    · rw [show s = -(ε / 2) by simp [s, h]]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h.le) (by linarith)
    · rw [show s = ε / 2 by simp [s, h]]
      exact mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) (by linarith)
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hz hin
  simp only [y, Complex.add_re, Complex.add_im, ofReal_re, ofReal_im, add_zero] at hin
  nlinarith only [hz, hin, hsq, hs]

private theorem disk_slice_right_endpoint (z p : ℂ) (r : ℝ)
    (hz : Complex.normSq (z - p) ≤ r) :
    let d := r - (z.im - p.im)^2
    let t := p.re - z.re + Real.sqrt d
    0 ≤ d ∧ 0 ≤ t ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ t → Complex.normSq (z + (x : ℂ) - p) ≤ r) ∧
      Complex.normSq (z + (t : ℂ) - p) = r := by
  dsimp only
  let a := z.re - p.re
  let d := r - (z.im - p.im)^2
  let u := Real.sqrt d
  have ha : a^2 ≤ d := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hz
    dsimp [a, d]
    nlinarith
  have hd : 0 ≤ d := (sq_nonneg a).trans ha
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = d := Real.sq_sqrt hd
  have haU : a ≤ u := by
    by_contra! h
    have hsq := sq_lt_sq' (show -a < u by linarith) h
    nlinarith
  have hUa : -u ≤ a := by
    by_contra! h
    have hsq := sq_lt_sq' (show -(-a) < u by linarith) (show u < -a by linarith)
    nlinarith
  have heq (x : ℝ) : Complex.normSq (z + (x : ℂ) - p) =
      (a+x)^2 + (z.im-p.im)^2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    dsimp [a]
    ring
  have ht : p.re - z.re + Real.sqrt (r - (z.im - p.im)^2) = u - a := by
    dsimp [a, d, u]
    ring
  rw [ht]
  refine ⟨hd, sub_nonneg.mpr haU, ?_, ?_⟩
  · intro x hx hx'
    rw [heq]
    have hleft : -u ≤ a+x := by linarith
    have hright : a+x ≤ u := by linarith
    have hsq := mul_nonneg (show 0 ≤ u - (a+x) by linarith)
      (show 0 ≤ u + (a+x) by linarith)
    dsimp [d] at hu2
    nlinarith
  · rw [heq]
    dsimp [d] at hu2
    nlinarith

private theorem intersect_disks_real_slice (z p q : ℂ) (r s : ℝ)
    (h₁ : Complex.normSq (z - p) ≤ r) (h₂ : Complex.normSq (z - q) ≤ s) :
    let t₁ := p.re - z.re + Real.sqrt (r - (z.im - p.im)^2)
    let t₂ := q.re - z.re + Real.sqrt (s - (z.im - q.im)^2)
    let t := min t₁ t₂
    0 ≤ t ∧ Complex.normSq (z + (t : ℂ) - p) ≤ r ∧
      Complex.normSq (z + (t : ℂ) - q) ≤ s ∧
      (Complex.normSq (z + (t : ℂ) - p) = r ∨
       Complex.normSq (z + (t : ℂ) - q) = s) := by
  let t₁ := p.re - z.re + Real.sqrt (r - (z.im - p.im)^2)
  let t₂ := q.re - z.re + Real.sqrt (s - (z.im - q.im)^2)
  let t := min t₁ t₂
  have h₁' := disk_slice_right_endpoint z p r h₁
  have h₂' := disk_slice_right_endpoint z q s h₂
  dsimp only at h₁' h₂'
  have ht₁ : 0 ≤ t₁ := h₁'.2.1
  have ht₂ : 0 ≤ t₂ := h₂'.2.1
  have ht : 0 ≤ t := le_min ht₁ ht₂
  refine ⟨ht, h₁'.2.2.1 t ht (min_le_left _ _), h₂'.2.2.1 t ht (min_le_right _ _), ?_⟩
  change Complex.normSq (z + (t : ℂ) - p) = r ∨
      Complex.normSq (z + (t : ℂ) - q) = s
  rcases le_total t₁ t₂ with h | h
  · have he : t = t₁ := min_eq_left h
    rw [he]
    exact Or.inl h₁'.2.2.2
  · have he : t = t₂ := min_eq_right h
    rw [he]
    exact Or.inr h₂'.2.2.2

private theorem rank_kronecker_of_outer_left (x y : Bool → ℂ) (R : Matrix Bool Bool ℂ) :
    (vecMulVec x y ⊗ₖ R).rank ≤ 2 := by
  let A : Matrix Bool Unit ℂ := fun i _ => x i
  let B : Matrix Unit Bool ℂ := fun _ j => y j
  have hAB : A * B = vecMulVec x y := by
    ext i j
    change (A * B) i j = x i * y j
    rw [Matrix.mul_apply]
    simp [A, B]
  have he := Matrix.mul_kronecker_mul A B (1 : Matrix Bool Bool ℂ) R
  rw [Matrix.one_mul, hAB] at he
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width (A ⊗ₖ (1 : Matrix Bool Bool ℂ)))

private theorem disk_endpoint_field (z p : ℂ) (r : ℝ)
    (qz : RationalEntry z) (qp : RationalEntry p) (qr : RationalReal r)
    (hz : normSq (z - p) ≤ r) :
    ∃ d : ℚ, 0 ≤ d ∧
      let F := Subfield.closure ((rationalComplex : Set ℂ) ∪ {↑(Real.sqrt (d : ℝ))})
      let w := z + (↑(p.re - z.re + Real.sqrt (r - (z.im - p.im)^2)) : ℂ)
      w ∈ F ∧ conj w ∈ F := by
  have qim : RationalReal (z.im - p.im) := by
    obtain ⟨_, a, _, ha⟩ := qz
    obtain ⟨_, c, _, hc⟩ := qp
    exact rrsub ⟨a, ha⟩ ⟨c, hc⟩
  have qd : RationalReal (r - (z.im - p.im)^2) :=
    rrsub qr (by simpa only [pow_two] using rrmul qim qim)
  obtain ⟨d, hd⟩ := qd
  have hd0 : 0 ≤ d := by
    have h : 0 ≤ (d : ℝ) := by
      rw [hd]
      exact (disk_slice_right_endpoint z p r hz).1
    exact_mod_cast h
  refine ⟨d, hd0, ?_⟩
  dsimp only
  let F := Subfield.closure ((rationalComplex : Set ℂ) ∪ {↑(Real.sqrt (d : ℝ))})
  have q (a : ℂ) (ha : RationalEntry a) : a ∈ F :=
    Subfield.subset_closure (Or.inl ha)
  have ha : (↑(p.re - z.re) : ℂ) ∈ F := q _ (realMk (rrsub (rreal qp) (rreal qz)))
  have hs : (↑(Real.sqrt (d : ℝ)) : ℂ) ∈ F :=
    Subfield.subset_closure (Or.inr rfl)
  rw [← hd, Complex.ofReal_add]
  refine ⟨F.add_mem (q _ qz) (F.add_mem ha hs), ?_⟩
  have hconj : conj z ∈ F := q (conj z) (rationalConjugate ⟨z, qz⟩).property
  change conj (z + ((↑(p.re - z.re) : ℂ) + ↑(Real.sqrt (d : ℝ)))) ∈ F
  rw [map_add, map_add, conj_ofReal, conj_ofReal]
  exact F.add_mem hconj (F.add_mem ha hs)

private theorem rank_singular_product (X Y : Matrix Bool Bool ℂ) (hX : X.PosSemidef)
    (hY : Y.PosSemidef) (ht : X.trace = Y.trace) (hd : X.det = 0 ∨ Y.det = 0) :
    ((X.trace⁻¹ • X) ⊗ₖ Y).rank ≤ 2 := by
  by_cases hz : X.trace = 0
  · rw [(hX.trace_eq_zero_iff).mp hz]
    simp
  have hinv : 0 ≤ X.trace⁻¹ := by
    have hlo := hX.trace_nonneg
    rw [Complex.nonneg_iff] at hlo ⊢
    simp [Complex.inv_re, Complex.inv_im, ← hlo.2, div_nonneg hlo.1 (Complex.normSq_nonneg _)]
  rcases hd with hx | hy
  · let W := X.trace⁻¹ • X
    have hW : W.PosSemidef := hX.smul hinv
    have htW : W.trace = 1 := by
      rw [show W = X.trace⁻¹ • X from rfl, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hz]
    have hdW : W.det = 0 := by simp [W, hx]
    obtain ⟨x, _, h⟩ := pure_of_singular W hW hdW htW
    change (W ⊗ₖ Y).rank ≤ 2
    rw [h]
    exact rank_kronecker_of_outer_left _ _ _
  · let W := X.trace⁻¹ • Y
    have hW : W.PosSemidef := hY.smul hinv
    have htW : W.trace = 1 := by
      rw [show W = X.trace⁻¹ • Y from rfl, Matrix.trace_smul, smul_eq_mul, ← ht,
        inv_mul_cancel₀ hz]
    have hdW : W.det = 0 := by simp [W, hy]
    obtain ⟨x, _, h⟩ := pure_of_singular W hW hdW htW
    have hs : (X.trace⁻¹ • X) ⊗ₖ Y =
        (W ⊗ₖ X).submatrix (Equiv.prodComm Bool Bool) (Equiv.prodComm Bool Bool) := by
      ext i j
      change (X.trace⁻¹ * X i.1 j.1) * Y i.2 j.2 =
        (X.trace⁻¹ * Y i.2 j.2) * X i.1 j.1
      ring
    rw [hs, Matrix.rank_submatrix, h]
    exact rank_kronecker_of_outer_left _ _ _

private theorem boundary_state (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (hb : 0 < b) (ht : L.trace + (b : ℂ) = 1) (hr : R.trace = L.trace)
    (F : Subfield ℂ) (qF : (rationalComplex : Set ℂ) ⊆ F)
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (qz : z ∈ F) (qzc : conj z ∈ F) :
    let C := correction b (middleRow u v w z)
    let X := L - partialTraceRight C
    let Y := R - partialTraceLeft C
    X.PosSemidef → Y.PosSemidef → (X.det = 0 ∨ Y.det = 0) →
    ∃ ρ : Matrix FibMarginalExtension.Word FibMarginalExtension.Word ℂ, ρ.PosSemidef ∧
      MatchesCoherentData b L R u v w z ρ ∧ ρ.rank ≤ 3 ∧ ∀ i j, ρ i j ∈ F := by
  dsimp only
  let row := middleRow u v w z
  let C := correction b row
  let X := L - partialTraceRight C
  let Y := R - partialTraceLeft C
  intro hX hY hd
  have htrace : X.trace = Y.trace := by
    simp [X, Y, Matrix.trace_sub, hr, trace_partialTraceRight, trace_partialTraceLeft]
  let S := (X.trace⁻¹ • X) ⊗ₖ Y
  obtain ⟨hS, hSL, hSR⟩ := product_completion_formula X Y hX hY htrace
  change S.PosSemidef at hS
  change partialTraceRight S = X at hSL
  change partialTraceLeft S = Y at hSR
  have hSr : S.rank ≤ 2 := rank_singular_product X Y hX hY htrace hd
  let T := S + C
  have hT : T - C = S := add_sub_cancel_right _ _
  have hTL : partialTraceRight T = L := by
    change partialTraceRight (S + C) = L
    rw [partialTraceRight_add, hSL, show X = _ from rfl, sub_add_cancel]
  have hTR : partialTraceLeft T = R := by
    change partialTraceLeft (S + C) = R
    rw [partialTraceLeft_add, hSR, show Y = _ from rfl, sub_add_cancel]
  have hpos := (block_psd b row T).mpr ⟨hb.le, fun h => (hb.ne' h).elim, hT ▸ hS⟩
  refine ⟨original (assemble b row T), hpos.submatrix _, ⟨?_, ?_, ?_, rfl⟩, ?_, ?_⟩
  · rwa [trace_original, trace_assemble, ← trace_partialTraceRight T, hTL]
  · rw [left_read, hTL]
    rfl
  · rw [right_read, hTR]
    rfl
  · rw [original, Matrix.rank_submatrix, assemble_rank b hb.ne', hT]
    omega
  · have qb : (b : ℂ) ∈ F := by
      rw [show (b : ℂ) = 1 - L.trace by linear_combination ht]
      exact F.sub_mem F.one_mem (F.sum_mem fun i _ => qF (qL i i))
    have inRow (i : Bool × Bool) : row i ∈ F ∧ conj (row i) ∈ F := by
      obtain ⟨i,j⟩ := i
      cases i <;> cases j
      · exact ⟨qF qu, qF (rationalConjugate ⟨_, qu⟩).property⟩
      · exact ⟨qF qw, qF (rationalConjugate ⟨_, qw⟩).property⟩
      · exact ⟨qF qv, qF (rationalConjugate ⟨_, qv⟩).property⟩
      · exact ⟨qz, qzc⟩
    have qC (i j : Bool × Bool) : C i j ∈ F := by
      change ((↑b⁻¹ : ℂ) * (conj (row i) * row j)) ∈ F
      rw [Complex.ofReal_inv]
      exact F.mul_mem (F.inv_mem qb) (F.mul_mem (inRow i).2 (inRow j).1)
    have qX (i j : Bool) : X i j ∈ F :=
      F.sub_mem (qF (qL i j)) (F.sum_mem fun k _ => qC (i,k) (j,k))
    have qY (i j : Bool) : Y i j ∈ F :=
      F.sub_mem (qF (qR i j)) (F.sum_mem fun k _ => qC (k,i) (k,j))
    have qt : X.trace ∈ F := F.sum_mem fun i _ => qX i i
    have qT (i j : Bool × Bool) : T i j ∈ F :=
      F.add_mem (F.mul_mem (F.mul_mem (F.inv_mem qt) (qX i.1 j.1)) (qY i.2 j.2)) (qC i j)
    intro i j
    change assemble b row T (wordEquiv.symm i) (wordEquiv.symm j) ∈ F
    cases wordEquiv.symm i <;> cases wordEquiv.symm j
    · rename_i a c
      cases a
      cases c
      exact qb
    · exact (inRow _).1
    · exact (inRow _).2
    · apply qT

/-- Compatible rational edge data at positive middle occupation admit rank at most three
over the field generated by the rational complex entries and one real square root. -/
theorem quadratic_rank_le_three (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (hb : 0 < b) (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (he : CoherentExtendible b L R u v w) :
    ∃ (d : ℚ), 0 ≤ d ∧ ∃ (z : ℂ) (ρ : Matrix Word Word ℂ),
      ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧ ρ.rank ≤ 3 ∧
      ∀ i j, ρ i j ∈ Subfield.closure ((rationalComplex : Set ℂ) ∪ {↑(Real.sqrt (d : ℝ))}) := by
  let z₀ := selectedCoupling b L R u v w
  obtain ⟨_, ht, hr, _, hleft, hright⟩ := (extendible_iff_selected b L R u v w).mp he
  have qb : RationalReal b := by
    have htq : RationalEntry L.trace := rationalComplex.sum_mem fun i _ => qL i i
    obtain ⟨q, hq⟩ := rreal htq
    have e := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at e
    refine ⟨1 - q, ?_⟩
    push_cast
    rw [hq]
    linarith
  obtain ⟨ρ₀, _, _, _, _, hcoupling, qρ₀⟩ :=
    (rational_coherent_extendible_iff b L R u v w qL qR qu qv qw).mp he
  have qz : RationalEntry z₀ := by
    dsimp only [z₀]
    rw [← hcoupling]
    exact qρ₀ (.inl 0) (.inr true)
  have hc : (correction b (middleRow u v w z₀)).PosSemidef := by
    unfold correction
    exact (posSemidef_vecMulVec_star_self _).smul (inv_nonneg.mpr hb.le)
  have hL : L.IsHermitian := by
    simpa [z₀] using (hleft.add (partialTraceRight_posSemidef hc)).isHermitian
  have hR : R.IsHermitian := by
    simpa [z₀] using (hright.add (partialTraceLeft_posSemidef hc)).isHermitian
  let A := edgeDisk b L u v w
  let B := edgeDisk b R u w v
  have ha : normSq (z₀ - A.1) ≤ A.2 := (edgeDisk_spec b L u v w z₀ hb hL).mp hleft
  have hb' : normSq (z₀ - B.1) ≤ B.2 := by
    apply (edgeDisk_spec b R u w v z₀ hb hR).mp
    rwa [← swapped_trace]
  let tA := A.1.re - z₀.re + Real.sqrt (A.2 - (z₀.im - A.1.im)^2)
  let tB := B.1.re - z₀.re + Real.sqrt (B.2 - (z₀.im - B.1.im)^2)
  let z := z₀ + (↑(min tA tB) : ℂ)
  have h := intersect_disks_real_slice z₀ A.1 B.1 A.2 B.2 ha hb'
  have hza : normSq (z - A.1) ≤ A.2 := h.2.1
  have hzb : normSq (z - B.1) ≤ B.2 := h.2.2.1
  have hbd : normSq (z - A.1) = A.2 ∨ normSq (z - B.1) = B.2 := h.2.2.2
  have hX := (edgeDisk_spec b L u v w z hb hL).mpr hza
  have hY := (edgeDisk_spec b R u w v z hb hR).mpr hzb
  rw [← swapped_trace] at hY
  have hd : (L - partialTraceRight (correction b (middleRow u v w z))).det = 0 ∨
      (R - partialTraceLeft (correction b (middleRow u v w z))).det = 0 := by
    rcases hbd with h | h
    · exact Or.inl (edge_singular_at_boundary b L u v w z hb hL h)
    · rw [swapped_trace]
      exact Or.inr (edge_singular_at_boundary b R u w v z hb hR h)
  have hfield : ∃ d : ℚ, 0 ≤ d ∧
      let F := Subfield.closure ((rationalComplex : Set ℂ) ∪ {↑(Real.sqrt (d : ℝ))})
      z ∈ F ∧ conj z ∈ F := by
    rcases le_total tA tB with h | h
    · obtain ⟨qp, qr⟩ := edgeDiskRational b L u v w qb qL qu qv qw
      simpa only [z, min_eq_left h, tA] using disk_endpoint_field z₀ A.1 A.2 qz qp qr ha
    · obtain ⟨qp, qr⟩ := edgeDiskRational b R u w v qb qR qu qw qv
      simpa only [z, min_eq_right h, tB] using disk_endpoint_field z₀ B.1 B.2 qz qp qr hb'
  obtain ⟨d, hd0, qz', qzc⟩ := hfield
  obtain ⟨ρ, hρ, hdata, hRank, qρ⟩ :=
    boundary_state b L R u v w z hb ht hr _ (fun _ h => Subfield.subset_closure (Or.inl h))
      qL qR qu qv qw qz' qzc hX hY hd
  exact ⟨d, hd0, z, ρ, hρ, hdata, hRank, qρ⟩

end D5.S3.Quantum.Entanglement.Marginals.FibQuadraticCompletion
