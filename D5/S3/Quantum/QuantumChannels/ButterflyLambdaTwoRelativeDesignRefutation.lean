/- GID: D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: Refute the single-pass butterfly relative-error exterior-square two-design claim. -/

/-
result proof_shape: content
escape_witness: circuit_minor_zero (private, content): the selected minor vanishes
for every K >= 2 and every parameter assignment, by inductive bit-support preservation.
admission_basis: open-problem-resolution (#11543; Refuted)
Direct frozen dependencies: none; canonical CP maps and Haar facts are pinned Mathlib.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.Star.Unitary

open Matrix MeasureTheory Set TopologicalSpace
open scoped BigOperators Matrix ComplexOrder MatrixOrder CStarAlgebra Kronecker
noncomputable section
namespace D5.S3.Quantum.QuantumChannels.ButterflyLambdaTwoRelativeDesignRefutation

/-!
Source: Kerenidis, arXiv:2607.24014v2, `quantum_v2.tex`,
`sec:butterfly_circuit` and `conj:lambda2_design`; preregistration #11543.
Bit zero is the first stride. The phase diagonal includes the global vacuum
phase of the full R_z layer. Exterior-square coordinates use ordered binary
mode pairs and the determinant expansion of `(W e_i) ∧ (W e_j)`.
The CP predicate includes complex linearity and every finite amplification.
-/

/-- Bit `l` has stride `2^l`; `finFunctionFinEquiv` identifies this with `Fin (2^K)`. -/
abbrev Mode (K : ℕ) := Fin K → Fin 2
abbrev Rest {K : ℕ} (l : Fin K) := {i : Fin K // i ≠ l} → Fin 2
abbrev AngleIndex (K : ℕ) := (Σ l : Fin K, Rest l) ⊕ (Fin K × Mode K)
abbrev Parameters (K : ℕ) := AngleIndex K → ℝ

def rbs {K : ℕ} (p : Parameters K) (l : Fin K) : Matrix (Mode K) (Mode K) ℂ :=
  (blockDiagonal fun q : Rest l =>
    (Matrix.planeConformalMatrix (Real.cos (p (.inl ⟨l,q⟩)) : ℂ)
      (-(Real.sin (p (.inl ⟨l,q⟩)) : ℂ)) (by
        have h := congrArg Complex.ofReal (Real.cos_sq_add_sin_sq (p (.inl ⟨l,q⟩)))
        simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] at h
        rw [neg_sq, h]
        exact one_ne_zero)).val).submatrix
    (Equiv.piSplitAt l (fun _ => Fin 2)) (Equiv.piSplitAt l (fun _ => Fin 2))

def phase {K : ℕ} (p : Parameters K) (l : Fin K) : Matrix (Mode K) (Mode K) ℂ :=
  diagonal fun j => (Circle.exp ((∑ i : Mode K, p (.inr (l,i))) / 2 - p (.inr (l,j))) : ℂ)

def layer {K : ℕ} (p : Parameters K) (l : Fin K) : Matrix (Mode K) (Mode K) ℂ :=
  rbs p l * phase p l

/-- Multiplication in descending index order gives the time order `U_K ... U_1`. -/
def circuit (K : ℕ) (p : Parameters K) : Matrix (Mode K) (Mode K) ℂ :=
  ((List.finRange K).reverse.map (layer p)).prod


/-- Independent uniform real angles on `[0,2π)`; endpoints have zero Lebesgue measure. -/
def parameterMeasure (K : ℕ) : Measure (Parameters K) :=
  Measure.pi fun _ => ProbabilityTheory.cond volume (Ico 0 (2 * Real.pi))

/-- The ordered-pair basis of the second exterior power, in binary mode order. -/
abbrev Wedge (K : ℕ) := {p : Mode K × Mode K //
  finFunctionFinEquiv p.1 < finFunctionFinEquiv p.2}

/-- The minors matrix in the basis `e_i ∧ e_j`, `i<j`.
Its entries are the coefficients obtained by expanding `(W e_i) ∧ (W e_j)`. -/
def exteriorSquare {K : ℕ} (W : Matrix (Mode K) (Mode K) ℂ) :
    Matrix (Wedge K) (Wedge K) ℂ := fun i j =>
  W i.1.1 j.1.1 * W i.1.2 j.1.2 - W i.1.1 j.1.2 * W i.1.2 j.1.1

abbrev TwoCopy (K : ℕ) := Wedge K × Wedge K

def secondAction {K : ℕ} (W : Matrix (Mode K) (Mode K) ℂ) :
    Matrix (TwoCopy K) (TwoCopy K) ℂ := exteriorSquare W ⊗ₖ exteriorSquare W

/-- Coordinatewise Bochner integral, the finite-dimensional matrix integral. -/
def twirl {K : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (W : X → Matrix (Mode K) (Mode K) ℂ) (Y : Matrix (TwoCopy K) (TwoCopy K) ℂ) :
    Matrix (TwoCopy K) (TwoCopy K) ℂ :=
  fun i j => ∫ p, (secondAction (W p) * Y * (secondAction (W p))ᴴ) i j ∂μ

def butterflyMoment (K : ℕ) := twirl (parameterMeasure K) (circuit K)

/-- U(n), using the operator-norm type copy of the same complex matrices. -/
abbrev Unitary (K : ℕ) := unitary (CStarMatrix (Mode K) (Mode K) ℂ)

private instance unitaryMeasurable (K : ℕ) : MeasurableSpace (Unitary K) := borel (Unitary K)

def haarProbability (K : ℕ) : Measure (Unitary K) := by
  letI : BorelSpace (Unitary K) := ⟨rfl⟩
  letI : CompactSpace (Unitary K) := by
    let : FiniteDimensional ℂ (CStarMatrix (Mode K) (Mode K) ℂ) :=
      Module.Finite.equiv (CStarMatrix.ofMatrixL (m := Mode K) (n := Mode K) (A := ℂ)).toLinearEquiv
    let : ProperSpace (CStarMatrix (Mode K) (Mode K) ℂ) := FiniteDimensional.proper ℂ _
    apply isCompact_iff_compactSpace.mp
    have hclosed : IsClosed (unitary (CStarMatrix (Mode K) (Mode K) ℂ) : Set (CStarMatrix (Mode K) (Mode K) ℂ)) :=
      isClosed_unitary (R := CStarMatrix (Mode K) (Mode K) ℂ)
    apply (isCompact_closedBall (0 : CStarMatrix (Mode K) (Mode K) ℂ) 1).of_isClosed_subset hclosed
    intro U hU
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (CStarRing.norm_coe_unitary ⟨U,hU⟩)
  exact Measure.haarMeasure ⊤

def haarMoment (K : ℕ) := twirl (haarProbability K)
  (fun U => CStarMatrix.ofMatrix.symm U.1)

/-- CP order of raw matrix actions through Mathlib's canonical completely positive maps. -/
def CPLe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F G : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop :=
  ∃ H : CompletelyPositiveMap (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ),
    ∀ Y, CStarMatrix.ofMatrix.symm (H (CStarMatrix.ofMatrix Y)) = G Y - F Y

def claim : Prop := ∃ (c : ℝ) (N₀ : ℕ), ∀ K : ℕ, N₀ ≤ 2^K →
  ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ c / (2^K : ℕ) ∧
    CPLe (fun Y => (1-ε) • haarMoment K Y) (butterflyMoment K) ∧
    CPLe (butterflyMoment K) (fun Y => (1+ε) • haarMoment K Y)

private theorem circuit_minor_zero {K : ℕ} (hK : 2 ≤ K) (p : Parameters K) :
    let z : Mode K := 0
    let a : Mode K := Pi.single ⟨0, by omega⟩ 1
    let b : Mode K := Pi.single ⟨1, by omega⟩ 1
    circuit K p z z * circuit K p b a - circuit K p z a * circuit K p b z = 0 := by
  cases K with
  | zero => omega
  | succ K =>
    let t : Fin (K+1) := 0
    let z : Mode (K+1) := 0
    let a : Mode (K+1) := Pi.single t 1
    let b : Mode (K+1) := Pi.single ⟨1, by omega⟩ 1
    change circuit (K+1) p z z * circuit (K+1) p b a -
      circuit (K+1) p z a * circuit (K+1) p b z = 0
    have support (l : Fin (K+1)) (i j : Mode (K+1)) (q : Fin (K+1))
        (hql : q ≠ l) (hij : i q ≠ j q) : layer p l i j = 0 := by
      have hrest : (Equiv.piSplitAt l (fun _ => Fin 2) i).2 ≠
          (Equiv.piSplitAt l (fun _ => Fin 2) j).2 := by
        intro h
        exact hij (congrFun h ⟨q,hql⟩)
      change (fun v : {q : Fin (K+1) // q ≠ l} => i v.1) ≠ (fun v => j v.1) at hrest
      simp [layer, phase, mul_diagonal, rbs, blockDiagonal_apply, hrest]
    have prod_support (ls : List (Fin (K+1))) (hs : ∀ l ∈ ls, l ≠ t)
        (i j : Mode (K+1)) (hij : i t ≠ j t) :
        (ls.map (layer p)).prod i j = 0 := by
      induction ls generalizing i j with
      | nil =>
        have hne : i ≠ j := fun h => hij (congrFun h t)
        simp [hne]
      | cons l ls ih =>
        simp only [List.map_cons, List.prod_cons, mul_apply]
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hik : i t = k t
        · rw [ih (fun v hv => hs v (by simp [hv])) k j (fun h => hij (hik.trans h))]
          exact mul_zero _
        · rw [support l i k t (hs l (by simp)).symm hik]
          exact zero_mul _
    let ls := ((List.finRange K).map Fin.succ).reverse
    let B : Matrix (Mode (K+1)) (Mode (K+1)) ℂ := (ls.map (layer p)).prod
    have hls : ∀ l ∈ ls, l ≠ t := by
      intro l hl
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hl)
      exact Fin.succ_ne_zero v
    have factor : circuit (K+1) p = B * layer p t := by
      simp [circuit, List.finRange_succ, List.reverse_cons, List.map_append,
        List.prod_append, B, ls, t]
    have az : a ≠ z := by
      intro h
      have := congrFun h t
      simp [a,z] at this
    have a_bit : a t = 1 := by simp [a]
    have b_bit : b t = 0 := by
      have ht : t ≠ (⟨1, by omega⟩ : Fin (K+1)) := by simp [t]
      simp [b, ht]
    have columns (i : Mode (K+1)) (hi : i t = 0) (j : Mode (K+1))
        (hj : (Equiv.piSplitAt t (fun _ => Fin 2) j).2 =
          (Equiv.piSplitAt t (fun _ => Fin 2) z).2) :
        circuit (K+1) p i j = B i z * layer p t z j := by
      rw [factor, mul_apply]
      apply Finset.sum_eq_single z
      · intro k hk hkz
        by_cases hka : k = a
        · subst k
          change (ls.map (layer p)).prod i a * _ = 0
          rw [prod_support ls hls i a (by rw [hi, a_bit]; decide)]
          exact zero_mul _
        · have hrest : (Equiv.piSplitAt t (fun _ => Fin 2) k).2 ≠
              (Equiv.piSplitAt t (fun _ => Fin 2) j).2 := by
            intro h
            have hrest := h.trans hj
            have hk0 : k t = 0 ∨ k t = 1 := by omega
            rcases hk0 with hk0 | hk1
            · apply hkz
              apply (Equiv.piSplitAt t (fun _ => Fin 2)).injective
              exact Prod.ext hk0 hrest
            · apply hka
              apply (Equiv.piSplitAt t (fun _ => Fin 2)).injective
              apply Prod.ext
              · simpa [a] using hk1
              · funext v
                have hv := congrFun hrest v
                simpa [a,z,Equiv.piSplitAt,Pi.single_apply,v.2] using hv
          change (fun v : {q : Fin (K+1) // q ≠ t} => k v.1) ≠ (fun v => j v.1) at hrest
          simp [layer, phase, mul_diagonal, rbs, blockDiagonal_apply, hrest]
      · simp
    have ja : (Equiv.piSplitAt t (fun _ => Fin 2) a).2 =
        (Equiv.piSplitAt t (fun _ => Fin 2) z).2 := by
      funext v
      simp [a,z,Equiv.piSplitAt, Pi.single_apply, v.2]
    rw [columns z rfl z rfl, columns b b_bit a ja,
      columns z rfl a ja, columns b b_bit z rfl]
    ring

private def inputWedge (K : ℕ) (hK : 2 ≤ K) : Wedge K :=
  ⟨(0, Pi.single ⟨0, by omega⟩ 1), by
    change (finFunctionFinEquiv (0 : Mode K) : ℕ) <
      (finFunctionFinEquiv (Pi.single (⟨0, by omega⟩ : Fin K) 1) : ℕ)
    rw [finFunctionFinEquiv_single]
    simp⟩

private def outputWedge (K : ℕ) (hK : 2 ≤ K) : Wedge K :=
  ⟨(0, Pi.single ⟨1, by omega⟩ 1), by
    change (finFunctionFinEquiv (0 : Mode K) : ℕ) <
      (finFunctionFinEquiv (Pi.single (⟨1, by omega⟩ : Fin K) 1) : ℕ)
    rw [finFunctionFinEquiv_single]
    simp⟩

private def minor {K : ℕ} (hK : 2 ≤ K) (W : Matrix (Mode K) (Mode K) ℂ) : ℂ :=
  exteriorSquare W (outputWedge K hK) (inputWedge K hK)


set_option maxHeartbeats 1000000 in
theorem result : ¬ claim := by
  have haar_positive {K : ℕ} (hK : 2 ≤ K) :
      0 < ∫ U : Unitary K, ‖minor hK (CStarMatrix.ofMatrix.symm U.1)‖^4 ∂haarProbability K := by
    let : BorelSpace (Unitary K) := ⟨rfl⟩
    let : CompactSpace (Unitary K) := by
      let : FiniteDimensional ℂ (CStarMatrix (Mode K) (Mode K) ℂ) :=
        Module.Finite.equiv (CStarMatrix.ofMatrixL (m := Mode K) (n := Mode K) (A := ℂ)).toLinearEquiv
      let : ProperSpace (CStarMatrix (Mode K) (Mode K) ℂ) := FiniteDimensional.proper ℂ _
      apply isCompact_iff_compactSpace.mp
      have hclosed : IsClosed (unitary (CStarMatrix (Mode K) (Mode K) ℂ) : Set (CStarMatrix (Mode K) (Mode K) ℂ)) :=
        isClosed_unitary (R := CStarMatrix (Mode K) (Mode K) ℂ)
      apply (isCompact_closedBall (0 : CStarMatrix (Mode K) (Mode K) ℂ) 1).of_isClosed_subset hclosed
      intro U hU
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (CStarRing.norm_coe_unitary ⟨U,hU⟩)
    let : (haarProbability K).IsHaarMeasure := by
      change (Measure.haarMeasure (⊤ : PositiveCompacts (Unitary K))).IsHaarMeasure
      infer_instance
    let z : Mode K := 0
    let a : Mode K := Pi.single ⟨0, by omega⟩ 1
    let b : Mode K := Pi.single ⟨1, by omega⟩ 1
    have haz : a ≠ z := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp [a,z] at this
    have hbz : b ≠ z := by
      intro h
      have := congrFun h ⟨1, by omega⟩
      simp [b,z] at this
    have hab : a ≠ b := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      have hn : (⟨0, by omega⟩ : Fin K) ≠ ⟨1, by omega⟩ := by simp
      simp [a,b,hn] at this
    let σ := Equiv.swap a b
    let P : Matrix (Mode K) (Mode K) ℂ := σ.permMatrix ℂ
    have hP : P ∈ Matrix.unitaryGroup (Mode K) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      change P * Pᴴ = 1
      simp [P, ← Matrix.permMatrix_mul]
    let U : Unitary K := ⟨CStarMatrix.ofMatrix P, by
      change P ∈ Matrix.unitaryGroup (Mode K) ℂ
      exact hP⟩
    have hm : minor hK (CStarMatrix.ofMatrix.symm U.1) = 1 := by
      change P z z * P b a - P z a * P b z = 1
      have hsz : σ z = z := Equiv.swap_apply_of_ne_of_ne haz.symm hbz.symm
      simp [P,σ,PEquiv.toMatrix,Equiv.toPEquiv,haz,hsz]
    have hc : Continuous (fun U : Unitary K =>
        ‖minor hK (CStarMatrix.ofMatrix.symm U.1)‖^4) := by
      have hv : Continuous (fun U : Unitary K => CStarMatrix.ofMatrix.symm U.1) :=
        (CStarMatrix.ofMatrixL (m := Mode K) (n := Mode K) (A := ℂ)).symm.continuous.comp
          continuous_subtype_val
      have he (i j : Mode K) : Continuous (fun U : Unitary K => CStarMatrix.ofMatrix.symm U.1 i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp hv)
      unfold minor exteriorSquare
      exact ((he _ _).mul (he _ _)).sub ((he _ _).mul (he _ _)) |>.norm |>.pow 4
    have hi : Integrable (fun U : Unitary K =>
        ‖minor hK (CStarMatrix.ofMatrix.symm U.1)‖^4) (haarProbability K) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact integral_pos_of_integrable_nonneg_nonzero hc hi
      (fun U => by positivity) (by rw [hm]; norm_num)
  have forced (K : ℕ) (hK : 2 ≤ K) (ε : ℝ)
      (hlow : CPLe (fun Y => (1-ε) • haarMoment K Y) (butterflyMoment K)) : 1 ≤ ε := by
    let x : TwoCopy K := (inputWedge K hK,inputWedge K hK)
    let u : TwoCopy K := (outputWedge K hK,outputWedge K hK)
    let Y : Matrix (TwoCopy K) (TwoCopy K) ℂ := Matrix.diagonal (Pi.single x 1)
    have hY : Y.PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro j
      by_cases hj : j = x <;> simp [hj]
    have kernel (A : Matrix (TwoCopy K) (TwoCopy K) ℂ) :
        (A * Y * Aᴴ) u u = A u x * star (A u x) := by
      simp [Y, Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, Matrix.conjTranspose_apply]
    have entry (W : Matrix (Mode K) (Mode K) ℂ) :
        (secondAction W * Y * (secondAction W)ᴴ) u u = (‖minor hK W‖^4 : ℝ) := by
      rw [kernel]
      change (minor hK W * minor hK W) * star (minor hK W * minor hK W) = _
      rw [show star (minor hK W * minor hK W) = (starRingEnd ℂ) (minor hK W * minor hK W) from rfl,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul]
      push_cast
      ring
    have hw : butterflyMoment K Y u u = 0 := by
      change (∫ p, (secondAction (circuit K p) * Y * (secondAction (circuit K p))ᴴ) u u
        ∂parameterMeasure K) = 0
      have hz (p : Parameters K) : minor hK (circuit K p) = 0 := circuit_minor_zero hK p
      simp_rw [entry, hz, norm_zero, zero_pow (by decide : 4 ≠ 0), Complex.ofReal_zero]
      exact integral_zero _ _
    let H : ℝ := ∫ U : Unitary K, ‖minor hK (CStarMatrix.ofMatrix.symm U.1)‖^4 ∂haarProbability K
    have hH : 0 < H := haar_positive hK
    have hh : haarMoment K Y u u = (H : ℂ) := by
      change (∫ U : Unitary K, (secondAction (CStarMatrix.ofMatrix.symm U.1) * Y *
        (secondAction (CStarMatrix.ofMatrix.symm U.1))ᴴ) u u ∂haarProbability K) = _
      simp_rw [entry]
      exact integral_complex_ofReal
    obtain ⟨F, hF⟩ := hlow
    let : OrderHomClass
        (CompletelyPositiveMap (CStarMatrix (TwoCopy K) (TwoCopy K) ℂ)
          (CStarMatrix (TwoCopy K) (TwoCopy K) ℂ))
        (CStarMatrix (TwoCopy K) (TwoCopy K) ℂ) (CStarMatrix (TwoCopy K) (TwoCopy K) ℂ) :=
      OrderHomClass.of_map_cstarMatrix_nonneg
        (fun φ k M hM => φ.map_cstarMatrix_nonneg' k M hM)
    have hpos : (CStarMatrix.ofMatrix.symm (F (CStarMatrix.ofMatrix Y))).PosSemidef := by
      apply Matrix.nonneg_iff_posSemidef.mp
      exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg F (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hY.nonneg))
    rw [hF Y] at hpos
    have hdiag := hpos.diag_nonneg (i := u)
    have hr := (Complex.nonneg_iff.mp hdiag).1
    change 0 ≤ ((butterflyMoment K Y) u u - (1-ε) • (haarMoment K Y) u u).re at hr
    rw [hw,hh] at hr
    simp only [Complex.sub_re, Complex.zero_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
    nlinarith
  rintro ⟨c,N₀,hclaim⟩
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (max c (N₀ : ℝ) + 4) (by norm_num : 1 < (2 : ℝ))
  let K := max m 2
  have hK : 2 ≤ K := le_max_right _ _
  have hmK : (2 : ℝ)^m ≤ (2 : ℝ)^K := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have hc : c < (2^K : ℕ) := by
    push_cast
    linarith [le_max_left c (N₀ : ℝ)]
  have hN : N₀ ≤ 2^K := by
    have hn : (N₀ : ℝ) < (2^K : ℕ) := by
      push_cast
      linarith [le_max_right c (N₀ : ℝ)]
    exact_mod_cast hn.le
  obtain ⟨ε,hε,hbound,hlow,hup⟩ := hclaim K hN
  have hnpos : (0 : ℝ) < (2^K : ℕ) := by positivity
  have hsmall : ε < 1 := hbound.trans_lt ((div_lt_one hnpos).mpr hc)
  have hlarge := forced K hK ε hlow
  linarith

#print axioms result
end D5.S3.Quantum.QuantumChannels.ButterflyLambdaTwoRelativeDesignRefutation
