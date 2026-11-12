/- GID: D5/S3/Quantum/Dynamics/NativeReader/Global
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Global
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full native auxiliary operators and source-column nonvanishing. -/

import D5.S3.Quantum.Dynamics.NativeReader.Uniform
import D5.S3.Quantum.Dynamics.NativeReader.Fibers
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! All extended legal paths remain in the actual operator and vector domain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader
open Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

/-- The fixed exterior bit b15 is retained when computing the last physical pulse. -/
def extendedBit (e : Extended) (k : ℕ) : Bool :=
  if h : k < 15 then e.1 ⟨k, h⟩ else true

/-- Literal native weighted legal-path coefficient at the actual physical center 10+j. -/
def fullProjection (j : Fin 5) : Matrix Extended Extended ℂ := fun e f =>
  if (∀ k : Fin 15, k.val ≠ 10 + j.val → e.1 k = f.1 k) ∧
      extendedBit e (9 + j.val) = extendedBit e (11 + j.val) then
    ((Real.sqrt (weight (extendedBit e (10 + j.val)) *
      weight (extendedBit f (10 + j.val))) /
      (Real.goldenRatio * weight (extendedBit e (9 + j.val))) : ℝ) : ℂ) else 0

private theorem fullProjection_source (j : Fin 5) (e f : Extended)
    (h : originalPart e ≠ originalPart f) : fullProjection j e f = 0 := by
  unfold fullProjection
  apply if_neg
  intro ha
  apply h
  apply Subtype.ext
  funext k
  by_cases hk : k.val < 10
  · simp only [originalPart, hk, dite_true]
    exact ha.1 ⟨k.val, by omega⟩ (by change k.val ≠ 10 + j.val; omega)
  · simp [originalPart, hk]

private theorem fullProjection_fiber (i : Bool) (q : SourceSector i) (j : Fin 5)
    (z w : Tail i) :
    fullProjection j (joinPath i q z) (joinPath i q w) = projection i j z w := by
  have hp :
      (∀ k : Fin 15, k.val ≠ 10 + j.val →
        (joinPath i q z).1 k = (joinPath i q w).1 k) ↔
      ∀ k : Fin 7, k.val ≠ j.val + 1 → z.1 k = w.1 k := by
    constructor
    · intro h k hk
      by_cases h0 : k.val = 0
      · have he : k = 0 := Fin.ext h0
        subst k
        exact z.2.1.trans w.2.1.symm
      · by_cases h6 : k.val = 6
        · have he : k = 6 := Fin.ext h6
          subst k
          exact z.2.2.1.trans w.2.2.1.symm
        · have h := h ⟨9 + k.val, by omega⟩ (by change 9 + k.val ≠ 10 + j.val; omega)
          simpa [joinPath, show ¬9 + k.val < 10 by omega,
            show 9 + k.val - 9 = k.val by omega] using h
    · intro h k hk
      by_cases h10 : k.val < 10
      · simp [joinPath, h10]
      · simpa [joinPath, h10] using h ⟨k.val - 9, by omega⟩ (by change k.val - 9 ≠ j.val + 1; omega)
  unfold fullProjection projection pathProjection
  have hz6 : z.1 6 = true := z.2.2.1
  have hneighbor : extendedBit (joinPath i q z) (9 + j.val) = z.1 ⟨j.val, by omega⟩ ∧
      extendedBit (joinPath i q z) (11 + j.val) = z.1 ⟨j.val + 2, by omega⟩ := by
    fin_cases j <;> simp [extendedBit, joinPath, q.2, z.2.1, hz6]
  have hcenter (v : Tail i) :
      extendedBit (joinPath i q v) (10 + j.val) = v.1 ⟨j.val + 1, by omega⟩ := by
    fin_cases j <;> simp [extendedBit, joinPath]
  simp only [hp, hneighbor.1, hneighbor.2, hcenter, Nat.add_sub_cancel]

set_option maxHeartbeats 1000000 in
private theorem fullProjection_blocks (j : Fin 5) :
    (fullProjection j).submatrix fullCarrierEquiv.symm fullCarrierEquiv.symm =
      Matrix.blockDiagonal' (fun q : Source => projection (q.1 9) j) := by
  classical
  funext a b
  rcases a with ⟨q, z⟩
  rcases b with ⟨r, w⟩
  simp only [Matrix.submatrix_apply]
  have hq : fullCarrierEquiv.symm ⟨q, z⟩ =
      joinPath (q.1 9) ⟨q, rfl⟩ z := by
    apply Subtype.ext
    funext k
    rfl
  have hr : fullCarrierEquiv.symm ⟨r, w⟩ =
      joinPath (r.1 9) ⟨r, rfl⟩ w := by
    apply Subtype.ext
    funext k
    rfl
  rw [hq, hr]
  by_cases h : q = r
  · subst r
    exact (fullProjection_fiber _ ⟨q, rfl⟩ j z w).trans
      (Matrix.blockDiagonal'_apply_eq
        (fun q : Source => projection (q.1 9) j) q z w).symm
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact fullProjection_source j _ _ (by rw [original_join, original_join]; exact h)

/-- Hermitian projection laws hold on the entire extended carrier, not just its interface. -/
theorem fullProjection_laws (j : Fin 5) :
    (fullProjection j).conjTranspose = fullProjection j ∧
      fullProjection j * fullProjection j = fullProjection j := by
  classical
  have hs : Function.Injective (fun M : Matrix Extended Extended ℂ =>
      M.submatrix fullCarrierEquiv.symm fullCarrierEquiv.symm) :=
    (Matrix.reindex fullCarrierEquiv fullCarrierEquiv).injective
  constructor
  · apply hs
    change ((fullProjection j).conjTranspose).submatrix
        fullCarrierEquiv.symm fullCarrierEquiv.symm =
      (fullProjection j).submatrix fullCarrierEquiv.symm fullCarrierEquiv.symm

    rw [← Matrix.conjTranspose_submatrix, fullProjection_blocks,
      Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext q
    exact (projection_laws (q.1 9) j).1
  · apply hs
    change (fullProjection j * fullProjection j).submatrix
        fullCarrierEquiv.symm fullCarrierEquiv.symm =
      (fullProjection j).submatrix fullCarrierEquiv.symm fullCarrierEquiv.symm
    rw [← Matrix.submatrix_mul_equiv _ _ _ fullCarrierEquiv.symm, fullProjection_blocks,
      ← Matrix.blockDiagonal'_mul]
    congr 1
    funext q
    exact (projection_laws (q.1 9) j).2

/-- The full native pulse, including its global phase and every complementary coordinate. -/
def fullPulse (j : Fin 5) (t : ℝ) : Matrix Extended Extended ℂ :=
  unitPhase t • (1 + (unitPhase t - 1) • fullProjection j)

/-- Source amplitudes multiply complete tail vectors; this is not a projected state update. -/
def globalVector (chi : Source → ℂ) (theta : (i : Bool) → Tail i → ℂ) : Extended → ℂ :=
  fun e => chi (originalPart e) * theta ((originalPart e).1 9) (auxiliaryPart e)

theorem globalVector_join (chi : Source → ℂ)
    (theta : (i : Bool) → Tail i → ℂ) (q : Source) (z : Tail (q.1 9)) :
    globalVector chi theta (joinPath (q.1 9) ⟨q, rfl⟩ z) = chi q * theta (q.1 9) z := by
  have h := (fullCarrierEquiv.right_inv ⟨q, z⟩)
  change (⟨originalPart (joinPath (q.1 9) ⟨q, rfl⟩ z),
    auxiliaryPart (joinPath (q.1 9) ⟨q, rfl⟩ z)⟩ : FiberCarrier) = ⟨q, z⟩ at h
  exact congrArg (fun p : FiberCarrier => chi p.1 * theta (p.1.1 9) p.2) h

private theorem fullProjection_global (j : Fin 5) (chi : Source → ℂ)
    (theta : (i : Bool) → Tail i → ℂ) (q : Source) (z : Tail (q.1 9)) :
    (fullProjection j *ᵥ globalVector chi theta) (joinPath (q.1 9) ⟨q, rfl⟩ z) =
      chi q * (projection (q.1 9) j *ᵥ theta (q.1 9)) z := by
  classical
  change (∑ e : Extended, fullProjection j (joinPath (q.1 9) ⟨q, rfl⟩ z) e *
    globalVector chi theta e) = _
  rw [← fullCarrierEquiv.symm.sum_comp]
  change (∑ p : FiberCarrier,
    fullProjection j (joinPath (q.1 9) ⟨q, rfl⟩ z) (joinPath (p.1.1 9) ⟨p.1, rfl⟩ p.2) *
      globalVector chi theta (joinPath (p.1.1 9) ⟨p.1, rfl⟩ p.2)) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single q]
  · simp only [fullProjection_fiber, globalVector_join, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro w _
    rw [fullProjection_source _ _ _ (by
      rw [original_join, original_join]
      exact Ne.symm hr), zero_mul]
  · simp

private theorem fullPulse_global (j : Fin 5) (t : ℝ) (chi : Source → ℂ)
    (theta : (i : Bool) → Tail i → ℂ) :
    fullPulse j t *ᵥ globalVector chi theta =
      globalVector chi (fun i => pulse i j t *ᵥ theta i) := by
  ext e
  have he := join_split e
  conv_lhs => rw [← he]
  conv_rhs => rw [← he]
  simp only [fullPulse, pulse, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, globalVector_join, fullProjection_global]
  ring

/-- Actual preparation output is supplied as its complete source vector, including zero columns. -/
def fullEntrance (chi : Source → ℂ) (lam : ℝ) : ℕ → Extended → ℂ
  | 0 => globalVector chi readyVector
  | k + 1 => fullPulse (address k) (angle lam (address k)) *ᵥ fullEntrance chi lam k

def fullDuring (chi : Source → ℂ) (lam : ℝ) (k : Fin 15) (s : ℝ) : Extended → ℂ :=
  fullPulse (address k) (angle lam (address k) * s) *ᵥ fullEntrance chi lam k

private theorem fullEntrance_factor (chi : Source → ℂ) (lam : ℝ) (k : ℕ) :
    fullEntrance chi lam k = globalVector chi (fun i => entrance i lam k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [fullEntrance, ih, fullPulse_global]; rfl

/-- Every coordinate is retained throughout the full native fifteen-call evolution. -/
theorem fullDuring_factor (chi : Source → ℂ) (lam : ℝ) (k : Fin 15) (s : ℝ) :
    fullDuring chi lam k s = globalVector chi (fun i => during i lam k s) := by
  rw [fullDuring, fullEntrance_factor, fullPulse_global]
  rfl

/-- The same neighborhood works for every complete source vector and every positive-support
    source entrance, with zero-support coordinates retained in the full vector domain. -/
theorem full_reader_uniform_nonvanishing :
    ∃ eta : ℝ, 0 < eta ∧ eta < min alpha (2 * Real.pi - alpha) ∧
      ∀ lam : ℝ, 0 < |lam - alpha| → |lam - alpha| < eta →
        ∀ (chi : Source → ℂ) (q : Source), chi q ≠ 0 →
          ∀ (k : Fin 15) (s : ℝ),
            fullDuring chi lam k s (joinPath (q.1 9) ⟨q, rfl⟩ (readyTail (q.1 9))) ≠ 0 := by
  obtain ⟨eta, he, ha, h⟩ := reader_uniform_nonvanishing
  refine ⟨eta, he, ha, ?_⟩
  intro lam hn hl chi q hq k s
  rw [fullDuring_factor, globalVector_join]
  exact mul_ne_zero hq (h lam hn hl (q.1 9) k s)

end D5.S3.Quantum.Dynamics.NativeReader
