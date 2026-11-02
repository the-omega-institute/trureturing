/- GID: D5/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete intensity and four anchor comparisons force complex linear isometry. -/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The complete output is a finite Hilbert direct sum. All comparisons use
the same actual function, with a shared complex reference in each channel.
The direct sum supplies no physical operation between different labels. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity

/-- Four calibrated orientations of each basis anchor, compared against every
input, determine the whole actual map. The exponent zero calibration is the
identity and imposes no extra condition beyond the three nonzero orientations.
The positive dimension is retained literally from the finite Hilbert interface. -/
theorem finite_oriented_anchor_rigidity
    {d : ℕ} (hd : 1 ≤ d)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {E : Type*} [Fintype E]
    {W : E → Type*} [∀ e, NormedAddCommGroup (W e)]
    [∀ e, InnerProductSpace ℂ (W e)] [∀ e, FiniteDimensional ℂ (W e)]
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → PiLp 2 W)
    (hmass : ∀ x, ∑ e, ‖F x e‖ ^ 2 = ‖x‖ ^ 2)
    (hphase : ∀ (j : Fin d) (k : Fin 4) (e : E),
      F ((Complex.I ^ k.val) • a j) e = (Complex.I ^ k.val) • F (a j) e)
    (hanchor : ∀ (x : H) (j : Fin d) (k : Fin 4),
      (∑ e, ‖F x e - F ((Complex.I ^ k.val) • a j) e‖ ^ 2) ≤
        ‖x - (Complex.I ^ k.val) • a j‖ ^ 2) :
    ∃! V : H →ₗᵢ[ℂ] PiLp 2 W,
      (∀ x, F x = V x) ∧ V.adjoint ∘ₗ V.toLinearMap = LinearMap.id := by
  classical
  have hnorm (x : H) : ‖F x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2] using hmass x
  have hcal (j : Fin d) (k : Fin 4) :
      F ((Complex.I ^ k.val) • a j) = (Complex.I ^ k.val) • F (a j) := by
    ext e
    exact hphase j k e
  have hcmp (x : H) (j : Fin d) (k : Fin 4) :
      ‖F x - F ((Complex.I ^ k.val) • a j)‖ ^ 2 ≤
        ‖x - (Complex.I ^ k.val) • a j‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply] using hanchor x j k
  have hreal (x : H) (j : Fin d) (k : Fin 4) :
      (inner ℂ x ((Complex.I ^ k.val) • a j)).re ≤
        (inner ℂ (F x) ((Complex.I ^ k.val) • F (a j))).re := by
    have h := hcmp x j k
    rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ),
      hnorm x, hnorm ((Complex.I ^ k.val) • a j), hcal j k] at h
    change ‖x‖ ^ 2 - 2 * (inner ℂ (F x) ((Complex.I ^ k.val) • F (a j))).re +
        ‖(Complex.I ^ k.val) • a j‖ ^ 2 ≤
      ‖x‖ ^ 2 - 2 * (inner ℂ x ((Complex.I ^ k.val) • a j)).re +
        ‖(Complex.I ^ k.val) • a j‖ ^ 2 at h
    linarith
  have hcoord (j : Fin d) (x : H) :
      inner ℂ (F x) (F (a j)) = inner ℂ x (a j) := by
    have h0 := hreal x j 0
    have h1 := hreal x j 1
    have h2 := hreal x j 2
    have h3 := hreal x j 3
    norm_num [pow_succ, inner_smul_right, Complex.mul_re, Complex.mul_im] at h0 h1 h2 h3
    apply Complex.ext <;> linarith
  have hortho : Orthonormal ℂ (fun j => F (a j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hcoord j (a i), a.inner_eq_ite]
  let L : H →ₗ[ℂ] PiLp 2 W := a.toBasis.constr ℂ (fun j => F (a j))
  have hL (j : Fin d) : L (a j) = F (a j) := a.toBasis.constr_basis ℂ _ j
  let V : H →ₗᵢ[ℂ] PiLp 2 W := L.isometryOfOrthonormal a.orthonormal (by
    simpa only [Function.comp_def, hL] using hortho)
  have hV (j : Fin d) : V (a j) = F (a j) := hL j
  have hsum (x : H) : V x = ∑ j, (inner ℂ (a j) x) • F (a j) := by
    calc
      V x = V (∑ j, (inner ℂ (a j) x) • a j) := by rw [a.sum_repr']
      _ = _ := by simp only [map_sum, map_smul, hV]
  have hcross (x : H) : inner ℂ (F x) (V x) = inner ℂ x x := by
    rw [hsum, inner_sum]
    simp only [inner_smul_right, hcoord]
    calc
      (∑ j, inner ℂ (a j) x * inner ℂ x (a j)) =
          inner ℂ x (∑ j, (inner ℂ (a j) x) • a j) := by
        simp only [inner_sum, inner_smul_right]
      _ = inner ℂ x x := by rw [a.sum_repr']
  have heq (x : H) : F x = V x := by
    have hz : ‖F x - V x‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), hnorm x, V.norm_map, hcross,
        inner_self_eq_norm_sq_to_K]
      simp only [Complex.ofReal_re]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (F x - V x)]))
  refine ⟨V, ⟨heq, V.adjoint_comp_self'⟩, ?_⟩
  intro U hU
  ext x
  exact (hU.1 x).symm.trans (heq x)

end D5.S3.Quantum.Foundation.FiniteOrientedAnchorRigidity
