import CFMPNormalizedInverseCore306Transient

noncomputable section
set_option autoImplicit false
open CFMPNormalizedInverseTangent107

namespace CFMPNormalizedInverseInvolution298Transient

/-- Unit-diagonal normalization of the inverse is an involution whenever
the original matrix is invertible and its inverse diagonal is positive. -/
theorem normalizedInverse_involutive {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (hG : IsUnit G.det)
    (hdiag : ∀ i, G i i = 1) (hpos : ∀ i, 0 < G⁻¹ i i) :
    normalizedInverse (normalizedInverse G) = G := by
  let D := normalScale G
  let K : Matrix n n ℝ := Matrix.diagonal (fun i => Real.sqrt (G⁻¹ i i))
  have hs (i : n) : Real.sqrt (G⁻¹ i i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
  have hDK : D*K = 1 := by
    change Matrix.diagonal (fun i => (Real.sqrt (G⁻¹ i i))⁻¹)*
      Matrix.diagonal (fun i => Real.sqrt (G⁻¹ i i)) = 1
    rw [Matrix.diagonal_mul_diagonal]
    have heq : (fun i => (Real.sqrt (G⁻¹ i i))⁻¹*Real.sqrt (G⁻¹ i i)) =
        (fun _ : n => (1 : ℝ)) := funext (fun i => inv_mul_cancel₀ (hs i))
    rw [heq]
    simp
  have hKD : K*D = 1 := by
    change Matrix.diagonal (fun i => Real.sqrt (G⁻¹ i i))*
      Matrix.diagonal (fun i => (Real.sqrt (G⁻¹ i i))⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    have heq : (fun i => Real.sqrt (G⁻¹ i i)*(Real.sqrt (G⁻¹ i i))⁻¹) =
        (fun _ : n => (1 : ℝ)) := funext (fun i => mul_inv_cancel₀ (hs i))
    rw [heq]
    simp
  let H := normalizedInverse G
  have hHG : (K*G*K)*H = 1 := by
    change (K*G*K)*(D*G⁻¹*D) = 1
    calc
      _ = K*(G*(K*D)*G⁻¹)*D := by noncomm_ring
      _ = K*(G*G⁻¹)*D := by rw [hKD];simp
      _ = 1 := by rw [Matrix.mul_nonsing_inv G hG];simpa using hKD
  have hHinv : H⁻¹ = K*G*K := Matrix.inv_eq_left_inv hHG
  have hHdiag (i : n) : H⁻¹ i i = G⁻¹ i i := by
    rw [hHinv]
    change (Matrix.diagonal (fun i => Real.sqrt (G⁻¹ i i))*G*
      Matrix.diagonal (fun i => Real.sqrt (G⁻¹ i i))) i i = G⁻¹ i i
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,hdiag i,mul_one]
    exact Real.mul_self_sqrt (hpos i).le
  have hscale : normalScale H = D := by
    change Matrix.diagonal (fun i => (Real.sqrt (H⁻¹ i i))⁻¹) =
      Matrix.diagonal (fun i => (Real.sqrt (G⁻¹ i i))⁻¹)
    congr 1
    funext i
    rw [hHdiag]
  change normalScale H*H⁻¹*normalScale H = G
  rw [hscale,hHinv]
  calc
    D*(K*G*K)*D = (D*K)*G*(K*D) := by noncomm_ring
    _ = G := by rw [hDK,hKD];simp

end CFMPNormalizedInverseInvolution298Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPNormalizedInverseInvolution298Transient.normalizedInverse_involutive
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP298 normalized-inverse involution theorem absent"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP298 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP298 CHECKED {name} axioms={axioms}"
