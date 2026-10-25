import CFMPOriginalAngleInverseCore309Transient
import CFMPCofactorNormalizedInverse307Transient

noncomputable section
set_option autoImplicit false
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface (gram)
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open CFMPNormalizedInverseTangent107 (normalizedInverse)
open CFMPStrictAngleGram296Transient
open CFMPStrictAngleCofactors297Transient
open CFMPCofactorLengthGram303Transient
open CFMPCofactorNormalizedInverse307Transient
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine)
open CFMPGenuineDomain108Transient (genuine_iff_lengthGram_det_neg)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle vertexPerm)
open CFMPSourceAngleKernel111 (normalized_source_cosine)

namespace CFMPOriginalStrictInverse310Transient

/-- Original six-angle inverse at the original six length positions. The
original genuine criterion is established before the cosine readout is used. -/
theorem original_strict_angle_inverse (α : Fin 6 → ℝ) (hα : ∀ q, 0 < α q)
    (hv0 : α 0+α 1+α 2 < Real.pi)
    (hv1 : α 0+α 5+α 4 < Real.pi)
    (hv2 : α 1+α 5+α 3 < Real.pi)
    (hv3 : α 2+α 4+α 3 < Real.pi) :
    ∃ l : Fin 6 → ℝ, genuine l ∧ ∀ q, sourceAngle l q = α q := by
  let G := gram (Real.cos (α 3)) (Real.cos (α 4)) (Real.cos (α 5))
    (Real.cos (α 0)) (Real.cos (α 1)) (Real.cos (α 2))
  have hdet : G.det < 0 := strict_angle_gram_det_neg
    (α 3) (α 4) (α 5) (α 2) (α 1) (α 0)
    (hα 3) (hα 4) (hα 5) (hα 2) (hα 1) (hα 0)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨hd,hg⟩ := strict_angle_cofactor_gaps
    (α 3) (α 4) (α 5) (α 2) (α 1) (α 0)
    (hα 3) (hα 4) (hα 5) (hα 2) (hα 1) (hα 0)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hsym : G.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdiag (i : Fin 4) : G i i = 1 := by fin_cases i <;> rfl
  let l := cofactorLength G
  have hlength := cofactor_lengths_det_neg G hsym hdet hd hg
  have hgen : genuine l := (genuine_iff_lengthGram_det_neg l).mpr hlength
  have hN : normalizedInverse (lengthGram l) = G :=
    normalizedInverse_lengthGram_cofactorLength G hsym hdet hdiag hd hg
  have hentry (q : Fin 6) : G (vertexPerm q 2) (vertexPerm q 3) =
      -Real.cos (α q) := by fin_cases q <;> rfl
  have hαπ (q : Fin 6) : α q ≤ Real.pi := by
    fin_cases q
    · change α 0 ≤ Real.pi
      linarith only [hv0, hα 1, hα 2]
    · change α 1 ≤ Real.pi
      linarith only [hv0, hα 0, hα 2]
    · change α 2 ≤ Real.pi
      linarith only [hv0, hα 0, hα 1]
    · change α 3 ≤ Real.pi
      linarith only [hv2, hα 1, hα 5]
    · change α 4 ≤ Real.pi
      linarith only [hv1, hα 0, hα 5]
    · change α 5 ≤ Real.pi
      linarith only [hv1, hα 0, hα 4]
  refine ⟨l,hgen,?_⟩
  intro q
  have hs := normalized_source_cosine l hgen q
  rw [hN,hentry q] at hs
  have hcos : sourceCosine l q = Real.cos (α q) := by linarith
  change Real.arccos (sourceCosine l q) = α q
  rw [hcos,Real.arccos_cos (hα q).le (hαπ q)]

end CFMPOriginalStrictInverse310Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPOriginalStrictInverse310Transient.original_strict_angle_inverse
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP310 original strict-angle inverse absent"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP310 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP310 CHECKED {name} axioms={axioms}"
