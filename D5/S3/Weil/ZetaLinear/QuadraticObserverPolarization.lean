/- GID: D5/S3/Weil/ZetaLinear/QuadraticObserverPolarization
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:structural-infinite-arena)
   anchors: []
   digest: Recover every binary real quadratic form from two diagonal probes and one mixed probe, with strict refinement in the existing semantic-kernel calculus. -/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion
import Mathlib.Tactic

/-!
# The object information carried by a mixed quadratic probe

The state space is Mathlib's full `QuadraticForm R (Fin 2 -> R)` for R = Real.
No theorem truth value, proof term, source name, or hash is used as a state
coordinate. The kernel and semantic closure are the repository's existing
owners. This infinite arena has a strict structural refinement certificate;
no finite escape-rate number or global information-seal result is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaLinear.QuadraticObserverPolarization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion

abbrev BinaryQuadratic := QuadraticForm ℝ (Fin 2 → ℝ)

/-- The actual standard coordinate vector, reused by all probes. -/
def axis (i : Fin 2) : Fin 2 → ℝ := Pi.single i 1

/-- A diagonal evaluation of an actual quadratic form. -/
def diagonalProbe (i : Fin 2) : Concept BinaryQuadratic ℝ := fun Q => Q (axis i)

/-- The evaluation containing the cross term. -/
def mixedProbe : Concept BinaryQuadratic ℝ := fun Q => Q (axis 0 + axis 1)

/-- The two diagonal evaluations, with their original object domain retained. -/
def diagonalLanguage : Set (Concept BinaryQuadratic ℝ) := Set.range diagonalProbe

/-- Exact reconstruction of all vector evaluations from the three probes.
The proof reuses Mathlib's polarization and homogeneity laws. -/
theorem binary_quadratic_polarization (Q : BinaryQuadratic) (v : Fin 2 → ℝ) :
    Q v = (v 0) ^ 2 * diagonalProbe 0 Q +
      (v 1) ^ 2 * diagonalProbe 1 Q +
      v 0 * v 1 * (mixedProbe Q - diagonalProbe 0 Q - diagonalProbe 1 Q) := by
  have hsplit : v = v 0 • axis 0 + v 1 • axis 1 := by
    funext i
    fin_cases i <;> simp [axis, Pi.single_apply]
  calc
    Q v = Q (v 0 • axis 0 + v 1 • axis 1) := congrArg Q hsplit
    _ = _ := by
      rw [QuadraticMap.map_add, Q.map_smul, Q.map_smul,
        Q.polar_smul_left, Q.polar_smul_right]
      simp only [smul_eq_mul, QuadraticMap.polar, diagonalProbe, mixedProbe]
      ring

/-- All three evaluations together distinguish every binary real quadratic
form, rather than merely a selected finite sample of forms. -/
theorem three_probe_readout_injective :
    Function.Injective (fun Q : BinaryQuadratic =>
      (diagonalProbe 0 Q, diagonalProbe 1 Q, mixedProbe Q)) := by
  intro Q R he
  have h0 := congrArg Prod.fst he
  have h1 := congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) he
  have hm := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) he
  apply DFunLike.ext
  intro v
  rw [binary_quadratic_polarization Q v, binary_quadratic_polarization R v,
    h0, h1, hm]

private theorem mixedProbe_outside_diagonal_closure :
    mixedProbe ∉ SemanticClosure diagonalLanguage := by
  intro hclosure
  let cross : BinaryQuadratic := QuadraticMap.proj (0 : Fin 2) 1
  have hsame : ((0 : BinaryQuadratic), cross) ∈
      jointKernel (fun probe : diagonalLanguage => probe.1) := by
    apply Set.mem_iInter.mpr
    rintro ⟨probe, i, rfl⟩
    change diagonalProbe i 0 = diagonalProbe i cross
    fin_cases i <;> norm_num [diagonalProbe, axis, cross,
      QuadraticMap.proj_apply, Pi.single_apply]
  have hbad : mixedProbe (0 : BinaryQuadratic) = mixedProbe cross := hclosure hsame
  norm_num [mixedProbe, axis, cross, QuadraticMap.proj_apply, Pi.single_apply] at hbad

/-- On the unchanged infinite object arena, the mixed probe strictly shrinks
the common kernel of the diagonal probes. This is the structural certificate
permitted by the single-compile intrinsic-information specification. -/
theorem mixed_probe_strict_kernel_refinement :
    jointKernel (fun probe : Set.insert mixedProbe diagonalLanguage => probe.1) ⊂
      jointKernel (fun probe : diagonalLanguage => probe.1) :=
  (strict_kernel_novelty_criterion diagonalLanguage mixedProbe).mpr
    mixedProbe_outside_diagonal_closure

#print axioms binary_quadratic_polarization
#print axioms three_probe_readout_injective
#print axioms mixed_probe_strict_kernel_refinement

end D5.S3.Weil.ZetaLinear.QuadraticObserverPolarization
