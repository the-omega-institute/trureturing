/- GID: D5/S3/Weil/ZetaLinear/QuadraticObserverPolarization
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:structural-infinite-arena)
   anchors: []
   digest: Reconstruct binary quadratic forms and certify every probe by deletion. -/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion
import Mathlib.Tactic

/-!
# The object information carried by quadratic probes

The state space is Mathlib's full `QuadraticForm R (Fin 2 -> R)` for R = Real.
No theorem truth value, proof term, source name, or hash is a state coordinate.
The kernel and semantic closure are the repository's existing owners.

The three evaluations form a fixed mathematical family. For every deleted
probe there is an explicit pair of actual quadratic forms agreeing on all
other probes. This is a structural infinite-arena result, not a finite
escape-rate computation or a seal of the system's maximal canonical catalog.
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
def diagonalProbe (i : Fin 2) (Q : BinaryQuadratic) : ℝ := Q (axis i)

/-- The evaluation containing the cross term. -/
def mixedProbe (Q : BinaryQuadratic) : ℝ := Q (axis 0 + axis 1)

/-- The two diagonal evaluations on their unchanged object domain. -/
def diagonalLanguage : Set (Concept BinaryQuadratic ℝ) := Set.range diagonalProbe

/-- Exact reconstruction of all vector evaluations from three probes.
Mathlib supplies the polarization and homogeneity laws. -/
theorem binary_quadratic_polarization (Q : BinaryQuadratic) (v : Fin 2 → ℝ) :
    Q v = (v 0) ^ 2 * diagonalProbe 0 Q +
      (v 1) ^ 2 * diagonalProbe 1 Q +
      v 0 * v 1 * (mixedProbe Q - diagonalProbe 0 Q - diagonalProbe 1 Q) := by
  unfold diagonalProbe mixedProbe
  have hsplit : v = v 0 • axis 0 + v 1 • axis 1 := by
    funext i
    fin_cases i <;> simp [axis]
  calc
    Q v = Q (v 0 • axis 0 + v 1 • axis 1) := congrArg (fun w => Q w) hsplit
    _ = _ := by
      rw [QuadraticMap.map_add (fun w => Q w) (v 0 • axis 0) (v 1 • axis 1),
        Q.map_smul, Q.map_smul, Q.polar_smul_left, Q.polar_smul_right]
      simp only [smul_eq_mul, QuadraticMap.polar]
      ring

/-- The three evaluations distinguish all binary real quadratic forms. -/
theorem three_probe_readout_injective :
    Function.Injective (fun Q : BinaryQuadratic =>
      (diagonalProbe 0 Q, diagonalProbe 1 Q, mixedProbe Q)) := by
  intro Q R he
  have h0 : diagonalProbe 0 Q = diagonalProbe 0 R := congrArg Prod.fst he
  have h1 : diagonalProbe 1 Q = diagonalProbe 1 R :=
    congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) he
  have hm : mixedProbe Q = mixedProbe R :=
    congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) he
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

/-- The mixed probe strictly refines the two diagonal evaluations. -/
theorem mixed_probe_strict_kernel_refinement :
    jointKernel (fun probe : Set.insert mixedProbe diagonalLanguage => probe.1) ⊂
      jointKernel (fun probe : diagonalLanguage => probe.1) :=
  (strict_kernel_novelty_criterion diagonalLanguage mixedProbe).mpr
    mixedProbe_outside_diagonal_closure

/-- The complete fixed family, indexed independently of declaration order. -/
def quadraticProbe (i : Fin 3) (Q : BinaryQuadratic) : ℝ :=
  if i = 0 then diagonalProbe 0 Q
  else if i = 1 then diagonalProbe 1 Q else mixedProbe Q

/-- Dual quadratic witnesses: x squared minus xy, y squared minus xy, and xy. -/
private def probeWitness (i : Fin 3) : BinaryQuadratic :=
  if i = 0 then QuadraticMap.proj (0 : Fin 2) 0 - QuadraticMap.proj 0 1
  else if i = 1 then QuadraticMap.proj (1 : Fin 2) 1 - QuadraticMap.proj 0 1
  else QuadraticMap.proj (0 : Fin 2) 1

private theorem probeWitness_evaluation (i j : Fin 3) :
    quadraticProbe j (probeWitness i) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [quadraticProbe, probeWitness, diagonalProbe, mixedProbe, axis,
      QuadraticMap.proj_apply, Pi.single_apply]

/-- Every probe has a genuine unique-capture pair against all the other probes. -/
theorem three_probe_leave_one_out_witness (i : Fin 3) :
    ∃ Q R : BinaryQuadratic,
      (∀ j : Fin 3, j ≠ i → quadraticProbe j Q = quadraticProbe j R) ∧
      quadraticProbe i Q ≠ quadraticProbe i R := by
  refine ⟨0, probeWitness i, ?_, ?_⟩
  · intro j hji
    have hij : i ≠ j := Ne.symm hji
    rw [probeWitness_evaluation, if_neg hij]
    simp [quadraticProbe, diagonalProbe, mixedProbe]
  · rw [probeWitness_evaluation, if_pos rfl]
    simp [quadraticProbe, diagonalProbe, mixedProbe]

/-- For this whole three-probe family, removing any one generator strictly
increases the existing joint kernel on the full infinite quadratic arena. -/
theorem three_probe_kernel_irredundant (i : Fin 3) :
    jointKernel (fun j : Fin 3 => quadraticProbe j) ⊂
      jointKernel (fun j : {j : Fin 3 // j ≠ i} => quadraticProbe j.1) := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro pair hp
    apply Set.mem_iInter.mpr
    intro j
    exact Set.mem_iInter.mp hp j.1
  · intro heq
    obtain ⟨Q, R, hagree, hseparate⟩ := three_probe_leave_one_out_witness i
    have hw : (Q, R) ∈
        jointKernel (fun j : {j : Fin 3 // j ≠ i} => quadraticProbe j.1) := by
      apply Set.mem_iInter.mpr
      intro j
      exact hagree j.1 j.2
    have hf : (Q, R) ∈ jointKernel (fun j : Fin 3 => quadraticProbe j) := by
      rw [heq]
      exact hw
    exact hseparate (Set.mem_iInter.mp hf i)

/-- The full kernel is exactly equality of quadratic forms, on all states. -/
theorem three_probe_full_kernel_eq_diagonal :
    jointKernel (fun j : Fin 3 => quadraticProbe j) =
      {pair : BinaryQuadratic × BinaryQuadratic | pair.1 = pair.2} := by
  ext pair
  constructor
  · intro hp
    apply three_probe_readout_injective
    have h0 : quadraticProbe 0 pair.1 = quadraticProbe 0 pair.2 :=
      Set.mem_iInter.mp hp 0
    have h1 : quadraticProbe 1 pair.1 = quadraticProbe 1 pair.2 :=
      Set.mem_iInter.mp hp 1
    have h2 : quadraticProbe 2 pair.1 = quadraticProbe 2 pair.2 :=
      Set.mem_iInter.mp hp 2
    simp only [quadraticProbe] at h0 h1 h2
    exact Prod.ext h0 (Prod.ext h1 h2)
  · intro hp
    change pair.1 = pair.2 at hp
    apply Set.mem_iInter.mpr
    intro j
    change quadraticProbe j pair.1 = quadraticProbe j pair.2
    rw [hp]

#print axioms binary_quadratic_polarization
#print axioms three_probe_readout_injective
#print axioms mixed_probe_strict_kernel_refinement
#print axioms three_probe_leave_one_out_witness
#print axioms three_probe_kernel_irredundant
#print axioms three_probe_full_kernel_eq_diagonal

end D5.S3.Weil.ZetaLinear.QuadraticObserverPolarization
