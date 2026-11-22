/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Recovering the weighted trace lift from the full seven-site projector. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactGraph
import Batteries.Tactic.OpenPrivate

/-! A linear trace-word decoder on the compact seven-site graph. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteLinearTraceLift

open Set Filter
open SevenSiteTraceBase SevenSiteCompactGraph
open PeriodicMPSProjectiveCoordinates (projector projector_scale continuousAt_projector
  projector_diag_ne_zero_iff)
open scoped Topology ComplexConjugate Matrix.Norms.Elementwise

open private form from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase

noncomputable section

/-- Fixed seven-letter trace contrasts obtained by expanding the two bond
commutators and using cyclicity of trace. -/
def linearReadout (T : Amp) : Fin 6 → ℂ :=
  ![-T ![0,0,0,0,0,1,1] - T ![0,0,0,0,1,0,1] + 2 * T ![0,0,0,1,0,0,1],
    -T ![0,0,0,0,1,1,1] + T ![0,0,0,1,0,1,1] - T ![0,0,0,1,1,0,1] +
      T ![0,0,1,0,0,1,1],
    -T ![0,0,0,1,1,1,1] + T ![0,0,1,1,0,1,1],
    -T ![0,0,0,0,1,0,1] + T ![0,0,0,1,0,0,1],
    T ![0,0,1,1,0,1,1] - T ![0,0,1,1,1,0,1],
    -T ![0,0,0,1,0,1,1] + T ![0,0,1,0,1,0,1]]

def commutatorSquare (p : Invariants) : ℂ :=
  p 4 ^ 2 - p 0 * p 1 * p 4 + p 0 ^ 2 * p 3 + p 1 ^ 2 * p 2 - 4 * p 2 * p 3

/-- The trace contrasts return a common multiple of all six weighted
coordinates, including when the commutator or either generator is singular. -/
theorem linearReadout_amplitude (p : Invariants) :
    linearReadout (amplitude p) = (commutatorSquare p * p 0) • weighted p := by
  funext i
  fin_cases i <;>
    simp [linearReadout, amplitude, wordPolynomial, form, weighted, commutatorSquare,
      List.ofFn_succ, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    ring

private theorem linearReadout_smul (c : ℂ) (T : Amp) :
    linearReadout (c • T) = c • linearReadout T := by
  funext i
  fin_cases i <;>
    simp [linearReadout, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring

def readColumn (j : Word 7) (P : Matrix (Word 7) (Word 7) ℂ) : Fin 6 → ℂ :=
  linearReadout fun i => P i j

theorem continuous_readColumn (j : Word 7) : Continuous (readColumn j) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [readColumn, linearReadout, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    fun_prop

private theorem readColumn_graph (j : Word 7) (p : Invariants) :
    readColumn j (graph p).2 =
      ((((PeriodicMPSProjectiveCoordinates.mass (amplitude p))⁻¹ : ℝ) : ℂ) *
        conj (amplitude p j) * (commutatorSquare p * p 0)) • weighted p := by
  let T : Amp := amplitude p
  let c : ℂ := ((PeriodicMPSProjectiveCoordinates.mass T)⁻¹ : ℝ) * conj (T j)
  have h : (fun i => projector T i j) = c • T := by
    funext i
    simp only [projector, PeriodicMPSProjectiveCoordinates.outer, Matrix.smul_apply,
      Complex.real_smul, Pi.smul_apply, smul_eq_mul, c]
    ring
  change linearReadout (fun i => projector T i j) = _
  rw [h, linearReadout_smul, linearReadout_amplitude, smul_smul]

/-- An observed full-projector column with a nonzero first trace contrast
determines the invariant projection throughout the compact graph. -/
theorem lift_eq_of_readColumn_ne_zero {x : Ambient} (hx : x ∈ source) (j : Word 7)
    (h : readColumn j x.2 0 ≠ 0) :
    x.1 = projector (readColumn j x.2) := by
  obtain ⟨p, _, _, _, _, hp, _⟩ := exists_lift_sequence hx
  have hlim := ((continuous_readColumn j).comp continuous_snd).continuousAt.tendsto.comp hp
  have he : ∀ᶠ n in atTop, readColumn j (graph (p n)).2 ≠ 0 := by
    have hn : readColumn j x.2 ≠ 0 := fun hz => h (congrFun hz 0)
    exact hlim.eventually_ne hn
  have hproj : Tendsto (fun n => projector (readColumn j (graph (p n)).2)) atTop
      (𝓝 (projector (readColumn j x.2))) :=
    (continuousAt_projector (fun hz => h (congrFun hz 0))).tendsto.comp hlim
  have hl : Tendsto (fun n => projector (readColumn j (graph (p n)).2)) atTop (𝓝 x.1) := by
    apply (continuous_fst.continuousAt.tendsto.comp hp).congr'
    filter_upwards [he] with n hn
    rw [readColumn_graph] at hn ⊢
    exact (projector_scale _ (fun hz => hn (by rw [hz, zero_smul]))).symm
  exact tendsto_nhds_unique hl hproj

theorem graph_lift_unique {x y : Ambient} (hx : x ∈ source) (hy : y ∈ source)
    (j : Word 7) (hj : readColumn j x.2 0 ≠ 0) (hxy : x.2 = y.2) : x = y := by
  apply Prod.ext _ hxy
  rw [lift_eq_of_readColumn_ne_zero hx j hj,
    lift_eq_of_readColumn_ne_zero hy j (hxy ▸ hj), hxy]

#print axioms linearReadout_amplitude
#print axioms graph_lift_unique

end

end D5.S3.Quantum.TensorNetworks.SevenSiteLinearTraceLift
