/- GID: D5/S3/Quantum/Decoherence/FinitePathCoherence
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/FinitePathCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-path qubit channels multiply coherence, with polar and closed-path gauge laws. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FinitePathCoherence

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open scoped Matrix

universe u w

local notation "M" => Matrix (Fin 2) (Fin 2) ℂ
local notation "Q" => QuantumChannel (Fin 2) (Fin 2)

def coefficient (v theta : ℝ) : ℂ :=
  (v : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)

def matrixAction (C : Q) (rho : M) : M :=
  D5.S3.Quantum.Foundation.FiniteTraceDistance.act (ι := Fin 2) C rho

def sourceMatrix (a : ℝ) (b : ℂ) (d : ℝ) : M :=
  !![(a : ℂ), b; star b, (d : ℂ)]

private def edgeKraus (v theta : ℝ) : Fin 2 → M :=
  ![!![coefficient v theta, 0; 0, 1],
    !![(Real.sqrt (1 - v ^ 2) : ℂ), 0; 0, 0]]

private theorem coefficient_norm (v theta : ℝ) (hv : 0 ≤ v) :
    ‖coefficient v theta‖ = v := by
  simp [coefficient, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hv]

private theorem coefficient_mul (v t w s : ℝ) :
    coefficient (v * w) (t + s) = coefficient v t * coefficient w s := by
  simp only [coefficient, Complex.ofReal_mul, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  ring

private theorem edge_kraus_normalized (v theta : ℝ) (hv : 0 < v ∧ v ≤ 1) :
    (∑ r : Fin 2, (edgeKraus v theta r).conjTranspose * edgeKraus v theta r) = 1 := by
  have hs : (Real.sqrt (1 - v ^ 2) : ℂ) ^ 2 = 1 - (v : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1 - v ^ 2 by nlinarith [hv.1, hv.2])
  have hz : (starRingEnd ℂ) (coefficient v theta) * coefficient v theta =
      (v : ℂ) ^ 2 := by
    simp [Complex.conj_mul', coefficient_norm v theta hv.1.le]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edgeKraus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, ← pow_two, hz, hs]

private theorem edge_kraus_action (v theta : ℝ) (hv : 0 < v ∧ v ≤ 1) (rho : M) :
    (∑ r : Fin 2, edgeKraus v theta r * rho * (edgeKraus v theta r).conjTranspose) =
      !![rho 0 0, coefficient v theta * rho 0 1;
        star (coefficient v theta) * rho 1 0, rho 1 1] := by
  have hs : (Real.sqrt (1 - v ^ 2) : ℂ) ^ 2 = 1 - (v : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1 - v ^ 2 by nlinarith [hv.1, hv.2])
  have hz : coefficient v theta * (starRingEnd ℂ) (coefficient v theta) =
      (v : ℂ) ^ 2 := by
    simp [Complex.mul_conj', coefficient_norm v theta hv.1.le]
  simp only [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;>
    dsimp [edgeKraus] <;> simp only [mul_zero, zero_mul, zero_add, add_zero,
      mul_one, one_mul, map_zero, map_one, Complex.conj_ofReal]
  · linear_combination rho 0 0 * hz + rho 0 0 * hs
  · ring

def edgeChannel (v theta : ℝ) (hv : 0 < v ∧ v ≤ 1) : Q :=
  (finite_kraus_quantum_channel (edgeKraus v theta)
    (edge_kraus_normalized v theta hv)).choose

/-- The canonical Kraus realization has the complete source matrix action. -/
theorem edgeChannel_action (v theta : ℝ) (hv : 0 < v ∧ v ≤ 1) (rho : M) :
    matrixAction (edgeChannel v theta hv) rho =
      !![rho 0 0, coefficient v theta * rho 0 1;
        star (coefficient v theta) * rho 1 0, rho 1 1] := by
  exact ((finite_kraus_quantum_channel (edgeKraus v theta)
    (edge_kraus_normalized v theta hv)).choose_spec rho).trans
      (edge_kraus_action v theta hv rho)

private theorem edge_channel_source_action (v theta : ℝ) (hv : 0 < v ∧ v ≤ 1)
    (a d : ℝ) (b : ℂ) :
    matrixAction (edgeChannel v theta hv) (sourceMatrix a b d) =
      sourceMatrix a (coefficient v theta * b) d := by
  rw [edgeChannel_action]
  simp [sourceMatrix, star_mul, mul_comm]

private theorem matrix_action_comp (D C : Q) (rho : M) :
    matrixAction (D.comp C) rho = matrixAction D (matrixAction C rho) := by
  simp [matrixAction, D5.S3.Quantum.Foundation.FiniteTraceDistance.act,
    QuantumChannel.comp_apply]

/-- Sequential application is justified by independently prepared auxiliary
resources, or by a factorization already established in the physical model.
This definition does not assert that correlated resource reuse factorizes. -/
def pathChannel {V : Type u} [Quiver.{w} V]
    (C : ∀ {i j : V}, (i ⟶ j) → Q) : ∀ {i j : V}, Quiver.Path i j → Q
  | _, _, .nil => edgeChannel 1 0 ⟨by norm_num, by norm_num⟩
  | _, _, .cons p e => (C e).comp (pathChannel C p)

/-- Actual sequential channel action, on the entire source Hermitian sector. -/
theorem path_channel_action {V : Type u} [Quiver.{w} V]
    (C : ∀ {i j : V}, (i ⟶ j) → Q)
    (z : ∀ {i j : V}, (i ⟶ j) → ℂ)
    (hC : ∀ {i j : V} (e : i ⟶ j) (a d : ℝ) (b : ℂ),
      matrixAction (C e) (sourceMatrix a b d) = sourceMatrix a (z e * b) d)
    {i j : V} (p : Quiver.Path i j) (a d : ℝ) (b : ℂ) :
    matrixAction (pathChannel C p) (sourceMatrix a b d) =
      sourceMatrix a (Quiver.Path.weight z p * b) d := by
  induction p with
  | nil => simp [pathChannel, edge_channel_source_action, coefficient]
  | cons p e ih =>
    rw [pathChannel, matrix_action_comp, ih, hC]
    simp [mul_left_comm, mul_assoc]

private theorem path_weight_polar {V : Type u} [Quiver.{w} V]
    (v theta : ∀ {i j : V}, (i ⟶ j) → ℝ) {i j : V} (p : Quiver.Path i j) :
    Quiver.Path.weight (fun {x y : V} (e : x ⟶ y) => coefficient (v e) (theta e)) p =
      coefficient (Quiver.Path.weight v p) (Quiver.Path.addWeight theta p) := by
  induction p with
  | nil => simp [coefficient]
  | cons p e ih => simp [ih, coefficient_mul]

private theorem path_weight_le_one {V : Type u} [Quiver.{w} V]
    (v : ∀ {i j : V}, (i ⟶ j) → ℝ)
    (hv : ∀ {i j : V} (e : i ⟶ j), 0 < v e ∧ v e ≤ 1)
    {i j : V} (p : Quiver.Path i j) : Quiver.Path.weight v p ≤ 1 := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simpa only [Quiver.Path.weight_cons, one_mul] using
      mul_le_mul ih (hv e).2 (hv e).1.le (by norm_num : (0 : ℝ) ≤ 1)

private theorem path_log {V : Type u} [Quiver.{w} V]
    (v : ∀ {i j : V}, (i ⟶ j) → ℝ)
    (hv : ∀ {i j : V} (e : i ⟶ j), 0 < v e)
    {i j : V} (p : Quiver.Path i j) :
    -Real.log (Quiver.Path.weight v p) =
      Quiver.Path.addWeight (fun {x y : V} (e : x ⟶ y) => -Real.log (v e)) p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.weight_cons, Quiver.Path.addWeight_cons,
      Real.log_mul (Quiver.Path.weight_pos hv p).ne' (hv e).ne', neg_add, ih]

private theorem coefficient_gauge (v theta a b : ℝ) :
    coefficient v (theta + b - a) =
      Complex.exp (((b - a : ℝ) : ℂ) * Complex.I) * coefficient v theta := by
  have h : theta + b - a = (b - a) + theta := by ring
  simp only [coefficient, h, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

private theorem path_vertex_gauge {V : Type u} [Quiver.{w} V]
    (z : ∀ {i j : V}, (i ⟶ j) → ℂ) (alpha : V → ℝ)
    {i j : V} (p : Quiver.Path i j) :
    Quiver.Path.weight (fun {x y : V} (e : x ⟶ y) =>
      Complex.exp (((alpha y - alpha x : ℝ) : ℂ) * Complex.I) * z e) p =
      Complex.exp (((alpha j - alpha i : ℝ) : ℂ) * Complex.I) *
        Quiver.Path.weight z p := by
  induction p with
  | nil => simp
  | @cons j k p e ih =>
    rw [Quiver.Path.weight_cons, Quiver.Path.weight_cons, ih]
    have h : (((alpha j - alpha i : ℝ) : ℂ) * Complex.I) +
        (((alpha k - alpha j : ℝ) : ℂ) * Complex.I) =
        (((alpha k - alpha i : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [show (Complex.exp (((alpha j - alpha i : ℝ) : ℂ) * Complex.I) *
        Quiver.Path.weight z p) *
        (Complex.exp (((alpha k - alpha j : ℝ) : ℂ) * Complex.I) * z e) =
        (Complex.exp (((alpha j - alpha i : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((alpha k - alpha j : ℝ) : ℂ) * Complex.I)) *
          (Quiver.Path.weight z p * z e) by ring,
      ← Complex.exp_add, h]

/-- The full finite-path law retains both polar coordinates of the actual
coherence multiplier. Reference changes cancel exactly on closed paths. -/
theorem source_path_coherence {V : Type u} [Quiver.{w} V]
    (C : ∀ {i j : V}, (i ⟶ j) → Q)
    (v theta : ∀ {i j : V}, (i ⟶ j) → ℝ)
    (hv : ∀ {i j : V} (e : i ⟶ j), 0 < v e ∧ v e ≤ 1)
    (hC : ∀ {i j : V} (e : i ⟶ j) (a d : ℝ) (b : ℂ),
      matrixAction (C e) (sourceMatrix a b d) =
        sourceMatrix a (coefficient (v e) (theta e) * b) d)
    {i j : V} (p : Quiver.Path i j) (a d : ℝ) (b : ℂ) :
    let z : ∀ {x y : V}, (x ⟶ y) → ℂ :=
      fun {x y} e => coefficient (v e) (theta e)
    let zP := Quiver.Path.weight z p
    matrixAction (pathChannel C p) (sourceMatrix a b d) = sourceMatrix a (zP * b) d ∧
      zP ≠ 0 ∧ ‖zP‖ = Quiver.Path.weight v p ∧ 0 < ‖zP‖ ∧ ‖zP‖ ≤ 1 ∧
      (Complex.arg zP : Real.Angle) = ((Quiver.Path.addWeight theta p : ℝ) : Real.Angle) ∧
      -Real.log ‖zP‖ =
        Quiver.Path.addWeight (fun {x y : V} (e : x ⟶ y) => -Real.log (v e)) p ∧
      zP = (‖zP‖ : ℂ) * Complex.exp ((Complex.arg zP : ℂ) * Complex.I) ∧
      ∀ alpha : V → ℝ,
        let zg : ∀ {x y : V}, (x ⟶ y) → ℂ := fun {x y} e =>
          Complex.exp (((alpha y - alpha x : ℝ) : ℂ) * Complex.I) * z e
        let Cg : ∀ {x y : V}, (x ⟶ y) → Q := fun {x y} e =>
          edgeChannel (v e) (theta e + alpha y - alpha x) (hv e)
        let zgP := Quiver.Path.weight zg p
        zgP = Complex.exp (((alpha j - alpha i : ℝ) : ℂ) * Complex.I) * zP ∧
          (i = j → zgP = zP) ∧
          (i = j → ((Complex.arg zgP : Real.Angle), ‖zgP‖) =
            ((Complex.arg zP : Real.Angle), ‖zP‖)) ∧
          (i = j → matrixAction (pathChannel Cg p) (sourceMatrix a b d) =
            matrixAction (pathChannel C p) (sourceMatrix a b d)) := by
  let z : ∀ {x y : V}, (x ⟶ y) → ℂ := fun {x y} e => coefficient (v e) (theta e)
  have hp := Quiver.Path.weight_pos (fun {x y} (e : x ⟶ y) => (hv e).1) p
  have hn : ‖Quiver.Path.weight z p‖ = Quiver.Path.weight v p := by
    rw [show Quiver.Path.weight z p = _ from path_weight_polar v theta p,
      coefficient_norm _ _ hp.le]
  refine ⟨path_channel_action C z hC p a d b, norm_pos_iff.mp (hn.symm ▸ hp), hn,
    hn.symm ▸ hp, hn.symm ▸ path_weight_le_one v hv p, ?_, ?_,
    (Complex.norm_mul_exp_arg_mul_I _).symm, ?_⟩
  · change (Complex.arg (Quiver.Path.weight z p) : Real.Angle) = _
    rw [show Quiver.Path.weight z p = _ from path_weight_polar v theta p]
    simp [coefficient, Complex.arg_real_mul _ hp, Complex.arg_exp_mul_I]
  · rw [hn]
    exact path_log v (fun {x y} e => (hv e).1) p
  · intro alpha
    dsimp only
    have hg := path_vertex_gauge z alpha p
    have hc (h : i = j) : Quiver.Path.weight (fun {x y : V} (e : x ⟶ y) =>
        Complex.exp (((alpha y - alpha x : ℝ) : ℂ) * Complex.I) * z e) p =
        Quiver.Path.weight z p := by simpa [h] using hg
    refine ⟨hg, hc, fun h => by rw [hc h], ?_⟩
    intro h
    rw [path_channel_action (fun {x y} (e : x ⟶ y) =>
      edgeChannel (v e) (theta e + alpha y - alpha x) (hv e))
      (fun {x y} (e : x ⟶ y) =>
        Complex.exp (((alpha y - alpha x : ℝ) : ℂ) * Complex.I) * z e)
      (fun {x y} e a d b => by
        rw [edge_channel_source_action, coefficient_gauge]), hc h, path_channel_action C z hC]

#print axioms edgeChannel_action
#print axioms path_channel_action
#print axioms source_path_coherence

end D5.S3.Quantum.Decoherence.FinitePathCoherence
