/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity; premises=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_convolutions
   digest: The full literal Barker numerator follows from the exact quotient annihilator and initial convolutions. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPartition
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPaths

/-! The reproduced formula is attributed to Colin Barker, OEIS A286848,
https://oeis.org/A286848, under CC-BY-SA-4.0,
https://creativecommons.org/licenses/by-sa/4.0/.
The quotient series is kept distinct from the actual-subset series until their
all-length counting correspondence is proved. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridSeries

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPartition
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPaths
open private rowEval orbit_values from D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridQuotient

/-- Lift a quotient vector to every full state in its literal class. -/
def lift : Vector →ₗ[ℤ] (State → ℤ) where
  toFun v s := v (classOf s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rows_nonneg : ∀ i : Fin 59,
    (rows i).Forall (fun e => 0 ≤ e.2) := by decide +kernel

private theorem expanded_row_sum (es : List (Fin 59 × ℤ))
    (h : es.Forall (fun e => 0 ≤ e.2)) (v : Vector) :
    ((es.flatMap fun e => List.replicate e.2.toNat e.1).map v).sum = rowEval es v := by
  induction es with
  | nil => simp [rowEval]
  | cons e es ih =>
    have he := ((List.forall_cons _ _ _).mp h).1
    have ht := ((List.forall_cons _ _ _).mp h).2
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, rowEval]
    rw [ih ht]
    simp only [nsmul_eq_mul, Int.toNat_of_nonneg he]

/-- The all-state finite row certificate intertwines the two linear transfers. -/
theorem intertwines (v : Vector) : fullStep (lift v) = lift (step v) := by
  funext s
  calc
    fullStep (lift v) s = ((successors s).map v).sum := by
      have h := List.sum_map_ite
        (fun m : Fin 8 => accepts (window s ⟨m.val, by omega⟩) = true)
        (fun m => v (classOf (append s m))) (fun _ => (0 : ℤ)) (List.finRange 8)
      simpa [fullStep, lift, successors, List.map_map, Function.comp_def, Fin.sum_univ_def] using h
    _ = ((quotientSuccessors (classOf s)).map v).sum :=
      ((row_certificate s).map v).sum_eq
    _ = lift (step v) s := expanded_row_sum (rows (classOf s)) (rows_nonneg _) v

/-- All full-state terminal-vector iterates are the lifted quotient iterates. -/
theorem lift_orbit (k : ℕ) : fullOrbit k = lift (orbit k) := by
  induction k with
  | zero => exact funext terminal_certificate
  | succ k ih => rw [fullOrbit, ih, intertwines, orbit]

private theorem alpha_nonneg : ∀ i : Fin 59, 0 ≤ alpha i := by decide +kernel

/-- Summing all 64 actual starts is exactly evaluation by the quotient initial row. -/
theorem initial_sum (v : Vector) :
    (∑ s : Fin 64, v (classOf ⟨s.val, by omega⟩)) = ∑ i : Fin 59, alpha i * v i := by
  calc
    (∑ s : Fin 64, v (classOf ⟨s.val, by omega⟩)) = (initialClasses.map v).sum := by
      simp [initialClasses, List.map_map, Function.comp_def, Fin.sum_univ_def]
    _ = (alphaClasses.map v).sum := (initial_certificate.map v).sum_eq
    _ = ∑ i : Fin 59, alpha i * v i := by
      simp only [alphaClasses, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def, List.map_replicate,
        List.sum_replicate, nsmul_eq_mul, Int.toNat_of_nonneg (alpha_nonneg _)]
      exact (Fin.sum_univ_def _).symm



/-- The complete numerator in increasing degree order, including its leading x. -/
def numerator : Fin 49 → ℤ := ![0, 2, 3, -2, -1, 4, 10, -14, -32, -29, -2, -21, -140, -140, 126, 80, 127, 143, 695, 401, 462, 582, -8, -490, -660, -721, -960, -714, -925, 25, 206, 255, 494, 155, 443, -118, 80, -71, -172, 78, -105, 79, 7, -28, 33, -7, -4, 3, -1]

/-- Evaluation by the exact initial row of the full-state quotient. -/
def evaluate : Vector →ₗ[ℤ] ℤ where
  toFun v := ∑ i : Fin 59, BarkerMinimalGridPartition.alpha i * v i
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply]
    ring

/-- The scalar quotient orbit with the separately prescribed positive-width
initial value and a zero series constant. This is not a definition of actualCount. -/
def quotientCoefficient (n : ℕ) : ℤ :=
  if n = 0 then 0 else if n = 1 then 2 else evaluate (orbit (n - 2))

/-- Exact finite orbit values used only for the initial coefficient range. -/
def initialCoefficient (n : Fin 50) : ℤ :=
  if n.val = 0 then 0 else if n.val = 1 then 2 else
    evaluate (values ⟨n.val - 2, by omega⟩)

private theorem coefficient_initial (n : Fin 50) :
    quotientCoefficient n.val = initialCoefficient n := by
  unfold quotientCoefficient initialCoefficient
  split_ifs with h₀ h₁
  · rfl
  · rfl
  · congr 1
    exact orbit_values ⟨n.val - 2, by omega⟩

/-- Every initial convolution, in degrees zero through 49, equals the complete
numerator; the extra degree 49 is checked to be zero. -/
theorem initial_convolutions : ∀ m : Fin 50,
    (∑ j : Fin 49, if j.val ≤ m.val then
      denominator j * initialCoefficient ⟨m.val - j.val, by omega⟩ else 0) =
      if h : m.val < 49 then numerator ⟨m.val, h⟩ else 0 := by
  decide +kernel

/-- The denominator recurrence holds at every coefficient from degree 50 onward. -/
theorem all_later_convolutions (m : ℕ) (hm : 50 ≤ m) :
    (∑ j : Fin 49, denominator j * quotientCoefficient (m - j.val)) = 0 := by
  have h := congrArg evaluate (shifted_annihilator (m - 50))
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  have h₀ : m - j.val ≠ 0 := by omega
  have h₁ : m - j.val ≠ 1 := by omega
  have he : m - j.val - 2 = m - 50 + 48 - j.val := by omega
  simp only [quotientCoefficient, if_neg h₀, if_neg h₁, he]

/-- The quotient-orbit series over the rationals. -/
def quotientSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (quotientCoefficient n : ℚ)

/-- The full literal numerator as a formal polynomial series. -/
def P : PowerSeries ℚ := PowerSeries.mk fun n =>
  if h : n < 49 then (numerator ⟨n, h⟩ : ℚ) else 0

/-- The full literal denominator as a finite sum of monomials. -/
noncomputable def Q : PowerSeries ℚ :=
  ∑ j : Fin 49, PowerSeries.C (denominator j : ℚ) * PowerSeries.X ^ j.val

private theorem coefficient_product (m : ℕ) :
    PowerSeries.coeff m (quotientSeries * Q) =
      ∑ j : Fin 49, if j.val ≤ m then
        (denominator j : ℚ) * (quotientCoefficient (m - j.val) : ℚ) else 0 := by
  simp only [Q, Finset.mul_sum, map_sum, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
    quotientSeries, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all [mul_comm]

/-- The exact quotient series has the complete numerator, including all initial
coefficients and the leading x, after multiplication by the literal denominator. -/
theorem quotientSeries_mul_Q : quotientSeries * Q = P := by
  apply PowerSeries.ext
  intro m
  rw [coefficient_product, P, PowerSeries.coeff_mk]
  by_cases hm : m < 50
  · have hi := initial_convolutions ⟨m, hm⟩
    have hc : ∀ j : Fin 49, j.val ≤ m →
        quotientCoefficient (m - j.val) = initialCoefficient ⟨m - j.val, by omega⟩ :=
      fun j _ => coefficient_initial ⟨m - j.val, by omega⟩
    simp_rw [show ∀ j : Fin 49, (if j.val ≤ m then
      (denominator j : ℚ) * (quotientCoefficient (m - j.val) : ℚ) else 0) =
      ((if j.val ≤ m then denominator j * initialCoefficient ⟨m - j.val, by omega⟩
        else 0 : ℤ) : ℚ) from fun j => by
          by_cases hj : j.val ≤ m
          · simp only [if_pos hj, hc j hj, Int.cast_mul]
          · simp only [if_neg hj, Int.cast_zero]]
    by_cases hp : m < 49
    · simp only [dif_pos hp] at hi ⊢
      exact_mod_cast hi
    · simp only [dif_neg hp] at hi ⊢
      exact_mod_cast hi
  · have hh : 50 ≤ m := by omega
    have hi := all_later_convolutions m hh
    have h49 : ¬ m < 49 := by omega
    rw [dif_neg h49]
    have hj : ∀ j : Fin 49, j.val ≤ m := fun j => by omega
    simp only [if_pos (hj _)]
    exact_mod_cast hi

/-- The constant term is one, so the literal denominator is a unit. -/
theorem Q_constant : PowerSeries.constantCoeff Q = 1 := by
  simp only [Q, map_sum, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X]
  calc
    _ = (denominator 0 : ℚ) * 0 ^ (0 : Fin 49).val := by
      apply Finset.sum_eq_single
      · intro b _ hb
        have hne : b.val ≠ 0 := fun h => hb (Fin.ext h)
        simp [hne]
      · simp
    _ = 1 := by norm_num [denominator]

/-- Inverse form of the full quotient-orbit identity. The actual-subset bridge
is an independent obligation, not an assumption of this theorem. -/
theorem quotientSeries_identity : quotientSeries = P * Q⁻¹ :=
  (PowerSeries.eq_mul_inv_iff_mul_eq (by rw [Q_constant]; norm_num)).mpr quotientSeries_mul_Q


/-- The original actual counts equal the certified quotient evaluation at every
width at least two, with no assumed count relation or recurrence. -/
theorem actualCount_quotient (k : ℕ) :
    (BarkerMinimalGridEncoding.actualCount (k + 2) : ℤ) = evaluate (orbit k) := by
  calc
    _ = ∑ s : Fin 64, fullOrbit k ⟨s.val, by omega⟩ := actualCount_fullOrbit k
    _ = ∑ s : Fin 64, orbit k (classOf ⟨s.val, by omega⟩) := by
      rw [lift_orbit]
      rfl
    _ = evaluate (orbit k) := initial_sum (orbit k)

/-- The requested series has the actual subset count at each positive width and
constant coefficient zero; no empty-grid count is redefined. -/
noncomputable def actualSeries : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else (BarkerMinimalGridEncoding.actualCount n : ℚ)

private theorem actualSeries_eq_quotientSeries : actualSeries = quotientSeries := by
  apply PowerSeries.ext
  intro n
  simp only [actualSeries, quotientSeries, PowerSeries.coeff_mk]
  by_cases h₀ : n = 0
  · subst n
    rfl
  · by_cases h₁ : n = 1
    · subst n
      simp [quotientCoefficient, actualCount_one]
    · simp only [if_neg h₀, quotientCoefficient, if_neg h₁]
      have he : n - 2 + 2 = n := by omega
      have hc := actualCount_quotient (n - 2)
      rw [he] at hc
      exact_mod_cast hc

/-- The complete unchanged Colin Barker OEIS A286848 identity for the actual
labelled inclusion-minimal dominating subsets of every ordinary open P3 × Pn. -/
theorem whole_identity : actualSeries = P * Q⁻¹ :=
  actualSeries_eq_quotientSeries.trans quotientSeries_identity

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridSeries
