/- GID: D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Locality and statewise truncation give common infinite vector word series. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.WeightedLocalCorrelator
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
Classical finite-word locality is supplied by common_cleared_fields. The native
series below is constructed from that common lower-bounded array, and all
signed coefficients are recovered after a statewise monomial shift.
The Matsuo--Nagatomo and Carnahan attributions are retained in the imports.
proof_shape: ungraded_local_word_common_series: bind-only
proof_shape: polynomialAction_map: bind-only
proof_shape: signedExtend_map: bind-only
These are common-series and linear-readout helpers for the actual inner
iterate transport. Their permutation and support facts come from the frozen
common_cleared_fields supplier; index conversion adds no separate mathematical
content. The inner transport supplies the signed collision inference.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.UngradedLocalWordSeries

open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Finite Laurent convolution commutes with a linear vector readout. -/
theorem polynomialAction_map {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (q : LaurentPolynomial N) (F : Distribution N V)
    (e : Exponent N) :
    f (polynomialAction q F e) =
      polynomialAction q (fun d => f (F d)) e := by
  classical
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q r hq hr =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hq, hr]
  | single b c =>
    simp only [polynomialAction, AddMonoidAlgebra.lift_single,
      LinearMap.smul_apply, Pi.smul_apply]
    change f (c • F (e - b)) = c • f (F (e - b))
    exact f.map_smul c _

/-- The native finitely supported multi-index on a finite label type.
This is an index, not a finite-support assertion about the power series. -/
def signedIndex (e : Exponent N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i).toNat)

/-- Zero extension of the native vector-valued MvPowerSeries to every signed
multi-index. P d is its native coefficient function; the named Mathlib coeff
linear map would unnecessarily require a semiring structure on V. -/
def signedExtend (P : MvPowerSeries (Fin N) V) (e : Exponent N) : V :=
  if ∀ i, 0 ≤ e i then P (signedIndex e) else 0

/-- Signed extension commutes with vector readouts, with no target multiplication. -/
theorem signedExtend_map {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (P : MvPowerSeries (Fin N) V) (e : Exponent N) :
    f (signedExtend P e) = signedExtend (fun d => f (P d)) e := by
  classical
  by_cases h : ∀ i, 0 ≤ e i <;> simp [signedExtend, h]

private theorem power_kills_of_le {X : Type*} [AddCommGroup X] [Module ℂ X]
    (E : Module.End ℂ X) (x : X) {r k : ℕ} (hrk : r ≤ k)
    (hx : (E ^ r) x = 0) : (E ^ k) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrk
  rw [add_comm r d, pow_add, Module.End.mul_apply, hx, map_zero]

/-- Pairwise locality orders have a finite common upper order. It is selected
from the labelled fields alone, before an input vector is supplied. -/
private theorem uniform_locality_order (A : Fin N → VertexOperator ℂ V)
    (locality : ∀ i j : Fin N, i < j →
      ∃ r : ℕ, (deltaEnd ^ r) (commutator (A i) (A j)) = 0) :
    ∃ k : ℕ, ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0 := by
  classical
  let r : Fin N × Fin N → ℕ := fun p =>
    if h : p.1 < p.2 then Classical.choose (locality p.1 p.2 h) else 0
  let k : ℕ := ∑ p ∈ labelledPairs N, r p
  refine ⟨k, ?_⟩
  intro i j hij
  have member : (i, j) ∈ labelledPairs N := by simp [labelledPairs, hij]
  have bound : r (i, j) ≤ k :=
    Finset.single_le_sum (fun p _ => Nat.zero_le (r p)) member
  have killed : (deltaEnd ^ r (i, j)) (commutator (A i) (A j)) = 0 := by
    simpa only [r, dite_eq_left hij] using Classical.choose_spec (locality i j hij)
  exact power_kills_of_le deltaEnd _ bound killed

/-- An arbitrary finite complete labelled word of mutually local actual fields
has a common, generally infinite, vector power series after polynomial clearing
and a statewise nonnegative monomial shift.

The order k is chosen before w. The tuple a comes only from truncation A_i on w.
The rectangle and common cleared product are conclusions. All signed regions,
including below support, and all permutations of distinct labels are covered.
Field values may repeat. For N=0 use order=[]; every construction is still total.
No polynomial inverse or cancellation on unrestricted distributions occurs. -/
theorem ungraded_local_word_common_series
    (A : Fin N → VertexOperator ℂ V) (order : List (Fin N))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (locality : ∀ i j : Fin N, i < j →
      ∃ r : ℕ, (deltaEnd ^ r) (commutator (A i) (A j)) = 0) :
    ∃ k : ℕ,
      (∀ i j : Fin N, i < j →
        (deltaEnd ^ k) (commutator (A i) (A j)) = 0) ∧
      ∀ w : V, ∃ a : Fin N → ℕ, ∃ P : MvPowerSeries (Fin N) V,
        (∀ (i : Fin N) (n : ℤ), (a i : ℤ) ≤ n → (A i [[n]]) w = 0) ∧
        ∀ (other : List (Fin N)), order.Perm other → ∀ e : Exponent N,
          polynomialAction (clearingPolynomial N k)
            (coefficientDistribution A w 1 other) (fun i => e i - a i) =
              signedExtend P e := by
  classical
  obtain ⟨k, hk⟩ := uniform_locality_order A locality
  refine ⟨k, hk, ?_⟩
  intro w
  let a : Fin N → ℕ := fun i =>
    (-((HahnModule.of ℂ).symm (A i w)).order).toNat
  have truncation : ∀ (i : Fin N) (n : ℤ),
      (a i : ℤ) ≤ n → (A i [[n]]) w = 0 := by
    intro i n hn
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    dsimp only [a] at hn
    omega
  let F : Distribution N V := polynomialAction (clearingPolynomial N k)
    (coefficientDistribution A w 1 order)
  obtain ⟨permutations, lower, _⟩ :=
    common_cleared_fields A w 1 (fun _ => k) hk order nodup all_labels
  have below (i : Fin N) (e : Exponent N) (he : e i < -(a i : ℤ)) : F e = 0 := by
    apply lower i e
    dsimp only [a] at he
    omega
  have equal (other : List (Fin N)) (hp : order.Perm other) :
      F = polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A w 1 other) :=
    permutations other hp
  let P : MvPowerSeries (Fin N) V := fun d => F (fun i => (d i : ℤ) - a i)
  refine ⟨a, P, truncation, ?_⟩
  · intro other hp e
    rw [← equal other hp]
    by_cases h : ∀ i, 0 ≤ e i
    · rw [signedExtend, ite_eq_left h]
      change F (fun i => e i - a i) =
        F (fun i => ((signedIndex e) i : ℤ) - a i)
      congr 1
      funext i
      simp [signedIndex, Int.toNat_of_nonneg (h i)]
    · rw [signedExtend, ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact below i _ (by change e i - (a i : ℤ) < -(a i : ℤ); omega)

#print axioms ungraded_local_word_common_series

end
end D5.S3.VertexAlgebra.UngradedLocalWordSeries
