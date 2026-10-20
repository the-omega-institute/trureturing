/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Centered row moments for singular positive semidefinite Schmidt tests. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
The row-moment mechanism uses actual positive semidefiniteness. It never
divides by the uniform quadratic form. The application from literal APPT to
the general-rank family of independently assigned Schmidt test matrices is
not asserted by these abstract structural statements.

proof_shape: centered_row_moment: content
proof_shape: centered_row_moment_of_nonpositive_offDiag: content
admission_basis: escape-witness
escape_witness: summing the coordinate Cauchy--Schwarz charges, and the
  absolute-value comparison followed by a singular-safe energy cancellation.
Private algebraic helpers are consumed by these estimates.
-/

set_option autoImplicit false

open Matrix Finset
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The actual row sum of the supplied matrix. -/
def rowSum (K : Matrix ι ι ℝ) (i : ι) : ℝ := ∑ j, K i j

/-- The uniform quadratic form, with no normalization. -/
def uniformCharge (K : Matrix ι ι ℝ) : ℝ := ∑ i, rowSum K i

/-- Square norm of the row-sum vector perpendicular to the uniform vector. -/
def centeredRowEnergy (K : Matrix ι ι ℝ) : ℝ :=
  ∑ i, (rowSum K i - uniformCharge K / Fintype.card ι) ^ 2

private theorem psd_cs {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (x y : ι → ℝ) :
    (x ⬝ᵥ (K *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (K *ᵥ x)) * (y ⬝ᵥ (K *ᵥ y)) := by
  classical
  let B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toLinearMap₂' ℝ K
  have hp : ∀ x, 0 ≤ B x x := by
    intro x
    simpa [B, Matrix.toLinearMap₂'_apply'] using hK.dotProduct_mulVec_nonneg x
  have hs : LinearMap.IsSymm B := by
    constructor
    intro x y
    simpa [B, Matrix.toLinearMap₂'_apply'] using
      hK.isHermitian.star_dotProduct_mulVec_comm x y
  simpa only [B, Matrix.toLinearMap₂'_apply'] using B.apply_sq_le_of_symm hp hs x y

private theorem centered_expansion (K : Matrix ι ι ℝ)
    (hc : (Fintype.card ι : ℝ) ≠ 0) :
    centeredRowEnergy K = (∑ i, (rowSum K i) ^ 2) -
      (uniformCharge K) ^ 2 / Fintype.card ι := by
  classical
  calc
    centeredRowEnergy K = ∑ i, ((rowSum K i)^2 -
        (2 * (uniformCharge K / Fintype.card ι)) * rowSum K i +
        (uniformCharge K / Fintype.card ι)^2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (rowSum K i)^2) -
        (2 * (uniformCharge K / Fintype.card ι)) * uniformCharge K +
        (Fintype.card ι : ℝ) * (uniformCharge K / Fintype.card ι)^2 := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul, uniformCharge]
    _ = _ := by field_simp; ring

private theorem row_square_le {K : Matrix ι ι ℝ} (hK : K.PosSemidef) (i : ι) :
    (rowSum K i) ^ 2 ≤ K i i * uniformCharge K := by
  classical
  simpa [rowSum, uniformCharge, dotProduct, mulVec, Pi.single_apply,
    Finset.sum_ite_irrel] using psd_cs hK (Pi.single i 1) (fun _ => 1)

/-- The trace branch of the centered PSD row moment. All singular matrices
and zero uniform charges remain in scope; only the dimension is nonzero. -/
theorem centered_row_moment [Nonempty ι] (K : Matrix ι ι ℝ) (hK : K.PosSemidef) :
    centeredRowEnergy K ≤ uniformCharge K *
      (K.trace - uniformCharge K / Fintype.card ι) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => row_square_le hK i)
  rw [← sum_mul] at hb
  rw [centered_expansion K hc]
  simp only [Matrix.trace, Matrix.diag_apply] at *
  calc
    _ ≤ (∑ i, K i i) * uniformCharge K -
        (uniformCharge K)^2 / Fintype.card ι := sub_le_sub_right hb _
    _ = _ := by ring

private theorem quadratic_upper_of_sign {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (hz : ∀ i j, i ≠ j → K i j ≤ 0) (c : ℝ)
    (hd : ∀ i, 2 * K i i ≤ c) (x : ι → ℝ) :
    x ⬝ᵥ (K *ᵥ x) ≤ c * ∑ i, (x i) ^ 2 := by
  classical
  have hp : 0 ≤ (fun i => |x i|) ⬝ᵥ (K *ᵥ (fun i => |x i|)) := by
    simpa using hK.dotProduct_mulVec_nonneg (fun i => |x i|)
  have hpoint (i j : ι) :
      x i * (K i j * x j) + |x i| * (K i j * |x j|) ≤
        if i = j then 2 * K i i * (x i) ^ 2 else 0 := by
    split_ifs with hij
    · subst j
      apply le_of_eq
      calc
        _ = K i i * ((x i)^2 + |x i|^2) := by ring
        _ = _ := by rw [sq_abs]; ring
    · have hh : 0 ≤ x i * x j + |x i| * |x j| := by
        rw [← abs_mul]
        linarith [neg_abs_le (x i * x j)]
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg (hz i j hij) hh]
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hpoint i j))
  simp only [sum_add_distrib] at hs
  have hd' := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (x i)))
  rw [← mul_sum] at hd'
  have hs' : x ⬝ᵥ (K *ᵥ x) +
      (fun i => |x i|) ⬝ᵥ (K *ᵥ (fun i => |x i|)) ≤
      ∑ i, 2 * K i i * (x i)^2 := by
    simpa only [dotProduct, mulVec, mul_sum, Fintype.sum_ite_eq] using hs
  linarith

private theorem square_energy_le {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (hu : ∀ x : ι → ℝ, x ⬝ᵥ (K *ᵥ x) ≤ c * ∑ i, (x i)^2)
    (x : ι → ℝ) :
    (∑ i, ((K *ᵥ x) i)^2) ≤ c * (x ⬝ᵥ (K *ᵥ x)) := by
  let E := ∑ i, ((K *ᵥ x) i)^2
  have he : 0 ≤ E := sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ x ⬝ᵥ (K *ᵥ x) := by simpa using hK.dotProduct_mulVec_nonneg x
  have hcs := psd_cs hK (K *ᵥ x) x
  have hm := mul_le_mul_of_nonneg_left (hu (K *ᵥ x)) hq
  have hd : (K *ᵥ x) ⬝ᵥ (K *ᵥ x) = E := by simp [dotProduct, E, pow_two]
  rw [hd] at hcs
  by_cases h : E = 0
  · change E ≤ _
    rw [h]
    exact mul_nonneg hc hq
  · have hep : 0 < E := lt_of_le_of_ne he (Ne.symm h)
    dsimp only [E] at *
    nlinarith [hcs, hm]

/-- The sign-sensitive centered row moment. If off-diagonal entries are
nonpositive and every diagonal is at most twice gamma, its spectral charge
is at most four gamma, without an inverse or a positive-definiteness premise. -/
theorem centered_row_moment_of_nonpositive_offDiag [Nonempty ι]
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (γ : ℝ)
    (hz : ∀ i j, i ≠ j → K i j ≤ 0) (hd : ∀ i, K i i ≤ 2 * γ) :
    centeredRowEnergy K ≤ 4 * γ * uniformCharge K -
      (uniformCharge K)^2 / Fintype.card ι := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : 0 ≤ 4 * γ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hp := hK.diag_nonneg (i := i)
    linarith [hd i]
  have hb := square_energy_le hK (4 * γ) hg
    (quadratic_upper_of_sign hK hz (4 * γ) (fun i => by linarith [hd i]))
    (fun _ => 1)
  have hb' : (∑ i, (rowSum K i)^2) ≤ 4 * γ * uniformCharge K := by
    simpa [rowSum, uniformCharge, dotProduct, mulVec] using hb
  rw [centered_expansion K hc]
  linarith [hb']

local instance : DecidableEq ι := Classical.decEq ι

/-- Uniform finite averaging, including all permutations rather than samples. -/
def permutationAverage (f : Equiv.Perm ι → ℝ) : ℝ :=
  (∑ π, f π) / Fintype.card (Equiv.Perm ι)

private theorem average_const (c : ℝ) :
    permutationAverage (fun _ : Equiv.Perm ι => c) = c := by
  have hc : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [permutationAverage, hc]

private theorem average_sum {κ : Type*} [Fintype κ] (f : κ → Equiv.Perm ι → ℝ) :
    permutationAverage (fun π => ∑ i, f i π) =
      ∑ i, permutationAverage (f i) := by
  unfold permutationAverage
  rw [sum_comm, sum_div]

private theorem average_mul (c : ℝ) (f : Equiv.Perm ι → ℝ) :
    permutationAverage (fun π => c * f π) = c * permutationAverage f := by
  simp [permutationAverage, ← mul_sum, mul_div_assoc]

private theorem average_right (f : Equiv.Perm ι → ℝ) (σ : Equiv.Perm ι) :
    permutationAverage (fun π => f (π * σ)) = permutationAverage f := by
  unfold permutationAverage
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ) f

private theorem average_slot (f : ℝ → ℝ) (z : ι → ℝ) (i j : ι) :
    permutationAverage (fun π => f (z (π i))) =
      permutationAverage (fun π => f (z (π j))) := by
  classical
  have h := average_right (fun π => f (z (π i))) (Equiv.swap i j)
  simpa using h.symm

private theorem average_slot_formula (f : ℝ → ℝ) (z : ι → ℝ) (i : ι) :
    (Fintype.card ι : ℝ) * permutationAverage (fun π => f (z (π i))) =
      ∑ j, f (z j) := by
  calc
    _ = ∑ j : ι, permutationAverage (fun π => f (z (π j))) := by
      simp_rw [average_slot f z _ i]
      simp
    _ = permutationAverage (fun π => ∑ j, f (z (π j))) := (average_sum _).symm
    _ = permutationAverage (fun _ : Equiv.Perm ι => ∑ j, f (z j)) := by
      congr 1
      funext π
      exact Equiv.sum_comp π (fun j => f (z j))
    _ = _ := average_const _

omit [Fintype ι] in
private theorem pair_injective (i j : ι) (hij : i ≠ j) :
    Function.Injective (fun b : Bool => if b then i else j) := by
  intro a b h
  cases a <;> cases b <;> simp_all

private theorem average_pair (z : ι → ℝ) (i j a b : ι)
    (hij : i ≠ j) (hab : a ≠ b) :
    permutationAverage (fun π => z (π i) * z (π j)) =
      permutationAverage (fun π => z (π a) * z (π b)) := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun t : Bool => if t then i else j) (fun t : Bool => if t then a else b)
    (pair_injective i j hij) (pair_injective a b hab)
  have hi : σ i = a := by simpa using hσ true
  have hj : σ j = b := by simpa using hσ false
  have h := average_right (fun π => z (π i) * z (π j)) σ
  simpa only [Equiv.Perm.mul_apply, hi, hj] using h.symm

private theorem average_pair_formula (z : ι → ℝ) (hz : ∑ i, z i = 0)
    (i j : ι) (hij : i ≠ j) :
    (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) *
      permutationAverage (fun π => z (π i) * z (π j)) = -∑ k, (z k)^2 := by
  classical
  let D := permutationAverage (fun π => (z (π i))^2)
  let C := permutationAverage (fun π => z (π i) * z (π j))
  have hzero : permutationAverage (fun π => ∑ k, z (π i) * z (π k)) = 0 := by
    have h (π : Equiv.Perm ι) : ∑ k, z (π i) * z (π k) = 0 := by
      rw [← mul_sum, Equiv.sum_comp π z, hz, mul_zero]
    simp_rw [h]
    exact average_const 0
  rw [average_sum] at hzero
  have hs : ∑ k, permutationAverage (fun π => z (π i) * z (π k)) =
      D + ((Fintype.card ι : ℝ) - 1) * C := by
    calc
      _ = ∑ k : ι, if k = i then D else C := by
        apply sum_congr rfl
        intro k _
        split_ifs with hki
        · subst k; simp [D, pow_two]
        · exact average_pair z i k i j (Ne.symm hki) hij
      _ = ∑ k : ι, (C + if k = i then D - C else 0) := by
        apply sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = _ := by
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
          sum_ite_eq', mem_univ, ite_true]
        ring
  have hd := average_slot_formula (fun x : ℝ => x^2) z i
  dsimp only [D, C] at hs
  rw [hs] at hzero
  nlinarith [hd]

/-- The exact second moment of a weighted uniformly permuted centered pool.
The cardinality condition excludes the singleton denominator; it imposes no
strict positivity, distinctness, or nonzero-variance condition on the pool. -/
theorem permutation_weighted_second_moment (z w : ι → ℝ)
    (hk : 2 ≤ Fintype.card ι) (hz : ∑ i, z i = 0) :
    permutationAverage (fun π => (∑ i, w i * z (π i))^2) =
      (∑ i, (z i)^2) /
        ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) *
        ((Fintype.card ι : ℝ) * (∑ i, (w i)^2) - (∑ i, w i)^2) := by
  classical
  have hk0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have hk1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    linarith
  let V : ℝ := ∑ i, (z i)^2
  have hdiag (i : ι) : permutationAverage (fun π => (z (π i))^2) =
      V / Fintype.card ι := by
    apply (eq_div_iff hk0).mpr
    simpa [V, mul_comm] using average_slot_formula (fun x : ℝ => x^2) z i
  have hoff (i j : ι) (hij : i ≠ j) :
      permutationAverage (fun π => z (π i) * z (π j)) =
        -V / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
    apply (eq_div_iff (mul_ne_zero hk0 hk1)).mpr
    simpa [V, mul_comm] using average_pair_formula z hz i j hij
  have hexpand (π : Equiv.Perm ι) : (∑ i, w i * z (π i))^2 =
      ∑ i, ∑ j, (w i * w j) * (z (π i) * z (π j)) := by
    simp only [pow_two, sum_mul, mul_sum]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    ring
  simp_rw [hexpand, average_sum, average_mul]
  have hcov (i j : ι) : permutationAverage (fun π => z (π i) * z (π j)) =
      (if i = j then V / ((Fintype.card ι : ℝ) - 1) else 0) -
        V / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
    split_ifs with hij
    · subst j
      simp only [← pow_two, hdiag]
      field_simp
    · rw [hoff i j hij]
      ring
  simp_rw [hcov, mul_sub, mul_ite, mul_zero, sum_sub_distrib]
  simp only [sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul]
  dsimp only [V]
  field_simp

/-!
The next layer isolates the finite assignment calculation used by the
general-r APPT moment.  `K` is deliberately supplied as a family of actual
real matrices; the hypotheses describe its row-sum and trace bookkeeping,
while `hK` and the sign hypotheses are the PSD facts that the literal product
corner must still provide.  Thus this theorem is a reusable assignment
engine, not an APPT surrogate: the product-corner/unitary realization is an
explicit downstream obligation.
-/

private theorem average_add {f g : Equiv.Perm ι → ℝ} :
    permutationAverage (fun π => f π + g π) =
      permutationAverage f + permutationAverage g := by
  simp [permutationAverage, sum_add_distrib, add_div]

private theorem average_sub {f g : Equiv.Perm ι → ℝ} :
    permutationAverage (fun π => f π - g π) =
      permutationAverage f - permutationAverage g := by
  simp [permutationAverage, Finset.sum_sub_distrib, sub_div]

private theorem centered_weighted_average [Nonempty ι] (z w : ι → ℝ)
    (hz : ∑ i, z i = 0) :
    permutationAverage (fun π => ∑ i, w i * z (π i)) = 0 := by
  rw [average_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [average_mul]
  have hslot := average_slot_formula (fun x : ℝ => x) z i
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hzavg : permutationAverage (fun π => z (π i)) = 0 := by
    apply (mul_left_cancel₀ hc)
    calc
      (Fintype.card ι : ℝ) * permutationAverage (fun π => z (π i)) =
          ∑ j, z j := hslot
      _ = (Fintype.card ι : ℝ) * 0 := by simp [hz]
  rw [hzavg]
  ring

private theorem double_centered_weighted_second_moment
    [Nonempty ι] {κ : Type*} [Fintype κ] [Nonempty κ]
    (z : ι → ℝ) (u : κ → ℝ)
    (w : ι → ℝ) (v : κ → ℝ)
    (hz : ∑ i, z i = 0) (hu : ∑ i, u i = 0)
    (hkι : 2 ≤ Fintype.card ι) (hkκ : 2 ≤ Fintype.card κ) :
    permutationAverage (fun π =>
      permutationAverage (fun σ =>
        (∑ i, w i * z (π i) + ∑ j, v j * u (σ j)) ^ 2)) =
      permutationAverage (fun π => (∑ i, w i * z (π i)) ^ 2) +
      permutationAverage (fun σ => (∑ j, v j * u (σ j)) ^ 2) := by
  let X : Equiv.Perm ι → ℝ := fun π => ∑ i, w i * z (π i)
  let Y : Equiv.Perm κ → ℝ := fun σ => ∑ j, v j * u (σ j)
  have hX : permutationAverage X = 0 := by
    exact centered_weighted_average z w hz
  have hY : permutationAverage Y = 0 := by
    exact centered_weighted_average u v hu
  have hinner (π : Equiv.Perm ι) :
      permutationAverage (fun σ => (X π + Y σ)^2) =
        (X π)^2 + permutationAverage (fun σ => (Y σ)^2) := by
    rw [show (fun σ => (X π + Y σ)^2) =
      (fun σ => (X π)^2 + 2 * X π * Y σ + (Y σ)^2) by
        funext σ; ring]
    rw [average_add, average_add, average_mul]
    rw [average_const, hY]
    ring
  change permutationAverage (fun π =>
      permutationAverage (fun σ => (X π + Y σ)^2)) =
    permutationAverage (fun π => (X π)^2) +
      permutationAverage (fun σ => (Y σ)^2)
  simp_rw [hinner]
  rw [average_add, average_const]

private theorem permutationAverage_mono {f g : Equiv.Perm ι → ℝ}
    (h : ∀ π, f π ≤ g π) : permutationAverage f ≤ permutationAverage g := by
  unfold permutationAverage
  apply div_le_div_of_nonneg_right
  · exact sum_le_sum (fun π _ => h π)
  · positivity

theorem general_r_assignment_moment
    {r a b : ℕ} (hr : 3 ≤ r) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (top : Fin a → ℝ) (bottom : Fin b → ℝ)
    (K : Equiv.Perm (Fin a) → Equiv.Perm (Fin b) → Matrix (Fin r) (Fin r) ℝ)
    (topWeight : Fin r → Fin a → ℝ)
    (bottomWeight : Fin r → Fin b → ℝ)
    (diagSlot : Fin r → Fin b) (s γ : ℝ)
    (hacard : (a : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2)
    (hbcard : (b : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2)
    (hA : 0 < (a : ℝ)) (hB : 0 < (b : ℝ))
    (ha1 : (a : ℝ) - 1 ≠ 0) (hb1 : (b : ℝ) - 1 ≠ 0)
    (hTopFactor : ∀ i,
      ((a : ℝ) * ∑ k, (topWeight i k)^2 - (∑ k, topWeight i k)^2) /
          ((a : ℝ) * ((a : ℝ) - 1)) =
        2 * (r - 1 : ℝ) / ((r : ℝ) * ((r : ℝ) + 1)))
    (hBottomFactor : ∀ i,
      ((b : ℝ) * ∑ k, (bottomWeight i k)^2 - (∑ k, bottomWeight i k)^2) /
          ((b : ℝ) * ((b : ℝ) - 1)) = 2 / (r : ℝ))
    (hTopSum : ∀ i, ∑ k, topWeight i k = -(r - 1 : ℝ))
    (hBottomSum : ∀ i, ∑ k, bottomWeight i k = (r + 1 : ℝ))
    (hrow : ∀ π σ i,
      rowSum (K π σ) i =
        (∑ k, topWeight i k * top (π k)) +
        (∑ k, bottomWeight i k * bottom (σ k)))
    (hcharge : ∀ π σ, uniformCharge (K π σ) = 2 * s)
    (htrace : ∀ π σ, Matrix.trace (K π σ) =
      2 * ∑ i, bottom (σ (diagSlot i)))
    (hK : ∀ π σ, (K π σ).PosSemidef)
    (hoff : ∀ π σ i j, i ≠ j → K π σ i j ≤ 0)
    (hdiag : ∀ π σ i, K π σ i i ≤ 2 * γ)
    (hs : ∑ i, bottom i - ∑ i, top i = s)
    (hmean0 :
      -(r - 1 : ℝ) * ((∑ i, top i) / (a : ℝ)) +
        (r + 1 : ℝ) * ((∑ i, bottom i) / (b : ℝ)) = 2 * s / (r : ℝ)) :
    ((r - 1 : ℝ) / ((r : ℝ) + 1)) *
          (∑ i, (top i - (∑ j, top j) / (a : ℝ))^2) +
        (∑ i, (bottom i - (∑ j, bottom j) / (b : ℝ))^2) ≤
      4 * s * min ((∑ i, bottom i) / ((r : ℝ) + 1)) γ -
        2 * s^2 / (r : ℝ) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin a) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt hA
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt hB
  let α : ℝ := (∑ i, top i) / (a : ℝ)
  let β : ℝ := (∑ i, bottom i) / (b : ℝ)
  let VT : ℝ := ∑ i, (top i - α)^2
  let VB : ℝ := ∑ i, (bottom i - β)^2
  have hztop : ∑ i, (top i - α) = 0 := by
    simp only [α, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hzbottom : ∑ i, (bottom i - β) = 0 := by
    simp only [β, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hmean : -(r - 1 : ℝ) * α + (r + 1 : ℝ) * β = 2 * s / (r : ℝ) := by
    simpa [α, β] using hmean0
  have htopavg (i : Fin r) :
      permutationAverage (fun π =>
        (∑ k, topWeight i k * (top (π k) - α))^2) =
        (2 * (r - 1 : ℝ) / ((r : ℝ) * ((r : ℝ) + 1))) * VT := by
    have h := permutation_weighted_second_moment
      (fun k : Fin a => top k - α) (topWeight i) (by simpa using ha2)
        (by simpa using hztop)
    calc
      _ = VT / ((a : ℝ) * ((a : ℝ) - 1)) *
          ((a : ℝ) * ∑ k, (topWeight i k)^2 - (∑ k, topWeight i k)^2) := by
            simpa [VT, α, Fintype.card_fin] using h
      _ = (2 * (r - 1 : ℝ) / ((r : ℝ) * ((r : ℝ) + 1))) * VT := by
        rw [← hTopFactor i]
        ring
  have hbotavg (i : Fin r) :
      permutationAverage (fun σ =>
        (∑ k, bottomWeight i k * (bottom (σ k) - β))^2) =
        (2 / (r : ℝ)) * VB := by
    have h := permutation_weighted_second_moment
      (fun k : Fin b => bottom k - β) (bottomWeight i) (by simpa using hb2)
        (by simpa using hzbottom)
    calc
      _ = VB / ((b : ℝ) * ((b : ℝ) - 1)) *
          ((b : ℝ) * ∑ k, (bottomWeight i k)^2 - (∑ k, bottomWeight i k)^2) := by
            simpa [VB, β, Fintype.card_fin] using h
      _ = (2 / (r : ℝ)) * VB := by
        rw [← hBottomFactor i]
        ring
  have hrowavg :
      permutationAverage (fun π => permutationAverage (fun σ =>
        centeredRowEnergy (K π σ))) =
      (2 * (r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + 2 * VB := by
    have hpoint (π : Equiv.Perm (Fin a)) (σ : Equiv.Perm (Fin b)) (i : Fin r) :
        rowSum (K π σ) i - 2 * s / (r : ℝ) =
          (∑ k, topWeight i k * (top (π k) - α)) +
          (∑ k, bottomWeight i k * (bottom (σ k) - β)) := by
      rw [hrow π σ i, ← hmean]
      calc
        (∑ k, topWeight i k * top (π k) +
              ∑ k, bottomWeight i k * bottom (σ k)) -
            (-(r - 1 : ℝ) * α + (r + 1 : ℝ) * β) =
          ((∑ k, topWeight i k * top (π k)) -
              (∑ k, topWeight i k) * α) +
            ((∑ k, bottomWeight i k * bottom (σ k)) -
              (∑ k, bottomWeight i k) * β) := by
                rw [hTopSum i, hBottomSum i]
                ring
        _ = (∑ k, topWeight i k * (top (π k) - α)) +
            (∑ k, bottomWeight i k * (bottom (σ k) - β)) := by
              simp only [mul_sub, sum_sub_distrib, sum_mul]
    have henergy (π : Equiv.Perm (Fin a)) (σ : Equiv.Perm (Fin b)) :
        centeredRowEnergy (K π σ) =
          ∑ i, (rowSum (K π σ) i - 2 * s / (r : ℝ))^2 := by
      simp [centeredRowEnergy, hcharge π σ, Fintype.card_fin]
    simp_rw [henergy, hpoint]
    let F : Fin r → Equiv.Perm (Fin a) → Equiv.Perm (Fin b) → ℝ := fun i π σ =>
      ((∑ k, topWeight i k * (top (π k) - α)) +
        (∑ k, bottomWeight i k * (bottom (σ k) - β))) ^ 2
    change permutationAverage (fun π => permutationAverage (fun σ => ∑ i, F i π σ)) = _
    have hsum (π : Equiv.Perm (Fin a)) :
        permutationAverage (fun σ => ∑ i, F i π σ) =
          ∑ i, permutationAverage (fun σ => F i π σ) := average_sum _
    rw [show permutationAverage (fun π => permutationAverage (fun σ => ∑ i, F i π σ)) =
        permutationAverage (fun π => ∑ i, permutationAverage (fun σ => F i π σ)) by
          congr 1; funext π; exact hsum π]
    rw [average_sum]
    have hF (i : Fin r) :
        permutationAverage (fun π => permutationAverage (fun σ => F i π σ)) =
          permutationAverage (fun π =>
            (∑ k, topWeight i k * (top (π k) - α))^2) +
          permutationAverage (fun σ =>
            (∑ k, bottomWeight i k * (bottom (σ k) - β))^2) := by
      simpa [F] using
        (double_centered_weighted_second_moment
          (z := fun k : Fin a => top k - α)
          (u := fun k : Fin b => bottom k - β)
          (w := topWeight i) (v := bottomWeight i)
          hztop hzbottom (by simpa using ha2) (by simpa using hb2))
    simp_rw [hF]
    simp_rw [htopavg, hbotavg]
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hr0, hr1]
  have htraceavg :
      permutationAverage (fun π => permutationAverage (fun σ => Matrix.trace (K π σ))) =
        2 * (r : ℝ) * ((∑ i, bottom i) / (b : ℝ)) := by
    have hcardb : (Fintype.card (Fin b) : ℝ) ≠ 0 := by
      simpa [Fintype.card_fin] using (show (b : ℝ) ≠ 0 by exact_mod_cast (show b ≠ 0 by omega))
    have hslot (i : Fin r) :
        permutationAverage (fun σ => bottom (σ (diagSlot i))) =
          (∑ j, bottom j) / (b : ℝ) := by
      apply (eq_div_iff (by simpa [Fintype.card_fin] using hcardb)).mpr
      simpa [Fintype.card_fin, mul_comm] using
        (average_slot_formula (fun x : ℝ => x) bottom (diagSlot i))
    have hinner (π : Equiv.Perm (Fin a)) :
        permutationAverage (fun σ => Matrix.trace (K π σ)) =
        2 * ∑ _i : Fin r, ((∑ j, bottom j) / (b : ℝ)) := by
      simp_rw [htrace, average_mul, average_sum, hslot]
    simp_rw [hinner, average_const]
    simp [Fintype.card_fin]
    ring
  have hbase :
      (2 * (r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + 2 * VB ≤
        2 * s * (2 * (r : ℝ) * ((∑ i, bottom i) / (b : ℝ)) - 2 * s / (r : ℝ)) := by
    have hineq (π : Equiv.Perm (Fin a)) (σ : Equiv.Perm (Fin b)) :
        centeredRowEnergy (K π σ) ≤
          2 * s * (Matrix.trace (K π σ) - 2 * s / (r : ℝ)) := by
      simpa [hcharge π σ, Fintype.card_fin] using
        centered_row_moment (K π σ) (hK π σ)
    have havgσ (π : Equiv.Perm (Fin a)) :=
      permutationAverage_mono (fun σ => hineq π σ)
    have havg := permutationAverage_mono havgσ
    have hRavg :
        permutationAverage (fun π => permutationAverage (fun σ =>
          2 * s * (Matrix.trace (K π σ) - 2 * s / (r : ℝ)))) =
          2 * s * (2 * (r : ℝ) * ((∑ i, bottom i) / (b : ℝ)) -
            2 * s / (r : ℝ)) := by
      simp_rw [average_mul, average_sub, htraceavg, average_const]
    rw [hrowavg, hRavg] at havg
    exact havg
  have hsign :
      (2 * (r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + 2 * VB ≤
        8 * γ * s - 4 * s^2 / (r : ℝ) := by
    have hineq (π : Equiv.Perm (Fin a)) (σ : Equiv.Perm (Fin b)) :
        centeredRowEnergy (K π σ) ≤
          4 * γ * (2 * s) - (2 * s)^2 / (r : ℝ) := by
      simpa [hcharge π σ, Fintype.card_fin] using
        centered_row_moment_of_nonpositive_offDiag (K π σ) (hK π σ) γ
          (hoff π σ) (hdiag π σ)
    have havgσ (π : Equiv.Perm (Fin a)) :=
      permutationAverage_mono (fun σ => hineq π σ)
    have havg := permutationAverage_mono havgσ
    have hRconst :
        permutationAverage (fun _π : Equiv.Perm (Fin a) =>
          permutationAverage (fun _σ : Equiv.Perm (Fin b) =>
          4 * γ * (2 * s) - (2 * s)^2 / (r : ℝ))) =
          8 * γ * s - 4 * s^2 / (r : ℝ) := by
      simp [average_const, pow_two]
      ring
    rw [hrowavg, hRconst] at havg
    exact havg
  have htracefactor :
      2 * (r : ℝ) * ((∑ i, bottom i) / (b : ℝ)) =
        4 * (∑ i, bottom i) / ((r : ℝ) + 1) := by
    rw [hbcard]
    field_simp [hr0, hr1]
    ring
  have hbase' :
      ((r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + VB ≤
        4 * s * ((∑ i, bottom i) / ((r : ℝ) + 1)) - 2 * s^2 / (r : ℝ) := by
    calc
      ((r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + VB =
          (1 / 2 : ℝ) *
            ((2 * (r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + 2 * VB) := by ring
      _ ≤ (1 / 2 : ℝ) *
          (2 * s * (2 * (r : ℝ) * ((∑ i, bottom i) / (b : ℝ)) -
            2 * s / (r : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = 4 * s * ((∑ i, bottom i) / ((r : ℝ) + 1)) -
          2 * s^2 / (r : ℝ) := by
            rw [htracefactor]
            ring
  have hsign' :
      ((r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + VB ≤
        4 * s * γ - 2 * s^2 / (r : ℝ) := by
    calc
      ((r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + VB =
          (1 / 2 : ℝ) *
            ((2 * (r - 1 : ℝ) / ((r : ℝ) + 1)) * VT + 2 * VB) := by ring
      _ ≤ (1 / 2 : ℝ) * (8 * γ * s - 4 * s^2 / (r : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsign (by norm_num)
      _ = 4 * s * γ - 2 * s^2 / (r : ℝ) := by ring
  have hs0 : 0 ≤ s := by
    have hq := (hK (Equiv.refl _) (Equiv.refl _)).dotProduct_mulVec_nonneg
      (fun _ : Fin r => 1)
    have hq' : 0 ≤ uniformCharge (K (Equiv.refl _) (Equiv.refl _)) := by
      simpa [uniformCharge, rowSum, dotProduct, mulVec] using hq
    rw [hcharge] at hq'
    linarith
  have hmin :
      min (4 * s * ((∑ i, bottom i) / ((r : ℝ) + 1)) - 2 * s^2 / (r : ℝ))
          (4 * s * γ - 2 * s^2 / (r : ℝ)) =
        4 * s * min ((∑ i, bottom i) / ((r : ℝ) + 1)) γ -
          2 * s^2 / (r : ℝ) := by
    rw [min_sub_sub_right]
    rw [← mul_min_of_nonneg _ _ (by positivity : 0 ≤ 4 * s)]
  rw [← hmin]
  exact le_min hbase' hsign'

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtDefectMoment
