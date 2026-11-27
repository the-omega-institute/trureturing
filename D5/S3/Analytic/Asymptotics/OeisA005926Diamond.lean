/- GID: D5/S3/Analytic/Asymptotics/OeisA005926Diamond
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/OeisA005926Diamond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: The OEIS A005926 diamond theta coefficient sum has normalized limit π/48. -/

module

public import D5.S3.Arith.Lattices.Counting.ShiftedBallCount
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import OmegaBuild.Commands

/-! The diamond theta series is given in N. J. A. Sloane, *Theta series and magic
numbers for diamond and certain ionic crystal structures*, J. Math. Phys. 28 (1987),
1653–1657, DOI 10.1063/1.527472. OEIS A005926 attributes the summatory conjecture to
Vaclav Kotesovec (November 26, 2026). -/

compile_only_with_mathlib

@[expose] public section

namespace D5.S3.Analytic.Asymptotics.OeisA005926Diamond

open D5.S3.Arith.Lattices.Counting.ShiftedBallCount Filter Set Metric MeasureTheory
open scoped BigOperators Topology Pointwise

private def toIndex (z : ℤ) : ℕ := (if 0 ≤ z then 2*z else -2*z-1).toNat

private theorem toIndex_cast (z : ℤ) :
    (toIndex z : ℤ) = if 0 ≤ z then 2*z else -2*z-1 := by
  unfold toIndex
  split <;> rw [Int.toNat_of_nonneg (by omega)]

private def fromIndex (j : ℕ) : ℤ := if j % 2 = 0 then (j : ℤ) / 2 else -((j : ℤ) + 1) / 2

private def indexEquiv : ℤ ≃ ℕ where
  toFun := toIndex
  invFun := fromIndex
  left_inv z := by
    have h := toIndex_cast z
    unfold fromIndex
    split at h <;> split <;> omega
  right_inv j := by
    have h := toIndex_cast (fromIndex j)
    apply Int.ofNat_inj.mp
    unfold fromIndex at h ⊢
    by_cases hj : j % 2 = 0 <;> simp only [hj, ite_true, ite_false] at h ⊢ <;>
      split at h <;> omega

def triangular (j : ℕ) : ℕ := j*(j+1)/2

private theorem triangular_cast_double (j : ℕ) :
    2 * (triangular j : ℤ) = (j : ℤ) * ((j : ℤ) + 1) := by
  unfold triangular
  have h : j * (j+1) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.add_mod j 1 2]
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  have h' : 2 * (j * (j+1) / 2) = j*(j+1) := by omega
  exact_mod_cast h'

private theorem triangular_index (z : ℤ) :
    (triangular (indexEquiv z) : ℤ) = 2*z^2+z := by
  have h := triangular_cast_double (toIndex z)
  rw [toIndex_cast] at h
  change (triangular (toIndex z) : ℤ) = _
  split at h <;> nlinarith

private def tripleEnergy (j : Fin 3 → ℕ) : ℕ := ∑ i, triangular (j i)
def squareEnergy (z : Fin 3 → ℤ) : ℤ := ∑ i, (4*z i+1)^2
private def sourceShell (n : ℕ) :=
  {j : Fin 3 → ℕ // 3 + 8 * tripleEnergy j = n ∧ tripleEnergy j % 2 = 0}
def latticeShell (n : ℕ) :=
  {z : Fin 3 → ℤ // squareEnergy z = (n : ℤ) ∧ (∑ i, z i) % 2 = 0}

private theorem bridge (z : Fin 3 → ℤ) :
    (3 + 8 * (tripleEnergy (fun i => indexEquiv (z i)) : ℤ)) = squareEnergy z ∧
    (tripleEnergy (fun i => indexEquiv (z i)) : ℤ) % 2 = (∑ i, z i) % 2 := by
  simp only [tripleEnergy, squareEnergy, Fin.sum_univ_three, Nat.cast_add, triangular_index]
  constructor
  · ring
  · omega

private def shellEquiv (n : ℕ) : latticeShell n ≃ sourceShell n :=
  (Equiv.piCongrRight fun _ : Fin 3 => indexEquiv).subtypeEquiv fun z => by
    have h := bridge z
    change (squareEnergy z = (n : ℤ) ∧ (∑ i, z i) % 2 = 0) ↔
      (3 + 8 * tripleEnergy (fun i => indexEquiv (z i)) = n ∧
        tripleEnergy (fun i => indexEquiv (z i)) % 2 = 0)
    rw [← h.1, ← h.2]
    constructor
    · rintro ⟨hE, hP⟩
      exact ⟨by exact_mod_cast hE, by exact_mod_cast hP⟩
    · rintro ⟨hE, hP⟩
      exact ⟨by exact_mod_cast hE, by exact_mod_cast hP⟩

private noncomputable def a005926 (n : ℕ) : ℕ := 2 * Nat.card (sourceShell n)
private noncomputable def sourcePrefix (N : ℕ) : ℕ := ∑ n ∈ Finset.range (N+1), a005926 n

private theorem a005926_eq_lattice (n : ℕ) : a005926 n = 2 * Nat.card (latticeShell n) := by
  rw [a005926, Nat.card_congr (shellEquiv n)]

private theorem a005926_small (n : ℕ) (hn : n < 3) : a005926 n = 0 := by
  have : IsEmpty (sourceShell n) := ⟨fun j => by have h := j.2.1; omega⟩
  simp [a005926, Nat.card_of_isEmpty]

private theorem index_le_triangular (j : ℕ) : j ≤ triangular j := by
  have h := triangular_cast_double j
  have hj : j = 0 ∨ 1 ≤ j := by omega
  rcases hj with rfl | hj
  · decide
  · have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have hh := mul_nonneg (show (0 : ℤ) ≤ j by positivity) (sub_nonneg.mpr hj')
    exact_mod_cast (show (j : ℤ) ≤ triangular j by nlinarith)

private theorem sourceBound {j : Fin 3 → ℕ} {N : ℕ} (h : 3 + 8 * tripleEnergy j ≤ N) (i : Fin 3) :
    j i ≤ N := by
  have hi : triangular (j i) ≤ tripleEnergy j :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (triangular (j k))) (Finset.mem_univ i)
  have hj := index_le_triangular (j i)
  omega

private instance sourceFinite (n : ℕ) : Finite (sourceShell n) :=
  Finite.of_injective
    (fun j (i : Fin 3) => (⟨j.1 i, Nat.lt_succ_of_le (sourceBound j.2.1.le i)⟩ : Fin (n + 1)))
    (fun _ _ h => Subtype.ext (funext fun i => congrArg Fin.val (congrFun h i)))

private def sourceCut (N : ℕ) :=
  {j : Fin 3 → ℕ // 3 + 8 * tripleEnergy j ≤ N ∧ tripleEnergy j % 2 = 0}
def latticeCut (N : ℕ) := {z : Fin 3 → ℤ // squareEnergy z ≤ (N : ℤ) ∧ (∑ i, z i) % 2 = 0}

private def cutEquiv (N : ℕ) : latticeCut N ≃ sourceCut N :=
  (Equiv.piCongrRight fun _ : Fin 3 => indexEquiv).subtypeEquiv fun z => by
    have h := bridge z
    change (squareEnergy z ≤ (N : ℤ) ∧ (∑ i, z i) % 2 = 0) ↔
      (3 + 8 * tripleEnergy (fun i => indexEquiv (z i)) ≤ N ∧
        tripleEnergy (fun i => indexEquiv (z i)) % 2 = 0)
    rw [← h.1, ← h.2]
    constructor
    · rintro ⟨hE, hP⟩
      exact ⟨by exact_mod_cast hE, by exact_mod_cast hP⟩
    · rintro ⟨hE, hP⟩
      exact ⟨by exact_mod_cast hE, by exact_mod_cast hP⟩

private def cutSigma (N : ℕ) : sourceCut N ≃ (Σ n : Fin (N+1), sourceShell n) where
  toFun j := ⟨⟨3 + 8 * tripleEnergy j.1, Nat.lt_succ_of_le j.2.1⟩, ⟨j.1, rfl, j.2.2⟩⟩
  invFun a := ⟨a.2.1, a.2.2.1.le.trans (Nat.le_of_lt_succ a.1.isLt), a.2.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨n, hn⟩, ⟨j, hj, hp⟩⟩
    dsimp at hj
    subst n
    rfl

private theorem prefix_eq_cut (N : ℕ) : sourcePrefix N = 2 * Nat.card (latticeCut N) := by
  rw [Nat.card_congr (cutEquiv N), Nat.card_congr (cutSigma N), Nat.card_sigma]
  simp only [sourcePrefix, a005926, Finset.mul_sum]
  exact (Fin.sum_univ_eq_sum_range (fun n => 2 * Nat.card (sourceShell n)) _).symm

private abbrev IndexBox (n : ℕ) := Fin 3 → Fin (n+1)
private def boxEnergy {n : ℕ} (j : IndexBox n) := tripleEnergy (fun i => (j i).val)

private noncomputable def groupedCoefficient (n : ℕ) : ℤ :=
  ∑ j : IndexBox n, if 3 + 8 * boxEnergy j = n then 1 + (-1 : ℤ) ^ boxEnergy j else 0

private theorem signWeight (s : ℕ) : 1 + (-1 : ℤ)^s = if s % 2 = 0 then 2 else 0 := by
  rw [neg_one_pow_eq_pow_mod_two]
  have h : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

private def shellBoxEquiv (n : ℕ) : sourceShell n ≃
    {j : IndexBox n // 3 + 8 * boxEnergy j = n ∧ boxEnergy j % 2 = 0} where
  toFun j := ⟨fun i => ⟨j.1 i, Nat.lt_succ_of_le (sourceBound j.2.1.le i)⟩, j.2⟩
  invFun j := ⟨fun i => (j.1 i).val, j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem groupedCoefficient_eq_a005926 (n : ℕ) : groupedCoefficient n = (a005926 n : ℤ) := by
  classical
  simp only [groupedCoefficient, signWeight, ← ite_and, a005926, Nat.cast_mul, Nat.cast_ofNat]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  apply congrArg (Int.ofNat)
  rw [Nat.card_congr (shellBoxEquiv n), Nat.card_eq_fintype_card, Fintype.card_subtype]

open PowerSeries

/-- Ramanujan's ψ series, with one monomial in each triangular degree. -/
noncomputable def psi : PowerSeries ℤ := by
  classical
  exact PowerSeries.mk fun n => if ∃ j, triangular j = n then 1 else 0

/-- Substitute a times the eighth power of the variable. -/
noncomputable def substitute (a : ℤ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.expand 8 (by decide) (PowerSeries.rescale a f)

/-- The diamond generating function X³(ψ(X⁸)³ + ψ(−X⁸)³). -/
noncomputable def thetaSeries : PowerSeries ℤ :=
  X ^ 3 * (substitute 1 psi ^ 3 + substitute (-1) psi ^ 3)

/-- The literal coefficient of degree n in the diamond generating function. -/
noncomputable def thetaCoefficient (n : ℕ) : ℤ := PowerSeries.coeff n thetaSeries

private theorem triangular_injective : Function.Injective triangular := by
  intro i j hij
  have h := triangular_cast_double i
  rw [hij, triangular_cast_double] at h
  have hprod : ((i : ℤ) - j) * ((i : ℤ) + j + 1) = 0 := by
    calc
      _ = (i : ℤ) * ((i : ℤ) + 1) - (j : ℤ) * ((j : ℤ) + 1) := by ring
      _ = 0 := sub_eq_zero.mpr h.symm
  rcases mul_eq_zero.mp hprod with he | he <;> omega

private noncomputable def psiTrunc (N : ℕ) : PowerSeries ℤ :=
  ∑ j : Fin (N + 1), monomial (triangular j) 1

private theorem coeff_psiTrunc (N m : ℕ) (hm : m ≤ N) :
    PowerSeries.coeff m (psiTrunc N) = PowerSeries.coeff m psi := by
  classical
  rw [psiTrunc, map_sum, psi, coeff_mk]
  simp only [coeff_monomial]
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    let k : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le ((index_le_triangular j).trans (hj ▸ hm))⟩
    rw [Finset.sum_eq_single k]
    · simp [k, hj]
    · intro i _ hi
      apply ite_eq_right
      intro he
      exact hi (Fin.ext (triangular_injective (he.symm.trans hj.symm)))
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => h ⟨i, hi.symm⟩)

private theorem coeff_mul_congr_through {f g f' g' : PowerSeries ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, PowerSeries.coeff m f = PowerSeries.coeff m f')
    (hg : ∀ m ≤ N, PowerSeries.coeff m g = PowerSeries.coeff m g') :
    ∀ m ≤ N, PowerSeries.coeff m (f * g) = PowerSeries.coeff m (f' * g') := by
  intro m hm
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  rw [hf _ ((Nat.le_add_right _ _).trans (hsum ▸ hm)),
    hg _ ((Nat.le_add_left _ _).trans (hsum ▸ hm))]

private theorem coeff_substituted_trunc (a : ℤ) (N m : ℕ) (hm : m ≤ N) :
    PowerSeries.coeff m (substitute a (psiTrunc N)) =
      PowerSeries.coeff m (substitute a psi) := by
  simp only [substitute, PowerSeries.coeff_expand, PowerSeries.coeff_rescale]
  split_ifs
  · rw [coeff_psiTrunc _ _ ((Nat.div_le_self m 8).trans hm)]
  · rfl

private theorem substitute_trunc (a : ℤ) (N : ℕ) :
    substitute a (psiTrunc N) =
      ∑ j : Fin (N + 1), monomial (8 * triangular j) (a ^ triangular j) := by
  rw [substitute, psiTrunc, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : PowerSeries.rescale a (monomial (triangular j) 1) =
      monomial (triangular j) (a ^ triangular j) := by
    ext m
    simp only [PowerSeries.coeff_rescale, coeff_monomial]
    split_ifs with hm <;> simp [hm]
  rw [h, PowerSeries.expand_monomial]

private theorem coeff_cube_shift (a : ℤ) (n : ℕ) :
    PowerSeries.coeff n (X ^ 3 * substitute a psi ^ 3) =
      ∑ j : IndexBox n, if 3 + 8 * boxEnergy j = n then a ^ boxEnergy j else 0 := by
  have h := coeff_substituted_trunc a n
  have hc : PowerSeries.coeff n (X ^ 3 * substitute a (psiTrunc n) ^ 3) =
      PowerSeries.coeff n (X ^ 3 * substitute a psi ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul]
    exact coeff_mul_congr_through (fun _ _ => rfl)
      (coeff_mul_congr_through (coeff_mul_congr_through h h) h) n le_rfl
  rw [← hc, substitute_trunc]
  let term (j : Fin (n + 1)) :
      PowerSeries ℤ := monomial (8 * triangular j) (a ^ triangular j)
  change PowerSeries.coeff n (X ^ 3 * (∑ j, term j) ^ 3) = _
  have hprod : (∑ j, term j) ^ 3 = ∑ j : IndexBox n, ∏ i : Fin 3, term (j i) := by
    rw [← Fintype.prod_sum (fun _ : Fin 3 => term), Finset.prod_const]
    rfl
  rw [hprod, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.prod_univ_three, term, PowerSeries.X_pow_eq,
    monomial_mul_monomial, one_mul, coeff_monomial, boxEnergy, tripleEnergy,
    Fin.sum_univ_three, pow_add]
  rw [show 3 + (8 * triangular (j 0) + 8 * triangular (j 1) + 8 * triangular (j 2)) =
    3 + 8 * (triangular (j 0) + triangular (j 1) + triangular (j 2)) by ring]
  by_cases hn : n = 3 + 8 * (triangular (j 0) + triangular (j 1) + triangular (j 2))
  · rw [ite_eq_left hn, ite_eq_left hn.symm]
  · rw [ite_eq_right hn, ite_eq_right (Ne.symm hn)]

private theorem theta_coefficient_grouped (n : ℕ) :
    thetaCoefficient n = groupedCoefficient n := by
  rw [thetaCoefficient, thetaSeries, mul_add, map_add, coeff_cube_shift, coeff_cube_shift,
    groupedCoefficient, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

private theorem coefficient_eq_a005926 (n : ℕ) : thetaCoefficient n = (a005926 n : ℤ) :=
  (theta_coefficient_grouped n).trans (groupedCoefficient_eq_a005926 n)

/-- The exponent shift by three forces all earlier coefficients to vanish. -/
theorem theta_coefficient_of_lt_three (n : ℕ) (hn : n < 3) : thetaCoefficient n = 0 := by
  rw [coefficient_eq_a005926, a005926_small n hn, Nat.cast_zero]

private def residue (b : Fin 4) : Fin 3 → ℤ :=
  ![![0,0,0], ![0,1,1], ![1,0,1], ![1,1,0]] b

private def expandZ (b : Fin 4) (k : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => 2 * k i + residue b i

private def parityIndex (z : Fin 3 → ℤ) : Fin 4 :=
  if z 0 % 2 = 0 then (if z 1 % 2 = 0 then 0 else 1)
  else (if z 1 % 2 = 0 then 2 else 3)

private theorem expandZ_even (b : Fin 4) (k : Fin 3 → ℤ) : (∑ i, expandZ b k i) % 2 = 0 := by
  rw [Fin.sum_univ_three]
  fin_cases b <;> simp [expandZ, residue, Matrix.cons_val_zero] <;> omega

private theorem residue_mod (z : Fin 3 → ℤ) (h : (∑ i, z i) % 2 = 0) (i : Fin 3) :
    residue (parityIndex z) i = z i % 2 := by
  rw [Fin.sum_univ_three] at h
  by_cases h0 : z 0 % 2 = 0 <;> by_cases h1 : z 1 % 2 = 0 <;>
    fin_cases i <;> simp [parityIndex, h0, h1, residue] <;> omega

private theorem parityIndex_expandZ (b : Fin 4) (k : Fin 3 → ℤ) :
    parityIndex (expandZ b k) = b := by
  have isEven (x : ℤ) : (2*x) % 2 = 0 := by omega
  fin_cases b <;> simp [parityIndex, expandZ, residue, isEven]

private theorem residue_binary (b : Fin 4) (i : Fin 3) : 0 ≤ residue b i ∧ residue b i < 2 := by
  fin_cases b <;> fin_cases i <;> decide

private def parityEquiv : (Fin 4 × (Fin 3 → ℤ)) ≃ {z : Fin 3 → ℤ // (∑ i, z i) % 2 = 0} where
  toFun x := ⟨expandZ x.1 x.2, expandZ_even x.1 x.2⟩
  invFun z := (parityIndex z.1, fun i => z.1 i / 2)
  left_inv := by
    rintro ⟨b,k⟩
    apply Prod.ext (parityIndex_expandZ b k)
    funext i
    have hb := residue_binary b i
    change (2*k i + residue b i) / 2 = k i
    omega
  right_inv := by
    intro z
    apply Subtype.ext
    funext i
    change 2 * (z.1 i / 2) + residue (parityIndex z.1) i = z.1 i
    rw [residue_mod z.1 z.2 i]
    omega

private def castPi (k : Fin 3 → ℤ) : P := fun i => k i

private theorem mem_grid_iff (p : P) : p ∈ grid ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i := by
  have h := (Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ p
  simpa [grid, Pi.basisFun_repr, Set.mem_range] using h

private noncomputable def gridEquiv : (Fin 3 → ℤ) ≃ grid where
  toFun k := ⟨castPi k, (mem_grid_iff _).mpr (fun i => ⟨k i, rfl⟩)⟩
  invFun p i := Classical.choose ((mem_grid_iff _).mp p.2 i)
  left_inv k := by
    funext i
    apply Int.cast_injective (α := ℝ)
    exact Classical.choose_spec ((mem_grid_iff _).mp
      ((mem_grid_iff (castPi k)).mpr (fun j => ⟨k j, rfl⟩)) i)
  right_inv p := by
    ext i
    exact Classical.choose_spec ((mem_grid_iff _).mp p.2 i)

private noncomputable def cosetOffset (b : Fin 4) : E :=
  toEuclid (fun i => -(4 * (residue b i : ℝ) + 1) / 8)

private theorem euclidean_sq (x : E) : ‖x‖ ^ 2 = ∑ i, (x i)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

private theorem ball_to_energy (N : ℕ) (b : Fin 4) (k : Fin 3 → ℤ) :
    toEuclid (castPi k) ∈ closedBall (cosetOffset b) (Real.sqrt (N : ℝ) / 8) ↔
    squareEnergy (expandZ b k) ≤ (N : ℤ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hR : 0 ≤ Real.sqrt (N : ℝ) / 8 := by positivity
  have hnorm : (8 * ‖toEuclid (castPi k) - cosetOffset b‖)^2 =
      (squareEnergy (expandZ b k) : ℝ) := by
    rw [mul_pow, euclidean_sq, Finset.mul_sum]
    simp only [squareEnergy, Int.cast_sum, Int.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_one]
    apply Finset.sum_congr rfl
    intro i _
    change (8 : ℝ)^2 * ((k i : ℝ) - (-(4*(residue b i : ℝ)+1)/8))^2 =
      (4 * (expandZ b k i : ℝ) + 1)^2
    push_cast [expandZ]
    ring
  have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hn : 0 ≤ ‖toEuclid (castPi k) - cosetOffset b‖ := norm_nonneg _
  rw [← Int.cast_le (R := ℝ), Int.cast_natCast, ← hnorm]
  conv_rhs => rw [← hs]
  constructor <;> intro h
  · exact pow_le_pow_left₀ (by positivity) (by linarith) _
  · have hh := (sq_le_sq₀ (by positivity : 0 ≤ 8*‖toEuclid (castPi k) - cosetOffset b‖)
        (Real.sqrt_nonneg (N : ℝ))).mp h
    linarith

private noncomputable def gridCutEquiv (N : ℕ) (b : Fin 4) :
    {k : Fin 3 → ℤ // squareEnergy (expandZ b k) ≤ (N : ℤ)} ≃
      ↑(body (cosetOffset b) (Real.sqrt (N : ℝ)/8) ∩ grid) := by
  let p : (Fin 3 → ℤ) → Prop := fun k => squareEnergy (expandZ b k) ≤ (N : ℤ)
  let q : grid → Prop := fun v => v.val ∈ body (cosetOffset b) (Real.sqrt (N : ℝ)/8)
  have h (k : Fin 3 → ℤ) : p k ↔ q (gridEquiv k) := (ball_to_energy N b k).symm
  let f : {k // p k} ≃ {v // q v} := gridEquiv.subtypeEquiv h
  let g : {v // q v} ≃ ↑(body (cosetOffset b) (Real.sqrt (N : ℝ)/8) ∩ grid) :=
    { toFun := fun v => ⟨v.1.1, v.2, v.1.2⟩
      invFun := fun v => ⟨⟨v.1, v.2.2⟩, v.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact f.trans g

private noncomputable def prefixByCosets (N : ℕ) : latticeCut N ≃
    (Σ b : Fin 4, ↑(body (cosetOffset b) (Real.sqrt (N : ℝ) / 8) ∩ grid)) := by
  let e₁ : latticeCut N ≃ {z : {z : Fin 3 → ℤ // (∑ i, z i) % 2 = 0} //
      squareEnergy z.1 ≤ (N : ℤ)} :=
    { toFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
      invFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ := parityEquiv.symm.subtypeEquiv (p := fun z => squareEnergy z.1 ≤ (N : ℤ))
    (q := fun a => squareEnergy (expandZ a.1 a.2) ≤ (N : ℤ)) (fun z => by
      have hz := congrArg Subtype.val (parityEquiv.apply_symm_apply z)
      change expandZ (parityEquiv.symm z).1 (parityEquiv.symm z).2 = z.1 at hz
      rw [hz])
  let e₃ : {a : Fin 4 × (Fin 3 → ℤ) // squareEnergy (expandZ a.1 a.2) ≤ (N : ℤ)} ≃
      (Σ b : Fin 4, {k : Fin 3 → ℤ // squareEnergy (expandZ b k) ≤ (N : ℤ)}) :=
    { toFun := fun a => ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
      invFun := fun a => ⟨(a.1, a.2.1), a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e₁.trans (e₂.trans (e₃.trans (Equiv.sigmaCongrRight (gridCutEquiv N))))

private theorem prefix_cosets (N : ℕ) :
    sourcePrefix N = 2 * ∑ b : Fin 4, centerCount (cosetOffset b) (Real.sqrt (N : ℝ)/8) := by
  rw [prefix_eq_cut, Nat.card_congr (prefixByCosets N)]
  let (b : Fin 4) : Finite ↑(body (cosetOffset b) (Real.sqrt (N : ℝ)/8) ∩ grid) :=
    (ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin 3)) (body_bounded _ _)).to_subtype
  rw [Nat.card_sigma]
  rfl

private noncomputable def cutoffRadius (N : ℕ) : ℝ := Real.sqrt (N : ℝ)/8

private theorem cutoffRadius_atTop : Tendsto cutoffRadius atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num))
  exact (tendsto_div_const_atTop_of_pos (show (0 : ℝ) < 8 by norm_num)).2
    (h.comp tendsto_natCast_atTop_atTop)

private theorem radius_pow (N : ℕ) : cutoffRadius N ^ 3 = (N : ℝ) ^ (3/2 : ℝ) / 512 := by
  rw [cutoffRadius, div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (show (0 : ℝ) ≤ (N : ℝ) by positivity)]
  norm_num

private theorem a005926_tendsto :
    Tendsto (fun N : ℕ => (sourcePrefix N : ℝ) / (N : ℝ)^(3/2 : ℝ))
      atTop (𝓝 (Real.pi/48)) := by
  have h (b : Fin 4) : Tendsto (fun N : ℕ =>
    (centerCount (cosetOffset b) (cutoffRadius N) : ℝ) / (cutoffRadius N)^3)
    atTop (𝓝 (4 * Real.pi / 3)) := (shifted_limit (cosetOffset b)).comp cutoffRadius_atTop
  have hsum := ((((h 0).add (h 1)).add (h 2)).add (h 3)).const_mul (2/512 : ℝ)
  rw [show (2/512 : ℝ) * ((4 * Real.pi / 3 + 4 * Real.pi / 3 + 4 * Real.pi / 3) +
      4 * Real.pi / 3) = Real.pi / 48 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hd : (N : ℝ) ^ (3/2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).ne'
  simp only [prefix_cosets, Nat.cast_mul, Nat.cast_ofNat, Fin.sum_univ_four, Nat.cast_add,
    radius_pow]
  unfold cutoffRadius
  field_simp

/-- In every degree, the source coefficient counts the even-parity lattice shell
with weight two. -/
theorem theta_coefficient_lattice (n : ℕ) :
    thetaCoefficient n = (2 * Nat.card (latticeShell n) : ℕ) := by
  rw [coefficient_eq_a005926, a005926_eq_lattice]

private theorem sum_theta_range (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), thetaCoefficient n) =
      ∑ n ∈ Finset.Icc 1 N, thetaCoefficient n := by
  have hr : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp), theta_coefficient_of_lt_three 0 (by decide), zero_add]

/-- The sum through the inclusive cutoff N is twice the parity-filtered lattice
count at squared radius N. -/
theorem theta_inclusive_cutoff (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, thetaCoefficient n) = (2 * Nat.card (latticeCut N) : ℕ) := by
  rw [← sum_theta_range]
  simp only [coefficient_eq_a005926]
  rw [← Nat.cast_sum]
  exact congrArg (fun k : ℕ => (k : ℤ)) (prefix_eq_cut N)

/-- Kotesovec's OEIS A005926 conjecture, with all natural cutoffs and the literal
sum from 1 through N. -/
theorem result :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) / (N : ℝ) ^ (3 / 2 : ℝ))
      atTop (𝓝 (Real.pi / 48)) := by
  have h (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, (thetaCoefficient n : ℝ)) =
      (sourcePrefix N : ℝ) := by
    rw [← Int.cast_sum, theta_inclusive_cutoff, Int.cast_natCast, prefix_eq_cut]
  simpa only [h] using a005926_tendsto

end D5.S3.Analytic.Asymptotics.OeisA005926Diamond
