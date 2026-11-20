/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostCurrentBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostCurrentBPZ
   mirror-E: none(waiver:algebraic-original-orbifold-brst-ghost-current-bpz)
   anchors: []
   utility: none
   digest: The native bc current has a three-unit BPZ correction supplied by its actual L(1). -/

import D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBPZ

/-! The normalized modes of the occupation state `b(-2)c(1)|0⟩` have a
statewise finite normal sum. Inversion shifts the normal-order cut, and the
mixed CAR at the three intervening indices gives the vacuum correction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostCurrentBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock BcGhostFock BcGhostCharge BcGhostStateField
open BcGhostHermitian (Homogeneous homogeneous_iff_number)
open BcGhostVirasoro (L normal ward_b ward_c)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_b beta_c)

open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private signedNormalMinusOne from D5.S3.Quantum.Fermionic.BcGhostStateField
open private normal_product integer_split identity_modes from
  D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
open private normal_finite L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private homogeneous_b homogeneous_c from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBPZ

/-- The ordered two-creator state with b preceding c. -/
def current : Fock := ket {0, 1}

/-- Weight one gives physical mode index equal to the vertex mode index. -/
def J (k : ℤ) : Module.End ℂ Fock := (Y current) [[k]]

theorem current_word : current = b (-2) (c 1 vacuum) := by
  rw [ghost_vacuum.2.2.1]
  norm_num [current, b, create_ket, phase, lowerCount, Finset.filter_singleton]

/-- The actual state field is the unweighted statewise finite bc normal sum. -/
theorem current_modes (k : ℤ) (v : Fock) :
    J k v = ∑ᶠ q : ℤ, normal (k - q) q v := by
  have hb : parity (ket {0}) = (-1 : ℂ) ^ (1 : ℕ) • ket {0} := by
    simp [parity_ket]
  have hc : parity (ket {1}) = (-1 : ℂ) ^ (1 : ℕ) • ket {1} := by
    simp [parity_ket]
  have hstate : ((Y (ket {0})) [[-1]]) (ket {1}) = current := by
    rw [stateField_creation.2.2.2.1, current_word, ghost_vacuum.2.2.1]
    rfl
  have hfield : Y current = (signedNormalMinusOne (-1) (Y (ket {0})) (Y (ket {1}))).1 := by
    have h := normal_product (ket {0}) (ket {1}) 1 1 hb hc
    rw [hstate, show (-1 : ℂ) ^ (1 * 1 : ℕ) = -1 by norm_num] at h
    exact h
  have hmode := (signedNormalMinusOne (-1) (Y (ket {0})) (Y (ket {1}))).2 k v
  rw [← hfield] at hmode
  change J k v = _ at hmode
  rw [hmode, integer_split _ (normal_finite k v) (k + 2)]
  simp only [stateField_creation.2.2.2.1, stateField_creation.2.2.2.2, neg_one_smul]
  have lower (i : ℕ) :
      normal (k - (k + 2 - i - 1)) (k + 2 - i - 1) v =
        -c (k - i - 1 + 2) (b ((i : ℤ) - 1) v) := by
    rw [show k - (k + 2 - (i : ℤ) - 1) = i - 1 by omega,
      show k + 2 - (i : ℤ) - 1 = k - i - 1 + 2 by omega, normal, ite_eq_right (by omega)]
    rfl
  have upper (i : ℕ) :
      normal (k - (k + 2 + i)) (k + 2 + i) v =
        b (-(i : ℤ) - 1 - 1) (c (k + i + 2) v) := by
    rw [show k - (k + 2 + (i : ℤ)) = -(i : ℤ) - 1 - 1 by omega,
      show k + 2 + (i : ℤ) = k + i + 2 by omega, normal, ite_eq_left (by omega)]
    rfl
  simp only [lower, upper, finsum_neg_distrib]
  exact add_comm _ _

/-- With the b-first convention, the zero mode is minus the diagonal charge. -/
theorem current_zero_mode : J 0 = -ghostNumber := by
  apply LinearMap.ext
  intro v
  rw [current_modes, LinearMap.neg_apply, ghost_number_normal_sum, ← finsum_neg_distrib]
  apply finsum_congr
  intro q
  by_cases hq : q ≤ 1
  · simp [normal, normalTerm, hq, show ¬(2 ≤ q) by omega]
  · simp [normal, normalTerm, hq, show 2 ≤ q by omega]

private theorem L_b_apply (m p : ℤ) (v : Fock) :
    L m (b p v) = ((m - p : ℤ) : ℂ) • b (m + p) v + b p (L m v) :=
  sub_eq_iff_eq_add.mp (LinearMap.congr_fun (ward_b m p) v)

private theorem L_c_apply (m q : ℤ) (v : Fock) :
    L m (c q v) = ((-2 * m - q : ℤ) : ℂ) • c (m + q) v + c q (L m v) :=
  sub_eq_iff_eq_add.mp (LinearMap.congr_fun (ward_c m q) v)

theorem current_L0 : L 0 current = current := by
  rw [current_word, L_b_apply, L_c_apply, L_vacuum_nonneg 0 (by omega)]
  norm_num [two_smul, map_neg]

theorem current_L1 : L 1 current = (3 : ℂ) • vacuum := by
  have contraction : b (-1) (c 1 vacuum) = vacuum := by
    have h := LinearMap.congr_fun (ghost_mixed_car (-1) 1) vacuum
    simpa [ghost_vacuum.1 (-1) (by omega)] using h
  rw [current_word, L_b_apply, L_c_apply, L_vacuum_nonneg 1 (by omega)]
  norm_num [contraction, ghost_vacuum.2.1 2 (by omega)]

theorem current_L1_squared : L 1 (L 1 current) = 0 := by
  rw [current_L1, map_smul, L_vacuum_nonneg 1 (by omega), smul_zero]

private theorem sign_square (r : ℤ) : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

private theorem beta_bc (p q : ℤ) {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (b p (c q x)) y = beta x (c (-q) (b (-p) y)) := by
  rw [beta_b p (homogeneous_c hx q), beta_c q hx,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  calc
    _ = ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) * beta x (c (-q) (b (-p) y)) := by ring
    _ = _ := by rw [sign_square, one_mul]

private theorem beta_cb (p q : ℤ) {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (c q (b p x)) y = beta x (b (-p) (c (-q) y)) := by
  rw [beta_c q (homogeneous_b hx p), beta_b p hx,
    zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  calc
    _ = ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) * beta x (b (-p) (c (-q) y)) := by ring
    _ = _ := by rw [sign_square, one_mul]

/-- Reflection cancels outside the three b indices between the two cuts. -/
private theorem normal_pair (p q : ℤ) {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (normal p q x) y + beta x (normal (-p) (-q) y) =
      if -1 ≤ p ∧ p ≤ 1 ∧ p + q = 0 then -(beta x y) else 0 := by
  by_cases hp : p ≤ -2
  · have hn : ¬ -p ≤ -2 := by omega
    have hb : ¬(-1 ≤ p ∧ p ≤ 1 ∧ p + q = 0) := by omega
    simp [normal, hp, hn, hb, beta_bc p q hx]
  by_cases hn : -p ≤ -2
  · have hb : ¬(-1 ≤ p ∧ p ≤ 1 ∧ p + q = 0) := by omega
    simp [normal, hp, hn, hb, beta_cb p q hx]
  have hlo : -1 ≤ p := by omega
  have hhi : p ≤ 1 := by omega
  have hcar := LinearMap.congr_fun (ghost_mixed_car (-p) (-q)) y
  simp only [LinearMap.add_apply, Module.End.mul_apply] at hcar
  simp only [normal, hp, hn, ite_false, LinearMap.neg_apply, Module.End.mul_apply,
    map_neg, beta_cb p q hx, hlo, hhi, true_and, ← neg_add, ← map_add]
  by_cases hz : p + q = 0
  · rw [ite_eq_left (by omega : -p + -q = 0), Module.End.one_apply] at hcar
    rw [ite_eq_left hz, hcar]
  · rw [ite_eq_right (by omega : -p + -q ≠ 0), LinearMap.zero_apply] at hcar
    rw [ite_eq_right hz, hcar, map_zero, neg_zero]

private theorem beta_current_mode_homogeneous (k : ℤ) {r : ℤ} {x : Fock}
    (hx : Homogeneous r x) (y : Fock) :
    beta (J k x) y + beta x (J (-k) y) = -(if k = 0 then 3 * beta x y else 0) := by
  classical
  let first (q : ℤ) := beta (normal (k - q) q x) y
  let second (q : ℤ) := beta x (normal (-k - -q) (-q) y)
  have hfirst : Function.HasFiniteSupport first :=
    (normal_finite k x).fun_comp ((beta.flip y).map_zero)
  have hsecond : Function.HasFiniteSupport second :=
    ((normal_finite (-k) y).fun_comp (beta x).map_zero).preimage
      (Equiv.neg ℤ).injective.injOn
  have leftSum : beta (J k x) y = ∑ᶠ q, first q := by
    rw [current_modes]
    exact map_finsum (beta.flip y) (normal_finite k x)
  have rightSum : beta x (J (-k) y) = ∑ᶠ q, second q := by
    rw [current_modes, map_finsum (beta x) (normal_finite (-k) y)]
    exact (finsum_comp_equiv (Equiv.neg ℤ)).symm
  let boundary : Finset ℤ := {-1, 0, 1}
  let defect (q : ℤ) : ℂ :=
    if q ∈ boundary then -(if k = 0 then beta x y else 0) else 0
  have term (q : ℤ) : first q + second q = defect q := by
    dsimp [first, second, defect]
    rw [show -k - -q = -(k - q) by omega, normal_pair (k - q) q hx]
    by_cases hk : k = 0
    · subst k
      have hm : q ∈ boundary ↔ -1 ≤ 0 - q ∧ 0 - q ≤ 1 := by
        simp only [boundary, Finset.mem_insert, Finset.mem_singleton]
        omega
      simp [hm]
    · simp [hk]
  rw [leftSum, rightSum, ← finsum_add_distrib hfirst hsecond, finsum_congr term]
  rw [finsum_eq_sum_of_support_subset _ (s := boundary) (by
    intro q hq
    by_contra hn
    exact hq (ite_eq_right hn))]
  have card : boundary.card = 3 := by decide
  simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, card]
  split_ifs <;> simp

/-- The transpose of every native current mode, on all finite Fock states. -/
theorem beta_current_mode (k : ℤ) (x y : Fock) :
    beta (J k x) y = -beta x (J (-k) y) - (if k = 0 then 3 * beta x y else 0) := by
  have h :
      beta (J k x) y + beta x (J (-k) y) = -(if k = 0 then 3 * beta x y else 0) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv =>
      simp only [map_add, LinearMap.add_apply]
      by_cases hk : k = 0
      · simp only [hk, ite_true] at hu hv ⊢
        linear_combination hu + hv
      · simp only [hk, ite_false, neg_zero] at hu hv ⊢
        linear_combination hu + hv
    | single S a =>
      have hs : Finsupp.single S a = a • ket S := by simp [ket]
      have hket : Homogeneous (charge S) (ket S) :=
        (homogeneous_iff_number _ _).mpr (number_ket S)
      have hk := beta_current_mode_homogeneous k hket y
      rw [hs]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      by_cases hz : k = 0 <;> simp only [hz, ite_true, ite_false] at hk ⊢ <;>
        linear_combination a * hk
  linear_combination h

/-- The vacuum correction is the reflected coefficient of the actual L(1) state. -/
theorem beta_current_mode_conformal (k : ℤ) (x y : Fock) :
    beta (J k x) y =
      -beta x (J (-k) y + ((Y (L 1 current)) [[-k - 1]]) y) := by
  let I : VertexOperator ℂ Fock := FieldNormalProduct.identityField
  have hcoeff : (((3 : ℂ) • I) [[-k - 1]]) y = (3 : ℂ) • (I [[-k - 1]]) y := by
    simp only [VertexOperator.ncoeff, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  rw [beta_current_mode, current_L1, map_smul, stateField_creation.1]
  rw [show (((3 : ℂ) • FieldNormalProduct.identityField) [[-k - 1]]) y =
    (3 : ℂ) • (FieldNormalProduct.identityField [[-k - 1]]) y from hcoeff, identity_modes]
  by_cases hk : k = 0
  · simp [hk, smul_eq_mul]
    ring
  · simp [hk, show -k - 1 ≠ -1 by omega]

#print axioms current
#print axioms J
#print axioms current_word
#print axioms current_modes
#print axioms current_zero_mode
#print axioms current_L0
#print axioms current_L1
#print axioms current_L1_squared
#print axioms beta_current_mode
#print axioms beta_current_mode_conformal

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostCurrentBPZ
