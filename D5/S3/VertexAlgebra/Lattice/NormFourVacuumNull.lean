/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumNull
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumNull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Production norm-four level-six vacuum coefficient cancellation. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumNullCalculus
import Batteries.Tactic.OpenPrivate

/-! The level-six vacuum null relation for the actual norm-four lattice vector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open private P P_neg alongPartial_P E Ei Atom Atom.value Atom.frequency Atom.degree
  Atom.one Atom.x1 Atom.x1sq Atom.x2 Atom.x1x2 Atom.x1four Atom.x1x3 Atom.x2sq
  Atom.coefficient rawPolynomial currentPolynomial quadraticPolynomial A A_atom atom tri S
  phase_same phase_zero phase_neg_left phase_neg_same
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumNullCalculus
open private opposite_phase from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualStateFieldCalculus MvPolynomial
open NormFourVirasoroVector
open scoped BigOperators VertexOperator

noncomputable section

-- The following finite production coefficient evaluations are consumed by
-- the four descendant identities and their final scalar cancellation.


private theorem bilinear_right_zero (D : LatticeData) (a : Charge D) :
    bilinear D a 0 = 0 := by simp [bilinear]

-- Each equality below is for an actual production mode on an actual single.
-- The full raw and normal-ordering sums have already been reduced above.
private theorem A2_z_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a 0 Atom.one) =
    tri D a
      (720 * (P D a 0) ^ 2)
      (2880 * (S D s))
      (2880 * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 2 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A3_z_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 3 (atom D a 0 Atom.one) =
    tri D a
      (1440 * (P D a 0) * (P D a 1))
      (2880 * (P D a 0) * (S D s))
      (-2880 * (P D a 0) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 3 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A6_z_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 6 (atom D a 0 Atom.one) =
    tri D a
      (1440 * (P D a 0) * (P D a 4) + 1440 * (P D a 1) * (P D a 3) + 720 * (P D a 2) ^ 2)
      (120 * (P D a 0) ^ 4 * (S D s) + 720 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 960 * (P D a 0) * (P D a 2) * (S D s) + 360 * (P D a 1) ^ 2 * (S D s) + 720 * (P D a 3) * (S D s))
      (120 * (P D a 0) ^ 4 * (S D s) - 720 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 960 * (P D a 0) * (P D a 2) * (S D s) + 360 * (P D a 1) ^ 2 * (S D s) - 720 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 6 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_z_x1sq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a 0 Atom.x1sq) =
    tri D a
      (720 * (P D a 0) ^ 4 + 11520 * (P D a 0) * (P D a 2))
      (2880 * (P D a 0) ^ 2 * (S D s) + 23040 * (P D a 1) * (S D s))
      (2880 * (P D a 0) ^ 2 * (S D s) - 23040 * (P D a 1) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 2 (by omega) Atom.x1sq
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_p_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a a Atom.one) =
    tri D a
      (120 * (P D a 0) ^ 4 * (S D s) - 720 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 960 * (P D a 0) * (P D a 2) * (S D s) + 360 * (P D a 1) ^ 2 * (S D s) - 720 * (P D a 3) * (S D s))
      (720 * (P D a 0) ^ 2 + 5760 * (P D a 1))
      (0) := by
  unfold atom
  rw [A_atom D a a s 2 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_n_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a (-a) Atom.one) =
    tri D a
      (120 * (P D a 0) ^ 4 * (S D s) + 720 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 960 * (P D a 0) * (P D a 2) * (S D s) + 360 * (P D a 1) ^ 2 * (S D s) + 720 * (P D a 3) * (S D s))
      (0)
      (720 * (P D a 0) ^ 2 - 5760 * (P D a 1)) := by
  unfold atom
  rw [A_atom D a (-a) s 2 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_z_x1four (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a 0 Atom.x1four) =
    tri D a
      (720 * (P D a 0) ^ 6 + 23040 * (P D a 0) ^ 3 * (P D a 2))
      (2880 * (P D a 0) ^ 4 * (S D s) - 46080 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 92160 * (P D a 1) ^ 2 * (S D s) + 184320 * (P D a 3) * (S D s))
      (2880 * (P D a 0) ^ 4 * (S D s) + 46080 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 92160 * (P D a 1) ^ 2 * (S D s) - 184320 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 2 (by omega) Atom.x1four
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_z_x1x3 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a 0 Atom.x1x3) =
    tri D a
      (720 * (P D a 0) ^ 3 * (P D a 2) + 17280 * (P D a 0) * (P D a 4) + 5760 * (P D a 2) ^ 2)
      (5760 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 2880 * (P D a 0) * (P D a 2) * (S D s) + 5760 * (P D a 1) ^ 2 * (S D s) + 11520 * (P D a 3) * (S D s))
      (-5760 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 2880 * (P D a 0) * (P D a 2) * (S D s) + 5760 * (P D a 1) ^ 2 * (S D s) - 11520 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 2 (by omega) Atom.x1x3
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_z_x2sq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a 0 Atom.x2sq) =
    tri D a
      (720 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 23040 * (P D a 1) * (P D a 3))
      (1920 * (P D a 0) ^ 4 * (S D s) + 15360 * (P D a 0) * (P D a 2) * (S D s) - 2880 * (P D a 1) ^ 2 * (S D s) + 11520 * (P D a 3) * (S D s))
      (1920 * (P D a 0) ^ 4 * (S D s) + 15360 * (P D a 0) * (P D a 2) * (S D s) - 2880 * (P D a 1) ^ 2 * (S D s) - 11520 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 2 (by omega) Atom.x2sq
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_p_x1sq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a a Atom.x1sq) =
    tri D a
      (-8 * (P D a 0) ^ 6 * (S D s) + 240 * (P D a 0) ^ 4 * (P D a 1) * (S D s) - 320 * (P D a 0) ^ 3 * (P D a 2) * (S D s) + 360 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) - 720 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 3840 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 4608 * (P D a 0) * (P D a 4) * (S D s) - 960 * (P D a 1) ^ 3 * (S D s) + 5760 * (P D a 1) * (P D a 3) * (S D s) + 2560 * (P D a 2) ^ 2 * (S D s) - 7680 * (P D a 5) * (S D s))
      (720 * (P D a 0) ^ 4 + 5760 * (P D a 0) ^ 2 * (P D a 1) + 11520 * (P D a 0) * (P D a 2))
      (0) := by
  unfold atom
  rw [A_atom D a a s 2 (by omega) Atom.x1sq
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_n_x1sq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a (-a) Atom.x1sq) =
    tri D a
      (-8 * (P D a 0) ^ 6 * (S D s) - 240 * (P D a 0) ^ 4 * (P D a 1) * (S D s) - 320 * (P D a 0) ^ 3 * (P D a 2) * (S D s) + 360 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) + 720 * (P D a 0) ^ 2 * (P D a 3) * (S D s) + 3840 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 4608 * (P D a 0) * (P D a 4) * (S D s) + 960 * (P D a 1) ^ 3 * (S D s) + 5760 * (P D a 1) * (P D a 3) * (S D s) + 2560 * (P D a 2) ^ 2 * (S D s) + 7680 * (P D a 5) * (S D s))
      (0)
      (720 * (P D a 0) ^ 4 - 5760 * (P D a 0) ^ 2 * (P D a 1) + 11520 * (P D a 0) * (P D a 2)) := by
  unfold atom
  rw [A_atom D a (-a) s 2 (by omega) Atom.x1sq
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_p_x2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a a Atom.x2) =
    tri D a
      (16 * (P D a 0) ^ 6 * (S D s) - 120 * (P D a 0) ^ 4 * (P D a 1) * (S D s) + 640 * (P D a 0) ^ 3 * (P D a 2) * (S D s) - 1440 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 960 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 2304 * (P D a 0) * (P D a 4) * (S D s) + 120 * (P D a 1) ^ 3 * (S D s) + 720 * (P D a 1) * (P D a 3) * (S D s) + 640 * (P D a 2) ^ 2 * (S D s) - 1920 * (P D a 5) * (S D s))
      (720 * (P D a 0) ^ 2 * (P D a 1) + 5760 * (P D a 1) ^ 2 + 11520 * (P D a 3))
      (0) := by
  unfold atom
  rw [A_atom D a a s 2 (by omega) Atom.x2
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A2_n_x2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 2 (atom D a (-a) Atom.x2) =
    tri D a
      (-16 * (P D a 0) ^ 6 * (S D s) - 120 * (P D a 0) ^ 4 * (P D a 1) * (S D s) - 640 * (P D a 0) ^ 3 * (P D a 2) * (S D s) - 1440 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 960 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) - 2304 * (P D a 0) * (P D a 4) * (S D s) + 120 * (P D a 1) ^ 3 * (S D s) - 720 * (P D a 1) * (P D a 3) * (S D s) - 640 * (P D a 2) ^ 2 * (S D s) - 1920 * (P D a 5) * (S D s))
      (0)
      (720 * (P D a 0) ^ 2 * (P D a 1) - 5760 * (P D a 1) ^ 2 + 11520 * (P D a 3)) := by
  unfold atom
  rw [A_atom D a (-a) s 2 (by omega) Atom.x2
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A3_z_x1x2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 3 (atom D a 0 Atom.x1x2) =
    tri D a
      (1440 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 11520 * (P D a 0) * (P D a 4) + 5760 * (P D a 1) * (P D a 3))
      (2880 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 11520 * (P D a 0) * (P D a 2) * (S D s) + 11520 * (P D a 3) * (S D s))
      (-2880 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 11520 * (P D a 0) * (P D a 2) * (S D s) - 11520 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 3 (by omega) Atom.x1x2
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A3_p_x1 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 3 (atom D a a Atom.x1) =
    tri D a
      (-8 * (P D a 0) ^ 6 * (S D s) + 160 * (P D a 0) ^ 3 * (P D a 2) * (S D s) + 360 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) - 720 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 1440 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 1728 * (P D a 0) * (P D a 4) * (S D s) - 240 * (P D a 1) ^ 3 * (S D s) + 1440 * (P D a 1) * (P D a 3) * (S D s) + 640 * (P D a 2) ^ 2 * (S D s) - 1920 * (P D a 5) * (S D s))
      (1440 * (P D a 0) ^ 2 * (P D a 1) + 5760 * (P D a 0) * (P D a 2) + 5760 * (P D a 3))
      (0) := by
  unfold atom
  rw [A_atom D a a s 3 (by omega) Atom.x1
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A3_n_x1 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 3 (atom D a (-a) Atom.x1) =
    tri D a
      (8 * (P D a 0) ^ 6 * (S D s) - 160 * (P D a 0) ^ 3 * (P D a 2) * (S D s) - 360 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) - 720 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 1440 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) - 1728 * (P D a 0) * (P D a 4) * (S D s) - 240 * (P D a 1) ^ 3 * (S D s) - 1440 * (P D a 1) * (P D a 3) * (S D s) - 640 * (P D a 2) ^ 2 * (S D s) - 1920 * (P D a 5) * (S D s))
      (0)
      (1440 * (P D a 0) ^ 2 * (P D a 1) - 5760 * (P D a 0) * (P D a 2) + 5760 * (P D a 3)) := by
  unfold atom
  rw [A_atom D a (-a) s 3 (by omega) Atom.x1
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A4_z_x1sq (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 4 (atom D a 0 Atom.x1sq) =
    tri D a
      (1440 * (P D a 0) ^ 3 * (P D a 2) + 720 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 11520 * (P D a 0) * (P D a 4))
      (-480 * (P D a 0) ^ 4 * (S D s) + 1440 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 7680 * (P D a 0) * (P D a 2) * (S D s) + 5760 * (P D a 1) ^ 2 * (S D s) + 11520 * (P D a 3) * (S D s))
      (-480 * (P D a 0) ^ 4 * (S D s) - 1440 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 7680 * (P D a 0) * (P D a 2) * (S D s) + 5760 * (P D a 1) ^ 2 * (S D s) - 11520 * (P D a 3) * (S D s)) := by
  unfold atom
  rw [A_atom D a 0 s 4 (by omega) Atom.x1sq
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A4_p_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 4 (atom D a a Atom.one) =
    tri D a
      (4 * (P D a 0) ^ 6 * (S D s) - 60 * (P D a 0) ^ 4 * (P D a 1) * (S D s) + 160 * (P D a 0) ^ 3 * (P D a 2) * (S D s) + 180 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) - 360 * (P D a 0) ^ 2 * (P D a 3) * (S D s) - 480 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 576 * (P D a 0) * (P D a 4) * (S D s) - 60 * (P D a 1) ^ 3 * (S D s) + 360 * (P D a 1) * (P D a 3) * (S D s) + 160 * (P D a 2) ^ 2 * (S D s) - 480 * (P D a 5) * (S D s))
      (1440 * (P D a 0) * (P D a 2) + 720 * (P D a 1) ^ 2 + 5760 * (P D a 3))
      (0) := by
  unfold atom
  rw [A_atom D a a s 4 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private theorem A4_n_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    A D a s 4 (atom D a (-a) Atom.one) =
    tri D a
      (4 * (P D a 0) ^ 6 * (S D s) + 60 * (P D a 0) ^ 4 * (P D a 1) * (S D s) + 160 * (P D a 0) ^ 3 * (P D a 2) * (S D s) + 180 * (P D a 0) ^ 2 * (P D a 1) ^ 2 * (S D s) + 360 * (P D a 0) ^ 2 * (P D a 3) * (S D s) + 480 * (P D a 0) * (P D a 1) * (P D a 2) * (S D s) + 576 * (P D a 0) * (P D a 4) * (S D s) + 60 * (P D a 1) ^ 3 * (S D s) + 360 * (P D a 1) * (P D a 3) * (S D s) + 160 * (P D a 2) ^ 2 * (S D s) + 480 * (P D a 5) * (S D s))
      (0)
      (1440 * (P D a 0) * (P D a 2) + 720 * (P D a 1) ^ 2 - 5760 * (P D a 3)) := by
  unfold atom
  rw [A_atom D a (-a) s 4 (by omega) Atom.one
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])
    (by norm_num [Atom.degree, bilinear_neg_left, bilinear_neg_right,
      bilinear_right_zero, ha])]
  norm_num [quadraticPolynomial, currentPolynomial, Atom.value, Atom.frequency,
    Atom.degree, Atom.coefficient, rawPolynomial, Ei, E, P_neg,
    Finset.sum_range_succ, Derivation.leibniz, Derivation.leibniz_pow,
    alongPartial_P, bilinear_neg_left, bilinear_neg_right, bilinear_right_zero, ha,
    phase_same D a ha, opposite_phase D a ha, phase_neg_left D a ha,
    phase_neg_same D a ha, phase_zero, smul_eq_C_mul]
  all_goals
    apply Finsupp.ext
    intro δ
    by_cases h0 : (0 : Charge D) = δ
    all_goals by_cases hp : a = δ
    all_goals by_cases hm : -a = δ
    all_goals
      simp_all [-sq_eq_one_iff, tri, S, Finsupp.single_apply, h0, hp, hm,
        smul_eq_C_mul, map_add, map_mul, map_neg, map_ofNat] <;> ring

private def V2 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  atom D a 0 Atom.x1sq + (4 * s) • atom D a a Atom.one +
    (4 * s) • atom D a (-a) Atom.one

private def V3 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  atom D a 0 Atom.x1x2 + (2 * s) • atom D a a Atom.x1 -
    (2 * s) • atom D a (-a) Atom.x1

private def V4 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  (7 : ℂ) • atom D a 0 Atom.x1four + (80 : ℂ) • atom D a 0 Atom.x1x3 +
    (12 : ℂ) • atom D a 0 Atom.x2sq +
    (24 * s) • atom D a a Atom.x1sq + (192 * s) • atom D a a Atom.x2 +
    (24 * s) • atom D a (-a) Atom.x1sq - (192 * s) • atom D a (-a) Atom.x2

private def V222 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  tri D a
      (5 * (P D a 0) ^ 6 + 208 * (P D a 0) ^ 3 * (P D a 2) + 12 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 1152 * (P D a 0) * (P D a 4) + 384 * (P D a 1) * (P D a 3) + 384 * (P D a 2) ^ 2)
      (28 * (P D a 0) ^ 4 * (S D s) + 192 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 320 * (P D a 0) * (P D a 2) * (S D s) + 1008 * (P D a 1) ^ 2 * (S D s) + 2112 * (P D a 3) * (S D s))
      (28 * (P D a 0) ^ 4 * (S D s) - 192 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 320 * (P D a 0) * (P D a 2) * (S D s) + 1008 * (P D a 1) ^ 2 * (S D s) - 2112 * (P D a 3) * (S D s))

private def V33 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  tri D a
      (-(P D a 0) ^ 6 + 20 * (P D a 0) ^ 3 * (P D a 2) + 90 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 576 * (P D a 0) * (P D a 4) + 360 * (P D a 1) * (P D a 3) + 80 * (P D a 2) ^ 2)
      (180 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 720 * (P D a 0) * (P D a 2) * (S D s) + 720 * (P D a 3) * (S D s))
      (-180 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 720 * (P D a 0) * (P D a 2) * (S D s) - 720 * (P D a 3) * (S D s))

private def V42 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  tri D a
      (2 * (P D a 0) ^ 6 + 170 * (P D a 0) ^ 3 * (P D a 2) + 135 * (P D a 0) ^ 2 * (P D a 1) ^ 2 + 1008 * (P D a 0) * (P D a 4) + 180 * (P D a 1) * (P D a 3) + 80 * (P D a 2) ^ 2)
      (-30 * (P D a 0) ^ 4 * (S D s) + 90 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 840 * (P D a 0) * (P D a 2) * (S D s) + 540 * (P D a 1) ^ 2 * (S D s) + 2160 * (P D a 3) * (S D s))
      (-30 * (P D a 0) ^ 4 * (S D s) - 90 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 840 * (P D a 0) * (P D a 2) * (S D s) + 540 * (P D a 1) ^ 2 * (S D s) - 2160 * (P D a 3) * (S D s))

private def V6 (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  tri D a
      (12 * (P D a 0) * (P D a 4) + 12 * (P D a 1) * (P D a 3) + 6 * (P D a 2) ^ 2)
      ((P D a 0) ^ 4 * (S D s) + 6 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 8 * (P D a 0) * (P D a 2) * (S D s) + 3 * (P D a 1) ^ 2 * (S D s) + 6 * (P D a 3) * (S D s))
      ((P D a 0) ^ 4 * (S D s) - 6 * (P D a 0) ^ 2 * (P D a 1) * (S D s) + 8 * (P D a 0) * (P D a 2) * (S D s) + 3 * (P D a 1) ^ 2 * (S D s) - 6 * (P D a 3) * (S D s))

private theorem A2_vacuum (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 2 (vacuum D) = (720 : ℂ) • V2 D a s := by
  change A D a s 2 (atom D a 0 Atom.one) = _
  rw [A2_z_one D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A3_vacuum (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 3 (vacuum D) = (1440 : ℂ) • V3 D a s := by
  change A D a s 3 (atom D a 0 Atom.one) = _
  rw [A3_z_one D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A6_vacuum (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 6 (vacuum D) = (120 : ℂ) • V6 D a s := by
  change A D a s 6 (atom D a 0 Atom.one) = _
  rw [A6_z_one D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A2_V2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 2 (V2 D a s) = (240 : ℂ) • V4 D a s := by
  simp only [V2, map_add, map_sub, map_smul]
  rw [A2_z_x1sq D a ha s, A2_p_one D a ha s, A2_n_one D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A2_V4 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 2 (V4 D a s) = (2160 : ℂ) • V222 D a s := by
  simp only [V4, map_add, map_sub, map_smul]
  rw [A2_z_x1four D a ha s, A2_z_x1x3 D a ha s, A2_z_x2sq D a ha s, A2_p_x1sq D a ha s, A2_p_x2 D a ha s, A2_n_x1sq D a ha s, A2_n_x2 D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A3_V3 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 3 (V3 D a s) = (32 : ℂ) • V33 D a s := by
  simp only [V3, map_add, map_sub, map_smul]
  rw [A3_z_x1x2 D a ha s, A3_p_x1 D a ha s, A3_n_x1 D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

private theorem A4_V2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    A D a s 4 (V2 D a s) = (16 : ℂ) • V42 D a s := by
  simp only [V2, map_add, map_sub, map_smul]
  rw [A4_z_x1sq D a ha s, A4_p_one D a ha s, A4_n_one D a ha s]
  have hS : (S D s) ^ 2 = 1 := by
    change (MvPolynomial.C s : Oscillator D) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V2, V3, V4, V222, V33, V42, V6, atom, Atom.value, S,
      Finsupp.single_apply, h0, hp, hm, smul_eq_C_mul, map_add, map_sub,
      map_mul, map_neg, map_ofNat] <;>
      (ring_nf <;> (try simp only [← map_pow, hs, map_one]) <;> ring)

-- Cancel the harmless integral scalings only after the actual coefficient
-- computations.  No Virasoro singular-vector argument is used here.
private theorem weight_two (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (16 : ℂ) • mode D a s (-2) (vacuum D) = V2 D a s := by
  apply smul_right_injective (Carrier D) (show (720 : ℂ) ≠ 0 by norm_num)
  simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
    show (720 : ℂ) * 16 = 11520 by norm_num] using A2_vacuum D a ha s hs

private theorem weight_three (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (8 : ℂ) • mode D a s (-3) (vacuum D) = V3 D a s := by
  apply smul_right_injective (Carrier D) (show (1440 : ℂ) ≠ 0 by norm_num)
  simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
    show (1440 : ℂ) * 8 = 11520 by norm_num] using A3_vacuum D a ha s hs

private theorem weight_six_single (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (96 : ℂ) • mode D a s (-6) (vacuum D) = V6 D a s := by
  apply smul_right_injective (Carrier D) (show (120 : ℂ) ≠ 0 by norm_num)
  simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
    show (120 : ℂ) * 96 = 11520 by norm_num] using A6_vacuum D a ha s hs

private theorem weight_four (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (768 : ℂ) • mode D a s (-2) (mode D a s (-2) (vacuum D)) = V4 D a s := by
  have action : (48 : ℂ) • mode D a s (-2) (V2 D a s) = V4 D a s := by
    apply smul_right_injective (Carrier D) (show (240 : ℂ) ≠ 0 by norm_num)
    simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
      show (240 : ℂ) * 48 = 11520 by norm_num] using A2_V2 D a ha s hs
  calc
    (768 : ℂ) • mode D a s (-2) (mode D a s (-2) (vacuum D)) =
        (48 : ℂ) • mode D a s (-2)
          ((16 : ℂ) • mode D a s (-2) (vacuum D)) := by
            simp only [map_smul, smul_smul]
            norm_num
    _ = (48 : ℂ) • mode D a s (-2) (V2 D a s) := by rw [weight_two D a ha s hs]
    _ = V4 D a s := action

private theorem weight_six_triple (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (12288 : ℂ) • mode D a s (-2)
      (mode D a s (-2) (mode D a s (-2) (vacuum D))) = (3 : ℂ) • V222 D a s := by
  have action : (16 : ℂ) • mode D a s (-2) (V4 D a s) =
      (3 : ℂ) • V222 D a s := by
    apply smul_right_injective (Carrier D) (show (720 : ℂ) ≠ 0 by norm_num)
    simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
      show (720 : ℂ) * 16 = 11520 by norm_num,
      show (720 : ℂ) * 3 = 2160 by norm_num] using A2_V4 D a ha s hs
  calc
    (12288 : ℂ) • mode D a s (-2)
        (mode D a s (-2) (mode D a s (-2) (vacuum D))) =
        (16 : ℂ) • mode D a s (-2)
          ((768 : ℂ) • mode D a s (-2) (mode D a s (-2) (vacuum D))) := by
            simp only [map_smul, smul_smul]
            norm_num
    _ = (16 : ℂ) • mode D a s (-2) (V4 D a s) := by rw [weight_four D a ha s hs]
    _ = (3 : ℂ) • V222 D a s := action

private theorem weight_six_pair_three (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (2880 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) = V33 D a s := by
  have action : (360 : ℂ) • mode D a s (-3) (V3 D a s) = V33 D a s := by
    apply smul_right_injective (Carrier D) (show (32 : ℂ) ≠ 0 by norm_num)
    simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
      show (32 : ℂ) * 360 = 11520 by norm_num] using A3_V3 D a ha s hs
  calc
    (2880 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) =
        (360 : ℂ) • mode D a s (-3)
          ((8 : ℂ) • mode D a s (-3) (vacuum D)) := by
            simp only [map_smul, smul_smul]
            norm_num
    _ = (360 : ℂ) • mode D a s (-3) (V3 D a s) := by rw [weight_three D a ha s hs]
    _ = V33 D a s := action

private theorem weight_six_pair_four_two (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (11520 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) = V42 D a s := by
  have action : (720 : ℂ) • mode D a s (-4) (V2 D a s) = V42 D a s := by
    apply smul_right_injective (Carrier D) (show (16 : ℂ) ≠ 0 by norm_num)
    simpa only [A, LinearMap.smul_apply, smul_smul, Nat.cast_ofNat,
      show (16 : ℂ) * 720 = 11520 by norm_num] using A4_V2 D a ha s hs
  calc
    (11520 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) =
        (720 : ℂ) • mode D a s (-4)
          ((16 : ℂ) • mode D a s (-2) (vacuum D)) := by
            simp only [map_smul, smul_smul]
            norm_num
    _ = (720 : ℂ) • mode D a s (-4) (V2 D a s) := by rw [weight_two D a ha s hs]
    _ = V42 D a s := action

private theorem coefficient_cancellation (D : LatticeData) (a : Charge D) (s : ℂ) :
    (15 : ℂ) • V222 D a s + (31 : ℂ) • V33 D a s -
      (22 : ℂ) • V42 D a s - (1080 : ℂ) • V6 D a s = 0 := by
  apply Finsupp.ext
  intro δ
  by_cases h0 : (0 : Charge D) = δ
  all_goals by_cases hp : a = δ
  all_goals by_cases hm : -a = δ
  all_goals
    simp_all [-sq_eq_one_iff, tri, V222, V33, V42, V6, S, Finsupp.single_apply,
      h0, hp, hm, smul_eq_C_mul, map_mul, map_ofNat] <;> ring

/-- The actual level-six Ising vacuum relation, in the production lattice carrier.
The hypothesis is only the norm-four direction and the complex sign s^2=1.
The proof computes actual creation, current and charge-transport coefficients. -/
theorem level_six_vacuum_null (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (64 : ℂ) • mode D a s (-2)
        (mode D a s (-2) (mode D a s (-2) (vacuum D))) +
      (93 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) -
      (264 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) -
      (108 : ℂ) • mode D a s (-6) (vacuum D) = 0 := by
  apply smul_right_injective (Carrier D) (show (960 : ℂ) ≠ 0 by norm_num)
  dsimp only
  rw [smul_zero]
  calc
    (960 : ℂ) • ((64 : ℂ) • mode D a s (-2)
          (mode D a s (-2) (mode D a s (-2) (vacuum D))) +
        (93 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) -
        (264 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) -
        (108 : ℂ) • mode D a s (-6) (vacuum D)) =
      (5 : ℂ) • ((12288 : ℂ) • mode D a s (-2)
        (mode D a s (-2) (mode D a s (-2) (vacuum D)))) +
      (31 : ℂ) • ((2880 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D))) -
      (22 : ℂ) • ((11520 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D))) -
      (1080 : ℂ) • ((96 : ℂ) • mode D a s (-6) (vacuum D)) := by module
    _ = (15 : ℂ) • V222 D a s + (31 : ℂ) • V33 D a s -
        (22 : ℂ) • V42 D a s - (1080 : ℂ) • V6 D a s := by
      rw [weight_six_triple D a ha s hs, weight_six_pair_three D a ha s hs,
        weight_six_pair_four_two D a ha s hs, weight_six_single D a ha s hs]
      module
    _ = 0 := coefficient_cancellation D a s

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull
