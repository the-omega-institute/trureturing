/- GID: D5/S3/ContinuousObservables/CyclicCovariantUniversal
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/CyclicCovariantUniversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct continuous matrix-field representations of cyclic covariant pairs. -/

import D5.S3.ContinuousObservables.CentralWinding
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic.NoncommRing

namespace D5.S3.ContinuousObservables.CyclicCovariantUniversal

open scoped BigOperators Matrix.Norms.L2Operator CStarAlgebra
open CentralWinding

noncomputable section

variable {M : ℕ} [NeZero M]

/-- Continuous readouts on the finite discrete cycle. -/
abbrev CyclicReadout (M : ℕ) := C(ZMod M, ℂ)

/-- Translation by an integer retains the infinite acting group. -/
def cyclicAction (n : ℤ) : CyclicReadout M →⋆ₐ[ℂ] CyclicReadout M :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨fun i => i - (n : ZMod M), continuous_of_discreteTopology⟩

/-- The constant diagonal readout in the original continuous matrix carrier. -/
def cyclicReadout : CyclicReadout M →⋆ₐ[ℂ] CyclicObservable M where
  toFun f := ContinuousMap.const _ (Matrix.diagonal f)
  map_one' := by ext t i j; simp
  map_zero' := by ext t i j; simp
  map_add' f g := by ext t i j; by_cases hij : i = j <;> simp [hij]
  map_mul' f g := by ext t i j; by_cases hij : i = j <;> simp [hij]
  commutes' c := by ext t i j; by_cases hij : i = j <;> simp [hij]
  map_star' f := by ext t i j; by_cases hij : i = j <;> simp [hij, eq_comm]

private def delta (i : ZMod M) : CyclicReadout M :=
  ⟨fun j => if j = i then 1 else 0, continuous_of_discreteTopology⟩

private def coefficient (F : CyclicObservable M) (i j : ZMod M) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun t => F t i j, (continuous_apply_apply i j).comp F.continuous⟩

variable {B : Type*} [CStarAlgebra B]

private def spectrumCircle (u : unitary B) : C(spectrum ℂ (u : B), Circle) where
  toFun z := ⟨z.1, by
    change (z : ℂ) ∈ Metric.sphere 0 1
    apply mem_sphere_zero_iff_norm.mpr
    exact CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary u.prop z.prop)⟩
  continuous_toFun := by fun_prop

private def spectrumPhase (u : unitary B) : C(spectrum ℂ (u : B), AddCircle (1 : ℝ)) :=
  ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm :
    C(Circle, AddCircle (1 : ℝ))).comp (spectrumCircle u)

private def phaseCalculus (u : unitary B) : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] B :=
  (cfcHom (show IsStarNormal (u : B) from inferInstance)).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (spectrumPhase u))

private theorem phaseCalculus_coordinate (u : unitary B) :
    phaseCalculus u windingPhase = (u : B) := by
  change cfcHom _ (windingPhase.comp (spectrumPhase u)) = _
  convert cfcHom_id (show IsStarNormal (u : B) from inferInstance) using 1
  congr 1
  ext z
  change (AddCircle.toCircle
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm _) : ℂ) = z.1
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp only [Homeomorph.apply_symm_apply]
  rfl

private theorem phaseCalculus_commute (u : unitary B) (b : B)
    (h : Commute (u : B) b) (hs : Commute (star (u : B)) b)
    (f : C(AddCircle (1 : ℝ), ℂ)) : Commute (phaseCalculus u f) b :=
  h.cfcHom (show IsStarNormal (u : B) from inferInstance) hs _

/-- The covariance condition uses the given one-step orientation. -/
def CyclicCovariant (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B) : Prop :=
  ∀ f, (v : B) * π f * star (v : B) = π (cyclicAction 1 f)

omit [NeZero M] in
private theorem delta_star (i : ZMod M) : star (delta i) = delta i := by
  ext j
  simp [delta]

omit [NeZero M] in
private theorem delta_mul (i j : ZMod M) :
    delta i * delta j = if i = j then delta i else 0 := by
  by_cases hij : i = j
  · subst j; ext k; simp [delta]
  · rw [if_neg hij]; ext k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [delta]

private theorem delta_sum : (∑ i : ZMod M, delta i) = 1 := by
  ext j
  simp [delta]

omit [NeZero M] in
private theorem covariant_power (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (n : ℕ) (f : CyclicReadout M) :
    Unitary.conjStarAlgAut ℂ B (v ^ n) (π f) = π (cyclicAction n f) := by
  induction n with
  | zero =>
    simp only [pow_zero, map_one, StarAlgEquiv.one_apply]
    congr 1; ext i; simp [cyclicAction]
  | succ n ih =>
    rw [pow_succ', Unitary.conjStarAlgAut_mul_apply, ih]
    change (v : B) * π (cyclicAction n f) * star (v : B) = _
    rw [h]
    congr 1
    ext i
    simp [cyclicAction, sub_sub, add_comm]

private theorem conjugate_delta (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i : ZMod M) :
    (v : B) ^ i.val * π (delta 0) * star ((v : B) ^ i.val) = π (delta i) := by
  have hpow := covariant_power π v h i.val (delta 0)
  simp only [Unitary.conjStarAlgAut_apply, SubmonoidClass.coe_pow] at hpow
  rw [hpow]
  congr 1
  ext j
  simp [cyclicAction, delta, sub_eq_zero]

omit [NeZero M] in
private theorem winding_commutes_readout (π : CyclicReadout M →⋆ₐ[ℂ] B)
    (v : unitary B) (h : CyclicCovariant π v) (f : CyclicReadout M) :
    Commute ((v : B) ^ M) (π f) := by
  apply (commute_unitary_iff_star_right_conjugate
    ((unitary B).pow_mem v.prop M)).mpr
  have hpow := covariant_power π v h M f
  simp only [Unitary.conjStarAlgAut_apply, SubmonoidClass.coe_pow] at hpow
  convert hpow using 1
  congr 1; ext i; simp [cyclicAction]

private def targetUnit (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (i j : ZMod M) : B :=
  (v : B) ^ i.val * π (delta 0) * star ((v : B) ^ j.val)

omit [NeZero M] in
private theorem targetUnit_star (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (i j : ZMod M) : star (targetUnit π v i j) = targetUnit π v j i := by
  simp [targetUnit, star_mul, ← map_star, delta_star, mul_assoc]

private theorem targetUnit_diagonal (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i : ZMod M) : targetUnit π v i i = π (delta i) :=
  conjugate_delta π v h i

private theorem targetUnit_sum (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) : (∑ i : ZMod M, targetUnit π v i i) = 1 := by
  simp_rw [targetUnit_diagonal π v h, ← map_sum, delta_sum, map_one]

private def column (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B) (i : ZMod M) : B :=
  (v : B) ^ i.val * π (delta 0)

omit [NeZero M] in
private theorem column_initial (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (i : ZMod M) : star (column π v i) * column π v i = π (delta 0) := by
  have hunit := Unitary.star_mul_self_of_mem ((unitary B).pow_mem v.prop i.val)
  have hp : π (delta 0) * π (delta 0) = π (delta 0) := by
    rw [← map_mul, delta_mul]; simp
  simp only [column, star_mul, ← map_star, delta_star]
  calc
    π (delta 0) * star ((v : B) ^ i.val) * ((v : B) ^ i.val * π (delta 0)) =
      π (delta 0) * (star ((v : B) ^ i.val) * (v : B) ^ i.val) * π (delta 0) := by
        noncomm_ring
    _ = π (delta 0) := by rw [hunit, mul_one, hp]

omit [NeZero M] in
private theorem column_outer (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (i j : ZMod M) : column π v i * star (column π v j) = targetUnit π v i j := by
  have hp : π (delta 0) * π (delta 0) = π (delta 0) := by
    rw [← map_mul, delta_mul]; simp
  simp only [column, star_mul, ← map_star, delta_star, targetUnit]
  calc
    (v : B) ^ i.val * π (delta 0) * (π (delta 0) * star ((v : B) ^ j.val)) =
      (v : B) ^ i.val * (π (delta 0) * π (delta 0)) * star ((v : B) ^ j.val) := by
        noncomm_ring
    _ = _ := by rw [hp]

private theorem column_support (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i : ZMod M) : π (delta i) * column π v i = column π v i := by
  rw [← targetUnit_diagonal π v h, ← column_outer, mul_assoc, column_initial]
  simp only [column, mul_assoc, ← map_mul, delta_mul, if_true]

private theorem column_inner (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i j : ZMod M) :
    star (column π v i) * column π v j = if i = j then π (delta 0) else 0 := by
  by_cases hij : i = j
  · subst j; simp [column_initial]
  · have hleft : star (column π v i) * π (delta i) = star (column π v i) := by
      simpa only [star_mul, ← map_star, delta_star] using congrArg star (column_support π v h i)
    rw [if_neg hij]
    calc
      star (column π v i) * column π v j =
          (star (column π v i) * π (delta i)) * (π (delta j) * column π v j) := by
            rw [hleft, column_support π v h]
      _ = star (column π v i) * (π (delta i) * π (delta j)) * column π v j := by
            noncomm_ring
      _ = 0 := by rw [← map_mul, delta_mul, if_neg hij, map_zero, mul_zero, zero_mul]

private theorem targetUnit_mul (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i j k l : ZMod M) :
    targetUnit π v i j * targetUnit π v k l =
      if j = k then targetUnit π v i l else 0 := by
  rw [← column_outer, ← column_outer]
  calc
    (column π v i * star (column π v j)) * (column π v k * star (column π v l)) =
      column π v i * (star (column π v j) * column π v k) * star (column π v l) := by
        noncomm_ring
    _ = _ := by
      rw [column_inner π v h]
      split_ifs
      · have hp : column π v i * π (delta 0) = column π v i := by
          simp only [column, mul_assoc, ← map_mul, delta_mul, if_true]
        rw [hp, column_outer]
      · simp

omit [NeZero M] in
private theorem targetUnit_commute (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (i j : ZMod M) :
    Commute ((v : B) ^ M) (targetUnit π v i j) := by
  have hv : Commute ((v : B) ^ M) (v : B) := (Commute.refl (v : B)).pow_left M
  have hvstar : Commute ((v : B) ^ M) (star (v : B)) := by
    exact hv.units_inv_right (u := Unitary.toUnits v)
  exact ((hv.pow_right i.val).mul_right (winding_commutes_readout π v h _)).mul_right
    (by simpa only [star_pow] using hvstar.pow_right j.val)

omit [NeZero M] in
private theorem coefficient_commute (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (f : C(AddCircle (1 : ℝ), ℂ)) (i j : ZMod M) :
    Commute (phaseCalculus (v ^ M) f) (targetUnit π v i j) := by
  have hw := targetUnit_commute π v h i j
  apply phaseCalculus_commute _ _ hw
  exact hw.units_inv_left (u := Unitary.toUnits (v ^ M))

private def fieldEntries : CyclicObservable M →⋆ₐ[ℂ]
    Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ) where
  toFun F := coefficient F
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases hij : i = j <;> simp [coefficient, Matrix.one_apply, hij]
  map_add' F G := by ext i j t; rfl
  map_mul' F G := by
    ext i j t
    change (∑ k, F t i k * G t k j) = (∑ k, coefficient F i k * coefficient G k j) t
    simp [coefficient]
  commutes' c := by
    ext i j t
    by_cases hij : i = j <;> simp [coefficient, Matrix.algebraMap_eq_diagonal, hij]
  map_star' F := by ext i j t; rfl

private def matrixAssemblyLinear (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B) :
    Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ) →ₗ[ℂ] B :=
  Matrix.liftLinear ℂ fun i j =>
    (LinearMap.mulRight ℂ (targetUnit π v i j)).comp (phaseCalculus (v ^ M)).toLinearMap

private theorem matrixAssemblyLinear_apply (π : CyclicReadout M →⋆ₐ[ℂ] B)
    (v : unitary B) (F : Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ)) :
    matrixAssemblyLinear π v F =
      ∑ i, ∑ j, phaseCalculus (v ^ M) (F i j) * targetUnit π v i j := by
  rw [matrixAssemblyLinear, Matrix.liftLinear_apply]
  rfl

private theorem matrixAssembly_one (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) : matrixAssemblyLinear π v 1 = 1 := by
  simp [matrixAssemblyLinear_apply, Matrix.one_apply, targetUnit_sum π v h]

private theorem matrixAssembly_mul (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v)
    (F G : Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ)) :
    matrixAssemblyLinear π v (F * G) = matrixAssemblyLinear π v F * matrixAssemblyLinear π v G := by
  simp only [matrixAssemblyLinear_apply]
  symm
  calc
    (∑ i, ∑ j, phaseCalculus (v ^ M) (F i j) * targetUnit π v i j) *
        (∑ k, ∑ l, phaseCalculus (v ^ M) (G k l) * targetUnit π v k l) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (phaseCalculus (v ^ M) (F i j) * targetUnit π v i j) *
          (phaseCalculus (v ^ M) (G k l) * targetUnit π v k l) := by
            simp_rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l, if j = k then
        phaseCalculus (v ^ M) (F i j * G k l) * targetUnit π v i l else 0 := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      rw [mul_assoc, ← mul_assoc (targetUnit π v i j),
        (coefficient_commute π v h (G k l) i j).symm.eq]
      simp only [mul_assoc]
      rw [targetUnit_mul π v h]
      split_ifs <;> simp [map_mul, mul_assoc]
    _ = ∑ i, ∑ l, phaseCalculus (v ^ M) ((F * G) i l) * targetUnit π v i l := by
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq,
        Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul]
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm

private theorem matrixAssembly_star (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v)
    (F : Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ)) :
    matrixAssemblyLinear π v (star F) = star (matrixAssemblyLinear π v F) := by
  simp only [matrixAssemblyLinear_apply, star_sum, star_mul, targetUnit_star,
    Matrix.star_apply, map_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simpa only [map_star] using (coefficient_commute π v h (star (F i j)) j i).eq

private def matrixAssembly (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) :
    Matrix (ZMod M) (ZMod M) C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] B where
  toFun := matrixAssemblyLinear π v
  map_zero' := map_zero _
  map_one' := matrixAssembly_one π v h
  map_add' := map_add _
  map_mul' := matrixAssembly_mul π v h
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, matrixAssembly_one π v h,
      Algebra.algebraMap_eq_smul_one]
  map_star' := matrixAssembly_star π v h

/-- The integrated map on all continuous matrix fields, using the actual spectrum of `v^M`. -/
def cyclic_covariant_lift (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) : CyclicObservable M →⋆ₐ[ℂ] B :=
  (matrixAssembly π v h).comp fieldEntries

private theorem readout_expansion (f : CyclicReadout M) :
    (∑ i : ZMod M, f i • delta i) = f := by
  ext j
  simp [delta]

private theorem phaseCalculus_const (u : unitary B) (c : ℂ) :
    phaseCalculus u (ContinuousMap.const _ c) = algebraMap ℂ B c :=
  (phaseCalculus u).commutes c

/-- The integrated map preserves every continuous readout. -/
theorem cyclic_covariant_lift_readout (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (f : CyclicReadout M) :
    cyclic_covariant_lift π v h (cyclicReadout f) = π f := by
  change matrixAssemblyLinear π v (fieldEntries (cyclicReadout f)) = _
  rw [matrixAssemblyLinear_apply]
  have he (i j : ZMod M) : fieldEntries (cyclicReadout f) i j =
      if i = j then ContinuousMap.const _ (f i) else 0 := by
    ext t
    change Matrix.diagonal (f : ZMod M → ℂ) i j =
      (if i = j then ContinuousMap.const _ (f i) else 0) t
    by_cases hij : i = j <;> simp [hij]
  simp_rw [he, apply_ite, phaseCalculus_const, map_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, targetUnit_diagonal π v h]
  calc
    _ = π (∑ i : ZMod M, f i • delta i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [map_smul, Algebra.smul_def]
    _ = π f := by rw [readout_expansion]

private theorem shift_entry (t : AddCircle (1 : ℝ)) (i j : ZMod M) :
    windingShiftObservable M t i j =
      (if i = 0 then windingPhase t else 1) * (if i - 1 = j then 1 else 0) := by
  change (Matrix.diagonal (fun k : ZMod M => if k = 0 then windingPhase t else 1) *
    Equiv.Perm.permMatrix ℂ (Equiv.subRight (1 : ZMod M))) i j = _
  rw [Matrix.diagonal_mul]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]

private theorem successor_val (j : ZMod M) :
    (j + 1).val = if j + 1 = 0 then 0 else j.val + 1 := by
  have hjcast : j + 1 = ((j.val + 1 : ℕ) : ZMod M) := by simp
  by_cases hj : j + 1 = 0
  · simp [hj]
  · rw [if_neg hj, hjcast, ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have hjlt := j.val_lt
    by_contra hle
    have heq : j.val + 1 = M := by omega
    apply hj
    rw [hjcast, heq]; simp

private theorem wrap_val (j : ZMod M) (hj : j + 1 = 0) : j.val + 1 = M := by
  have hjcast : j + 1 = ((j.val + 1 : ℕ) : ZMod M) := by simp
  have hmod : (j.val + 1) % M = 0 := by
    rw [hjcast] at hj
    have hv := congrArg ZMod.val hj
    simpa only [ZMod.val_natCast, ZMod.val_zero] using hv
  have hjlt := j.val_lt
  have hn : ¬ j.val + 1 < M := by
    intro hh
    rw [Nat.mod_eq_of_lt hh] at hmod
    omega
  omega

private theorem targetUnit_step (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) (j : ZMod M) :
    (if j + 1 = 0 then (v : B) ^ M else 1) * targetUnit π v (j + 1) j =
      (v : B) * π (delta j) := by
  rw [← conjugate_delta π v h j]
  by_cases hj : j + 1 = 0
  · simp only [targetUnit, hj, if_true, ZMod.val_zero, pow_zero, one_mul]
    rw [show (v : B) ^ M = (v : B) ^ (j.val + 1) from congrArg _ (wrap_val j hj).symm, pow_succ']
    noncomm_ring
  · simp only [one_mul, targetUnit, successor_val, if_neg hj, pow_succ']
    noncomm_ring

/-- The given winding shift, including its wrap phase, maps to the prescribed unitary. -/
theorem cyclic_covariant_lift_update (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) :
    cyclic_covariant_lift π v h (windingShiftObservable M) = (v : B) := by
  change matrixAssemblyLinear π v (fieldEntries (windingShiftObservable M)) = _
  rw [matrixAssemblyLinear_apply, Finset.sum_comm]
  have he (i j : ZMod M) : fieldEntries (windingShiftObservable M) i j =
      if i = j + 1 then (if i = 0 then windingPhase else 1) else 0 := by
    ext t
    change windingShiftObservable M t i j =
      (if i = j + 1 then (if i = 0 then windingPhase else 1) else 0) t
    rw [shift_entry]
    by_cases hij : i = j + 1
    · subst i
      simp only [add_sub_cancel_right]
      split_ifs <;> simp
    · have hsub : i - 1 ≠ j := fun hh => hij (sub_eq_iff_eq_add.mp hh)
      simp [hij, hsub]
  simp_rw [he, apply_ite, map_one, map_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, phaseCalculus_coordinate,
    SubmonoidClass.coe_pow]
  simp_rw [← ite_mul, targetUnit_step π v h]
  rw [← Finset.mul_sum, ← map_sum, delta_sum, map_one, mul_one]

private def sourceShift : unitary (CyclicObservable M) :=
  ⟨windingShiftObservable M, winding_shift_unitary⟩

private theorem source_covariant : CyclicCovariant (cyclicReadout (M := M)) sourceShift := by
  intro f
  have hcomm : windingShiftObservable M * cyclicReadout f =
      cyclicReadout (cyclicAction 1 f) * windingShiftObservable M := by
    ext t i j
    change (windingShiftObservable M t * Matrix.diagonal f) i j =
      (Matrix.diagonal (cyclicAction 1 f) * windingShiftObservable M t) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, shift_entry]
    by_cases hij : i - 1 = j
    · subst j; simp [cyclicAction, mul_comm]
    · simp [hij]
  change windingShiftObservable M * cyclicReadout f * star (windingShiftObservable M) = _
  rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem winding_shift_unitary, mul_one]

private theorem readout_injective : Function.Injective (cyclicReadout (M := M)) := by
  intro f g h
  ext i
  simpa [cyclicReadout] using congrArg (fun F : CyclicObservable M => F 0 i i) h

private def constantUnit (i j : ZMod M) : CyclicObservable M :=
  ContinuousMap.const _ (Matrix.single i j 1)

private theorem shift_constant_column (k : ZMod M) (hk : k + 1 ≠ 0) :
    windingShiftObservable M * constantUnit k 0 = constantUnit (k + 1) 0 := by
  ext t i j
  change (windingShiftObservable M t * Matrix.single k (0 : ZMod M) (1 : ℂ)) i j =
    Matrix.single (k + 1) (0 : ZMod M) (1 : ℂ) i j
  by_cases hj : j = 0
  · subst j
    rw [Matrix.mul_single_apply_same, mul_one, shift_entry]
    by_cases hi : i = k + 1
    · subst i; simp [hk]
    · have hsub : i - 1 ≠ k := fun hh => hi (sub_eq_iff_eq_add.mp hh)
      simp [hsub, hi, Matrix.single, eq_comm]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
    simp [Matrix.single, hj, eq_comm]

private theorem source_column (n : ℕ) (hn : n < M) :
    windingShiftObservable M ^ n * cyclicReadout (delta 0) = constantUnit (n : ZMod M) 0 := by
  induction n with
  | zero =>
    ext t i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [constantUnit, cyclicReadout, delta, Matrix.single,
        Matrix.diagonal_apply, hi, hj, eq_comm]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih (by omega)]
    have hnz : (n : ZMod M) + 1 ≠ 0 := by
      intro hz
      have hncast : ((n + 1 : ℕ) : ZMod M) = 0 := by simpa using hz
      have hv := congrArg ZMod.val hncast
      rw [ZMod.val_natCast_of_lt hn, ZMod.val_zero] at hv
      omega
    simpa only [Nat.cast_succ] using shift_constant_column (n : ZMod M) hnz

private theorem sourceUnit_eq_constant (i j : ZMod M) :
    targetUnit cyclicReadout sourceShift i j = constantUnit i j := by
  rw [← column_outer]
  have hc (k : ZMod M) : column cyclicReadout sourceShift k = constantUnit k 0 := by
    simpa only [column, sourceShift, ZMod.natCast_zmod_val] using source_column k.val k.val_lt
  rw [hc, hc]
  ext t a b
  change (Matrix.single i (0 : ZMod M) (1 : ℂ) *
    star (Matrix.single j (0 : ZMod M) (1 : ℂ))) a b = _
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, constantUnit]

private def scalarField : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] CyclicObservable M where
  toFun := PhaseFunctionCenter.phaseScalarObservable
  map_zero' := by ext t i j; simp [PhaseFunctionCenter.phaseScalarObservable]
  map_one' := by ext t i j; simp [PhaseFunctionCenter.phaseScalarObservable]
  map_add' f g := by
    ext t i j; by_cases hij : i = j <;> simp [PhaseFunctionCenter.phaseScalarObservable, hij]
  map_mul' f g := by
    ext t i j; by_cases hij : i = j <;> simp [PhaseFunctionCenter.phaseScalarObservable, hij]
  commutes' c := by
    ext t i j; by_cases hij : i = j <;> simp [PhaseFunctionCenter.phaseScalarObservable, hij]
  map_star' f := by
    ext t i j; by_cases hij : i = j <;>
      simp [PhaseFunctionCenter.phaseScalarObservable, hij, eq_comm]

private theorem scalarField_coordinate : scalarField windingPhase = windingShiftObservable M ^ M :=
  winding_shift_pow_card.symm

private theorem field_reconstruction (F : CyclicObservable M) :
    F = ∑ i : ZMod M, ∑ j : ZMod M, scalarField (coefficient F i j) * constantUnit i j := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.sum_apply]
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  rw [Matrix.matrix_eq_sum_single (F t)]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  change Matrix.single i j (F t i j) = Matrix.scalar _ (F t i j) * Matrix.single i j 1
  ext a b
  simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.single]

private theorem phase_hom_ext (φ ψ : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] B)
    (h : φ windingPhase = ψ windingPhase) : φ = ψ := by
  let e := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).compStarAlgEquiv' ℂ ℂ
  let : CompactSpace (↑(Submonoid.unitSphere ℂ) : Set ℂ) :=
    inferInstanceAs (CompactSpace Circle)
  have he : φ.comp e.toStarAlgHom = ψ.comp e.toStarAlgHom := by
    apply ContinuousMap.starAlgHom_ext_map_X (map_continuous _) (map_continuous _)
    have hx : e ((Polynomial.toContinuousMapOnAlgHom
        (↑(Submonoid.unitSphere ℂ) : Set ℂ)) Polynomial.X) = windingPhase := by
      ext t
      change Polynomial.eval
        (↑((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) t) : ℂ)
        Polynomial.X = (t.toCircle : ℂ)
      rw [Polynomial.eval_X, AddCircle.homeomorphCircle_apply]
    change φ (e _) = ψ (e _)
    rw [hx, h]
  ext f
  obtain ⟨g, rfl⟩ := e.surjective f
  exact DFunLike.congr_fun he g

private theorem lift_unique (φ ψ : CyclicObservable M →⋆ₐ[ℂ] B)
    (hd : ∀ f, φ (cyclicReadout f) = ψ (cyclicReadout f))
    (hs : φ (windingShiftObservable M) = ψ (windingShiftObservable M)) : φ = ψ := by
  have hz : φ.comp scalarField = ψ.comp scalarField := by
    apply phase_hom_ext
    change φ (scalarField windingPhase) = ψ (scalarField windingPhase)
    rw [scalarField_coordinate, map_pow, map_pow, hs]
  have he (i j : ZMod M) : φ (constantUnit i j) = ψ (constantUnit i j) := by
    rw [← sourceUnit_eq_constant]
    simp only [targetUnit, sourceShift, map_mul, map_pow, map_star]
    rw [hd, hs]
  ext F
  rw [field_reconstruction F, map_sum, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [map_mul, map_mul, he]
  exact congrArg (· * ψ (constantUnit i j)) (DFunLike.congr_fun hz (coefficient F i j))

/-- Every cyclic covariant pair admits exactly one integrated unital complex star homomorphism. -/
theorem cyclic_covariant_universal_property (π : CyclicReadout M →⋆ₐ[ℂ] B) (v : unitary B)
    (h : CyclicCovariant π v) :
    ∃! L : CyclicObservable M →⋆ₐ[ℂ] B,
      (∀ f, L (cyclicReadout f) = π f) ∧ L (windingShiftObservable M) = (v : B) := by
  refine ⟨cyclic_covariant_lift π v h,
    ⟨cyclic_covariant_lift_readout π v h, cyclic_covariant_lift_update π v h⟩, ?_⟩
  intro L hL
  exact lift_unique L _ (fun f => (hL.1 f).trans (cyclic_covariant_lift_readout π v h f).symm)
    (hL.2.trans (cyclic_covariant_lift_update π v h).symm)

private theorem source_generates :
    (StarAlgebra.adjoin ℂ
      (Set.range (cyclicReadout (M := M)) ∪ {windingShiftObservable M})).topologicalClosure =
      ⊤ := by
  let S := StarAlgebra.adjoin ℂ
    (Set.range (cyclicReadout (M := M)) ∪ {windingShiftObservable M})
  let A := S.topologicalClosure
  let : IsClosed (A : Set (CyclicObservable M)) := S.isClosed_topologicalClosure
  let : CStarAlgebra A := StarSubalgebra.cstarAlgebra A
  have hd (f : CyclicReadout M) : cyclicReadout f ∈ A :=
    S.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨f, rfl⟩))
  have hs : windingShiftObservable M ∈ A :=
    S.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl))
  let π : CyclicReadout M →⋆ₐ[ℂ] A := cyclicReadout.codRestrict A hd
  let v : unitary A := ⟨⟨windingShiftObservable M, hs⟩, by
    apply Unitary.mem_iff.mpr
    constructor <;> apply Subtype.ext
    · exact Unitary.star_mul_self_of_mem winding_shift_unitary
    · exact Unitary.mul_star_self_of_mem winding_shift_unitary⟩
  have hc : CyclicCovariant π v := by
    intro f
    apply Subtype.ext
    exact source_covariant f
  obtain ⟨L, hL, _⟩ := cyclic_covariant_universal_property π v hc
  have he : A.subtype.comp L = StarAlgHom.id ℂ (CyclicObservable M) := by
    apply lift_unique
    · intro f
      change (L (cyclicReadout f) : CyclicObservable M) = cyclicReadout f
      rw [hL.1]; rfl
    · change (L (windingShiftObservable M) : CyclicObservable M) = windingShiftObservable M
      rw [hL.2]
  apply top_unique
  intro F _
  have hh := (L F).prop
  have hv : (L F : CyclicObservable M) = F := DFunLike.congr_fun he F
  simpa only [hv] using hh

/-- The faithful readout and original unitary shift generate the entire closed star algebra. -/
theorem cyclic_covariant_model :
    Function.Injective (cyclicReadout (M := M)) ∧
      windingShiftObservable M ∈ unitary (CyclicObservable M) ∧
      (∀ f, windingShiftObservable M * cyclicReadout f * star (windingShiftObservable M) =
        cyclicReadout (cyclicAction 1 f)) ∧
      (StarAlgebra.adjoin ℂ
        (Set.range (cyclicReadout (M := M)) ∪ {windingShiftObservable M})).topologicalClosure =
        ⊤ :=
  ⟨readout_injective, winding_shift_unitary, source_covariant, source_generates⟩

/-- A separately universal covariant algebra has a unique generator-preserving star isometry.
Only its universal contracts at itself and at the concrete model are needed for comparison. -/
theorem cyclic_covariant_unique_isomorphism
    {A : Type*} [CStarAlgebra A] (ι : CyclicReadout M →⋆ₐ[ℂ] A) (u : unitary A)
    (hc : CyclicCovariant ι u)
    (hself : ∀ (π : CyclicReadout M →⋆ₐ[ℂ] A) (v : unitary A), CyclicCovariant π v →
      ∃! L : A →⋆ₐ[ℂ] A, (∀ f, L (ι f) = π f) ∧ L (u : A) = (v : A))
    (hmodel : ∀ (π : CyclicReadout M →⋆ₐ[ℂ] CyclicObservable M)
      (v : unitary (CyclicObservable M)), CyclicCovariant π v →
      ∃! L : A →⋆ₐ[ℂ] CyclicObservable M,
        (∀ f, L (ι f) = π f) ∧ L (u : A) = (v : CyclicObservable M)) :
    ∃! Φ : A ≃⋆ₐ[ℂ] CyclicObservable M,
      (∀ f, Φ (ι f) = cyclicReadout f) ∧
        Φ (u : A) = windingShiftObservable M ∧ Isometry Φ := by
  obtain ⟨F, hF, hFu⟩ := hmodel cyclicReadout sourceShift (cyclic_covariant_model.2.2.1)
  obtain ⟨G, hG, _⟩ := cyclic_covariant_universal_property ι u hc
  have hGF : G.comp F = StarAlgHom.id ℂ A := by
    obtain ⟨K, _, hK⟩ := hself ι u hc
    apply (hK _ ?_).trans (hK _ ?_).symm
    · constructor
      · intro f; change G (F (ι f)) = ι f; rw [hF.1, hG.1]
      · change G (F (u : A)) = (u : A); rw [hF.2]; exact hG.2
    · exact ⟨fun _ => rfl, rfl⟩
  have hFG : F.comp G = StarAlgHom.id ℂ (CyclicObservable M) := by
    apply lift_unique
    · intro f; change F (G (cyclicReadout f)) = cyclicReadout f; rw [hG.1, hF.1]
    · change F (G (windingShiftObservable M)) = windingShiftObservable M
      rw [hG.2]; exact hF.2
  let Φ := StarAlgEquiv.ofStarAlgHom F G hGF hFG
  refine ⟨Φ, ⟨hF.1, hF.2, StarAlgEquiv.isometry Φ⟩, ?_⟩
  intro Ψ hΨ
  have hΨF : Ψ.toStarAlgHom = F := hFu _ ⟨hΨ.1, hΨ.2.1⟩
  apply StarAlgEquiv.ext
  intro a
  exact DFunLike.congr_fun hΨF a

end

end D5.S3.ContinuousObservables.CyclicCovariantUniversal
