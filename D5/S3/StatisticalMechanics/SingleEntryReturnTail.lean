/- GID: D5/S3/StatisticalMechanics/SingleEntryReturnTail
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntryReturnTail
   mirror-E: none(waiver:single-entry-return-tail)
   anchors: []
   utility: none
   digest: The secular derivative controls the positive slow return tail. -/

import D5.S3.StatisticalMechanics.SingleEntrySpectralGap
import D5.S3.StatisticalMechanics.SingleEntrySlowTail

/-! # The positive slow return current of the actual finite-site network -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Filter

namespace D5.S3.StatisticalMechanics.SingleEntryReturnTail
open SingleEntrySecularRoot SingleEntrySpectralGap

private def symmetricModes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) :
    Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ :=
  let d : Option (Finset ι) → ℝ
    | none => 0
    | some S => subsetRate k.a k.b S
  let v : Option (Finset ι) → ℝ
    | none => Real.sqrt k.theta
    | some S => -Real.sqrt k.eta * Real.sqrt (modeWeight k.a k.b S)
  diagonal d + vecMulVec v v

private def modeScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) : Option (Finset ι) → ℝ
  | none => 1
  | some S => Real.sqrt k.theta * Real.sqrt (modeWeight k.a k.b S) / Real.sqrt k.eta

private theorem modeScale_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (x : Option (Finset ι)) :
    0 < modeScale k x := by
  cases x with
  | none => norm_num [modeScale]
  | some S =>
    exact div_pos (mul_pos (Real.sqrt_pos.mpr k.theta_pos)
      (Real.sqrt_pos.mpr (weight_pos k.a k.b k.a_pos k.b_pos S)))
      (Real.sqrt_pos.mpr k.eta_pos)

private theorem symmetricModes_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) : (symmetricModes k).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.diagonal
    intro x
    cases x with
    | none => exact le_rfl
    | some S => exact Finset.sum_nonneg (fun i _ => (add_pos (k.a_pos i) (k.b_pos i)).le)
  · convert Matrix.posSemidef_vecMulVec_self_star
      (fun x : Option (Finset ι) => match x with
      | none => Real.sqrt k.theta
      | some S => -Real.sqrt k.eta * Real.sqrt (modeWeight k.a k.b S)) using 1

private theorem symmetricModes_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (x y : Option (Finset ι)) :
    symmetricModes k x y * modeScale k x =
      modeNegativeGenerator k.a k.b k.eta k.theta x y * modeScale k y := by
  have he : Real.sqrt k.eta ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr k.eta_pos)
  cases x with
  | none =>
    cases y with
    | none => simp [symmetricModes, modeScale, modeNegativeGenerator,
        diagonal, vecMulVec, Real.sq_sqrt k.theta_pos.le, ← pow_two]
    | some S =>
      simp [symmetricModes, modeScale, modeNegativeGenerator, diagonal, vecMulVec]
      field_simp [he]
      ring_nf
      simp only [Real.sq_sqrt k.eta_pos.le]
      <;> ring
  | some S =>
    have hW := weight_pos k.a k.b k.a_pos k.b_pos S
    cases y with
    | none =>
      simp [symmetricModes, modeScale, modeNegativeGenerator, diagonal, vecMulVec]
      field_simp [he]
      ring_nf
      simp only [Real.sq_sqrt hW.le, Real.sq_sqrt k.theta_pos.le]
      <;> ring
    | some T =>
      by_cases hST : S = T
      · subst T
        have hprod :
            (-Real.sqrt k.eta * Real.sqrt (modeWeight k.a k.b S)) *
              (-Real.sqrt k.eta * Real.sqrt (modeWeight k.a k.b S)) =
            k.eta * modeWeight k.a k.b S := by
          calc
            _ = Real.sqrt k.eta ^ 2 * Real.sqrt (modeWeight k.a k.b S) ^ 2 := by ring
            _ = _ := by rw [Real.sq_sqrt k.eta_pos.le, Real.sq_sqrt hW.le]
        simpa [symmetricModes, modeNegativeGenerator, diagonal, vecMulVec] using
          congrArg (fun z => (subsetRate k.a k.b S + z) * modeScale k (some S)) hprod
      · simp [symmetricModes, modeScale, modeNegativeGenerator, diagonal, vecMulVec, hST]
        field_simp [he]
        ring_nf
        simp only [pow_succ, Real.sq_sqrt hW.le, Real.sq_sqrt k.eta_pos.le]
        <;> ring

private theorem symmetricModes_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (v : Option (Finset ι) → ℝ) :
    modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ (fun x => modeScale k x * v x) =
      fun x => modeScale k x * (symmetricModes k *ᵥ v) x := by
  funext x
  simp only [mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (modeNegativeGenerator k.a k.b k.eta k.theta x y * modeScale k y) * v y := by ring
    _ = _ := by rw [← symmetricModes_scale k x y]; ring

private theorem symmetricModes_forward {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (p : ℝ → Option (Finset ι) → ℝ)
    (hp : SingleEntryFiniteNetwork.ForwardSolution k p) :
    let y := fun t x => (coordinateTransform k.a k.b *ᵥ p t) x / modeScale k x
    y 0 = Pi.single none 1 ∧
    ∀ t, 0 ≤ t → ∀ x, HasDerivAt (fun u => y u x) (-(symmetricModes k *ᵥ y t) x) t := by
  let T := coordinateTransform k.a k.b
  let y := fun t x => (T *ᵥ p t) x / modeScale k x
  change y 0 = Pi.single none 1 ∧ _
  have hd (x : Option (Finset ι)) : modeScale k x ≠ 0 := ne_of_gt (modeScale_pos k x)
  constructor
  · funext x
    cases x <;> simp [y, T, hp.1, coordinateTransform, mulVec, dotProduct,
      Fintype.sum_option, Pi.single_apply, modeScale]
  · intro t ht x
    have hm : T *ᵥ p t = fun z => modeScale k z * y t z := by
      funext z
      dsimp [y]
      field_simp [hd z]
    have hder := (HasDerivAt.fun_sum (u := Finset.univ)
      (fun z _ => (hp.2 t ht z).const_mul (T x z))).div_const (modeScale k x)
    change HasDerivAt (fun u => y u x) _ t at hder
    convert hder using 1
    change -(symmetricModes k *ᵥ y t) x =
      (T *ᵥ (SingleEntryFiniteNetwork.generator k *ᵥ p t)) x / modeScale k x
    rw [show T = coordinateTransform k.a k.b from rfl,
      transform_generator, Pi.neg_apply, hm, symmetricModes_mulVec]
    field_simp [hd x]

private theorem symmetric_eigen_to_mode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ) (u : Option (Finset ι) → ℝ)
    (hu : symmetricModes k *ᵥ u = l • u) :
    modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ (fun x => modeScale k x * u x) =
      l • (fun x => modeScale k x * u x) := by
  rw [symmetricModes_mulVec, hu]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem mode_eigen_to_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ) (m : Option (Finset ι) → ℝ)
    (hm : modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ m = l • m) :
    symmetricModes k *ᵥ (fun x => m x / modeScale k x) =
      l • (fun x => m x / modeScale k x) := by
  have hsc : (fun x => modeScale k x * (m x / modeScale k x)) = m := by
    funext x
    field_simp [ne_of_gt (modeScale_pos k x)]
  have hb := symmetricModes_mulVec k (fun x => m x / modeScale k x)
  rw [hsc, hm] at hb
  funext x
  have hh := congrFun hb x
  simp only [Pi.smul_apply, smul_eq_mul] at hh ⊢
  rw [← mul_div_assoc]
  apply (eq_div_iff (ne_of_gt (modeScale_pos k x))).mpr
  nlinarith [hh]

private def rootSymmetricMode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ) : Option (Finset ι) → ℝ
  | none => 1
  | some S => l * modeWeight k.a k.b S /
      ((subsetRate k.a k.b S - l) * modeScale k (some S))

private theorem rootSymmetric_eigenspace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ)
    (hpole : ∀ S : Finset ι, subsetRate k.a k.b S - l ≠ 0)
    (u : Option (Finset ι) → ℝ) (hu : symmetricModes k *ᵥ u = l • u) :
    ∀ x, u x = u none * rootSymmetricMode k l x := by
  have he := symmetric_eigen_to_mode k l u hu
  have hR := congrFun he none
  rw [action_none] at hR
  simp only [modeScale, Pi.smul_apply, smul_eq_mul, one_mul] at hR
  intro x
  cases x with
  | none => simp [rootSymmetricMode]
  | some S =>
    have hS := congrFun he (some S)
    rw [action_some] at hS
    simp only [modeScale, Pi.smul_apply, smul_eq_mul, one_mul] at hS
    dsimp [rootSymmetricMode]
    rw [← mul_div_assoc]
    apply (eq_div_iff (mul_ne_zero (hpole S)
      (ne_of_gt (modeScale_pos k (some S))))).mpr
    dsimp [modeScale]
    nlinarith [congrArg (fun t : ℝ => modeWeight k.a k.b S * t) hR]

private theorem rootSymmetric_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ)
    (hpole : ∀ S : Finset ι, subsetRate k.a k.b S - l ≠ 0)
    (hm : ∃ m : Option (Finset ι) → ℝ, m ≠ 0 ∧
      modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ m = l • m) :
    symmetricModes k *ᵥ rootSymmetricMode k l = l • rootSymmetricMode k l := by
  obtain ⟨m, hmn, hme⟩ := hm
  let u := fun x => m x / modeScale k x
  have hu : symmetricModes k *ᵥ u = l • u := mode_eigen_to_symmetric k l m hme
  have hspace := rootSymmetric_eigenspace k l hpole u hu
  have huR : u none ≠ 0 := by
    intro hz
    apply hmn
    funext x
    have hh := hspace x
    rw [hz, zero_mul] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right (ne_of_gt (modeScale_pos k x))
  have hueq : u = u none • rootSymmetricMode k l := by
    funext x
    exact hspace x
  rw [hueq, mulVec_smul] at hu
  funext x
  have hh := congrFun hu x
  simp only [Pi.smul_apply, smul_eq_mul] at hh ⊢
  exact mul_left_cancel₀ huR (by nlinarith [hh])

private theorem rootSymmetric_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ) (hl : l ≠ 0)
    (hpole : ∀ S : Finset ι, subsetRate k.a k.b S - l ≠ 0)
    (hF : secular k.a k.b k.eta k.theta l = 0) :
    k.theta * (∑ x, rootSymmetricMode k l x ^ 2) =
      -l * secularSlope k.a k.b k.eta l := by
  have hterm (S : Finset ι) : k.theta * rootSymmetricMode k l (some S) ^ 2 =
      k.eta * l ^ 2 * modeWeight k.a k.b S / (subsetRate k.a k.b S - l) ^ 2 := by
    have hW := weight_pos k.a k.b k.a_pos k.b_pos S
    have hd : modeScale k (some S) ^ 2 = k.theta * modeWeight k.a k.b S / k.eta := by
      simp only [modeScale, div_pow, mul_pow,
        Real.sq_sqrt k.theta_pos.le, Real.sq_sqrt k.eta_pos.le, Real.sq_sqrt hW.le]
    simp only [rootSymmetricMode, div_pow, mul_pow, hd]
    field_simp [ne_of_gt k.theta_pos, ne_of_gt k.eta_pos, ne_of_gt hW, hpole S]
    <;> ring
  have he : k.theta * rootSymmetricMode k l (some ∅) ^ 2 =
      k.eta * modeWeight k.a k.b ∅ := by
    rw [hterm]
    simp only [subsetRate, Finset.sum_empty, zero_sub, neg_sq]
    field_simp [hl]
  have hnonempty : ∀ S ∈ Finset.univ.erase (∅ : Finset ι),
      modeWeight k.a k.b S / (subsetRate k.a k.b S - l) +
        l * modeWeight k.a k.b S / (subsetRate k.a k.b S - l) ^ 2 =
      modeWeight k.a k.b S * subsetRate k.a k.b S /
        (subsetRate k.a k.b S - l) ^ 2 := by
    intro S _
    field_simp [hpole S]
    <;> ring
  have hsum := Finset.sum_congr rfl hnonempty
  rw [Finset.sum_add_distrib] at hsum
  have hroot : k.theta + k.eta * modeWeight k.a k.b ∅ =
      l + k.eta * l * (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        modeWeight k.a k.b S / (subsetRate k.a k.b S - l)) := by
    dsimp [secular] at hF
    linarith
  rw [Fintype.sum_option, mul_add, show rootSymmetricMode k l none = 1 from rfl]
  norm_num only [one_pow, mul_one]
  rw [Finset.mul_sum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset ι)), he]
  simp_rw [hterm]
  dsimp [secularSlope]
  have hscaled :
      (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        k.eta * l ^ 2 * modeWeight k.a k.b S / (subsetRate k.a k.b S - l) ^ 2) =
      k.eta * l * (∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        l * modeWeight k.a k.b S / (subsetRate k.a k.b S - l) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [hscaled]
  linear_combination hroot + k.eta * l * hsum

private theorem symmetric_projection_weight {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (o : V) (l : ℝ) (v : V → ℝ)
    (hvo : v o = 1) (hv : A *ᵥ v = l • v)
    (hsimple : ∀ u : V → ℝ, A *ᵥ u = l • u → ∀ i, u i = u o * v i) :
    (∑ j, if hA.1.eigenvalues j = l then
      (hA.1.eigenvectorUnitary : Matrix V V ℝ) o j ^ 2 else 0) * (∑ i, v i ^ 2) = 1 := by
  let U : Matrix V V ℝ := hA.1.eigenvectorUnitary
  let z : V → ℝ := fun j => ∑ i, U i j * v i
  have heig (j i : V) : (∑ k, A i k * U k j) = hA.1.eigenvalues j * U i j := by
    simpa [U, mulVec, dotProduct] using congrFun (hA.1.mulVec_eigenvectorBasis j) i
  have hsym (i k : V) : A i k = A k i := by
    have hh := congrFun (congrFun hA.1.eq k) i
    simpa using hh
  have horth (j : V) : (hA.1.eigenvalues j - l) * z j = 0 := by
    have hh := congrArg (fun w : V → ℝ => ∑ i, U i j * w i) hv
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hh
    have hleft : (∑ i, U i j * ∑ k, A i k * v k) =
        hA.1.eigenvalues j * z j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ k, (∑ i, A k i * U i j) * v k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [hsym i k]
          ring
        _ = _ := by
          simp_rw [heig]
          simp only [z, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    rw [hleft] at hh
    have hr : (∑ i, U i j * (l * v i)) = l * z j := by
      simp only [z, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hr] at hh
    nlinarith
  have hz (j : V) : z j = if hA.1.eigenvalues j = l then U o j * (∑ i, v i ^ 2) else 0 := by
    by_cases hj : hA.1.eigenvalues j = l
    · have he : A *ᵥ (fun i => U i j) = l • (fun i => U i j) := by
        simpa [U, hj] using hA.1.mulVec_eigenvectorBasis j
      have hs := hsimple _ he
      simp only [if_pos hj, z, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i]
      ring
    · rw [if_neg hj]
      exact (mul_eq_zero.mp (horth j)).resolve_left (sub_ne_zero.mpr hj)
  have hU : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have hrec := congrFun (mulVec_mulVec v U U.transpose) o
  rw [hU, one_mulVec] at hrec
  have hsum : (∑ j, U o j * z j) = 1 := by
    simpa only [mulVec, dotProduct, transpose_apply, z, hvo] using hrec
  rw [Finset.sum_mul]
  calc
    _ = ∑ j, U o j * z j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hz]
      split_ifs <;> ring
    _ = 1 := hsum

/-- A single least positive eigenvalue of the actual negative generator governs
the net entry current and every distinct site pair. Both exact secular tail
coefficients are positive. The initial law is the repressed point mass. -/
theorem finite_network_common_slow_tail {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (p : ℝ → Option (Finset ι) → ℝ)
    (hp : SingleEntryFiniteNetwork.ForwardSolution k p) :
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < siteRate k.a k.b i) ∧
      secular k.a k.b k.eta k.theta l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        (-SingleEntryFiniteNetwork.generator k) *ᵥ x = l • x) ∧
      (∀ μ : ℝ, 0 < μ →
        (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
          (-SingleEntryFiniteNetwork.generator k) *ᵥ x = μ • x) → l ≤ μ) ∧
      Tendsto (fun t => Real.exp (l * t) *
        (k.theta * p t none - k.eta * p t (some ∅))) atTop
        (nhds (-k.theta / secularSlope k.a k.b k.eta l)) ∧
      0 < -k.theta / secularSlope k.a k.b k.eta l ∧
      ∀ i j : ι, i ≠ j →
        Tendsto (fun t => Real.exp (l * t) * SingleEntryFiniteNetwork.association p i j t)
          atTop (nhds (-k.theta * (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅)) *
            occupancy k.a k.b i * occupancy k.a k.b j /
            ((siteRate k.a k.b i + siteRate k.a k.b j - l) * secularSlope k.a k.b k.eta l))) ∧
        0 < -k.theta * (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅)) *
          occupancy k.a k.b i * occupancy k.a k.b j /
          ((siteRate k.a k.b i + siteRate k.a k.b j - l) * secularSlope k.a k.b k.eta l) := by
  obtain ⟨l, hl, hupper, hF, hmode, hmin⟩ :=
    secular_root_least_mode_eigenvalue k.a k.b k.eta k.theta
      k.a_pos k.b_pos k.eta_pos k.theta_pos
  have hpole (S : Finset ι) : subsetRate k.a k.b S - l ≠ 0 := by
    by_cases hS : S = ∅
    · subst S
      simp [subsetRate, ne_of_gt hl]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hs : siteRate k.a k.b i ≤ subsetRate k.a k.b S :=
        Finset.single_le_sum (fun j _ => (add_pos (k.a_pos j) (k.b_pos j)).le) hi
      exact ne_of_gt (by linarith [hupper i])
  have hA := symmetricModes_pos k
  let A := symmetricModes k
  let U : Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ := hA.1.eigenvectorUnitary
  let lam := hA.1.eigenvalues
  let y := fun t x => (coordinateTransform k.a k.b *ᵥ p t) x / modeScale k x
  have hy := symmetricModes_forward k p hp
  have hdiag : 0 < A none none := by
    simpa [A, symmetricModes, diagonal, vecMulVec, ← pow_two,
      Real.sq_sqrt k.theta_pos.le] using k.theta_pos
  obtain ⟨ls, cs, hn, hsum, hpositive, hreturn, hdecr, L, hlim, hstat,
      hbindings, hfull⟩ :=
    SingleEntryFiveState.symmetric_return_data A hA none hdiag y hy.1 hy.2
  rcases hbindings with ⟨rfl, rfl⟩
  have hret (t : ℝ) : y t none = p t none := by
    simp [y, modeScale, coordinateTransform, mulVec, dotProduct, Fintype.sum_option]
  have hgen (t : ℝ) : (SingleEntryFiniteNetwork.generator k *ᵥ p t) none =
      -k.theta * p t none + k.eta * p t (some ∅) := by
    have hh := SingleEntryFiniteNetwork.dual_backward k (Pi.single none 1) (p t)
    simpa [SingleEntryFiniteNetwork.backward, Pi.single_apply, Fintype.sum_option] using hh
  have hcurrent (t : ℝ) (ht : 0 < t) :
      k.theta * p t none - k.eta * p t (some ∅) =
        ∑ j, lam j * U none j ^ 2 * Real.exp (-lam j * t) := by
    have hseries : HasDerivAt
        (fun u => ∑ j, U none j ^ 2 * Real.exp (-lam j * u))
        (∑ j, -(lam j * U none j ^ 2 * Real.exp (-lam j * t))) t := by
      apply HasDerivAt.fun_sum
      intro j _
      convert (((hasDerivAt_id t).const_mul (-lam j)).exp.const_mul (U none j ^ 2)) using 1
      all_goals (first | rfl | (dsimp; ring))
    have heq : (fun u => p u none) =ᶠ[nhds t]
        (fun u => ∑ j, U none j ^ 2 * Real.exp (-lam j * u)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) (fun u hu => by
        simpa only [hret, U, lam, A] using hreturn u hu.le)
    have hh := heq.deriv_eq
    rw [(hp.2 t ht.le none).deriv, hgen, hseries.deriv, Finset.sum_neg_distrib] at hh
    linarith
  have heig (j : Option (Finset ι)) : A *ᵥ (fun i => U i j) = lam j • (fun i => U i j) := by
    simpa [U, lam, A] using hA.1.mulVec_eigenvectorBasis j
  have hleast (j : Option (Finset ι)) (hj : 0 < lam j) : l ≤ lam j := by
    apply hmin _ hj
    refine ⟨fun x => modeScale k x * U x j, ?_, symmetric_eigen_to_mode k _ _ (heig j)⟩
    intro hz
    have hUzero : (fun x => U x j) = 0 := by
      funext x
      have hh := congrFun hz x
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt (modeScale_pos k x))
    have hne : (fun x => U x j) ≠ 0 := by
      simpa only [U, Matrix.IsHermitian.eigenvectorUnitary_apply] using
        (WithLp.ofLp_eq_zero 2).ne.2 (hA.1.eigenvectorBasis.orthonormal.ne_zero j)
    exact hne hUzero
  have hproj := symmetric_projection_weight A hA none l (rootSymmetricMode k l)
    rfl (rootSymmetric_eigen k l hpole hmode)
    (rootSymmetric_eigenspace k l hpole)
  have hnorm := rootSymmetric_norm k l (ne_of_gt hl) hpole hF
  let C := ∑ j, if lam j = l then U none j ^ 2 else 0
  have hCN : C * (∑ x, rootSymmetricMode k l x ^ 2) = 1 := hproj
  have hslope := ((secular_unique_root k.a k.b k.eta k.theta
    k.a_pos k.b_pos k.eta_pos k.theta_pos).2 l hl.le hupper).2
  have hcoefficient : l * C = -k.theta / secularSlope k.a k.b k.eta l := by
    apply (eq_div_iff (ne_of_lt hslope)).mpr
    have hn1 := congrArg (fun z : ℝ => C * z) hnorm
    have hn2 := congrArg (fun z : ℝ => k.theta * z) hCN
    nlinarith [hn1, hn2]
  have hterm (j : Option (Finset ι)) :
      Tendsto (fun t : ℝ => Real.exp (l * t) *
        (lam j * U none j ^ 2 * Real.exp (-lam j * t))) atTop
        (nhds (if lam j = l then l * U none j ^ 2 else 0)) := by
    by_cases hz : lam j = 0
    · simp [hz, ne_of_gt hl, ne_of_lt hl]
    · have hjpos : 0 < lam j := lt_of_le_of_ne (hA.eigenvalues_nonneg j) (Ne.symm hz)
      by_cases he : lam j = l
      · have heq (t : ℝ) : Real.exp (l * t) *
            (lam j * U none j ^ 2 * Real.exp (-lam j * t)) = l * U none j ^ 2 := by
          rw [he]
          calc
            _ = (l * U none j ^ 2) * (Real.exp (l * t) * Real.exp (-l * t)) := by ring
            _ = _ := by rw [← Real.exp_add]; simp
        simp_rw [heq, if_pos he]
        exact tendsto_const_nhds
      · have hlt : l < lam j := lt_of_le_of_ne (hleast j hjpos) (Ne.symm he)
        have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (sub_pos.mpr hlt))
        have heq (t : ℝ) : Real.exp (l * t) *
            (lam j * U none j ^ 2 * Real.exp (-lam j * t)) =
            (lam j * U none j ^ 2) * Real.exp (-((lam j - l) * t)) := by
          rw [show -((lam j - l) * t) = l * t + -lam j * t by ring, Real.exp_add]
          ring
        simp_rw [heq]
        simpa only [if_neg he, mul_zero, Function.comp_apply, id_eq] using hexp.const_mul (lam j * U none j ^ 2)
  have hsumlim := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  have hright : (∑ j, if lam j = l then l * U none j ^ 2 else 0) = l * C := by
    simp only [C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hright, hcoefficient] at hsumlim
  have hcurrentlim : Tendsto (fun t => Real.exp (l * t) *
      (k.theta * p t none - k.eta * p t (some ∅))) atTop
      (nhds (-k.theta / secularSlope k.a k.b k.eta l)) := by
    apply Tendsto.congr' _ hsumlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hcurrent t ht, Finset.mul_sum]
  obtain ⟨m, hm, hmupper, hmF, hmeigen, hmleast⟩ :=
    secular_root_least_generator_eigenvalue k
  have hml : m = l := by
    obtain ⟨c, hc, huniq⟩ := (secular_unique_root k.a k.b k.eta k.theta
      k.a_pos k.b_pos k.eta_pos k.theta_pos).1
    exact (huniq m ⟨hm, hmupper, hmF⟩).trans (huniq l ⟨hl, hupper, hF⟩).symm
  subst m
  refine ⟨l, hl, hupper, hF, hmeigen, hmleast, hcurrentlim,
    div_pos_of_neg_of_neg (neg_neg_of_pos k.theta_pos) hslope, ?_⟩
  intro i j hij
  obtain ⟨_, _, _, _, _, hD, _⟩ :=
    (SingleEntryFiniteNetwork.finite_network_strict_pair k).2 p hp i j hij 1 (by norm_num)
  have hK := (SingleEntrySlowTail.finite_network_equilibrium_moments k p hp i j hij).2
  have hslow : l < k.a i + k.b i + k.a j + k.b j := by
    have hjrate := add_pos (k.a_pos j) (k.b_pos j)
    dsimp [siteRate] at hupper
    linarith [hupper i]
  have hr : 0 < k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅) :=
    div_pos k.theta_pos (add_pos k.theta_pos
      (mul_pos k.eta_pos (weight_pos k.a k.b k.a_pos k.b_pos ∅)))
  have hqi := div_pos (k.a_pos i) (add_pos (k.a_pos i) (k.b_pos i))
  have hqj := div_pos (k.a_pos j) (add_pos (k.a_pos j) (k.b_pos j))
  simpa only [occupancy, siteRate, add_assoc] using
    SingleEntrySlowTail.association_tail_from_input_tail
      (SingleEntryFiniteNetwork.association p i j)
      (fun t => k.theta * p t none - k.eta * p t (some ∅))
      (SingleEntryFiniteNetwork.joint p i j)
      (k.a i + k.b i + k.a j + k.b j) l k.theta
      (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅))
      (k.a i / (k.a i + k.b i)) (k.a j / (k.a j + k.b j))
      (secularSlope k.a k.b k.eta l) hslow k.theta_pos hr hqi hqj hslope hD hcurrentlim hK

#print axioms finite_network_common_slow_tail

end D5.S3.StatisticalMechanics.SingleEntryReturnTail
