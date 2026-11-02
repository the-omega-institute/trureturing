/- GID: D5/S3/Quantum/SpinChains/DiamondSingletExclusion
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/DiamondSingletExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual four-spin diamond carrier and its total-weight restriction. -/

import D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment

/-! The coefficient-one diamond on four complete normalized spin factors. -/

noncomputable section
open scoped BigOperators Matrix Kronecker
open Matrix Complex
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)
open D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation (siteOperator)
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (raising_entry)

namespace D5.S3.Quantum.SpinChains.DiamondSingletExclusion

abbrev Weight (S : ℕ) := Fin (2 * S + 1)
abbrev Configuration (S : ℕ) := Fin 4 → Weight S
abbrev Operator (S : ℕ) := Matrix (Configuration S) (Configuration S) ℂ
abbrev State (S : ℕ) := EuclideanSpace ℂ (Configuration S)

def site (S : ℕ) (i : Fin 4) (A : Matrix (Weight S) (Weight S) ℂ) : Operator S :=
  siteOperator (fun _ : Fin 4 => 2 * S) i A

def raising (S : ℕ) (i : Fin 4) : Operator S := site S i (Jplus (2 * S))
def lowering (S : ℕ) (i : Fin 4) : Operator S := site S i (Jplus (2 * S))ᴴ

def edges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)}

def hamiltonian (S : ℕ) : Operator S :=
  ∑ e ∈ edges, (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2)

def totalRaising (S : ℕ) : Operator S := ∑ i : Fin 4, raising S i
def totalLowering (S : ℕ) : Operator S := ∑ i : Fin 4, lowering S i

def totalWeight (S : ℕ) : Operator S := ∑ i : Fin 4, site S i (Jz (2 * S))

def singletSpace (S : ℕ) : Submodule ℂ (Configuration S → ℂ) :=
  LinearMap.ker (Matrix.toLin' (totalRaising S)) ⊓
    LinearMap.ker (Matrix.toLin' (totalLowering S))

def zeroWeightSpace (S : ℕ) : Submodule ℂ (Configuration S → ℂ) :=
  LinearMap.ker (Matrix.toLin' (totalWeight S))

abbrev ZeroConfiguration (S : ℕ) := {x : Configuration S // ∑ i : Fin 4, (x i).val = 4 * S}

def restrictedHamiltonian (S : ℕ) : Matrix (ZeroConfiguration S) (ZeroConfiguration S) ℂ :=
  (hamiltonian S).submatrix Subtype.val Subtype.val

def groundEnergy (S : ℕ) : ℝ := sInf (spectrum ℝ (restrictedHamiltonian S))

def groundSpace (S : ℕ) : Submodule ℂ (Configuration S → ℂ) :=
  LinearMap.ker (Matrix.toLin' (hamiltonian S - (groundEnergy S : ℂ) • 1)) ⊓
    zeroWeightSpace S

def singletLowerBound (S : ℕ) : ℝ := -4 * (S : ℝ) ^ 2 - 8 / 3 * S

def claim : Prop := ∀ S : ℕ, 1 ≤ S →
  (∀ v : State S, v.ofLp ∈ singletSpace S → ‖v‖ = 1 →
    singletLowerBound S ≤ (star v.ofLp ⬝ᵥ (hamiltonian S *ᵥ v.ofLp)).re) ∧
  groundEnergy S < singletLowerBound S ∧
  groundSpace S ⊓ singletSpace S = ⊥

private lemma site_action (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ) (x : Configuration S) :
    (site S i A *ᵥ v) x = ∑ a : Weight S, A (x i) a * v (Function.update x i a) := by
  let e := Equiv.funSplitAt i (Weight S)
  have he (a : Weight S) :
      e.symm (a, fun j => x j.val) = Function.update x i a := by
    funext j
    by_cases hj : j = i <;> simp [e, Equiv.funSplitAt_symm_apply, hj]
  have hk (a : Weight S) (z : {j : Fin 4 // j ≠ i} → Weight S) :
      site S i A x (e.symm (a, z)) =
        A (x i) a * (if (fun j : {j : Fin 4 // j ≠ i} => x j.val) = z then 1 else 0) := by
    have hp : (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        if x j = e.symm (a, z) j then (1 : ℂ) else 0) =
        if (fun j : {j : Fin 4 // j ≠ i} => x j.val) = z then 1 else 0 := by
      simp only [Finset.prod_boole]
      congr 1
      apply propext
      constructor
      · intro h
        funext j
        have hj := h j.val (by simp [j.property])
        simpa [e, Equiv.funSplitAt_symm_apply, j.property] using hj
      · intro h j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hh := congrFun h ⟨j, hji⟩
        simpa [e, Equiv.funSplitAt_symm_apply, hji] using hh
    unfold site siteOperator
    rw [hp]
    congr 1
    simp [e, Equiv.funSplitAt_symm_apply]
  change (∑ y : Configuration S, site S i A x y * v y) = _
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, hk, ite_mul, mul_ite, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]

private lemma site_commute (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A B : Matrix (Weight S) (Weight S) ℂ) :
    site S i A * site S j B = site S j B * site S i A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, site_action]
  simp only [Function.update_of_ne hij, Function.update_of_ne hij.symm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Function.update_comm hij]
  ring

private lemma site_adjoint (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) :
    (site S i A)ᴴ = site S i Aᴴ := by
  ext x y
  simp [site, siteOperator, Matrix.conjTranspose_apply, eq_comm]

private lemma edge_hermitian (S : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    (raising S i * lowering S j + lowering S i * raising S j).IsHermitian := by
  change (_ + _)ᴴ = _
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, raising, lowering,
    site_adjoint, Matrix.conjTranspose_conjTranspose]
  rw [site_commute S j i hij.symm, site_commute S j i hij.symm, add_comm]

theorem hamiltonian_hermitian (S : ℕ) : (hamiltonian S).IsHermitian := by
  unfold hamiltonian
  apply isSelfAdjoint_sum
  intro e he
  apply edge_hermitian
  simp only [edges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

theorem restricted_hermitian (S : ℕ) : (restrictedHamiltonian S).IsHermitian :=
  (hamiltonian_hermitian S).submatrix Subtype.val

private lemma site_mul (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ) :
    site S i (A * B) = site S i A * site S i B := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, site_action, Matrix.mul_apply,
    Function.update_self, Function.update_idem]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private lemma site_sub (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ) :
    site S i (A - B) = site S i A - site S i B := by
  ext x y
  simp [site, siteOperator, sub_mul]

private lemma site_smul (S : ℕ) (i : Fin 4) (c : ℂ)
    (A : Matrix (Weight S) (Weight S) ℂ) :
    site S i (c • A) = c • site S i A := by
  ext x y
  simp [site, siteOperator, mul_assoc]

private lemma raising_times_lowering (n : ℕ) :
    Jplus n * (Jplus n)ᴴ = diagonal (fun i : Fin (n + 1) =>
      ((((i.val : ℝ) + 1) * ((n : ℝ) - i.val) : ℝ) : ℂ)) := by
  ext i j
  by_cases hi : i.val < n
  · let k : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · by_cases hij : i = j
      · subst j
        simp only [Matrix.conjTranspose_apply, raising_entry,
          show i.val + 1 = k.val from rfl, ite_true, Complex.star_def,
          Complex.conj_ofReal, diagonal_apply_eq]
        rw [← Complex.ofReal_mul]
        congr 1
        have hk : (k.val : ℝ) = (i.val : ℝ) + 1 := by dsimp [k]; push_cast; rfl
        rw [hk]
        have hn : 0 ≤ (n : ℝ) - i.val := sub_nonneg.mpr (by exact_mod_cast hi.le)
        rw [show ((i.val : ℝ) + 1) * ((n : ℝ) + 1 - ((i.val : ℝ) + 1)) =
          ((i.val : ℝ) + 1) * ((n : ℝ) - i.val) by ring]
        exact Real.mul_self_sqrt (mul_nonneg (by positivity) hn)
      · have hj : ¬j.val + 1 = k.val := by
          intro h
          apply hij
          apply Fin.ext
          dsimp [k] at h
          omega
        simp [Matrix.conjTranspose_apply, raising_entry, hj, diagonal_apply_ne _ hij]
    · intro a _ ha
      have hia : ¬i.val + 1 = a.val := by
        intro h
        apply ha
        apply Fin.ext
        exact h.symm
      simp [raising_entry, hia]
    · simp
  · have hin : i.val = n := by have := i.isLt; omega
    rw [Matrix.mul_apply]
    have hz : ∀ k : Fin (n + 1), Jplus n i k = 0 := by
      intro k
      rw [raising_entry, ite_eq_right (by have := k.isLt; omega)]
    simp only [hz, zero_mul, Finset.sum_const_zero]
    by_cases hij : i = j
    · subst j
      simp [diagonal_apply_eq, hin]
    · simp [diagonal_apply_ne _ hij]

private lemma lowering_times_raising (n : ℕ) :
    (Jplus n)ᴴ * Jplus n = diagonal (fun i : Fin (n + 1) =>
      (((i.val : ℝ) * ((n : ℝ) + 1 - i.val) : ℝ) : ℂ)) := by
  ext i j
  by_cases hi : 0 < i.val
  · let k : Fin (n + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hki : k.val + 1 = i.val := by dsimp [k]; omega
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · by_cases hij : i = j
      · subst j
        simp only [Matrix.conjTranspose_apply, raising_entry, hki, ite_true,
          Complex.star_def, Complex.conj_ofReal, diagonal_apply_eq]
        rw [← Complex.ofReal_mul]
        congr 1
        apply Real.mul_self_sqrt
        apply mul_nonneg (by positivity)
        have hle : (i.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
        linarith
      · have hj : ¬k.val + 1 = j.val := by
          intro h
          exact hij (Fin.ext (hki.symm.trans h))
        simp [Matrix.conjTranspose_apply, raising_entry, hj, diagonal_apply_ne _ hij]
    · intro a _ ha
      have hai : ¬a.val + 1 = i.val := by
        intro h
        apply ha
        apply Fin.ext
        dsimp [k]
        omega
      simp [Matrix.conjTranspose_apply, raising_entry, hai]
    · simp
  · have hiz : i.val = 0 := by omega
    rw [Matrix.mul_apply]
    have hz : ∀ k : Fin (n + 1), (Jplus n)ᴴ i k = 0 := by
      intro k
      simp [Matrix.conjTranspose_apply, raising_entry, hiz]
    simp only [hz, zero_mul, Finset.sum_const_zero]
    by_cases hij : i = j
    · subst j
      simp [diagonal_apply_eq, hiz]
    · simp [diagonal_apply_ne _ hij]

private lemma ladder_commutator (n : ℕ) :
    Jplus n * (Jplus n)ᴴ - (Jplus n)ᴴ * Jplus n = (2 : ℂ) • Jz n := by
  rw [raising_times_lowering, lowering_times_raising]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, diagonal_apply_eq, Jz, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · simp [Jz, hij]

private lemma total_ladder_commutator (S : ℕ) :
    totalRaising S * totalLowering S - totalLowering S * totalRaising S =
      (2 : ℂ) • totalWeight S := by
  unfold totalRaising totalLowering totalWeight
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => lhs; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have hrow (i : Fin 4) :
      (∑ j : Fin 4, (raising S i * lowering S j - lowering S j * raising S i)) =
      (2 : ℂ) • site S i (Jz (2 * S)) := by
    rw [Finset.sum_eq_single i]
    · simp only [raising, lowering, ← site_mul, ← site_sub, ladder_commutator, site_smul]
    · intro j _ hji
      exact sub_eq_zero.mpr (site_commute S i j hji.symm _ _)
    · simp
  simp_rw [hrow]
  rw [Finset.smul_sum]

theorem singlet_has_zero_weight (S : ℕ) : singletSpace S ≤ zeroWeightSpace S := by
  intro v hv
  rcases hv with ⟨hp, hm⟩
  change totalRaising S *ᵥ v = 0 at hp
  change totalLowering S *ᵥ v = 0 at hm
  change totalWeight S *ᵥ v = 0
  have h := congrArg (fun A : Operator S => A *ᵥ v) (total_ladder_commutator S)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hp, hm,
    Matrix.mulVec_zero, sub_self, Matrix.smul_mulVec] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num)

private lemma site_diagonal (S : ℕ) (i : Fin 4) (d : Weight S → ℂ) :
    site S i (diagonal d) = diagonal (fun x : Configuration S => d (x i)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [site, siteOperator]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hi : x i = y i
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
      have hji : j ≠ i := by intro h; subst j; exact hj hi
      have hz : (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          if x j = y j then (1 : ℂ) else 0) = 0 := by
        apply Finset.prod_eq_zero_iff.mpr
        exact ⟨j, by simp [hji], by simp [hj]⟩
      simp [site, siteOperator, hz]
    · simp [site, siteOperator, Matrix.diagonal_apply_ne _ hi]

private lemma total_weight_diagonal (S : ℕ) :
    totalWeight S = diagonal (fun x : Configuration S =>
      (4 * S : ℂ) - (∑ i : Fin 4, (x i).val : ℕ)) := by
  unfold totalWeight
  simp only [Jz, site_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Complex.ofReal_sum, ← Nat.cast_sum]
    push_cast
    ring
  · simp [Matrix.sum_apply, hxy]

theorem zero_weight_coordinates (S : ℕ) (v : Configuration S → ℂ) :
    v ∈ zeroWeightSpace S ↔
      ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → v x = 0 := by
  change totalWeight S *ᵥ v = 0 ↔ _
  rw [total_weight_diagonal]
  simp only [Matrix.mulVec_diagonal, funext_iff, Pi.zero_apply]
  constructor
  · intro h x hx
    have hn : (4 * S : ℂ) - (∑ i : Fin 4, (x i).val : ℕ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hx.symm
    exact (mul_eq_zero.mp (h x)).resolve_left hn
  · intro h x
    by_cases hx : (∑ i : Fin 4, (x i).val) = 4 * S
    · simp [hx]
    · rw [h x hx, mul_zero]

def middleConfiguration (S : ℕ) : Configuration S := fun _ => ⟨S, by omega⟩

instance (S : ℕ) : Nonempty (ZeroConfiguration S) :=
  ⟨⟨middleConfiguration S, by simp [middleConfiguration]⟩⟩

theorem zero_weight_nonzero (S : ℕ) : zeroWeightSpace S ≠ ⊥ := by
  intro h
  have hv : (Pi.single (middleConfiguration S) (1 : ℂ)) ∈ zeroWeightSpace S := by
    rw [zero_weight_coordinates]
    intro x hx
    have hxm : x ≠ middleConfiguration S := by
      intro hxm
      subst x
      exact hx (by simp [middleConfiguration])
    simp [hxm]
  rw [h, Submodule.mem_bot] at hv
  have hv' := congrFun hv (middleConfiguration S)
  simp at hv'

private lemma local_weight_raising (n : ℕ) :
    Jz n * Jplus n - Jplus n * Jz n = Jplus n := by
  ext i j
  simp only [Matrix.sub_apply, Jz, Matrix.diagonal_mul, Matrix.mul_diagonal,
    raising_entry]
  by_cases hij : i.val + 1 = j.val
  · rw [if_pos hij]
    push_cast
    rw [show (j.val : ℂ) = (i.val : ℂ) + 1 by exact_mod_cast hij.symm]
    ring
  · simp [hij]

private lemma total_weight_raising (S : ℕ) (i : Fin 4) :
    totalWeight S * raising S i - raising S i * totalWeight S = raising S i := by
  unfold totalWeight
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [raising, ← site_mul, ← site_sub, local_weight_raising]
  · intro j _ hji
    exact sub_eq_zero.mpr (site_commute S j i hji _ _)
  · simp

private lemma total_weight_adjoint (S : ℕ) : (totalWeight S)ᴴ = totalWeight S := by
  rw [total_weight_diagonal]
  simp

private lemma total_weight_lowering (S : ℕ) (i : Fin 4) :
    totalWeight S * lowering S i - lowering S i * totalWeight S = -lowering S i := by
  have h := congrArg Matrix.conjTranspose (total_weight_raising S i)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, total_weight_adjoint,
    raising, site_adjoint] at h
  change lowering S i * totalWeight S - totalWeight S * lowering S i = lowering S i at h
  calc
    totalWeight S * lowering S i - lowering S i * totalWeight S =
        -(lowering S i * totalWeight S - totalWeight S * lowering S i) := by abel
    _ = -lowering S i := congrArg Neg.neg h

private lemma balanced_product {S : ℕ} (A B : Operator S)
    (hA : totalWeight S * A - A * totalWeight S = A)
    (hB : totalWeight S * B - B * totalWeight S = -B) :
    totalWeight S * (A * B) = (A * B) * totalWeight S := by
  have ha : totalWeight S * A = A * totalWeight S + A := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hA
  have hb : totalWeight S * B = B * totalWeight S - B := by
    have h := sub_eq_iff_eq_add.mp hB
    simpa only [sub_eq_add_neg, add_comm] using h
  calc
    totalWeight S * (A * B) = (totalWeight S * A) * B := (Matrix.mul_assoc ..).symm
    _ = (A * totalWeight S + A) * B := by rw [ha]
    _ = A * (totalWeight S * B) + A * B := by noncomm_ring
    _ = A * (B * totalWeight S - B) + A * B := by rw [hb]
    _ = (A * B) * totalWeight S := by noncomm_ring

theorem hamiltonian_preserves_weight (S : ℕ) :
    totalWeight S * hamiltonian S = hamiltonian S * totalWeight S := by
  unfold hamiltonian
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [balanced_product _ _ (total_weight_raising S e.1) (total_weight_lowering S e.2)]
  have hh := balanced_product (raising S e.2) (lowering S e.1)
    (total_weight_raising S e.2) (total_weight_lowering S e.1)
  have hij : e.1 ≠ e.2 := by
    simp only [edges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : lowering S e.1 * raising S e.2 = raising S e.2 * lowering S e.1 :=
    site_commute S e.1 e.2 hij _ _
  rw [hc, hh]

theorem zero_weight_invariant (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) : hamiltonian S *ᵥ v ∈ zeroWeightSpace S := by
  change totalWeight S *ᵥ v = 0 at hv
  change totalWeight S *ᵥ (hamiltonian S *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, hamiltonian_preserves_weight,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end D5.S3.Quantum.SpinChains.DiamondSingletExclusion
