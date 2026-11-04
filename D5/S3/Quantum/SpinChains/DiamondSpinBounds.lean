/- GID: D5/S3/Quantum/SpinChains/DiamondSpinBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/DiamondSpinBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native equal-spin diamond identities and whole-carrier pair bounds. -/

import D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-! The coefficient-one diamond on four complete normalized spin factors. -/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix Complex
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)
open D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation (siteOperator)
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (raising_entry)

namespace D5.S3.Quantum.SpinChains.DiamondSpinBounds

abbrev Weight (S : ℕ) := Fin (2 * S + 1)
abbrev Configuration (S : ℕ) := Fin 4 → Weight S
abbrev Operator (S : ℕ) := Matrix (Configuration S) (Configuration S) ℂ
abbrev State (S : ℕ) := EuclideanSpace ℂ (Configuration S)

def site (S : ℕ) (i : Fin 4) (A : Matrix (Weight S) (Weight S) ℂ) : Operator S :=
  siteOperator (fun _ : Fin 4 => 2 * S) i A

def raising (S : ℕ) (i : Fin 4) : Operator S := site S i (Jplus (2 * S))
def lowering (S : ℕ) (i : Fin 4) : Operator S := site S i ((Jplus (2 * S))ᴴ)

def edges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)}

def hamiltonian (S : ℕ) : Operator S :=
  ∑ e ∈ edges, (2 : ℂ) •
    (site S e.1 (Jx (2 * S)) * site S e.2 (Jx (2 * S)) +
      site S e.1 (Jy (2 * S)) * site S e.2 (Jy (2 * S)))

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

private lemma site_add (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ) :
    site S i (A + B) = site S i A + site S i B := by
  ext x y
  simp [site, siteOperator, add_mul]


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


private lemma edge_cartesian (S : ℕ) (i j : Fin 4) :
    (2 : ℂ) • (site S i (Jx (2 * S)) * site S j (Jx (2 * S)) +
      site S i (Jy (2 * S)) * site S j (Jy (2 * S))) =
      raising S i * lowering S j + lowering S i * raising S j := by
  have hc : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp [Complex.I_sq]
  simp only [Jx, Jy, site_smul, site_add, site_sub, hc, raising, lowering,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

private lemma hamiltonian_ladder (S : ℕ) :
    hamiltonian S = ∑ e ∈ edges,
      (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2) := by
  unfold hamiltonian
  apply Finset.sum_congr rfl
  intro e _
  exact edge_cartesian S e.1 e.2

private lemma edge_hermitian (S : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    (raising S i * lowering S j + lowering S i * raising S j).IsHermitian := by
  change (_ + _)ᴴ = _
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, raising, lowering,
    site_adjoint, Matrix.conjTranspose_conjTranspose]
  rw [site_commute S j i hij.symm, site_commute S j i hij.symm, add_comm]

private theorem hamiltonian_hermitian (S : ℕ) : (hamiltonian S).IsHermitian := by
  rw [hamiltonian_ladder]
  apply isSelfAdjoint_sum
  intro e he
  apply edge_hermitian
  simp only [edges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem restricted_hermitian (S : ℕ) : (restrictedHamiltonian S).IsHermitian :=
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

private theorem singlet_has_zero_weight (S : ℕ) : singletSpace S ≤ zeroWeightSpace S := by
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

private theorem zero_weight_coordinates (S : ℕ) (v : Configuration S → ℂ) :
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

private lemma local_weight_raising (n : ℕ) :
    Jz n * Jplus n - Jplus n * Jz n = Jplus n := by
  ext i j
  simp only [Matrix.sub_apply, Jz, Matrix.diagonal_mul, Matrix.mul_diagonal,
    raising_entry]
  by_cases hij : i.val + 1 = j.val
  · rw [ite_eq_left hij]
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

private theorem hamiltonian_preserves_weight (S : ℕ) :
    totalWeight S * hamiltonian S = hamiltonian S * totalWeight S := by
  rw [hamiltonian_ladder]
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

private theorem zero_weight_invariant (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S) : hamiltonian S *ᵥ v ∈ zeroWeightSpace S := by
  change totalWeight S *ᵥ v = 0 at hv
  change totalWeight S *ᵥ (hamiltonian S *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, hamiltonian_preserves_weight,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private lemma positive_eigenvector_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℝ) (hA : (A.map Complex.ofReal).IsHermitian)
    (hpos : ∀ i j, 0 ≤ A i j) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℝ) (hr : 0 < r) (he : A *ᵥ w = r • w) :
    ((r : ℂ) • (1 : Matrix ι ι ℂ) - A.map Complex.ofReal).PosSemidef := by
  let B := (r : ℂ) • (1 : Matrix ι ι ℂ) - A.map Complex.ofReal
  have hB : B.IsHermitian := by
    change ((r : ℂ) • 1 - A.map Complex.ofReal)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hA.eq]
    rfl
  apply hB.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hB.eigenvalues i
  let v : ι → ℂ := (hB.eigenvectorBasis i).ofLp
  have hv : v ≠ 0 := by
    intro hv
    have hh := hB.eigenvectorBasis.orthonormal.ne_zero i
    apply hh
    exact (WithLp.ofLp_injective 2) hv
  have hev := hB.mulVec_eigenvectorBasis i
  have heA : (A.map (algebraMap ℝ ℂ)) *ᵥ v =
      ((r : ℂ) - (hB.eigenvalues i : ℂ)) • v := by
    change ((r : ℂ) • 1 - A.map Complex.ofReal) *ᵥ v = (hB.eigenvalues i : ℂ) • v at hev
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hev
    ext j
    have hj := congrFun hev j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    change (A.map Complex.ofReal *ᵥ v) j = _
    linear_combination -hj
  have habs := Matrix.eigenvalue_abs_subinvariant hpos heA
  have hnorm : (fun j => ‖v j‖) ≠ 0 := Matrix.normFun_complex_ne_zero_of_ne_zero hv
  have hle := Matrix.CollatzWielandt.le_of_subinvariant hpos
    (fun j => norm_nonneg (v j)) hnorm habs
  have hub := Matrix.CollatzWielandt.le_eigenvalue_of_right_eigenvector hpos hr hw he
    (fun j => norm_nonneg (v j)) hnorm
  have hh : |r - hB.eigenvalues i| ≤ r := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hle.trans hub
  have hh' := (abs_le.mp hh).2
  linarith

def z (S : ℕ) (i : Fin 4) : Operator S := site S i (Jz (2 * S))

def xy (S : ℕ) (i j : Fin 4) : Operator S :=
  raising S i * lowering S j + lowering S i * raising S j

def zz (S : ℕ) (i j : Fin 4) : Operator S := z S i * z S j

def dot (S : ℕ) (i j : Fin 4) : Operator S :=
  (1 / 2 : ℂ) • xy S i j + zz S i j

def isotropic (S : ℕ) : Operator S := ∑ e ∈ edges, dot S e.1 e.2

def vertical (S : ℕ) : Operator S := ∑ e ∈ edges, zz S e.1 e.2

def expect {S : ℕ} (v : Configuration S → ℂ) (A : Operator S) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)

private lemma expect_add {S : ℕ} (v : Configuration S → ℂ) (A B : Operator S) :
    expect v (A + B) = expect v A + expect v B := by
  simp [expect, Matrix.add_mulVec, dotProduct_add]

private lemma expect_sub {S : ℕ} (v : Configuration S → ℂ) (A B : Operator S) :
    expect v (A - B) = expect v A - expect v B := by
  simp [expect, Matrix.sub_mulVec, dotProduct_sub]

private lemma expect_smul {S : ℕ} (v : Configuration S → ℂ) (c : ℂ) (A : Operator S) :
    expect v (c • A) = c * expect v A := by
  simp [expect, Matrix.smul_mulVec, dotProduct_smul]

private lemma expect_sum {S : ℕ} {κ : Type*} (v : Configuration S → ℂ)
    (s : Finset κ) (A : κ → Operator S) :
    expect v (∑ k ∈ s, A k) = ∑ k ∈ s, expect v (A k) := by
  simp [expect, Matrix.sum_mulVec, dotProduct_sum]

private lemma singlet_commutator {S : ℕ} (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S) (U : Operator S) :
    expect v (totalLowering S * U - U * totalLowering S) = 0 := by
  rcases hv with ⟨hp, hm⟩
  change totalRaising S *ᵥ v = 0 at hp
  change totalLowering S *ᵥ v = 0 at hm
  have hstar : (totalLowering S)ᴴ = totalRaising S := by
    simp [totalLowering, totalRaising, lowering, raising, Matrix.conjTranspose_sum, site_adjoint]
  simp only [expect, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hm,
    Matrix.mulVec_zero, sub_zero]
  rw [dotProduct_mulVec]
  have hz : star v ᵥ* totalLowering S = 0 := by
    calc
      _ = star ((totalLowering S)ᴴ *ᵥ v) := by
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      _ = 0 := by rw [hstar, hp]; simp
  rw [hz, zero_dotProduct]

private lemma lowering_raising_commutator (S : ℕ) (i : Fin 4) :
    totalLowering S * raising S i - raising S i * totalLowering S =
      (-2 : ℂ) • z S i := by
  unfold totalLowering
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · have hh := congrArg (site S i) (ladder_commutator (2 * S))
    simp only [site_sub, site_mul, site_smul] at hh
    change lowering S i * raising S i - raising S i * lowering S i = _
    change raising S i * lowering S i - lowering S i * raising S i = (2 : ℂ) • z S i at hh
    calc
      _ = -(raising S i * lowering S i - lowering S i * raising S i) := by abel
      _ = _ := by rw [hh]; module
  · intro j _ hji
    exact sub_eq_zero.mpr (site_commute S j i hji _ _)
  · simp

private lemma lowering_z_commutator (S : ℕ) (i : Fin 4) :
    totalLowering S * z S i - z S i * totalLowering S = lowering S i := by
  unfold totalLowering
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · have h := congrArg Matrix.conjTranspose (local_weight_raising (2 * S))
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      show (Jz (2 * S))ᴴ = Jz (2 * S) from by simp [Jz]] at h
    simpa only [lowering, z, raising, ← site_mul, ← site_sub] using congrArg (site S i) h
  · intro j _ hji
    exact sub_eq_zero.mpr (site_commute S j i hji _ _)
  · simp

private lemma commutator_product {S : ℕ} (Q A B : Operator S) :
    Q * (A * B) - (A * B) * Q = (Q * A - A * Q) * B + A * (Q * B - B * Q) := by
  noncomm_ring

private lemma singlet_edge_isotropy (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S) (i j : Fin 4) :
    expect v (xy S i j) = 4 * expect v (zz S i j) := by
  have hh := singlet_commutator v hv (raising S i * z S j + z S i * raising S j)
  have hU : totalLowering S * (raising S i * z S j + z S i * raising S j) -
      (raising S i * z S j + z S i * raising S j) * totalLowering S =
      xy S i j - (4 : ℂ) • zz S i j := by
    rw [Matrix.mul_add, Matrix.add_mul]
    rw [show totalLowering S * (raising S i * z S j) +
        totalLowering S * (z S i * raising S j) -
        (raising S i * z S j * totalLowering S + z S i * raising S j * totalLowering S) =
        (totalLowering S * (raising S i * z S j) - raising S i * z S j * totalLowering S) +
        (totalLowering S * (z S i * raising S j) - z S i * raising S j * totalLowering S) by abel]
    rw [commutator_product, commutator_product, lowering_raising_commutator,
      lowering_z_commutator, lowering_raising_commutator, lowering_z_commutator]
    unfold xy zz
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [hU, expect_sub, expect_smul] at hh
  exact sub_eq_zero.mp hh

private lemma singlet_isotropy (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S) :
    expect v (hamiltonian S) = (4 / 3 : ℂ) * expect v (isotropic S) := by
  have h : expect v (hamiltonian S) = (4 : ℂ) * expect v (vertical S) := by
    rw [hamiltonian_ladder]
    unfold vertical
    rw [expect_sum, expect_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact singlet_edge_isotropy S v hv e.1 e.2
  have hi : expect v (isotropic S) =
      (1 / 2 : ℂ) * expect v (hamiltonian S) + expect v (vertical S) := by
    rw [hamiltonian_ladder]
    unfold isotropic vertical
    simp only [expect_sum, dot, expect_add, expect_smul, Finset.sum_add_distrib,
      xy]
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [hi]
  linear_combination (1 / 3 : ℂ) * h

private lemma positive_complex_eigenvector_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 ≤ A i j) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℝ) (hr : 0 < r) (he : A *ᵥ (fun i => (w i : ℂ)) = (r : ℂ) • (fun i => (w i : ℂ))) :
    ((r : ℂ) • (1 : Matrix ι ι ℂ) - A).PosSemidef := by
  have hm : (A.map Complex.re).map Complex.ofReal = A := by
    ext i j
    exact (Complex.eq_re_of_ofReal_le (hpos i j)).symm
  have he' : A.map Complex.re *ᵥ w = r • w := by
    ext i
    have hh := congrArg Complex.re (congrFun he i)
    simpa [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] using hh
  have hh := positive_eigenvector_bound (A.map Complex.re) (by rwa [hm])
    (fun i j => (hpos i j).1) w hw r hr he'
  rwa [hm] at hh

private def productVector (S : ℕ) (f : Weight S → ℂ) : Configuration S → ℂ :=
  fun x => ∏ i : Fin 4, f (x i)

private lemma product_update (S : ℕ) (f : Weight S → ℂ) (x : Configuration S)
    (i : Fin 4) (a : Weight S) :
    productVector S f (Function.update x i a) =
      f a * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, f (x j) := by
  unfold productVector
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

private lemma site_product (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (f : Weight S → ℂ) (x : Configuration S) :
    (site S i A *ᵥ productVector S f) x =
      (A *ᵥ f) (x i) * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, f (x j) := by
  rw [site_action]
  simp only [product_update, ← mul_assoc, ← Finset.sum_mul]
  rfl

def binomialProduct (S : ℕ) : Configuration S → ℂ :=
  productVector S (D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.binomVector (2 * S) 1)

def binomialProductReal (S : ℕ) : Configuration S → ℝ :=
  fun x => ∏ i : Fin 4,
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.spinRad (2 * S) (x i)

private lemma binomialProduct_real (S : ℕ) (x : Configuration S) :
    binomialProduct S x = (binomialProductReal S x : ℂ) := by
  simp [binomialProduct, productVector, binomialProductReal,
    D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.binomVector,
    D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.coeff]

private lemma binomialProduct_positive (S : ℕ) (x : Configuration S) :
    0 < binomialProductReal S x := by
  apply Finset.prod_pos
  intro i _
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (x i).isLt)

private lemma raising_product (S : ℕ) (i : Fin 4) (x : Configuration S) :
    (raising S i *ᵥ binomialProduct S) x =
      ((2 * S : ℂ) - (x i).val) * binomialProduct S x := by
  unfold raising binomialProduct
  rw [site_product, D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.raising_action]
  simp only [Complex.ofReal_one, mul_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_assoc]
  congr 1
  exact Finset.mul_prod_erase _ (fun j : Fin 4 =>
    D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.binomVector (2 * S) 1 (x j))
    (Finset.mem_univ i)

private lemma lowering_product (S : ℕ) (i : Fin 4) (x : Configuration S) :
    (lowering S i *ᵥ binomialProduct S) x =
      ((x i).val : ℂ) * binomialProduct S x := by
  unfold lowering binomialProduct
  rw [site_product]
  have hh := D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.lowering_action
    (2 * S) 1 (x i)
  simp only [Complex.ofReal_one, mul_one] at hh
  rw [hh, mul_assoc]
  congr 1
  exact Finset.mul_prod_erase _ (fun j : Fin 4 =>
    D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.binomVector (2 * S) 1 (x j))
    (Finset.mem_univ i)

private lemma site_spectator (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ)
    (c : Weight S → ℂ) (x : Configuration S) :
    (site S i A *ᵥ (fun y => c (y j) * v y)) x = c (x j) * (site S i A *ᵥ v) x := by
  simp only [site_action, Function.update_of_ne hij.symm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma z_action (S : ℕ) (i : Fin 4) (v : Configuration S → ℂ) (x : Configuration S) :
    (z S i *ᵥ v) x = ((S : ℂ) - (x i).val) * v x := by
  simp only [z, Jz, site_diagonal, Matrix.mulVec_diagonal]
  push_cast
  ring

private lemma dot_product_eigenvector (S : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    dot S i j *ᵥ binomialProduct S = ((S : ℂ) ^ 2) • binomialProduct S := by
  ext x
  simp only [dot, xy, zz, Matrix.add_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show lowering S j *ᵥ binomialProduct S =
      (fun y => ((y j).val : ℂ) * binomialProduct S y) by
        ext y
        exact lowering_product S j y]
  rw [show raising S j *ᵥ binomialProduct S =
      (fun y => ((2 * S : ℂ) - (y j).val) * binomialProduct S y) by
        ext y
        exact raising_product S j y]
  rw [show raising S i = site S i (Jplus (2 * S)) from rfl,
    show lowering S i = site S i ((Jplus (2 * S))ᴴ) from rfl]
  rw [site_spectator S i j hij (Jplus (2 * S)) (binomialProduct S)
      (fun a => (a.val : ℂ)) x,
    site_spectator S i j hij ((Jplus (2 * S))ᴴ) (binomialProduct S)
      (fun a => (2 * S : ℂ) - a.val) x]
  change (1 / 2 : ℂ) * (((x j).val : ℂ) * (raising S i *ᵥ binomialProduct S) x +
      ((2 * S : ℂ) - (x j).val) * (lowering S i *ᵥ binomialProduct S) x) + _ = _
  rw [raising_product, lowering_product, z_action, z_action]
  ring

private lemma raising_nonneg (S : ℕ) (i : Fin 4) (x y : Configuration S) :
    0 ≤ raising S i x y := by
  unfold raising site siteOperator
  apply mul_nonneg
  · rw [raising_entry]
    split_ifs <;> positivity
  · apply Finset.prod_nonneg
    intro j _
    split_ifs <;> norm_num

private lemma lowering_nonneg (S : ℕ) (i : Fin 4) (x y : Configuration S) :
    0 ≤ lowering S i x y := by
  have h : lowering S i = (raising S i)ᴴ := by simp [lowering, raising, site_adjoint]
  rw [h, Matrix.conjTranspose_apply]
  exact star_nonneg_iff.mpr (raising_nonneg S i y x)

private lemma xy_nonneg (S : ℕ) (i j : Fin 4) (x y : Configuration S) :
    0 ≤ xy S i j x y := by
  unfold xy
  simp only [Matrix.add_apply, Matrix.mul_apply]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (raising_nonneg S i x k) (lowering_nonneg S j k y)
  · apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (lowering_nonneg S i x k) (raising_nonneg S j k y)

private lemma z_diagonal (S : ℕ) (i : Fin 4) :
    z S i = diagonal (fun x : Configuration S => (S : ℂ) - (x i).val) := by
  simp only [z, Jz, site_diagonal]
  congr 1
  funext x
  push_cast
  ring

private lemma zz_shift_nonneg (S : ℕ) (i j : Fin 4) (x y : Configuration S) :
    0 ≤ (zz S i j + (S : ℂ)^2 • 1) x y := by
  simp only [zz, z_diagonal, Matrix.diagonal_mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one]
    have hi : (x i).val ≤ 2 * S := Nat.le_of_lt_succ (x i).isLt
    have hj : (x j).val ≤ 2 * S := Nat.le_of_lt_succ (x j).isLt
    have hi' : ((x i).val : ℝ) ≤ 2 * (S : ℝ) := by exact_mod_cast hi
    have hj' : ((x j).val : ℝ) ≤ 2 * (S : ℝ) := by exact_mod_cast hj
    have h : 0 ≤ ((S : ℝ) - (x i).val) * (S - (x j).val) + S^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hi') (sub_nonneg.mpr hj'),
        mul_nonneg (Nat.cast_nonneg (x i).val : (0 : ℝ) ≤ (x i).val)
          (Nat.cast_nonneg (x j).val : (0 : ℝ) ≤ (x j).val)]
    exact_mod_cast h
  · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]

private lemma dot_hermitian (S : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    (dot S i j).IsHermitian := by
  have hz (k : Fin 4) : (z S k)ᴴ = z S k := by simp [z_diagonal]
  have hzz : (zz S i j).IsHermitian := by
    change (z S i * z S j)ᴴ = _
    rw [Matrix.conjTranspose_mul, hz, hz]
    exact site_commute S j i hij.symm _ _
  exact ((edge_hermitian S i j hij).smul (by simp)).add hzz

private lemma pair_upper_bound (S : ℕ) (hS : 1 ≤ S) (i j : Fin 4) (hij : i ≠ j) :
    ((S : ℂ)^2 • (1 : Operator S) - dot S i j).PosSemidef := by
  let A := dot S i j + (S : ℂ)^2 • (1 : Operator S)
  have hA : A.IsHermitian := (dot_hermitian S i j hij).add
    ((isHermitian_one : (1 : Operator S).IsHermitian).smul ((IsSelfAdjoint.natCast S).pow 2))
  have hpos : ∀ x y, 0 ≤ A x y := by
    intro x y
    have h := add_nonneg (mul_nonneg (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)
      (xy_nonneg S i j x y)) (zz_shift_nonneg S i j x y)
    convert h using 1
    simp only [A, dot, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have he : A *ᵥ binomialProduct S = (2 * (S : ℂ)^2) • binomialProduct S := by
    dsimp [A]
    rw [Matrix.add_mulVec, dot_product_eigenvector S i j hij,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    module
  have he' : A *ᵥ (fun x => (binomialProductReal S x : ℂ)) =
      ((2 * (S : ℝ)^2 : ℝ) : ℂ) • (fun x => (binomialProductReal S x : ℂ)) := by
    simpa [← binomialProduct_real] using he
  have hr : 0 < 2 * (S : ℝ)^2 := by
    have hSp : (0 : ℝ) < S := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hS)
    positivity
  have hh := positive_complex_eigenvector_bound A hA hpos (binomialProductReal S)
    (binomialProduct_positive S) (2 * (S : ℝ)^2) hr he'
  convert hh using 1
  dsimp [A]
  module



/-- Native site, weight, ladder, singlet and pair-order relations on the full carrier. -/
theorem native_relations :
  (∀ (S : ℕ) (hS : 1 ≤ S) (i j : Fin 4) (hij : i ≠ j),
    ((S : ℂ)^2 • (1 : Operator S) - dot S i j).PosSemidef) ∧
  (∀ (S : ℕ) (x : Configuration S),
    0 < binomialProductReal S x) ∧
  (∀ (S : ℕ) (x : Configuration S),
    binomialProduct S x = (binomialProductReal S x : ℂ)) ∧
  (∀ {S : ℕ} (Q A B : Operator S),
    Q * (A * B) - (A * B) * Q = (Q * A - A * Q) * B + A * (Q * B - B * Q)) ∧
  (∀ (S : ℕ),
    hamiltonian S = ∑ e ∈ edges,
      (raising S e.1 * lowering S e.2 + lowering S e.1 * raising S e.2)) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (lowering S i *ᵥ binomialProduct S) x =
      ((x i).val : ℂ) * binomialProduct S x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * raising S i - raising S i * totalLowering S =
      (-2 : ℂ) • z S i) ∧
  (∀ (n : ℕ),
    (Jplus n)ᴴ * Jplus n = diagonal (fun i : Fin (n + 1) =>
      (((i.val : ℝ) * ((n : ℝ) + 1 - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ) (i : Fin 4),
    totalLowering S * z S i - z S i * totalLowering S = lowering S i) ∧
  (∀ (S : ℕ) (i : Fin 4) (x : Configuration S),
    (raising S i *ᵥ binomialProduct S) x =
      ((2 * S : ℂ) - (x i).val) * binomialProduct S x) ∧
  (∀ (n : ℕ),
    Jplus n * (Jplus n)ᴴ = diagonal (fun i : Fin (n + 1) =>
      ((((i.val : ℝ) + 1) * ((n : ℝ) - i.val) : ℝ) : ℂ))) ∧
  (∀ (S : ℕ),
    (restrictedHamiltonian S).IsHermitian) ∧
  (∀ (S : ℕ),
    singletSpace S ≤ zeroWeightSpace S) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ singletSpace S),
    expect v (hamiltonian S) = (4 / 3 : ℂ) * expect v (isotropic S)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ) (v : Configuration S → ℂ) (x : Configuration S),
    (site S i A *ᵥ v) x = ∑ a : Weight S, A (x i) a * v (Function.update x i a)) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A + B) = site S i A + site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A : Matrix (Weight S) (Weight S) ℂ),
    (site S i A)ᴴ = site S i Aᴴ) ∧
  (∀ (S : ℕ) (i j : Fin 4) (hij : i ≠ j)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i A * site S j B = site S j B * site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4)
    (A B : Matrix (Weight S) (Weight S) ℂ),
    site S i (A * B) = site S i A * site S i B) ∧
  (∀ (S : ℕ) (i : Fin 4) (c : ℂ)
    (A : Matrix (Weight S) (Weight S) ℂ),
    site S i (c • A) = c • site S i A) ∧
  (∀ (S : ℕ) (i : Fin 4) (v : Configuration S → ℂ) (x : Configuration S),
    (z S i *ᵥ v) x = ((S : ℂ) - (x i).val) * v x) ∧
  (∀ (S : ℕ) (i : Fin 4),
    z S i = diagonal (fun x : Configuration S => (S : ℂ) - (x i).val)) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ),
    v ∈ zeroWeightSpace S ↔
      ∀ x : Configuration S, (∑ i : Fin 4, (x i).val) ≠ 4 * S → v x = 0) ∧
  (∀ (S : ℕ) (v : Configuration S → ℂ)
    (hv : v ∈ zeroWeightSpace S),
    hamiltonian S *ᵥ v ∈ zeroWeightSpace S) := by
  exact ⟨pair_upper_bound, binomialProduct_positive, binomialProduct_real, commutator_product, hamiltonian_ladder, lowering_product, lowering_raising_commutator, lowering_times_raising, lowering_z_commutator, raising_product, raising_times_lowering, restricted_hermitian, singlet_has_zero_weight, singlet_isotropy, site_action, site_add, site_adjoint, site_commute, site_mul, site_smul, z_action, z_diagonal, zero_weight_coordinates, zero_weight_invariant⟩

end D5.S3.Quantum.SpinChains.DiamondSpinBounds
