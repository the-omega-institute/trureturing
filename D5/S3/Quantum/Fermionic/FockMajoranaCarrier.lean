/- GID: D5/S3/Quantum/Fermionic/FockMajoranaCarrier
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/FockMajoranaCarrier
   mirror-E: none(waiver:general-fock-operator-relations)
   anchors: []
   utility: none
   digest: Occupation-space Majoranas satisfy Clifford relations, and the counted number operator exponentiates to number parity. -/

/-
majorana_clifford_and_parity:
  proof_shape: content
  escape_witness: majorana_clifford_and_parity (form 2): finite occupation-factor
    calculation proves annihilator nilpotence and reverses the counted occupation parity.
numberOperator_eq_diagonal:
  proof_shape: content
  escape_witness: numberOperator_eq_diagonal (form 2): the explicit occupation-factor
    calculation identifies the sum of Jordan–Wigner creation-annihilation products with
    the occupation-count diagonal.
numberParity_eq_diagonal:
  proof_shape: content
  escape_witness: numberParity_eq_diagonal (form 2): the same-delivery occupation-factor
    calculation of numberOperator, followed by the diagonal exponential, gives
    the occupation parity of the source operator power.
admission_basis: escape-witness
Same-delivery inlined content: local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR
    statement_id: sha256:91a39cca0cc0155aec0a40a8280d10bd356a0d091f81f8031b64299b1ade63de
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt
    statement_id: sha256:1db13273a320d9215f5583b5d1bcd5cf5cff7952171e37a663fc509057aaacd4
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt
    statement_id: sha256:eb93c9ae1da812ac8631c45850a4bd5f0d160da82cbfe9ad9d4377f14362f664
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
computational_content.kind: none; the theorem concerns arbitrary finite mode counts
  and exact operator relations rather than a fixed finite certificate.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

open Matrix
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

noncomputable section
namespace D5.S3.Quantum.Fermionic.FockMajoranaCarrier

def majorana {N : ℕ} (j : Fin N) (b : Bool) : FullOperator N :=
  if b then Complex.I • (fullC j - (fullC j)ᴴ) else fullC j + (fullC j)ᴴ

def numberOperator (N : ℕ) : FullOperator N :=
  ∑ j : Fin N, (fullC j)ᴴ * fullC j

def numberParity (N : ℕ) : FullOperator N :=
  NormedSpace.exp ((Real.pi * Complex.I) • numberOperator N)

theorem numberOperator_eq_diagonal (N : ℕ) :
    numberOperator N = Matrix.diagonal (fun s => (occupationCount s : ℂ)) := by
  classical
  have term_eq (j : Fin N) (s t : Assignment N) :
      ((fullC j)ᴴ * fullC j) s t = if s = t then if s j then 1 else 0 else 0 := by
    classical
    have entries (u v : Assignment N) : fullC j u v = ∏ k : Fin N,
        fermionWord j k (u k) (v k) := by
      simp [fullC, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    simp_rw [entries]
    simp only [star_prod]
    simp_rw [← Finset.prod_mul_distrib]
    change (∑ x : Assignment N, ∏ k : Fin N,
      star (fermionWord j k (x k) (s k)) * fermionWord j k (x k) (t k)) = _
    rw [(Fintype.prod_sum (fun (k : Fin N) (b : Bool) =>
      star (fermionWord j k b (s k)) * fermionWord j k b (t k))).symm]
    change (∏ k : Fin N, ∑ b : Bool,
      star (fermionWord j k b (s k)) * fermionWord j k b (t k)) = _
    have hlocal (k : Fin N) :
        (∑ b : Bool, star (fermionWord j k b (s k)) *
          fermionWord j k b (s k)) =
          if k = j then (if s k then 1 else 0) else 1 := by
      by_cases hkj : k = j
      · subst k
        cases hs : s j <;>
          norm_num [fermionWord, hs, Matrix.single, Fintype.sum_bool]
      · by_cases hlt : k < j
        · simp only [fermionWord, if_pos hlt, if_neg hkj]
          cases hs : s k <;>
            norm_num [D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv,
              Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply,
              Matrix.single, Matrix.one_apply, Fintype.sum_bool]
        · simp only [fermionWord, if_neg hlt, if_neg hkj]
          simp [Matrix.single, Matrix.one_apply, Fintype.sum_bool]
    by_cases hst : s = t
    · subst t
      simp only [if_pos rfl, if_true]
      simp_rw [hlocal]
      simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp only [if_neg hst]
      have hzero : ∃ k : Fin N, s k ≠ t k := by
        by_contra h
        push Not at h
        exact hst (funext h)
      obtain ⟨k, hk⟩ := hzero
      have hz : (∑ b : Bool,
          star (fermionWord j k b (s k)) * fermionWord j k b (t k)) = 0 := by
        by_cases hkj : k = j
        · subst k
          cases hs : s j <;> cases ht : t j <;>
            try { exfalso; apply hk; simp [hs, ht] }
          all_goals norm_num [fermionWord, hs, ht, Matrix.single, Matrix.one_apply,
            Fintype.sum_bool]
        · by_cases hlt : k < j
          · simp only [fermionWord, if_pos hlt]
            cases hs : s k <;> cases ht : t k <;>
              try { exfalso; apply hk; simp [hs, ht] }
            all_goals norm_num [D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv,
              Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply,
              Matrix.single, Matrix.one_apply, Fintype.sum_bool]
          · simp only [fermionWord, if_neg hlt, if_neg hkj]
            cases hs : s k <;> cases ht : t k <;>
              try { exfalso; apply hk; simp [hs, ht] }
            all_goals norm_num [Matrix.single, Matrix.one_apply, Fintype.sum_bool]
      exact Finset.prod_eq_zero (Finset.mem_univ k) hz
  ext s t
  simp only [numberOperator, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hst : s = t
  · subst t
    simp only [if_pos rfl]
    simp_rw [term_eq]
    have hcount (j : Fin N) : (if s j then (1 : ℂ) else 0) = ((s j).toNat : ℂ) := by
      cases s j <;> simp
    simp_rw [hcount]
    simp [occupationCount]
  · simp only [if_neg hst]
    have hterm (j : Fin N) : ((fullC j)ᴴ * fullC j) s t = 0 := by
      simpa [hst] using term_eq j s t
    simp_rw [hterm]
    simp

theorem numberParity_eq_diagonal (N : ℕ) :
    numberParity N = Matrix.diagonal (fun s => (-1 : ℂ) ^ occupationCount s) := by
  rw [numberParity, numberOperator_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  rw [Pi.exp_def]
  congr 1
  funext s
  change NormedSpace.exp ((Real.pi * Complex.I) * (occupationCount s : ℂ)) = _
  rw [← Complex.exp_eq_exp_ℂ]
  rw [show (Real.pi * Complex.I) * (occupationCount s : ℂ) =
      (occupationCount s : ℂ) * (Real.pi * Complex.I) by ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- The actual Jordan–Wigner matrices obey CAR and are odd for number parity. -/
theorem majorana_clifford_and_parity (N : ℕ) :
    (numberParity N).IsHermitian ∧
    numberParity N * numberParity N = 1 ∧
    (∀ p : Fin N × Bool, (majorana p.1 p.2).IsHermitian) ∧
    (∀ p q : Fin N × Bool,
      majorana p.1 p.2 * majorana q.1 q.2 +
        majorana q.1 q.2 * majorana p.1 p.2 =
          if p = q then (2 : ℂ) • (1 : FullOperator N) else 0) ∧
    (∀ p : Fin N × Bool,
      numberParity N * majorana p.1 p.2 + majorana p.1 p.2 * numberParity N = 0) := by
  classical
  have parity_diagonal (K : ℕ) : numberParity K = Matrix.diagonal
      (fun s => (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card) := by
    rw [numberParity_eq_diagonal]
    congr 1
    funext s
    congr 1
    unfold occupationCount
    have hbool (j : Fin K) : (s j).toNat = if s j = true then 1 else 0 := by
      cases s j <;> simp
    simp_rw [hbool]
    simp
  have annihilator_nilpotent {N : ℕ} (j : Fin N) : fullC j * fullC j = 0 := by
    classical
    have entries (s t : Assignment N) :
        fullC j s t = ∏ k : Fin N,
          fermionWord j k (s k) (t k) := by
      simp [fullC, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
    ext s t
    rw [Matrix.mul_apply]
    simp_rw [entries, ← Finset.prod_mul_distrib]
    change (∑ x : Assignment N, ∏ k : Fin N,
      fermionWord j k (s k) (x k) * fermionWord j k (x k) (t k)) = 0
    rw [(Fintype.prod_sum (fun (k : Fin N) (b : Bool) =>
      fermionWord j k (s k) b * fermionWord j k b (t k))).symm]
    change (∏ k : Fin N, ∑ b : Bool,
      fermionWord j k (s k) b * fermionWord j k b (t k)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [fermionWord, lt_self_iff_false, ite_false, ite_true]
    cases hs : s j <;> cases ht : t j <;>
      norm_num [Matrix.single, Fintype.sum_bool, hs, ht]
  have majorana_hermitian {N : ℕ} (j : Fin N) (b : Bool) : (majorana j b).IsHermitian := by
    cases b
    · change (fullC j + (fullC j)ᴴ)ᴴ = fullC j + (fullC j)ᴴ
      simp [Matrix.conjTranspose_add, add_comm]
    · change (Complex.I • (fullC j - (fullC j)ᴴ))ᴴ =
        Complex.I • (fullC j - (fullC j)ᴴ)
      simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
        Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      simp only [neg_smul, smul_sub]
      simp [sub_eq_add_neg, add_comm]
  have mixed_distinct {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
      fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact fullC_mixed_anticomm_of_lt i j h
    · have ht := congrArg Matrix.conjTranspose (fullC_mixed_anticomm_of_lt j i h)
      simpa using ht
  have majorana_square {N : ℕ} (j : Fin N) (b : Bool) :
      majorana j b * majorana j b = 1 := by
    have hn := annihilator_nilpotent j
    have hs : (fullC j)ᴴ * (fullC j)ᴴ = 0 := by
      simpa using congrArg Matrix.conjTranspose hn
    have hcar := fullC_CAR j
    cases b
    · change (fullC j + (fullC j)ᴴ) * (fullC j + (fullC j)ᴴ) = 1
      calc
        _ = fullC j * fullC j + (fullC j)ᴴ * (fullC j)ᴴ +
          (fullC j * (fullC j)ᴴ + (fullC j)ᴴ * fullC j) := by noncomm_ring
        _ = _ := by rw [hn, hs, hcar]; simp
    · change (Complex.I • (fullC j - (fullC j)ᴴ)) *
        (Complex.I • (fullC j - (fullC j)ᴴ)) = 1
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
      have hh : (fullC j - (fullC j)ᴴ) * (fullC j - (fullC j)ᴴ) = -1 := by
        calc
          _ = fullC j * fullC j + (fullC j)ᴴ * (fullC j)ᴴ -
            (fullC j * (fullC j)ᴴ + (fullC j)ᴴ * fullC j) := by noncomm_ring
          _ = _ := by rw [hn, hs, hcar]; simp
      rw [hh, neg_neg]
  have majorana_same_mixed {N : ℕ} (j : Fin N) :
      majorana j false * majorana j true + majorana j true * majorana j false = 0 := by
    have hn := annihilator_nilpotent j
    have hs : (fullC j)ᴴ * (fullC j)ᴴ = 0 := by
      simpa using congrArg Matrix.conjTranspose hn
    change (fullC j + (fullC j)ᴴ) * (Complex.I • (fullC j - (fullC j)ᴴ)) +
      (Complex.I • (fullC j - (fullC j)ᴴ)) * (fullC j + (fullC j)ᴴ) = 0
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
    have h : (fullC j + (fullC j)ᴴ) * (fullC j - (fullC j)ᴴ) +
        (fullC j - (fullC j)ᴴ) * (fullC j + (fullC j)ᴴ) = 0 := by
      calc
        _ = fullC j * fullC j + fullC j * fullC j -
          ((fullC j)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC j)ᴴ) := by noncomm_ring
        _ = 0 := by rw [hn, hs]; simp
    rw [h, smul_zero]
  have majorana_distinct {N : ℕ} (i j : Fin N) (hij : i ≠ j) (b c : Bool) :
      majorana i b * majorana j c + majorana j c * majorana i b = 0 := by
    have hnn : fullC i * fullC j + fullC j * fullC i = 0 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact fullC_anticomm_of_lt i j h
      · simpa only [add_comm] using fullC_anticomm_of_lt j i h
    have hns := mixed_distinct i j hij
    have hsn : (fullC i)ᴴ * fullC j + fullC j * (fullC i)ᴴ = 0 := by
      simpa only [add_comm] using mixed_distinct j i hij.symm
    have hss : (fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ = 0 := by
      simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_zero, add_comm] using congrArg Matrix.conjTranspose hnn
    cases b <;> cases c
    · change (fullC i + (fullC i)ᴴ) * (fullC j + (fullC j)ᴴ) +
        (fullC j + (fullC j)ᴴ) * (fullC i + (fullC i)ᴴ) = 0
      calc
        _ = (fullC i * fullC j + fullC j * fullC i) +
            (fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i) +
            ((fullC i)ᴴ * fullC j + fullC j * (fullC i)ᴴ) +
            ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) := by noncomm_ring
        _ = 0 := by rw [hnn, hns, hsn, hss]; simp
    · change (fullC i + (fullC i)ᴴ) * (Complex.I • (fullC j - (fullC j)ᴴ)) +
        (Complex.I • (fullC j - (fullC j)ᴴ)) * (fullC i + (fullC i)ᴴ) = 0
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      have h : (fullC i + (fullC i)ᴴ) * (fullC j - (fullC j)ᴴ) +
          (fullC j - (fullC j)ᴴ) * (fullC i + (fullC i)ᴴ) = 0 := by
        calc
          _ = (fullC i * fullC j + fullC j * fullC i) -
              (fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i) +
              ((fullC i)ᴴ * fullC j + fullC j * (fullC i)ᴴ) -
              ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) := by noncomm_ring
          _ = 0 := by rw [hnn, hns, hsn, hss]; simp
      rw [h, smul_zero]
    · change (Complex.I • (fullC i - (fullC i)ᴴ)) * (fullC j + (fullC j)ᴴ) +
        (fullC j + (fullC j)ᴴ) * (Complex.I • (fullC i - (fullC i)ᴴ)) = 0
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
      have h : (fullC i - (fullC i)ᴴ) * (fullC j + (fullC j)ᴴ) +
          (fullC j + (fullC j)ᴴ) * (fullC i - (fullC i)ᴴ) = 0 := by
        calc
          _ = (fullC i * fullC j + fullC j * fullC i) +
              (fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i) -
              ((fullC i)ᴴ * fullC j + fullC j * (fullC i)ᴴ) -
              ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) := by noncomm_ring
          _ = 0 := by rw [hnn, hns, hsn, hss]; simp
      rw [h, smul_zero]
    · change (Complex.I • (fullC i - (fullC i)ᴴ)) * (Complex.I • (fullC j - (fullC j)ᴴ)) +
        (Complex.I • (fullC j - (fullC j)ᴴ)) * (Complex.I • (fullC i - (fullC i)ᴴ)) = 0
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
      have h : (fullC i - (fullC i)ᴴ) * (fullC j - (fullC j)ᴴ) +
          (fullC j - (fullC j)ᴴ) * (fullC i - (fullC i)ᴴ) = 0 := by
        calc
          _ = (fullC i * fullC j + fullC j * fullC i) -
              (fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i) -
              ((fullC i)ᴴ * fullC j + fullC j * (fullC i)ᴴ) +
              ((fullC i)ᴴ * (fullC j)ᴴ + (fullC j)ᴴ * (fullC i)ᴴ) := by noncomm_ring
          _ = 0 := by rw [hnn, hns, hsn, hss]; simp
      rw [← neg_add, h, neg_zero]
  have parity_anticomm (N : ℕ) (j : Fin N) :
      numberParity N * fullC j + fullC j * numberParity N = 0 := by
    classical
    have signs (s : Assignment N) :
        (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card =
          ∏ k : Fin N, if s k then (-1 : ℂ) else 1 := by
      rw [← Finset.prod_filter]
      simp [Finset.prod_const]
    have entries (s t : Assignment N) : fullC j s t =
        ∏ k : Fin N, fermionWord j k (s k) (t k) := by
      simp [fullC, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
    have off (k : Fin N) (hk : k ≠ j) (a b : Bool) (hab : a ≠ b) :
        fermionWord j k a b = 0 := by
      by_cases hkj : k < j
      · cases a <;> cases b <;> simp_all [fermionWord,
          D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv]
      · simp [fermionWord, hkj, hk, hab]
    ext s t
    change (numberParity N * fullC j + fullC j * numberParity N) s t = 0
    simp only [parity_diagonal, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      signs, entries]
    by_cases hrest : ∀ k, k ≠ j → s k = t k
    · have hprod : (∏ k ∈ Finset.univ.erase j, if s k then (-1 : ℂ) else 1) =
          (∏ k ∈ Finset.univ.erase j, if t k then (-1 : ℂ) else 1) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [hrest k (Finset.ne_of_mem_erase hk)]
      rw [← Finset.mul_prod_erase Finset.univ
          (fun k : Fin N => if s k then (-1 : ℂ) else 1) (Finset.mem_univ j),
        ← Finset.mul_prod_erase Finset.univ
          (fun k : Fin N => if t k then (-1 : ℂ) else 1) (Finset.mem_univ j), hprod]
      cases hs : s j <;> cases ht : t j
      · have hz : (∏ k : Fin N, fermionWord j k (s k) (t k)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
      · simp [mul_comm]
      · have hz : (∏ k : Fin N, fermionWord j k (s k) (t k)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
      · have hz : (∏ k : Fin N, fermionWord j k (s k) (t k)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by simp [fermionWord, hs, ht, Matrix.single])
        rw [hz]; simp
    · push Not at hrest
      obtain ⟨k, hk, hst⟩ := hrest
      have hz : (∏ k : Fin N, fermionWord j k (s k) (t k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (off k hk _ _ hst)
      rw [hz]; simp
  have parity_hermitian : (numberParity N).IsHermitian := by
    rw [parity_diagonal]
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    change star ((-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card) = _
    simp only [star_pow, star_neg, star_one]
  have parity_square : numberParity N * numberParity N = 1 := by
    rw [parity_diagonal, Matrix.diagonal_mul_diagonal]
    have h (s : Assignment N) :
        (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card *
        (-1 : ℂ) ^ (Finset.univ.filter (fun j => s j = true)).card = 1 := by
      rw [← mul_pow]; simp
    simp only [h, Matrix.diagonal_one]
  refine ⟨parity_hermitian, parity_square, fun p => majorana_hermitian p.1 p.2, ?_, ?_⟩
  · intro p q
    by_cases hij : p.1 = q.1
    · rcases p with ⟨i, b⟩
      rcases q with ⟨j, c⟩
      change i = j at hij
      subst j
      by_cases hbc : b = c
      · subst c
        simp only [↓reduceIte]
        rw [majorana_square]
        simp [two_smul]
      · have hne : (i, b) ≠ (i, c) := fun h => hbc (congrArg Prod.snd h)
        rw [if_neg hne]
        cases b <;> cases c
        · exact False.elim (hbc rfl)
        · exact majorana_same_mixed i
        · simpa only [add_comm] using majorana_same_mixed i
        · exact False.elim (hbc rfl)
    · rw [if_neg (fun h => hij (congrArg Prod.fst h))]
      exact majorana_distinct p.1 q.1 hij p.2 q.2
  · rintro ⟨j, b⟩
    have hc := parity_anticomm N j
    have hd : numberParity N * (fullC j)ᴴ + (fullC j)ᴴ * numberParity N = 0 := by
      have hh := congrArg Matrix.conjTranspose hc
      simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        parity_hermitian.eq, Matrix.conjTranspose_zero, add_comm] using hh
    cases b
    · change numberParity N * (fullC j + (fullC j)ᴴ) +
        (fullC j + (fullC j)ᴴ) * numberParity N = 0
      calc
        _ = (numberParity N * fullC j + fullC j * numberParity N) +
          (numberParity N * (fullC j)ᴴ + (fullC j)ᴴ * numberParity N) := by noncomm_ring
        _ = 0 := by rw [hc, hd]; simp
    · change numberParity N * (Complex.I • (fullC j - (fullC j)ᴴ)) +
        (Complex.I • (fullC j - (fullC j)ᴴ)) * numberParity N = 0
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
      have hh : numberParity N * (fullC j - (fullC j)ᴴ) +
          (fullC j - (fullC j)ᴴ) * numberParity N = 0 := by
        calc
          _ = (numberParity N * fullC j + fullC j * numberParity N) -
            (numberParity N * (fullC j)ᴴ + (fullC j)ᴴ * numberParity N) := by noncomm_ring
          _ = 0 := by rw [hc, hd]; simp
      rw [hh, smul_zero]

end D5.S3.Quantum.Fermionic.FockMajoranaCarrier
