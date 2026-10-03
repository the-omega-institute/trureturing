/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/EndpointIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A period-three anticommutator reduces to endpoint occupations. -/
/-
endpoint_identity:
  proof_shape: content
  escape_witness: endpoint_identity (form 2): Cubic-product localization, cancellation of hopping currents, and the period-three occupation telescope produce the endpoint operator.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.FullEndpointIdentity, D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression; freeze in topological import order.
Reused predicate: D5/S1/Words/AdmissibleWords/AdmissibleCount.Adm.
Pointwise exclusion: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true; sha256:1fd94a32ad20c5e9f47c8843c130133ce27a104e2f7f75cb9bf9916f8085bc2b.
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.FullEndpointIdentity
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)
namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.EndpointIdentity
noncomputable section
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicCompression
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.FullEndpointIdentity
def EndpointIdentity : Prop := ∀ n : ℕ, 1 ≤ n → ∀ a b cc : ℝ,
  let q := Qmat (3 * n) (periodThree a b cc)
  let r := Rmat (3 * n) a b cc
  q * r + r * q + (q * r + r * q)ᴴ =
    (2 * b ^ 2 : ℝ) • ((cc ^ 2 : ℝ) • number 1 - (a ^ 2 : ℝ) • number (3 * n))
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem endpoint_identity : EndpointIdentity := by
  have adjacent_iff {M : ℕ} (s : Assignment M) :
      Adm M s ↔ ∀ i k : Fin M, i.val + 1 = k.val → s i = true → s k = false := by
    simp only [adm_iff_no_adjacent_true, or_iff_not_imp_left, Bool.eq_true_eq_not_eq_false]
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have antiAd_reindexed {N : ℕ} (A B : FullOperator N) :
      ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm A) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm B))) = A * B + B * A := by
    simp only [D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd, map_add, map_mul, AlgEquiv.apply_symm_apply]
  have number_commutes_c {N : ℕ} (k j : ℕ) (hkj : k ≠ j) :
      number (N := N) k * c j = c j * number k := by
    have occupied_update_other {N : ℕ} (t : Assignment N) (i : Fin N)
        (k : ℕ) (hne : k ≠ i.val + 1) :
        occupied (Function.update t i false) k = occupied t k := by
      unfold occupied
      split_ifs with hk
      · apply Function.update_of_ne
        intro h
        have hv := congrArg Fin.val h
        simp only at hv
        apply hne
        omega
      · rfl
    classical
    ext s t
    simp only [number,Matrix.diagonal_mul,Matrix.mul_diagonal]
    by_cases hj : 0 < j ∧ j ≤ N
    · simp only [c,dif_pos hj,annihilationAt]
      by_cases ht : t.val ⟨j - 1, by omega⟩ = true ∧
          s.val = Function.update t.val ⟨j - 1, by omega⟩ false
      · rw [if_pos ht]
        have ho : occupied s.val k = occupied t.val k := by
          rw [ht.2]
          apply occupied_update_other
          simp only
          omega
        rw [ho]
        exact mul_comm _ _
      · simp only [if_neg ht,mul_zero,zero_mul]
    · simp [c,hj]
  have c_absorbs_number {N : ℕ} (j : ℕ) :
      c (N := N) j * number j = c j := by
    classical
    ext s t
    simp only [number,Matrix.mul_diagonal]
    by_cases hj : 0 < j ∧ j ≤ N
    · simp only [c,dif_pos hj,annihilationAt]
      by_cases ht : t.val ⟨j - 1, by omega⟩ = true ∧
          s.val = Function.update t.val ⟨j - 1, by omega⟩ false
      · have ho : occupied t.val j = true := by simpa only [occupied,dif_pos hj] using ht.1
        simp [ht,ho]
      · simp [ht]
    · simp [c,hj]
  have restrictOp_mul {N : ℕ} (A B : D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.FullOperator N)
      (hB : ∀ (s t : Assignment N), Adm N t → B s t ≠ 0 → Adm N s) :
      (Matrix.submatrix (A * B) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) * (Matrix.submatrix B (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := by
    classical
    ext s t
    simp only [Matrix.submatrix, Matrix.mul_apply]
    have hz : (∑ u : {u : Assignment N // ¬Adm N u},
        A s.val u.val * B u.val t.val) = 0 := by
      apply Finset.sum_eq_zero
      intro u _hu
      have hb : B u.val t.val = 0 := by
        by_contra hn
        exact u.property (hB u.val t.val t.property hn)
      rw [hb,mul_zero]
    have hs := Fintype.sum_subtype_add_sum_subtype (Adm N)
      (fun u => A s.val u * B u t.val)
    rw [hz,add_zero] at hs
    exact hs.symm
  have occupied_neighbours_empty {N : ℕ} (s : HardCore N) (j : ℕ)
      (hj : occupied s.val j = true) :
      occupied s.val (j - 1) = false ∧ occupied s.val (j + 1) = false := by
    have hjb : 0 < j ∧ j ≤ N := by
      by_contra h
      simp [occupied, h] at hj
    have ho : s.val ⟨j - 1, by omega⟩ = true := by
      simpa only [occupied, dif_pos hjb] using hj
    constructor
    · by_cases hb : 0 < j - 1 ∧ j - 1 ≤ N
      · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1 - 1, by omega⟩ ⟨j - 1, by omega⟩
        have hfalse : s.val ⟨j - 1 - 1, by omega⟩ = false := by
          cases hv : s.val ⟨j - 1 - 1, by omega⟩
          · rfl
          · have hc := hp (by simp only; omega) hv
            rw [ho] at hc
            contradiction
        simpa only [occupied, dif_pos hb] using hfalse
      · simp only [occupied, dif_neg hb]
    · by_cases hb : 0 < j + 1 ∧ j + 1 ≤ N
      · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1, by omega⟩ ⟨j + 1 - 1, by omega⟩
        simpa only [occupied, dif_pos hb] using hp (by simp only; omega) ho
      · simp only [occupied, dif_neg hb]
  have dressed_eq_c {N : ℕ} (j : ℕ) : d (N := N) j = c j := by
    have occupied_neighbours_empty {N : ℕ} (s : HardCore N) (j : ℕ)
        (hj : occupied s.val j = true) :
        occupied s.val (j - 1) = false ∧ occupied s.val (j + 1) = false := by
      have hjb : 0 < j ∧ j ≤ N := by
        by_contra h
        simp [occupied, h] at hj
      have ho : s.val ⟨j - 1, by omega⟩ = true := by
        simpa only [occupied, dif_pos hjb] using hj
      constructor
      · by_cases hb : 0 < j - 1 ∧ j - 1 ≤ N
        · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1 - 1, by omega⟩ ⟨j - 1, by omega⟩
          have hfalse : s.val ⟨j - 1 - 1, by omega⟩ = false := by
            cases hv : s.val ⟨j - 1 - 1, by omega⟩
            · rfl
            · have hc := hp (by simp only; omega) hv
              rw [ho] at hc
              contradiction
          simpa only [occupied, dif_pos hb] using hfalse
        · simp only [occupied, dif_neg hb]
      · by_cases hb : 0 < j + 1 ∧ j + 1 ≤ N
        · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1, by omega⟩ ⟨j + 1 - 1, by omega⟩
          simpa only [occupied, dif_pos hb] using hp (by simp only; omega) ho
        · simp only [occupied, dif_neg hb]
    have P_diagonal {N : ℕ} (j : ℕ) :
        P (N := N) j = Matrix.diagonal (fun s => if occupied s.val j then 0 else 1) := by
      classical
      ext s t
      simp only [P, number, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
      by_cases h : s = t
      · subst t
        cases occupied s.val j <;> simp
      · simp [h]
    classical
    ext s t
    simp only [d, P_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hj : 0 < j ∧ j ≤ N
    · simp only [c, dif_pos hj, annihilationAt]
      by_cases ht : t.val ⟨j - 1, by omega⟩ = true ∧
          s.val = Function.update t.val ⟨j - 1, by omega⟩ false
      · rw [if_pos ht]
        have hocc : occupied t.val j = true := by
          simpa only [occupied, dif_pos hj] using ht.1
        obtain ⟨hprev,hnext⟩ := occupied_neighbours_empty t j hocc
        have hsPrev : occupied s.val (j - 1) = false := by
          rw [ht.2]
          unfold occupied
          split_ifs with hp
          · rw [Function.update_of_ne (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)]
            have := hprev
            simpa only [occupied, dif_pos hp] using this
          · rfl
        simp [hnext, hsPrev]
      · simp only [if_neg ht, mul_zero, zero_mul]
    · simp [c, hj]
  have adjacent_number_zero {N : ℕ} (j : ℕ) :
      number (N := N) j * number (j + 1) = 0 := by
    have occupied_neighbours_empty {N : ℕ} (s : HardCore N) (j : ℕ)
        (hj : occupied s.val j = true) :
        occupied s.val (j - 1) = false ∧ occupied s.val (j + 1) = false := by
      have hjb : 0 < j ∧ j ≤ N := by
        by_contra h
        simp [occupied, h] at hj
      have ho : s.val ⟨j - 1, by omega⟩ = true := by
        simpa only [occupied, dif_pos hjb] using hj
      constructor
      · by_cases hb : 0 < j - 1 ∧ j - 1 ≤ N
        · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1 - 1, by omega⟩ ⟨j - 1, by omega⟩
          have hfalse : s.val ⟨j - 1 - 1, by omega⟩ = false := by
            cases hv : s.val ⟨j - 1 - 1, by omega⟩
            · rfl
            · have hc := hp (by simp only; omega) hv
              rw [ho] at hc
              contradiction
          simpa only [occupied, dif_pos hb] using hfalse
        · simp only [occupied, dif_neg hb]
      · by_cases hb : 0 < j + 1 ∧ j + 1 ≤ N
        · have hp := ((adjacent_iff s.val).mp s.property) ⟨j - 1, by omega⟩ ⟨j + 1 - 1, by omega⟩
          simpa only [occupied, dif_pos hb] using hp (by simp only; omega) ho
        · simp only [occupied, dif_neg hb]
    classical
    unfold number
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    funext s
    by_cases hj : occupied s.val j = true
    · have hn := (occupied_neighbours_empty s j hj).2
      simp [hj, hn]
    · simp [hj]
  let DiagonalAnticommutator : Prop :=
    ∀ n : ℕ, 1 ≤ n → ∀ a b cc : ℝ,
      let q := Qmat (3 * n) (periodThree a b cc)
      let r := Rmat (3 * n) a b cc
      q * r + r * q + (q * r + r * q)ᴴ =
        Matrix.diagonal (fun s => ((2 * diagonalCoefficient (3 * n) a b cc s : ℝ) : ℂ))
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) : tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have periodThree_periodic (a b cc : ℝ) (j : ℕ) : periodThree a b cc (j + 3) = periodThree a b cc j := by simp [periodThree, Nat.add_mod]
  have w_periodic (a b cc : ℝ) (j : ℕ) : w a b cc (j + 3) = w a b cc j := by
    simp only [w]
    rw [show j + 3 + 1 = (j + 1) + 3 by omega,
        show j + 3 + 2 = (j + 2) + 3 by omega,
        periodThree_periodic, periodThree_periodic]
  have shifted_sum_telescope (f : ℕ → ℝ) (k : ℕ) : (∑ i ∈ Finset.range k, (f (i + 1) - f (i + 3))) = f 1 + f 2 - f (k + 1) - f (k + 2) := by
    have h := Finset.sum_range_sub' (fun i => f (i + 1) + f (i + 2)) k
    have he : (∑ i ∈ Finset.range k, (f (i + 1) - f (i + 3))) = ∑ i ∈ Finset.range k, ((f (i + 1) + f (i + 2)) - (f (i + 1 + 1) + f (i + 1 + 2))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show i + 1 + 1 = i + 2 by omega, show i + 1 + 2 = i + 3 by omega]; ring
    rw [he, h]; norm_num; ring
  have diagonal_bulk_telescope (N : ℕ) (hN : 3 ≤ N) (wt x : ℕ → ℝ) (hw : ∀ j, wt (j + 3) = wt j) (hx0 : x 0 = 0) (hxN : x (N + 1) = 0) : (∑ i ∈ Finset.range (N - 2), (wt (i + 1) * x (i + 1) * (1 - x (i + 4)) - wt (i + 3) * x (i + 3) * (1 - x i))) = wt 1 * x 1 + wt 2 * x 2 - wt (N - 1) * x (N - 1) - wt N * x N := by
    let f := fun j => wt j * x j
    let g := fun j => wt j * x j * x (j + 3)
    have he : (∑ i ∈ Finset.range (N - 2), (wt (i + 1) * x (i + 1) * (1 - x (i + 4)) - wt (i + 3) * x (i + 3) * (1 - x i))) = (∑ i ∈ Finset.range (N - 2), (f (i + 1) - f (i + 3))) - (∑ i ∈ Finset.range (N - 2), (g (i + 1) - g i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [f, g]
      rw [hw, show i + 1 + 3 = i + 4 by omega]; ring
    rw [he, shifted_sum_telescope, Finset.sum_range_sub]
    dsimp [f, g]
    rw [show N - 2 + 3 = N + 1 by omega, hx0, hxN]
    simp only [mul_zero, zero_mul, sub_zero, show N - 2 + 1 = N - 1 by omega,
      show N - 2 + 2 = N by omega]
  have diagonalCoefficient_endpoint (n : ℕ) (hn : 1 ≤ n) (a b cc : ℝ) (s : HardCore (3 * n)) : diagonalCoefficient (3 * n) a b cc s = b ^ 2 * (cc ^ 2 * occReal s 1 - a ^ 2 * occReal s (3 * n)) := by
    have hN : 3 ≤ 3 * n := by omega
    have hx0 : occReal s 0 = 0 := by simp [occReal, occupied]
    have hxN : occReal s (3 * n + 1) = 0 := by simp [occReal, occupied]
    have ht := diagonal_bulk_telescope (3 * n) hN (w a b cc) (occReal s)
      (w_periodic a b cc) hx0 hxN
    unfold diagonalCoefficient; rw [ht]
    have hmod0 : (3 * n) % 3 = 0 := by omega
    have hmod1 : (3 * n - 1) % 3 = 2 := by omega
    have hw1 : w a b cc 1 = b ^ 2 * cc ^ 2 := by norm_num [w, periodThree]
    have hw2 : w a b cc 2 = cc ^ 2 * a ^ 2 := by norm_num [w, periodThree]
    have hwN1 : w a b cc (3 * n - 1) = cc ^ 2 * a ^ 2 := by
      unfold w
      rw [show 3 * n - 1 + 1 = 3 * n by omega,
          show 3 * n - 1 + 2 = 3 * n + 1 by omega]
      simp [periodThree, hmod0, Nat.add_mod]
    have hwN : w a b cc (3 * n) = a ^ 2 * b ^ 2 := by simp [w, periodThree, hmod0, Nat.add_mod]
    rw [hw1, hw2, hwN1, hwN]; ring
  have diagonal_anticommutator_implies_identity (hdiag : DiagonalAnticommutator) : EndpointIdentity := by
    intro n hn a b cc
    have h := hdiag n hn a b cc
    dsimp only at h ⊢
    rw [h]
    ext s t
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.sub_apply,
      number, Pi.smul_apply]
    by_cases hst : s = t
    · subst t
      rw [if_pos rfl]
      simp only [Matrix.diagonal_apply_eq, diagonalCoefficient_endpoint n hn,
        occReal, smul_eq_mul, Complex.real_smul]
      cases occupied s.val 1 <;> cases occupied s.val (3 * n) <;>
        norm_num <;> ring
    · simp [hst, Matrix.diagonal_apply]
  have restrictOp_adjoint {N : ℕ} (A : FullOperator N) : (Matrix.submatrix Aᴴ (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ((Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)))ᴴ := rfl
  have annihilationAt_eq_c {N : ℕ} (i : Fin N) : annihilationAt i = c (i.val + 1) := by
    have hi : 0 < i.val + 1 ∧ i.val + 1 ≤ N := by omega
    simp only [c, dif_pos hi, Nat.add_sub_cancel]
  have restrictOp_sum {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → FullOperator N) : (Matrix.submatrix (∑ i ∈ s, f i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ∑ i ∈ s, (Matrix.submatrix (f i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := by
    ext a b
    simp [Matrix.submatrix,Matrix.sum_apply]
  have restrictOp_complex_smul {N : ℕ} (z : ℂ) (A : FullOperator N) : (Matrix.submatrix (z • A) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = z • (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := rfl
  have restrictOp_fullQ (N : ℕ) (coupling : ℕ → ℝ) : (Matrix.submatrix (fullQ (fun i : Fin N => coupling (i.val + 1))) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = Qmat N coupling := by
    classical
    unfold fullQ Qmat; rw [restrictOp_sum]; rw [← Fin.sum_univ_eq_sum_range (fun j => (coupling (j + 1) : ℂ) • d (N := N) (j + 1)) N]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [restrictOp_complex_smul,restrictOp_fullD,annihilationAt_eq_c,dressed_eq_c]
  have restrictOp_add {N : ℕ} (A B : FullOperator N) : (Matrix.submatrix (A+B) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) + (Matrix.submatrix B (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := rfl
  have restrictOp_fullD_adjoint_mul {N : ℕ} (A : FullOperator N) (i : Fin N) : (Matrix.submatrix (A * (fullD i)ᴴ) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) * (annihilationAt i)ᴴ := by
    rw [restrictOp_mul,restrictOp_adjoint,restrictOp_fullD]
    intro s t ht hst
    have hh : fullD i t s ≠ 0 := by simpa only [Matrix.conjTranspose_apply,star_ne_zero] using hst
    exact (fullD_hardCore_iff i t s hh).mp ht
  have restrictOp_real_smul {N : ℕ} (z : ℝ) (A : FullOperator N) : (Matrix.submatrix (z • A) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = z • (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := rfl
  have P_commutes_c {N : ℕ} (k j : ℕ) (hkj : k ≠ j) : P (N := N) k * c j = c j * P k := by simp only [P,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]; rw [number_commutes_c k j hkj]
  have previous_number_zero {N : ℕ} (j : ℕ) : number (N := N) j * number (j - 1) = 0 := by
    classical
    unfold number; rw [Matrix.diagonal_mul_diagonal]; rw [← Matrix.diagonal_zero]
    congr 1
    funext s
    by_cases hj : occupied s.val j = true
    · have hn := (occupied_neighbours_empty s j hj).1
      simp [hj, hn]
    · simp [hj]
  have number_absorbs_neighbour_P {N : ℕ} (j : ℕ) : number (N := N) j * P (j - 1) = number j ∧
      number (N := N) j * P (j + 1) = number j := by
    constructor <;> simp [P, Matrix.mul_sub, previous_number_zero, adjacent_number_zero]
  have c_absorbs_neighbour_P {N : ℕ} (j : ℕ) : c (N := N) j * P (j - 1) = c j ∧ c (N := N) j * P (j + 1) = c j := by
    constructor
    · calc
        c j * P (j - 1) = (c j * number j) * P (j - 1) := by rw [c_absorbs_number]
        _ = c j * (number j * P (j - 1)) := Matrix.mul_assoc _ _ _
        _ = c j * number j := by rw [(number_absorbs_neighbour_P j).1]
        _ = c j := c_absorbs_number j
    · calc
        c j * P (j + 1) = (c j * number j) * P (j + 1) := by rw [c_absorbs_number]
        _ = c j * (number j * P (j + 1)) := Matrix.mul_assoc _ _ _
        _ = c j * number j := by rw [(number_absorbs_neighbour_P j).2]
        _ = c j := c_absorbs_number j
  have number_self_adjoint {N : ℕ} (j : ℕ) : (number (N := N) j)ᴴ = number j := by
    classical
    ext s t
    simp only [number, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : s = t
    · subst t
      cases occupied s.val j <;> simp
    · simp [h, Ne.symm h]
  have P_self_adjoint {N : ℕ} (j : ℕ) : (P (N := N) j)ᴴ = P j := by simp only [P,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,number_self_adjoint]
  have cubic_outer_projectors_absorbed {N : ℕ} (j : ℕ) : P (N := N) (j - 1) * (c j)ᴴ * (c (j + 2))ᴴ * c (j + 1) * P (j + 3) =
        (c j)ᴴ * (c (j + 2))ᴴ * c (j + 1) := by
    have hleft : P (N := N) (j - 1) * (c j)ᴴ = (c j)ᴴ := by
      have h := congrArg Matrix.conjTranspose (c_absorbs_neighbour_P (N := N) j).1
      simpa only [Matrix.conjTranspose_mul,P_self_adjoint] using h
    have hright : (c (N := N) (j + 2))ᴴ * P (j + 3) = (c (j + 2))ᴴ := by
      have hcomm := P_commutes_c (N := N) (j + 3) (j + 2) (by omega)
      have habs := (c_absorbs_neighbour_P (N := N) (j + 2)).2
      have h := congrArg Matrix.conjTranspose (hcomm.trans (by simpa only [Nat.add_assoc] using habs))
      simpa only [Matrix.conjTranspose_mul,P_self_adjoint] using h
    rw [hleft]; simp only [Matrix.mul_assoc]
    rw [← P_commutes_c (j + 3) (j + 1) (by omega),
      ← Matrix.mul_assoc ((c (N := N) (j + 2))ᴴ) (P (j + 3)) (c (j + 1)),hright]
  have restrictOp_fullD_mul {N : ℕ} (A : FullOperator N) (i : Fin N) : (Matrix.submatrix (A * fullD i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) * annihilationAt i := by
    rw [restrictOp_mul,restrictOp_fullD]
    intro s t ht hst
    exact (fullD_hardCore_iff i s t hst).mpr ht
  have restrictOp_fullSplit {N : ℕ} (j : Fin N) (hr : j.val + 2 < N) : (Matrix.submatrix (fullSplit j) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = P (j.val) * (c (j.val + 1))ᴴ * (c (j.val + 3))ᴴ * c (j.val + 2) * P (j.val + 4) := by
    rw [fullSplit_eq_dressed_product j hr,
      restrictOp_fullD_mul,restrictOp_fullD_adjoint_mul,
      restrictOp_adjoint,restrictOp_fullD]
    simp only [annihilationAt_eq_c]; rw [← cubic_outer_projectors_absorbed (j.val + 1)]; simp only [Nat.add_sub_cancel,Nat.add_assoc]
  have restrictOp_sub {N : ℕ} (A B : FullOperator N) : (Matrix.submatrix (A-B) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = (Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) - (Matrix.submatrix B (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) := rfl
  have restrictOp_sum_fin {N k : ℕ} (f : Fin k → FullOperator N) (g : ℕ → Operator N) (h : ∀ i : Fin k, (Matrix.submatrix (f i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = g i.val) : (Matrix.submatrix (∑ i : Fin k, f i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ∑ j ∈ Finset.range k, g j := by
    classical
    rw [restrictOp_sum,← Fin.sum_univ_eq_sum_range g k]
    apply Finset.sum_congr rfl
    intro i _hi
    exact h i
  have restrictOp_fullR (N : ℕ) (hN : 0 < N) (a b cc : ℝ) : (Matrix.submatrix (fullR N a b cc) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = Rmat N a b cc := by
    classical
    have hp : (Matrix.submatrix (∑ k : Fin (N-2), (periodThree a b cc (k.val+3) * periodThree a b cc (k.val+2)^2 : ℝ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp (⟨k.val,by omega⟩ : Fin N) (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD (⟨k.val+2,by omega⟩ : Fin N))ᴴ)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ∑ k ∈ Finset.range (N-2), (periodThree a b cc (k+3) * periodThree a b cc (k+2)^2 : ℝ) • (number (k+1) * (d (k+3))ᴴ) := by
      apply restrictOp_sum_fin
      intro k
      rw [restrictOp_real_smul,restrictOp_fullD_adjoint_mul,restrictOp_fullNumber]; simp only [annihilationAt_eq_c,dressed_eq_c,Nat.add_assoc]
    have hm : (Matrix.submatrix (∑ k : Fin (N-2), (periodThree a b cc (k.val+1) * periodThree a b cc (k.val+2)^2 : ℝ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp (⟨k.val+2,by omega⟩ : Fin N) (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD (⟨k.val,by omega⟩ : Fin N))ᴴ)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ∑ k ∈ Finset.range (N-2), (periodThree a b cc (k+1) * periodThree a b cc (k+2)^2 : ℝ) • (number (k+3) * (d (k+1))ᴴ) := by
      apply restrictOp_sum_fin
      intro k
      rw [restrictOp_real_smul,restrictOp_fullD_adjoint_mul,restrictOp_fullNumber]; simp only [annihilationAt_eq_c,dressed_eq_c,Nat.add_assoc]
    have hs : (Matrix.submatrix (∑ k : Fin (N-2), fullSplit (⟨k.val,by omega⟩ : Fin N)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ∑ k ∈ Finset.range (N-2), P k * (c (k+1))ᴴ * (c (k+3))ᴴ * c (k+2) * P (k+4) := by
      apply restrictOp_sum_fin
      intro k
      exact restrictOp_fullSplit ⟨k.val,by omega⟩ (by dsimp; omega)
    unfold fullR; rw [dif_pos hN]
    simp only [restrictOp_add,restrictOp_sub,restrictOp_real_smul,restrictOp_adjoint,
      restrictOp_fullD,annihilationAt_eq_c,hp,hm,hs]
    unfold Rmat
    have hlast : N-1+1=N := by omega
    simp only [hlast,zero_add,dressed_eq_c]
    congr 3
    all_goals apply Finset.sum_congr rfl
    all_goals intro k _hk
    all_goals dsimp
    all_goals congr 2 <;> omega
  have HCBlock_complex_smul {N : ℕ} (z : ℂ) {A : FullOperator N} (hA : HCBlock A) : HCBlock (z • A) := by
    intro s t h
    apply hA s t
    intro hz
    exact h (by simp [Matrix.smul_apply,hz])
  have HCBlock_sum {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → FullOperator N) (hf : ∀ i ∈ s, HCBlock (f i)) : HCBlock (∑ i ∈ s, f i) := by
    classical
    intro a b h
    simp only [Matrix.sum_apply] at h
    obtain ⟨i,hi,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact hf i hi a b hn
  have HCBlock_fullD {N : ℕ} (i : Fin N) : HCBlock (fullD i) :=
    fullD_hardCore_iff i
  have HCBlock_fullQ (N : ℕ) (g : Fin N → ℝ) : HCBlock (fullQ g) := by
    unfold fullQ
    apply HCBlock_sum
    intro i _hi
    exact HCBlock_complex_smul _ (HCBlock_fullD i)
  have HCBlock_zero (N : ℕ) : HCBlock (0 : FullOperator N) := by
    intro s t h
    exact (h rfl).elim
  have HCBlock_add {N : ℕ} {A B : FullOperator N} (hA : HCBlock A) (hB : HCBlock B) : HCBlock (A+B) := by
    intro s t h
    by_cases ha : A s t = 0
    · apply hB s t
      intro hb
      exact h (by simp [Matrix.add_apply,ha,hb])
    · exact hA s t ha
  have HCBlock_real_smul {N : ℕ} (z : ℝ) {A : FullOperator N} (hA : HCBlock A) : HCBlock (z • A) := by
    intro s t h
    apply hA s t
    intro hz
    exact h (by simp [Matrix.smul_apply,hz])
  have HCBlock_neg {N : ℕ} {A : FullOperator N} (hA : HCBlock A) : HCBlock (-A) := by
    intro s t h
    apply hA s t
    simpa only [Matrix.neg_apply,neg_ne_zero] using h
  have HCBlock_sub {N : ℕ} {A B : FullOperator N} (hA : HCBlock A) (hB : HCBlock B) : HCBlock (A-B) := by rw [sub_eq_add_neg]; exact HCBlock_add hA (HCBlock_neg hB)
  have HCBlock_mul {N : ℕ} {A B : FullOperator N} (hA : HCBlock A) (hB : HCBlock B) : HCBlock (A*B) := by
    classical
    intro s t h
    simp only [Matrix.mul_apply] at h
    obtain ⟨u,_hu,hab⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hn := mul_ne_zero_iff.mp hab
    exact (hA s u hn.1).trans (hB u t hn.2)
  have HCBlock_adjoint {N : ℕ} {A : FullOperator N} (hA : HCBlock A) : HCBlock Aᴴ := by
    intro s t h
    have ha : A t s ≠ 0 := by simpa only [Matrix.conjTranspose_apply,star_ne_zero] using h
    exact (hA t s ha).symm
  have HCBlock_fullSplit {N : ℕ} (i : Fin N) (hi : i.val+2<N) : HCBlock (fullSplit i) := by
    rw [fullSplit_eq_dressed_product i hi]
    exact HCBlock_mul (HCBlock_mul (HCBlock_adjoint (HCBlock_fullD _))
      (HCBlock_adjoint (HCBlock_fullD _))) (HCBlock_fullD _)
  have HCBlock_fullR (N : ℕ) (a b cc : ℝ) : HCBlock (fullR N a b cc) := by
    classical
    unfold fullR
    split_ifs
    · repeat' first
        | apply HCBlock_add
        | apply HCBlock_sub
        | apply HCBlock_real_smul
        | apply HCBlock_mul
        | apply HCBlock_adjoint
        | apply HCBlock_sum
        | exact HCBlock_fullD _
        | exact HCBlock_fullNumber _
        | exact HCBlock_fullSplit _ (by dsimp; omega)
        | intro i hi
    · exact HCBlock_zero N
  have restrictOp_QR (N : ℕ) (hN : 0<N) (a b cc : ℝ) : (Matrix.submatrix (symOp (((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)) (D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion.antiAd ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullQ (fun i : Fin N => periodThree a b cc (i.val+1)))) ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.piCongrRight fun _ : Fin N => finTwoEquiv)).symm (fullR N a b cc)))))) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = let q := Qmat N (periodThree a b cc)
        let r := Rmat N a b cc
        q*r+r*q+(q*r+r*q)ᴴ := by
    classical
    have hQ := HCBlock_fullQ N (fun i : Fin N => periodThree a b cc (i.val+1))
    have hR := HCBlock_fullR N a b cc
    simp only [antiAd_reindexed]
    unfold symOp
    rw [restrictOp_add (N := N),restrictOp_adjoint (N := N),restrictOp_add (N := N),
      restrictOp_mul _ _ (fun s t ht hn => (hR s t hn).mpr ht),
      restrictOp_mul _ _ (fun s t ht hn => (hQ s t hn).mpr ht),
      restrictOp_fullQ,restrictOp_fullR N hN]
  have tensorOp_mul {N : ℕ} (u v : Fin N → Local) : tensorProduct u * tensorProduct v = tensorProduct (fun i => u i * v i) := by
    classical
    rw [tensorOp_entries, tensorOp_entries, tensorOp_entries]
    ext s t
    change (∑ x : Assignment N, (∏ i : Fin N, u i (s i) (x i)) * (∏ i : Fin N, v i (x i) (t i))) =
      ∏ i : Fin N, ∑ b : Bool, u i (s i) b * v i b (t i)
    simp_rw [← Finset.prod_mul_distrib]; exact (Fintype.prod_sum (fun i b => u i (s i) b * v i b (t i))).symm
  have tensorOp_one {N : ℕ} : tensorProduct (fun _ : Fin N => (1 : Local)) = (1 : FullOperator N) := by
    classical
    ext s t
    simp only [tensorOp_entries, Matrix.one_apply]
    by_cases h : s = t
    · subst t
      simp
    · rw [if_neg h]
      have he : ∃ i, s i ≠ t i := by
        by_contra hh
        push Not at hh
        exact h (funext hh)
      obtain ⟨i,hi⟩ := he
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have tensorOp_update {N : ℕ} (w : Fin N → Local) (i : Fin N) (m : Local) (s t : Assignment N) : tensorProduct (Function.update w i m) s t = m (s i) (t i) * ∏ k ∈ Finset.univ.erase i, w k (s k) (t k) := by
    classical
    simp only [tensorOp_entries]; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  have tensorOp_update_add {N : ℕ} (w : Fin N → Local) (i : Fin N) (u v : Local) : tensorProduct (Function.update w i (u + v)) = tensorProduct (Function.update w i u) + tensorProduct (Function.update w i v) := by
    classical
    ext s t
    simp only [tensorOp_update, Matrix.add_apply]; ring
  have fullNumber_eq_occupation {N : ℕ} (i : Fin N) : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = fullOccupationAt N i.val := by
    classical
    have h1 : numberWord i = Function.update (fun _ : Fin N => (1 : Local)) i (1-spinP) := by
      funext k
      simp [numberWord,Function.update]
    have h2 : (fun k : Fin N => if k.val=i.val then spinP else 1) = Function.update (fun _ : Fin N => (1 : Local)) i spinP := by
      funext k
      simp [Function.update,Fin.ext_iff]
    have he : ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) + fullPAt N i.val = 1 := by rw [localOp_as_tensor]; unfold fullPAt; rw [h1,h2,← tensorOp_update_add,sub_add_cancel]; rw [Function.update_eq_self_iff.mpr rfl,tensorOp_one]
    unfold fullOccupationAt; exact eq_sub_of_add_eq he
  have fullLeftP_eq (N j : ℕ) : fullLeftP N j = if j=0 then 1 else fullPAt N (j-1) := by
    classical
    by_cases hj : j=0
    · subst j
      change tensorProduct (fun k : Fin N => if k.val + 1 = 0 then spinP else 1) = 1
      have he : (fun k : Fin N => if k.val + 1 = 0 then spinP else (1 : Local)) = fun _ => 1 := by
        funext k
        simp
      rw [he,tensorOp_one]
    · rw [if_neg hj]
      unfold fullLeftP fullPAt
      congr 1
      funext k
      have he : k.val+1=j ↔ k.val=j-1 := by omega
      simp only [he]
  have fullPAt_eq_complement (N j : ℕ) : fullPAt N j = 1-fullOccupationAt N j := by
    unfold fullOccupationAt
    abel
  have fullOccupationAt_outside (N j : ℕ) (hj : N≤j) : fullOccupationAt N j = 0 := by
    have he : (fun k : Fin N => if k.val=j then spinP else (1 : Local)) = fun _ => 1 := by
      funext k
      have hn : k.val ≠ j := by omega
      simp [hn]
    change (1 : FullOperator N) - tensorProduct (fun k : Fin N => if k.val = j then spinP else 1) = 0
    rw [he,tensorOp_one,sub_self]
  have neighbourP_explicit {N : ℕ} (j : Fin N) : tensorProduct (neighbourPWord j) = fullLeftP N j.val * fullPAt N (j.val+1) := by
    unfold fullLeftP fullPAt; rw [tensorOp_mul]
    congr 1
    funext k
    unfold neighbourPWord
    by_cases hl : k.val+1=j.val
    · have hr : ¬k.val=j.val+1 := by omega
      simp only [if_pos (Or.inl hl),if_pos hl,if_neg hr,mul_one]
    · by_cases hr : k.val=j.val+1
      · simp only [if_pos (Or.inr hr),if_neg hl,if_pos hr,one_mul]
      · simp only [if_neg (not_or.mpr ⟨hl,hr⟩),if_neg hl,if_neg hr,one_mul]
  have fullPAt_outside (N j : ℕ) (hj : N≤j) : fullPAt N j = 1 := by rw [fullPAt_eq_complement,fullOccupationAt_outside N j hj]; simp
  have restrictOp_one (N : ℕ) : (Matrix.submatrix (1 : FullOperator N) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = 1 := by
    classical
    ext s t
    simp [Matrix.submatrix,Matrix.one_apply,Subtype.ext_iff]
  have restrictOp_fullPAt (N j : ℕ) : (Matrix.submatrix (fullPAt N j) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = P (j+1) := by
    by_cases hj : j<N
    · have he := fullNumber_eq_occupation (⟨j,hj⟩ : Fin N)
      rw [fullPAt_eq_complement,← he,restrictOp_sub,restrictOp_one,restrictOp_fullNumber]
      rfl
    · rw [fullPAt_outside N j (by omega),restrictOp_one]
      have hn : ¬(0<j+1 ∧ j+1≤N) := by omega
      simp [P,number,occupied,hn,hj]
  have P_diagonal {N : ℕ} (j : ℕ) : P (N := N) j = Matrix.diagonal (fun s => if occupied s.val j then 0 else 1) := by
    classical
    ext s t
    simp only [P, number, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases h : s = t
    · subst t
      cases occupied s.val j <;> simp
    · simp [h]
  have P_sub_diagonal {N : ℕ} (u v : ℕ) : P (N := N) u - P v = Matrix.diagonal
        (fun s : HardCore N => ((occReal s v-occReal s u : ℝ) : ℂ)) := by
    rw [P_diagonal,P_diagonal,Matrix.diagonal_sub]
    congr 1
    funext s
    cases hu : occupied s.val u <;> cases hv : occupied s.val v <;>
      norm_num [occReal,hu,hv]
  have HCBlock_neighbourP {N : ℕ} (j : Fin N) : HCBlock (tensorProduct (neighbourPWord j)) := by
    have hcar := fullD_CAR j
    change fullD j * (fullD j)ᴴ + (fullD j)ᴴ * fullD j = tensorProduct (neighbourPWord j) at hcar
    rw [← hcar]; exact HCBlock_add (HCBlock_mul (HCBlock_fullD _) (HCBlock_adjoint (HCBlock_fullD _)))
      (HCBlock_mul (HCBlock_adjoint (HCBlock_fullD _)) (HCBlock_fullD _))
  have HCBlock_one (N : ℕ) : HCBlock (1 : FullOperator N) := by
    intro s t h
    have he : s=t := by
      by_contra hh
      exact h (by simp [Matrix.one_apply,hh])
    subst t
    rfl
  have HCBlock_fullPAt (N j : ℕ) : HCBlock (fullPAt N j) := by
    by_cases hj : j<N
    · have he := fullNumber_eq_occupation (⟨j,hj⟩ : Fin N)
      rw [fullPAt_eq_complement,← he]; exact HCBlock_sub (HCBlock_one N) (HCBlock_fullNumber _)
    · rw [fullPAt_outside N j (by omega)]
      exact HCBlock_one N
  have boundary_projectors {N : ℕ} : P (N := N) 0 = 1 ∧ P (N := N) (N + 1) = 1 := by
    constructor <;> simp [P, number, occupied]
  have restrictOp_fullLeftP (N j : ℕ) : (Matrix.submatrix (fullLeftP N j) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = P j := by
    rw [fullLeftP_eq]
    by_cases hj : j=0
    · rw [if_pos hj,restrictOp_one,hj,(boundary_projectors (N := N)).1]
    · rw [if_neg hj,restrictOp_fullPAt,show j-1+1=j by omega]
  have restrictOp_neighbourP {N : ℕ} (j : Fin N) : (Matrix.submatrix (tensorProduct (neighbourPWord j)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = P j.val * P (j.val+2) := by
    rw [neighbourP_explicit,restrictOp_mul _ _
      (fun s t ht hn => (HCBlock_fullPAt N (j.val+1) s t hn).mpr ht),
      restrictOp_fullLeftP,restrictOp_fullPAt]
  have restrictOp_number_neighbourP {N : ℕ} (k j : Fin N) : (Matrix.submatrix (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord j)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = number (k.val+1) * (P j.val * P (j.val+2)) := by
    rw [restrictOp_mul _ _ (fun s t ht hn => (HCBlock_neighbourP j s t hn).mpr ht),
      restrictOp_fullNumber,restrictOp_neighbourP]
  have P_commute {N : ℕ} (j k : ℕ) : P (N := N) j * P k = P k * P j := by
    rw [P_diagonal,P_diagonal,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext s
    ring
  have restrictOp_blockDiagonal {N : ℕ} (a b cc : ℝ) (k : Fin N) (hr : k.val+2<N) : (Matrix.submatrix (blockDiagonal a b cc k hr) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = ((2 * chainG a b cc (k.val+2)^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) • (number (k.val+1) * P (k.val+4)) - ((2 * chainG a b cc k.val^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) • (number (k.val+3) * P k.val) := by
    unfold blockDiagonal
    change (Matrix.submatrix (((2 * chainG a b cc (k.val+2)^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord (⟨k.val+2,hr⟩ : Fin N))) - ((2 * chainG a b cc k.val^2 * chainG a b cc (k.val+1)^2 : ℝ) : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp (⟨k.val+2,hr⟩ : Fin N) (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * tensorProduct (neighbourPWord k))) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = _
    simp only [restrictOp_sub,restrictOp_complex_smul,restrictOp_number_neighbourP]
    have hp : number (N := N) (k.val+1) * (P (k.val+2) * P (k.val+4)) =
        number (k.val+1) * P (k.val+4) := by
      rw [← Matrix.mul_assoc]
      have he := (number_absorbs_neighbour_P (N := N) (k.val+1)).2
      rw [show k.val+1+1=k.val+2 by omega] at he; rw [he]
    have hm : number (N := N) (k.val+3) * (P k.val * P (k.val+2)) =
        number (k.val+3) * P k.val := by
      rw [P_commute k.val (k.val+2),← Matrix.mul_assoc]
      have he := (number_absorbs_neighbour_P (N := N) (k.val+3)).1
      rw [show k.val+3-1=k.val+2 by omega] at he; rw [he]
    simpa only [Nat.add_assoc,hp,hm]
  have numberP_diagonal {N : ℕ} (u v : ℕ) : number (N := N) u * P v = Matrix.diagonal
        (fun s : HardCore N => ((occReal s u * (1-occReal s v) : ℝ) : ℂ)) := by
    rw [number,P_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    funext s
    cases hu : occupied s.val u <;> cases hv : occupied s.val v <;>
      norm_num [occReal,hu,hv]
  have restrictOp_blockDiagonal_matrix {N : ℕ} (a b cc : ℝ) (k : Fin N) (hr : k.val+2<N) : (Matrix.submatrix (blockDiagonal a b cc k hr) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = Matrix.diagonal (fun s : HardCore N => ((2 * (w a b cc (k.val+1) * occReal s (k.val+1) * (1-occReal s (k.val+4)) - w a b cc (k.val+3) * occReal s (k.val+3) * (1-occReal s k.val)) : ℝ) : ℂ)) := by
    rw [restrictOp_blockDiagonal,numberP_diagonal,numberP_diagonal,
      ← Matrix.diagonal_smul,← Matrix.diagonal_smul,Matrix.diagonal_sub]
    congr 1
    funext s
    have hp : w a b cc (k.val+1) = chainG a b cc (k.val+1)^2 * chainG a b cc (k.val+2)^2 := by simp only [w,chainG,Nat.add_assoc]
    have hm : w a b cc (k.val+3) = chainG a b cc k.val^2 * chainG a b cc (k.val+1)^2 := by rw [w_periodic]; simp only [w,chainG,Nat.add_assoc]
    rw [hp,hm]; simp only [Pi.smul_apply,smul_eq_mul]; push_cast; ring
  have matrix_diagonal_sum {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → HardCore N → ℂ) : (∑ i ∈ s, Matrix.diagonal (f i)) = Matrix.diagonal (fun a => ∑ i ∈ s, f i a) := by
    classical
    ext a b
    by_cases h : a=b <;> simp [Matrix.sum_apply,Matrix.diagonal_apply,h]
  have restrictOp_diagonal_total (N : ℕ) (hN : 3≤N) (a b cc : ℝ) : (Matrix.submatrix (((2*a^2*cc^2 : ℝ) : ℂ) • (fullPAt N 1 - fullPAt N (N-2)) + ∑ k : Fin (N-2), blockDiagonal a b cc (⟨k.val,by omega⟩ : Fin N) (by dsimp; omega)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = Matrix.diagonal (fun s => ((2 * diagonalCoefficient N a b cc s : ℝ) : ℂ)) := by
    classical
    rw [restrictOp_add,restrictOp_complex_smul,restrictOp_sub,
      restrictOp_fullPAt,restrictOp_fullPAt]
    rw [show N-2+1=N-1 by omega,P_sub_diagonal,← Matrix.diagonal_smul]; rw [restrictOp_sum]; simp only [restrictOp_blockDiagonal_matrix]; rw [matrix_diagonal_sum,Matrix.diagonal_add]
    congr 1
    funext s
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((2 *
      (w a b cc (j+1) * occReal s (j+1) * (1-occReal s (j+4)) -
       w a b cc (j+3) * occReal s (j+3) * (1-occReal s j)) : ℝ) : ℂ)) (N-2)]
    unfold diagonalCoefficient; push_cast; rw [← Finset.mul_sum]; ring
  apply diagonal_anticommutator_implies_identity
  change DiagonalAnticommutator
  intro n hn a b cc
  have hN : 3≤3*n := by omega
  have hm : (3*n)%3=0 := by omega
  have he := congrArg ((fun {N : ℕ} (A : FullOperator N) => Matrix.submatrix A (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) (N := 3*n))
    (full_symmetrized_diagonal (3*n) hN hm a b cc)
  simp only [chainG] at he; rw [restrictOp_QR (3*n) (by omega) a b cc,restrictOp_diagonal_total (3*n) hN a b cc] at he; exact he
end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.EndpointIdentity
