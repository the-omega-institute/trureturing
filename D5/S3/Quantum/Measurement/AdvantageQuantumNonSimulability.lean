/- GID: D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AdvantageQuantumNonSimulability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Advantage-quantum binary measurements admit no finite-copy quantum simulation. -/

import D5.S3.Resource.CompositeCones
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation

/-! Binary advantage-quantum measurements cannot be simulated on any finite number of copies. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace
open D5.S3.Resource.CompositeCones (blockPositive)
open D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability

abbrev BipartiteMatrix (dA dB : ℕ) :=
  Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ

def binaryEffect {dA dB : ℕ} (E : BipartiteMatrix dA dB) (i : Fin 2) :
    BipartiteMatrix dA dB := ![E, 1 - E] i

def IsDovm {dA dB : ℕ} (E : BipartiteMatrix dA dB) : Prop :=
  ∀ i, (binaryEffect E i).IsHermitian ∧ blockPositive (binaryEffect E i)

def aqLeastEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : ℝ := sInf (Set.range hA.eigenvalues)

def aqGreatestEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : ℝ := sSup (Set.range hA.eigenvalues)

def IsAdvantageQuantum {dA dB : ℕ} (E : BipartiteMatrix dA dB) (hE : IsDovm E) : Prop :=
  ∃ i, aqLeastEigenvalue (hE i).1 < 0 ∧
    1 + aqLeastEigenvalue (hE i).1 < aqGreatestEigenvalue (hE i).1 ∧
    aqGreatestEigenvalue (hE i).1 < 1

def InMeasurementDomain {dA dB : ℕ} (E ρ : BipartiteMatrix dA dB) : Prop :=
  ρ.PosSemidef ∧ trace ρ = 1 ∧ ∀ i, 0 ≤ (trace (ρ * binaryEffect E i)).re

def copyState {ι : Type*} [Fintype ι] (n : ℕ) (ρ : Matrix ι ι ℂ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun x y => ∏ k : Fin n, ρ (x k) (y k)

def QuantumSimulable {dA dB : ℕ} (E : BipartiteMatrix dA dB) (n : ℕ) : Prop :=
  ∃ N : Fin 2 → Matrix (Fin n → Fin dA × Fin dB) (Fin n → Fin dA × Fin dB) ℂ,
    IsPOVM N ∧ ∀ ρ, InMeasurementDomain E ρ →
      ∀ i, (trace (copyState n ρ * N i)).re = (trace (ρ * binaryEffect E i)).re

def claim : Prop :=
  ∀ dA dB : ℕ, 1 ≤ dA → 1 ≤ dB → ∀ E : BipartiteMatrix dA dB,
    ∀ hE : IsDovm E, IsAdvantageQuantum E hE → ∀ n : ℕ, ¬ QuantumSimulable E n

private theorem block_trace_nonnegative {dA dB : ℕ} {A : BipartiteMatrix dA dB}
    (hA : blockPositive A) : 0 ≤ (trace A).re := by
  classical
  rw [trace, Complex.re_sum]
  apply Finset.sum_nonneg
  rintro ⟨a, b⟩ _
  change 0 ≤ (A (a, b) (a, b)).re
  have hv : (fun ij : Fin dA × Fin dB =>
      (Pi.single a 1 : Fin dA → ℂ) ij.1 * (Pi.single b 1 : Fin dB → ℂ) ij.2) =
      (Pi.single (a, b) 1 : Fin dA × Fin dB → ℂ) := by
    ext ⟨x, y⟩
    simp only [Pi.single_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  have h := hA (Pi.single a 1) (Pi.single b 1)
  rw [hv] at h
  simpa [dotProduct, mulVec, Pi.single_apply] using h

private theorem eigenstate_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    let P := vecMulVec (⇑(hA.eigenvectorBasis i)) (star (⇑(hA.eigenvectorBasis i)))
    P.PosSemidef ∧ trace P = 1 ∧ (trace (P * A)).re = hA.eigenvalues i := by
  dsimp only
  have hv : star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1 := by
    rw [dotProduct_comm]
    exact hA.eigenvectorBasis.inner_eq_one i
  refine ⟨posSemidef_vecMulVec_self_star _, ?_, ?_⟩
  · rw [trace_vecMulVec, dotProduct_comm, hv]
  · rw [trace_mul_comm, mul_vecMulVec, hA.mulVec_eigenvectorBasis,
      trace_vecMulVec, smul_dotProduct, dotProduct_comm, hv]
    simp only [Complex.smul_re, smul_eq_mul, Complex.one_re, mul_one]

private theorem copyState_posDef {ι : Type*} [Fintype ι]
    {ρ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (n : ℕ) : (copyState n ρ).PosDef := by
  classical
  induction n with
  | zero =>
      have he : copyState 0 ρ = 1 := by
        ext x y
        simp only [copyState, Finset.univ_eq_empty, Finset.prod_empty, one_apply]
        exact (ite_eq_left (Subsingleton.elim x y)).symm
      rw [he]
      exact PosDef.one
  | succ n ih =>
      let e := Fin.succFunEquiv ι n
      have he : copyState (n + 1) ρ = (copyState n ρ ⊗ₖ ρ).submatrix e e := by
        ext x y
        change (∏ k : Fin (n + 1), ρ (x k) (y k)) =
          (∏ k : Fin n, ρ (x k.castSucc) (y k.castSucc)) *
            ρ (x (Fin.last n)) (y (Fin.last n))
        exact Fin.prod_univ_castSucc _
      rw [he]
      exact (ih.kronecker hρ).submatrix e.injective

private theorem faithful_zero_effect {ι : Type*} [Fintype ι]
    {ρ N : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hN : N.PosSemidef)
    (hz : (trace (ρ * N)).re = 0) : N = 0 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let R := ρ.submatrix e e
  let S := N.submatrix e e
  have hR : R.PosDef := hρ.submatrix e.injective
  have hS : S.PosSemidef := hN.submatrix e
  have ht : trace (R * S) = 0 := by
    dsimp only [R, S]
    rw [submatrix_mul_equiv]
    change (∑ i, diag (ρ * N) (e i)) = 0
    exact (e.sum_comp (diag (ρ * N))).trans
      (Complex.ext hz (Complex.nonneg_iff.mp (hρ.posSemidef.trace_mul_nonneg hN)).2.symm)
  have hm := D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero
    R S hR.posSemidef hS ht
  have hs : S = 0 := hR.isUnit.mul_left_cancel (hm.trans (mul_zero R).symm)
  ext i j
  have hij := congrFun (congrFun hs (e.symm i)) (e.symm j)
  change N (e (e.symm i)) (e (e.symm j)) = 0 at hij
  rw [e.apply_symm_apply, e.apply_symm_apply] at hij
  exact hij

private theorem domain_of_selected_probability {dA dB : ℕ} (E ρ : BipartiteMatrix dA dB)
    (hρ : ρ.PosSemidef) (ht : trace ρ = 1) (i : Fin 2)
    (hlo : 0 ≤ (trace (ρ * binaryEffect E i)).re)
    (hhi : (trace (ρ * binaryEffect E i)).re ≤ 1) : InMeasurementDomain E ρ := by
  refine ⟨hρ, ht, ?_⟩
  have hc : (trace (ρ * (1 - E))).re = 1 - (trace (ρ * E)).re := by
    rw [mul_sub, mul_one, trace_sub, ht, Complex.sub_re, Complex.one_re]
  fin_cases i <;> intro j <;> fin_cases j
  · exact hlo
  · change 0 ≤ (trace (ρ * (1 - E))).re
    rw [hc]
    exact sub_nonneg.mpr hhi
  · change (trace (ρ * (1 - E))).re ≤ 1 at hhi
    rw [hc] at hhi
    change 0 ≤ (trace (ρ * E)).re
    linarith
  · exact hlo

private theorem boundary_states {dA dB : ℕ} [Nonempty (Fin dA)] [Nonempty (Fin dB)]
    {A : BipartiteMatrix dA dB} (hA : A.IsHermitian) (hb : blockPositive A)
    (hlo : aqLeastEigenvalue hA < 0) (hhi : aqGreatestEigenvalue hA < 1) :
    (∃ ρ : BipartiteMatrix dA dB, ρ.PosDef ∧ trace ρ = 1 ∧ (trace (ρ * A)).re = 0) ∧
    (∃ σ : BipartiteMatrix dA dB, σ.PosSemidef ∧ trace σ = 1 ∧
      0 < (trace (σ * A)).re ∧ (trace (σ * A)).re < 1) := by
  classical
  obtain ⟨l, hl⟩ : ∃ l, hA.eigenvalues l = aqLeastEigenvalue hA :=
    (Set.range_nonempty hA.eigenvalues).csInf_mem (Set.finite_range _)
  obtain ⟨u, hu⟩ : ∃ u, hA.eigenvalues u = aqGreatestEigenvalue hA :=
    (Set.range_nonempty hA.eigenvalues).csSup_mem (Set.finite_range _)
  have hl0 : hA.eigenvalues l < 0 := hl.trans_lt hlo
  have htr := block_trace_nonnegative hb
  have hsum : (trace A).re = ∑ j, hA.eigenvalues j := by
    change RCLike.re (trace A) = _
    rw [hA.trace_eq_sum_eigenvalues, map_sum]
    simp only [RCLike.ofReal_re]
  have hu0 : 0 < hA.eigenvalues u := by
    by_contra! hn
    have hall : ∀ j, hA.eigenvalues j ≤ 0 := by
      intro j
      apply le_trans ?_ hn
      rw [hu]
      exact le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩
    have hs : (∑ j, hA.eigenvalues j) < ∑ _j : Fin dA × Fin dB, (0 : ℝ) :=
      Finset.sum_lt_sum (fun j _ => hall j) ⟨l, Finset.mem_univ l, hl0⟩
    simp only [Finset.sum_const_zero] at hs
    linarith
  let P := vecMulVec (⇑(hA.eigenvectorBasis l)) (star (⇑(hA.eigenvectorBasis l)))
  let Q := vecMulVec (⇑(hA.eigenvectorBasis u)) (star (⇑(hA.eigenvectorBasis u)))
  obtain ⟨hP, htP, heP⟩ := eigenstate_data hA l
  obtain ⟨hQ, htQ, heQ⟩ := eigenstate_data hA u
  change P.PosSemidef at hP
  change trace P = 1 at htP
  change (trace (P * A)).re = hA.eigenvalues l at heP
  change Q.PosSemidef at hQ
  change trace Q = 1 at htQ
  change (trace (Q * A)).re = hA.eigenvalues u at heQ
  refine ⟨?_, ⟨Q, hQ, htQ, by rw [heQ]; exact hu0, by rw [heQ, hu]; exact hhi⟩⟩
  let d : ℝ := Fintype.card (Fin dA × Fin dB)
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  let a := (trace A).re / d
  have ha : 0 ≤ a := div_nonneg htr hd.le
  have hden : 0 < a - hA.eigenvalues l := by linarith
  let p := -hA.eigenvalues l / (a - hA.eigenvalues l)
  have hp : 0 < p := div_pos (neg_pos.mpr hl0) hden
  have hp1 : p ≤ 1 := (div_le_one hden).mpr (by linarith)
  let ρ : BipartiteMatrix dA dB := (p / d : ℝ) • 1 + (1 - p : ℝ) • P
  have hρ : ρ.PosDef := (PosDef.one.smul (div_pos hp hd)).add_posSemidef
    (hP.smul (sub_nonneg.mpr hp1))
  refine ⟨ρ, hρ, ?_, ?_⟩
  · dsimp only [ρ]
    rw [trace_add, trace_smul, trace_smul, trace_one, htP]
    have hdc : (Fintype.card (Fin dA × Fin dB) : ℂ) = (d : ℂ) := by
      simp only [d, Complex.ofReal_natCast]
    rw [hdc]
    change (p / d : ℝ) • (d : ℂ) + (1 - p : ℝ) • (1 : ℂ) = 1
    simp only [Complex.real_smul]
    norm_cast
    field_simp [ne_of_gt hd]
    ring
  · dsimp only [ρ]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, trace_add,
      trace_smul, trace_smul]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [heP]
    calc
      p / d * (trace A).re + (1 - p) * hA.eigenvalues l =
          p * a + (1 - p) * hA.eigenvalues l := by dsimp only [a]; ring
      _ = 0 := by
        dsimp only [p]
        field_simp [ne_of_gt hden]
        ring

theorem result : claim := by
  intro dA dB hdA hdB E hE hAQ n hsim
  let : Nonempty (Fin dA) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin dB) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hlo, _, hhi⟩ := hAQ
  obtain ⟨⟨ρ, hρ, htρ, hz⟩, ⟨σ, hσ, htσ, hp, hp1⟩⟩ :=
    boundary_states (hE i).1 (hE i).2 hlo hhi
  obtain ⟨N, hN, hs⟩ := hsim
  have hdρ : InMeasurementDomain E ρ :=
    domain_of_selected_probability E ρ hρ.posSemidef htρ i (by rw [hz]) (by rw [hz]; norm_num)
  have hdσ : InMeasurementDomain E σ :=
    domain_of_selected_probability E σ hσ htσ i hp.le hp1.le
  have hn : N i = 0 := faithful_zero_effect (copyState_posDef hρ n) (hN.1 i)
    ((hs ρ hdρ i).trans hz)
  have he := hs σ hdσ i
  rw [hn, mul_zero, trace_zero, Complex.zero_re] at he
  exact (ne_of_gt hp) he.symm

end D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
