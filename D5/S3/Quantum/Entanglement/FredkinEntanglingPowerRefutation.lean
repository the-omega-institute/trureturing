/- GID: D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.claim; result=D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result; claim=D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.claim
   digest: The four-qubit Fredkin gate makes more than 2 ebits across AD:BC (2410.15253). -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit input: the output
  amplitude is expanded, the reduced state is conjugated to a rational matrix whose spectrum
  is checked by `decide`, the existing spectral bridges give the entropy, and pinned
  logarithm bounds with `norm_num` and `nlinarith` compare it with two ebits)
escape_witness: null
admission_basis: open-problem-resolution (issue #11460; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition
  (`DensityState`), D5/S3/Quantum/Divergence/VonNeumannEntropyPinching (`vonNeumannEntropy`),
  D5/S3/Quantum/Information/PartialTraceMutualInformation (`marginalRight`,
  `spectral_sum_eq_of_charpoly_prod`), D5/S3/Quantum/Information/InputInformationBalance
  (`entropy_eq_sum`)
-/

import D5.S3.Quantum.Information.InputInformationBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.FredkinEntanglingPowerRefutation

/-!
X. Qiu, Z. Song and L. Chen, *Multipartite entangling power by von Neumann entropy*,
arXiv:2410.15253 (Phys. Rev. A 111, 022407 (2025)). The entanglement generation `K_{L:Lᶜ}(U)` of
a gate `U` on parties `A₁, …, Aₙ` is the supremum, over pure inputs `ψᵢ` of each party together
with a local auxiliary system `Rᵢ`, of the von Neumann entropy in ebits of the reduced state of
`U(ψ₁ ⊗ ⋯ ⊗ ψₙ)` on `L`. For the four-qubit Fredkin gate
`F₄ = (|00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10|)_{AB} ⊗ I_{CD} + |11⟩⟨11|_{AB} ⊗ (S₂)_{CD}` the paper shows
`K_{AD:BC}(F₄) ∈ [2, log₂ 5]` and conjectures `K_{AD:BC}(F₄) = 2`. The conjecture fails: for
`ψ_A = (3|0⟩ + 20|1⟩)/√409`, `ψ_B = √(2/75)|0⟩ + √(73/75)|1⟩` and
`ψ_C = ψ_D = ½(|00⟩ + |01⟩ + |10⟩ − |11⟩)` (a qubit with an auxiliary qubit), the reduced state on
`A D R_D` has spectrum `(1752, 1460, 1460, 1460, 3, 0, 0, 0)/6135` and entropy
`2.00034… > 2` ebits.
-/

open Matrix Polynomial
open scoped Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance

/-- A party: a qubit together with a local auxiliary system of dimension `d`. -/
abbrev Party (d : ℕ) := Fin 2 × Fin d

/-- The SWAP gate `S₂` on two qubits, the permutation matrix of `(c, d) ↦ (d, c)`. -/
def swapGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (Equiv.prodComm (Fin 2) (Fin 2)).toPEquiv.toMatrix

/-- The four-qubit Fredkin gate on the qubit labels `((a, b), (c, d))`:
`F₄ = (|00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10|)_{AB} ⊗ I_{CD} + |11⟩⟨11|_{AB} ⊗ (S₂)_{CD}`. -/
def fredkin4 :
    Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  (single (0, 0) (0, 0) 1 + single (0, 1) (0, 1) 1 + single (1, 0) (1, 0) 1) ⊗ₖ 1 +
    single (1, 1) (1, 1) 1 ⊗ₖ swapGate

/-- The amplitudes of `(F₄ ⊗ I_R)(ψ_A ⊗ ψ_B ⊗ ψ_C ⊗ ψ_D)`, indexed by the cut
`A R_A D R_D : B R_B C R_C`: `F₄` acts on the qubits and the identity on the auxiliary
systems. -/
def output {dA dB dC dD : ℕ} (ψA : Party dA → ℂ) (ψB : Party dB → ℂ) (ψC : Party dC → ℂ)
    (ψD : Party dD → ℂ) (z : (Party dA × Party dD) × (Party dB × Party dC)) : ℂ :=
  ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
    fredkin4 ((z.1.1.1, z.2.1.1), (z.2.2.1, z.1.2.1)) q *
      (ψA (q.1.1, z.1.1.2) * ψB (q.1.2, z.2.1.2) * ψC (q.2.1, z.2.2.2) * ψD (q.2.2, z.1.2.2))

/-- The entanglement in ebits across `A R_A D R_D : B R_B C R_C` that `F₄` generates from product
inputs: for auxiliary dimensions `d_A, …, d_D`, unit inputs `ψ_A, …, ψ_D` and the pure output
state `ρ`, the von Neumann entropy of the reduced state on `A R_A D R_D` divided by `log 2`. -/
def generatedEntanglement : Set ℝ :=
  {E | ∃ (dA dB dC dD : ℕ) (ψA : Party dA → ℂ) (ψB : Party dB → ℂ) (ψC : Party dC → ℂ)
      (ψD : Party dD → ℂ) (ρ : DensityState ((Party dA × Party dD) × (Party dB × Party dC))),
      star ψA ⬝ᵥ ψA = 1 ∧ star ψB ⬝ᵥ ψB = 1 ∧ star ψC ⬝ᵥ ψC = 1 ∧ star ψD ⬝ᵥ ψD = 1 ∧
      (∀ i j, ρ.1 i j = output ψA ψB ψC ψD i * star (output ψA ψB ψC ψD j)) ∧
      E = vonNeumannEntropy (marginalRight ρ) / Real.log 2}

/-- The entanglement generation `K_{AD:BC}(F₄)`, the supremum of the generated entanglement. -/
noncomputable def entanglementGeneration : ℝ := sSup generatedEntanglement

/-- The conjecture of arXiv:2410.15253: `K_{AD:BC}(F₄) = 2`. -/
def claim : Prop := entanglementGeneration = 2

/-! The input of the counterexample and the rational data of its reduced state. -/

private abbrev Cut := Party 1 × Party 2

private def enc (x : Cut) : Fin 8 := ⟨4 * x.1.1.val + 2 * x.2.1.val + x.2.2.val, by omega⟩

private def chiq (p : Party 2) : ℚ := if p.1 = 1 ∧ p.2 = 1 then -1/2 else 1/2

private def Nq : Matrix Cut Cut ℚ := fun x y =>
  if x.1.1 = 1 ∧ y.1.1 = 1 then chiq (x.2.1, y.2.2) * chiq (y.2.1, x.2.2)
  else chiq y.2 * chiq x.2

private def Vq : Matrix Cut Cut ℚ := diagonal fun x => if x.1.1 = 0 then 9/409 else 400/409
private def Wq : Matrix Cut Cut ℚ := diagonal fun y => if y.1.1 = 0 then 2/75 else 73/75

private def Ptab : Fin 8 → Fin 8 → ℚ := ![
  ![-1, -1, 1, 70, 0, 0, 0, -40],
  ![1, 0, 0, 70, 0, 0, 0, -40],
  ![0, 1, 0, 70, 0, 0, 0, -40],
  ![0, 0, 1, -70, 0, 0, 0, 40],
  ![0, 0, 0, -3, -1, -1, 1, -21],
  ![0, 0, 0, -3, 1, 0, 0, -21],
  ![0, 0, 0, -3, 0, 1, 0, -21],
  ![0, 0, 0, 3, 0, 0, 1, 21]]
private def Qtab : Fin 8 → Fin 8 → ℚ := fun i j => (![
  ![-1590, 4770, -1590, 1590, 0, 0, 0, 0],
  ![-1590, -1590, 4770, 1590, 0, 0, 0, 0],
  ![1590, 1590, 1590, 4770, 0, 0, 0, 0],
  ![21, 21, 21, -21, -40, -40, -40, 40],
  ![0, 0, 0, 0, -1590, 4770, -1590, 1590],
  ![0, 0, 0, 0, -1590, -1590, 4770, 1590],
  ![0, 0, 0, 0, 1590, 1590, 1590, 4770],
  ![-3, -3, -3, 3, -70, -70, -70, 70]] i j) / 6360
private def mu : Fin 8 → ℚ :=
  ![0, 0, 0, 3/6135, 1460/6135, 1460/6135, 1460/6135, 1752/6135]

private def Pq : Matrix Cut Cut ℚ := fun x y => Ptab (enc x) (enc y)
private def Qq : Matrix Cut Cut ℚ := fun x y => Qtab (enc x) (enc y)
private def Dq : Matrix Cut Cut ℚ := diagonal fun x => mu (enc x)

private noncomputable def ψA : Party 1 → ℂ := fun p =>
  (((if p.1 = 0 then 3 else 20 : ℝ) / Real.sqrt 409 : ℝ) : ℂ)
private noncomputable def ψB : Party 1 → ℂ := fun p =>
  (((if p.1 = 0 then Real.sqrt (2/75) else Real.sqrt (73/75)) : ℝ) : ℂ)
private def χ : Party 2 → ℂ := fun p => ((chiq p : ℚ) : ℂ)

private noncomputable def Φ : Cut × Cut → ℂ := output ψA ψB χ χ
private noncomputable def Mx : Matrix Cut Cut ℂ := Matrix.of fun x y => Φ (x, y)
private noncomputable def Dx : Matrix Cut Cut ℂ := diagonal fun x => ψA x.1
private noncomputable def Dy : Matrix Cut Cut ℂ := diagonal fun y => ψB y.1

/-- The conjecture fails: the input above generates `2.00034…` ebits across `AD:BC`. -/
theorem result : ¬ claim := by
  intro h
  -- The Fredkin gate on a product input.
  have hout : ∀ z : Cut × Cut, Φ z = ψA z.1.1 * ψB z.2.1 *
      (if z.1.1.1 = 1 ∧ z.2.1.1 = 1 then χ (z.1.2.1, z.2.2.2) * χ (z.2.2.1, z.1.2.2)
        else χ z.2.2 * χ z.1.2) := by
    rintro ⟨⟨⟨a, ra⟩, ⟨d, rd⟩⟩, ⟨⟨b, rb⟩, ⟨c, rc⟩⟩⟩
    simp only [Φ, output, fredkin4, swapGate, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.add_apply, kroneckerMap_apply, single_apply, one_apply, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp <;> ring
  have hΦ : ∀ z : Cut × Cut, Φ z = ψA z.1.1 * ψB z.2.1 * ((Nq z.1 z.2 : ℚ) : ℂ) := by
    intro z
    rw [hout]
    simp only [Nq, χ, chiq]
    split_ifs <;> push_cast <;> ring
  -- Removing the square roots: `M = D_A N D_B`.
  have hM : Mx = Dx * Nq.map (Rat.castHom ℂ) * Dy := by
    ext x y
    simp only [Mx, Dx, Dy, of_apply, diagonal_mul, mul_diagonal, map_apply, Rat.coe_castHom, hΦ]
    ring
  have hDy : Dy * Dyᴴ = Wq.map (Rat.castHom ℂ) := by
    have h1 : Real.sqrt (2/75) * Real.sqrt (2/75) = 2/75 := Real.mul_self_sqrt (by norm_num)
    have h2 : Real.sqrt (73/75) * Real.sqrt (73/75) = 73/75 := Real.mul_self_sqrt (by norm_num)
    rw [Dy, diagonal_conjTranspose, diagonal_mul_diagonal, Wq, diagonal_map (map_zero _)]
    congr 1
    funext y
    simp only [ψB, Pi.star_apply, Rat.coe_castHom]
    split_ifs
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, h1]; push_cast; ring
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, h2]; push_cast; ring
  have hDx : Dxᴴ * Dx = Vq.map (Rat.castHom ℂ) := by
    have h409 : Real.sqrt 409 * Real.sqrt 409 = 409 := Real.mul_self_sqrt (by norm_num)
    rw [Dx, diagonal_conjTranspose, diagonal_mul_diagonal, Vq, diagonal_map (map_zero _)]
    congr 1
    funext x
    simp only [ψA, Pi.star_apply, Rat.coe_castHom]
    split_ifs
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, div_mul_div_comm, h409]
      push_cast; ring
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, div_mul_div_comm, h409]
      push_cast; ring
  have hN : (Nq.map (Rat.castHom ℂ))ᴴ = Nqᵀ.map (Rat.castHom ℂ) := by
    ext x y
    simp [conjTranspose_apply]
  have hcomm : Mx * Mxᴴ = Dx * (Nq.map (Rat.castHom ℂ) * (Dy * Dyᴴ) *
      (Nq.map (Rat.castHom ℂ))ᴴ * Dxᴴ) := by
    rw [hM, conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hrat : Nq.map (Rat.castHom ℂ) * (Dy * Dyᴴ) * (Nq.map (Rat.castHom ℂ))ᴴ * Dxᴴ * Dx =
      (Nq * Wq * Nqᵀ * Vq).map (Rat.castHom ℂ) := by
    rw [Matrix.mul_assoc _ Dxᴴ Dx, hDx, hDy, hN]
    simp only [Matrix.map_mul]
  -- The rational matrix `N W Nᵀ V` is `P diag(μ) P⁻¹`.
  have hT : (Nq * Wq * Nqᵀ * Vq).charpoly = ∏ x, (X - C (mu (enc x))) := by
    have hPQ : Pq * Qq = 1 := by decide +kernel
    have hTP : Nq * Wq * Nqᵀ * Vq * Pq = Pq * Dq := by decide +kernel
    have e : Nq * Wq * Nqᵀ * Vq = Pq * (Dq * Qq) := by
      rw [← Matrix.mul_assoc, ← hTP, Matrix.mul_assoc _ Pq Qq, hPQ, Matrix.mul_one]
    rw [e, charpoly_mul_comm, Matrix.mul_assoc, mul_eq_one_comm.mp hPQ, Matrix.mul_one, Dq,
      charpoly_diagonal]
  have hcharpoly : (Mx * Mxᴴ).charpoly = ∏ x, (X - C ((mu (enc x) : ℚ) : ℂ)) := by
    rw [hcomm, charpoly_mul_comm, hrat, charpoly_map, hT, Polynomial.map_prod]
    simp
  have htrace : (Mx * Mxᴴ).trace = 1 := by
    have htr : (Nq * Wq * Nqᵀ * Vq).trace = 1 := by decide +kernel
    rw [hcomm, trace_mul_comm, hrat]
    simp only [Matrix.trace, diag_apply, map_apply]
    rw [← map_sum, show (∑ i, (Nq * Wq * Nqᵀ * Vq) i i) = 1 from htr, map_one]
  -- The pure output state and its reduced state on `A D R_D`.
  let ρ : DensityState (Cut × Cut) :=
    ⟨CStarMatrix.ofMatrix (vecMulVec Φ (star Φ)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (posSemidef_vecMulVec_self_star Φ).nonneg, by
        simp only [Matrix.trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, Mx,
          of_apply] at htrace
        change ∑ z, vecMulVec Φ (star Φ) z z = 1
        simp only [vecMulVec_apply, Pi.star_apply]
        rw [Fintype.sum_prod_type]
        exact htrace⟩
  have hmarg : CStarMatrix.ofMatrix.symm (marginalRight ρ).1 = Mx * Mxᴴ := by
    ext a c
    simp [ρ, marginalRight, partialTraceRight, vecMulVec_apply, Matrix.mul_apply,
      conjTranspose_apply, Mx]
  have hH : (CStarMatrix.ofMatrix.symm (marginalRight ρ).1).IsHermitian := by
    rw [hmarg]; exact isHermitian_mul_conjTranspose_self Mx
  have hc : (CStarMatrix.ofMatrix.symm (marginalRight ρ).1).charpoly =
      ∏ x, (X - C ((RCLike.ofReal ((mu (enc x) : ℝ))) : ℂ)) := by
    rw [hmarg, hcharpoly]
    simp
  have hentropy : vonNeumannEntropy (marginalRight ρ) =
      Real.negMulLog (3/6135) + 3 * Real.negMulLog (1460/6135) +
        Real.negMulLog (1752/6135) := by
    rw [entropy_eq_sum, spectral_sum_eq_of_charpoly_prod hH _ Real.negMulLog hc]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, enc, mu]
    ring
  -- The entropy exceeds two ebits.
  have hlog : 2 * Real.log 2 < Real.negMulLog (3/6135) + 3 * Real.negMulLog (1460/6135) +
      Real.negMulLog (1752/6135) := by
    have key : ∀ k : ℝ, 0 < k → Real.negMulLog (k / 6135) =
        k / 6135 * (2 * Real.log 2 + Real.log (6135 / (4 * k))) := by
      intro k hk
      rw [Real.negMulLog, show k / 6135 = (4 * (6135 / (4 * k)))⁻¹ by field_simp, Real.log_inv,
        Real.log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow]
      field_simp
      push_cast
      ring
    rw [key 3 (by norm_num), key 1460 (by norm_num), key 1752 (by norm_num)]
    have l1 : 6 < Real.log (6135 / (4 * 3)) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h6]
      calc Real.exp 1 ^ 6 < 2.7182818286 ^ 6 :=
            pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
        _ < 6135 / (4 * 3) := by norm_num
    have l2 : -((-295/5840 : ℝ) + (-295/5840)^2/2 + (-295/5840)^3/3) -
        (295/5840)^4/(1 - 295/5840) ≤ Real.log (6135 / (4 * 1460)) := by
      have h := Real.abs_log_sub_add_sum_range_le (x := -295/5840) (by norm_num [abs_of_neg]) 3
      rw [show (1 : ℝ) - -295/5840 = 6135 / (4 * 1460) by norm_num] at h
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num [abs_of_neg] at h ⊢
      linarith [(abs_le.mp h).1]
    have l3 : -((873/7008 : ℝ) + (873/7008)^2/2 + (873/7008)^3/3 + (873/7008)^4/4) -
        (873/7008)^5/(1 - 873/7008) ≤ Real.log (6135 / (4 * 1752)) := by
      have h := Real.abs_log_sub_add_sum_range_le (x := 873/7008) (by norm_num [abs_of_pos]) 4
      rw [show (1 : ℝ) - 873/7008 = 6135 / (4 * 1752) by norm_num] at h
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
      norm_num [abs_of_pos] at h ⊢
      linarith [(abs_le.mp h).1]
    norm_num at l1 l2 l3 ⊢
    linarith only [l1, l2, l3]
  -- The input is admissible.
  have hunitA : star ψA ⬝ᵥ ψA = 1 := by
    have h409 : Real.sqrt 409 * Real.sqrt 409 = 409 := Real.mul_self_sqrt (by norm_num)
    simp only [dotProduct, Pi.star_apply, ψA, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_one, Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False by decide, if_false,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      div_mul_div_comm, h409]
    norm_num
  have hunitB : star ψB ⬝ᵥ ψB = 1 := by
    have h1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2/75 by norm_num)
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 73/75 by norm_num)
    simp only [dotProduct, Pi.star_apply, ψB, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_one, Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False by decide, if_false,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add, h1, h2]
    norm_num
  have hunitC : star χ ⬝ᵥ χ = 1 := by
    simp only [dotProduct, Pi.star_apply, χ, chiq, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  have hw : vonNeumannEntropy (marginalRight ρ) / Real.log 2 ∈ generatedEntanglement :=
    ⟨1, 1, 2, 2, ψA, ψB, χ, χ, ρ, hunitA, hunitB, hunitC, hunitC,
      fun i j => by simp [ρ, Φ, vecMulVec_apply], rfl⟩
  have hgt : 2 < vonNeumannEntropy (marginalRight ρ) / Real.log 2 := by
    rw [hentropy, lt_div_iff₀ (Real.log_pos (by norm_num))]
    linarith [hlog]
  -- `K = 2` would force `sSup` to bound the witness, or to vanish.
  by_cases hb : BddAbove generatedEntanglement
  · have hle := le_csSup hb hw
    rw [show sSup generatedEntanglement = 2 from h] at hle
    linarith
  · rw [claim, entanglementGeneration, Real.sSup_of_not_bddAbove hb] at h
    norm_num at h

end D5.S3.Quantum.Entanglement.FredkinEntanglingPowerRefutation
