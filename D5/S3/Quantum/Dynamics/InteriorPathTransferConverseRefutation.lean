/- GID: D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim; result=D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result; claim=D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim
   digest: A five-vertex weighted path transfers interior states but never transfers endpoint states. -/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-!
# Interior transfer without endpoint transfer

The five-vertex path with weights `2√2, √5, √5, 2√2` has perfect transfer
between its two noncentral interior vertices. Its kernel mode vanishes there,
but fixes the endpoint transfer phase to one. The remaining endpoint phases
would require an odd integer to equal an even integer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Dynamics.InteriorPathTransferConverseRefutation
open Matrix Complex
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-- Interior mirror transfer forces endpoint transfer on every positive weighted path. -/
def claim : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ (r : Fin m → ℝ), (∀ k, 0 < r k) →
    ∀ (q : Fin (m + 1) → ℝ) (j : Fin (m + 1)),
      1 ≤ j.val → j.val ≤ m - 1 → j.val ≠ m - j.val →
        (∃ t : ℝ, 0 < t ∧ HasPST (pathHamiltonian r q) t j (Fin.rev j)) →
          ∃ s : ℝ, 0 < s ∧ HasPST (pathHamiltonian r q) s 0 (Fin.last m)

private def weights : Fin 4 → ℝ := ![2 * Real.sqrt 2, Real.sqrt 5, Real.sqrt 5, 2 * Real.sqrt 2]
private def H : Matrix (Fin 5) (Fin 5) ℂ := pathHamiltonian weights 0
private def u (z : ℂ) : Fin 5 → ℂ := ![1, z, 0, -z, -1]
private def w (z : ℂ) : Fin 5 → ℂ :=
  ![2, 3 * z, (Real.sqrt 2 : ℂ) * Real.sqrt 5, 3 * z, 2]
private def v₀ : Fin 5 → ℂ := ![-(Real.sqrt 5 : ℂ), 0, 2 * Real.sqrt 2, 0, -(Real.sqrt 5 : ℂ)]
private def τ : ℝ := 2 * Real.pi / (2 * Real.sqrt 2)

private lemma weights_pos : ∀ k, 0 < weights k := by
  intro k
  fin_cases k <;> norm_num [weights]

private lemma hamiltonian_entries : H =
    !![0, 2 * (Real.sqrt 2 : ℂ), 0, 0, 0;
       2 * (Real.sqrt 2 : ℂ), 0, Real.sqrt 5, 0, 0;
       0, Real.sqrt 5, 0, Real.sqrt 5, 0;
       0, 0, Real.sqrt 5, 0, 2 * (Real.sqrt 2 : ℂ);
       0, 0, 0, 2 * (Real.sqrt 2 : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, pathHamiltonian, weights]

private lemma spectral_data :
    H *ᵥ v₀ = (0 : ℂ) • v₀ ∧
    H *ᵥ u 1 = (2 * (Real.sqrt 2 : ℂ)) • u 1 ∧
    H *ᵥ u (-1) = (-2 * (Real.sqrt 2 : ℂ)) • u (-1) ∧
    H *ᵥ w 1 = (3 * (Real.sqrt 2 : ℂ)) • w 1 ∧
    H *ᵥ w (-1) = (-3 * (Real.sqrt 2 : ℂ)) • w (-1) := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have h5 : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [hamiltonian_entries]
  repeat' apply And.intro
  all_goals
    ext i
    fin_cases i <;>
      norm_num [u, w, v₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring_nf <;> simp [h2, h5] <;> ring

private lemma eigen_exp (s : ℝ) (v : Fin 5 → ℂ) (E : ℂ)
    (hv : H *ᵥ v = E • v) :
    NormedSpace.exp (((s : ℂ) * I) • H) *ᵥ v =
      Complex.exp ((s : ℂ) * I * E) • v := by
  apply exp_mulVec_of_eigenvector
  rw [smul_mulVec, hv, smul_smul]

private lemma interior_decomposition :
    (Pi.single 1 1 : Fin 5 → ℂ) =
      (1 / 4 : ℂ) • u 1 - (1 / 4 : ℂ) • u (-1) +
        (1 / 12 : ℂ) • w 1 - (1 / 12 : ℂ) • w (-1) ∧
    (Pi.single 3 1 : Fin 5 → ℂ) =
      -(1 / 4 : ℂ) • u 1 + (1 / 4 : ℂ) • u (-1) +
        (1 / 12 : ℂ) • w 1 - (1 / 12 : ℂ) • w (-1) := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [u, w, Pi.single_apply]

private lemma phases :
    Complex.exp ((τ : ℂ) * I * (2 * (Real.sqrt 2 : ℂ))) = 1 ∧
    Complex.exp ((τ : ℂ) * I * (-2 * (Real.sqrt 2 : ℂ))) = 1 ∧
    Complex.exp ((τ : ℂ) * I * (3 * (Real.sqrt 2 : ℂ))) = -1 ∧
    Complex.exp ((τ : ℂ) * I * (-3 * (Real.sqrt 2 : ℂ))) = -1 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have ht : (τ : ℂ) * (Real.sqrt 2 : ℂ) = Real.pi := by
    dsimp [τ]
    push_cast
    field_simp
    <;> ring
  have hp (n : ℕ) : Complex.exp ((τ : ℂ) * I * (n * (Real.sqrt 2 : ℂ))) = (-1 : ℂ) ^ n := by
    rw [show (τ : ℂ) * I * (n * (Real.sqrt 2 : ℂ)) =
      n * ((τ : ℂ) * (Real.sqrt 2 : ℂ)) * I by ring, ht,
      mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hn (n : ℕ) : Complex.exp ((τ : ℂ) * I * (- (n : ℂ) * (Real.sqrt 2 : ℂ))) =
      ((-1 : ℂ) ^ n)⁻¹ := by
    rw [show (τ : ℂ) * I * (- (n : ℂ) * (Real.sqrt 2 : ℂ)) =
      -((τ : ℂ) * I * (n * (Real.sqrt 2 : ℂ))) by ring,
      Complex.exp_neg, hp]
  have p2 := hp 2
  have pn2 := hn 2
  have p3 := hp 3
  have pn3 := hn 3
  norm_num at p2 pn2 p3 pn3
  exact ⟨p2, by simpa only [neg_mul, mul_neg] using pn2,
    p3, by simpa only [neg_mul, mul_neg] using pn3⟩

private lemma interior_transfer : ∃ t : ℝ, 0 < t ∧ HasPST H t 1 3 := by
  obtain ⟨_, ea, ena, em, enm⟩ := spectral_data
  obtain ⟨pa, pna, pm, pnm⟩ := phases
  have hu := eigen_exp τ _ _ ea
  have hun := eigen_exp τ _ _ ena
  have hw := eigen_exp τ _ _ em
  have hwn := eigen_exp τ _ _ enm
  rw [pa, one_smul] at hu
  rw [pna, one_smul] at hun
  rw [pm, neg_one_smul] at hw
  rw [pnm, neg_one_smul] at hwn
  have hv : NormedSpace.exp (((τ : ℂ) * I) • H) *ᵥ (Pi.single 3 1 : Fin 5 → ℂ) =
      -(Pi.single 1 1 : Fin 5 → ℂ) := by
    rw [interior_decomposition.2, mulVec_sub, mulVec_add, mulVec_add,
      mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, hu, hun, hw, hwn,
      interior_decomposition.1]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨τ, by dsimp [τ]; positivity, ?_⟩
  have he := congrFun hv 1
  simp only [mulVec_single_one, col_apply, Pi.neg_apply, Pi.single_eq_same] at he
  unfold HasPST
  rw [hamiltonianPropagator_neg, he]
  norm_num

private lemma endpoint_column (s : ℝ) (hpst : HasPST H s 0 4) (x : Fin 5) :
    NormedSpace.exp (((s : ℂ) * I) • H) x 4 =
      if x = 0 then NormedSpace.exp (((s : ℂ) * I) • H) 0 4 else 0 := by
  let A := (((s / Real.pi : ℝ) : ℂ)) • H
  have hscale : (((Real.pi : ℂ) * I) • A) = ((s : ℂ) * I) • H := by
    dsimp only [A]
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  have hA : A.IsHermitian :=
    (pathHamiltonian_isHermitian weights 0).smul (by
      change star ((s / Real.pi : ℝ) : ℂ) = _
      simp)
  have hp : HasPST A Real.pi 0 4 := by
    unfold HasPST at hpst ⊢
    rw [hamiltonianPropagator_neg, hscale]
    simpa only [hamiltonianPropagator_neg] using hpst
  simpa only [hscale] using pst_column hA 0 4 hp x

private lemma endpoint_eigen_phase (s : ℝ) (hpst : HasPST H s 0 4)
    (v : Fin 5 → ℂ) (E : ℂ) (hv : H *ᵥ v = E • v) :
    Complex.exp ((s : ℂ) * I * E) * v 4 =
      NormedSpace.exp (((s : ℂ) * I) • H) 0 4 * v 0 := by
  have hT : (NormedSpace.exp (((s : ℂ) * I) • H))ᵀ =
      NormedSpace.exp (((s : ℂ) * I) • H) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
    change NormedSpace.exp (_ • (pathHamiltonian weights 0)ᵀ) = _
    rw [pathHamiltonian_transpose]
    rfl
  have he := congrFun (eigen_exp s v E hv) 4
  simp only [Pi.smul_apply, smul_eq_mul] at he
  rw [← he]
  change (∑ k, NormedSpace.exp (((s : ℂ) * I) • H) 4 k * v k) = _
  calc
    _ = ∑ k, (if k = 0 then NormedSpace.exp (((s : ℂ) * I) • H) 0 4 else 0) * v k := by
      apply Finset.sum_congr rfl
      intro k _
      have hk := congrFun (congrFun hT k) 4
      rw [transpose_apply] at hk
      rw [hk, endpoint_column s hpst]
    _ = _ := by simp

private lemma no_endpoint_transfer (s : ℝ) : ¬ HasPST H s 0 4 := by
  intro hpst
  obtain ⟨e0, ea, _, em, _⟩ := spectral_data
  have h0 := endpoint_eigen_phase s hpst v₀ 0 e0
  have hn : (-(Real.sqrt 5 : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
  have hγ : NormedSpace.exp (((s : ℂ) * I) • H) 0 4 = 1 := by
    apply mul_right_cancel₀ hn
    simpa [v₀] using h0.symm
  have ha : Complex.exp ((s : ℂ) * I * (2 * (Real.sqrt 2 : ℂ))) = -1 := by
    have he := endpoint_eigen_phase s hpst (u 1) _ ea
    simp [u, hγ] at he
    linear_combination -he
  have hm : Complex.exp ((s : ℂ) * I * (3 * (Real.sqrt 2 : ℂ))) = 1 := by
    have he := endpoint_eigen_phase s hpst (w 1) _ em
    norm_num [w, hγ] at he
    exact he
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hka : Complex.exp ((Real.pi : ℂ) * I *
      ((s * (2 * Real.sqrt 2) / Real.pi : ℝ) : ℂ)) = -1 := by
    convert ha using 1
    push_cast
    field_simp
  have hlm : Complex.exp ((Real.pi : ℂ) * I *
      ((s * (3 * Real.sqrt 2) / Real.pi : ℝ) : ℂ)) = 1 := by
    convert hm using 1
    push_cast
    field_simp
  obtain ⟨k, hk⟩ := exists_int_of_exp_eq_neg_one hka
  obtain ⟨l, hl⟩ := exists_int_of_exp_eq_one hlm
  have hrel : 3 * (s * (2 * Real.sqrt 2) / Real.pi) =
      2 * (s * (3 * Real.sqrt 2) / Real.pi) := by ring
  rw [hk, hl] at hrel
  have hi : 6 * k + 3 = 4 * l := by
    exact_mod_cast (show (6 : ℝ) * k + 3 = 4 * l by linarith)
  omega

theorem result : ¬ claim := by
  intro hc
  obtain ⟨s, _, hs⟩ := hc 4 (by omega) weights weights_pos 0 1
    (by decide) (by decide) (by decide) interior_transfer
  exact no_endpoint_transfer s hs

end D5.S3.Quantum.Dynamics.InteriorPathTransferConverseRefutation
