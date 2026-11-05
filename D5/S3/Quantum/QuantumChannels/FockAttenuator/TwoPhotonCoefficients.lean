/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoPhotonCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/TwoPhotonCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact symbolic two-photon transition coefficients on the completed Fock space. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.OccupationCoefficients
import Mathlib.Data.Nat.Choose.Cast

/-! # Completed balanced two-photon occupation coefficients

The finite binomial identity is joined to the continuous occupation-coordinate
formula, so the final coefficient formula applies to arbitrary Fock inputs.
-/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter

private theorem guarded_binomial_reciprocity (m n i j k : ℕ)
    (hN : i+j=m+n) (hk : k ≤ n) :
    (if k ≤ i then (m.choose (i-k) : ℝ)*(n.choose k : ℝ) else 0) *
      (i.factorial : ℝ)*(j.factorial : ℝ) =
        (m.factorial : ℝ)*(n.factorial : ℝ)*
          (i.choose k : ℝ)*(j.choose (n-k) : ℝ) := by
  have hf (a : ℕ) : (a.factorial : ℝ) ≠ 0 := by positivity
  by_cases hki : k ≤ i
  · rw [if_pos hki]
    by_cases hnj : n-k ≤ j
    · have him : i-k ≤ m := by omega
      have heq : m-(i-k) = j-(n-k) := by omega
      rw [Nat.cast_choose ℝ him, Nat.cast_choose ℝ hk,
        Nat.cast_choose ℝ hki, Nat.cast_choose ℝ hnj, heq]
      field_simp [hf]
      <;> ring
    · have hmi : m < i-k := by omega
      rw [Nat.choose_eq_zero_of_lt hmi,
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hnj)]
      simp only [Nat.cast_zero, zero_mul, mul_zero]
  · rw [if_neg hki, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hki)]
    simp only [Nat.cast_zero, zero_mul, mul_zero]

private def twoPhotonBinomial (m i : ℕ) : ℝ :=
  ∑ k : Fin 3,
    (if (k : ℕ) ≤ i then (m.choose (i-k) : ℝ)*(Nat.choose 2 k : ℝ) else 0) *
      (-1 : ℝ)^(k : ℕ)

private theorem two_photon_binomial_factorial (m i j : ℕ) (hN : i+j=m+2) :
    twoPhotonBinomial m i * (i.factorial : ℝ)*(j.factorial : ℝ) =
      (m.factorial : ℝ)*(((i : ℝ)-(j : ℝ))^2-((i : ℝ)+(j : ℝ))) := by
  calc
    _ = ∑ k : Fin 3,
        ((m.factorial : ℝ)*(Nat.factorial 2 : ℝ)*
          (i.choose k : ℝ)*(j.choose (2-k) : ℝ)) * (-1 : ℝ)^(k : ℕ) := by
      simp only [twoPhotonBinomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      have h := guarded_binomial_reciprocity m 2 i j k hN (by omega)
      linear_combination (-1 : ℝ)^(k : ℕ) * h
    _ = _ := by
      norm_num [Fin.sum_univ_succ, Nat.cast_choose_two]
      ring

private theorem equal_parameter_fock_coordinate (t : ℝ) (m n i j : ℕ)
    (hN : i+j=m+n) :
    fockExpansion t t m n j i =
      ((t^(m+n)*Real.sqrt (i.factorial : ℝ)*Real.sqrt (j.factorial : ℝ) /
        (Real.sqrt (m.factorial : ℝ)*Real.sqrt (n.factorial : ℝ)) *
          ∑ b : Fin (n+1),
            (if (b : ℕ) ≤ i then
              (m.choose (i-b) : ℝ)*(n.choose b : ℝ) else 0)*(-1 : ℝ)^(b : ℕ) : ℝ) : ℂ) := by
  classical
  let L : ℝ := t^(m+n)*Real.sqrt (i.factorial : ℝ)*Real.sqrt (j.factorial : ℝ) /
    (Real.sqrt (m.factorial : ℝ)*Real.sqrt (n.factorial : ℝ))
  have hterm (a : Fin (m+1)) (b : Fin (n+1)) :
      (((m.choose a : ℝ)*(n.choose b : ℝ)*t^(a : ℕ)*t^(m-a)*
        (-t)^(b : ℕ)*t^(n-b)*Real.sqrt (((a : ℕ)+b).factorial : ℝ)*
        Real.sqrt ((m-a+(n-b)).factorial : ℝ) /
        (Real.sqrt (m.factorial : ℝ)*Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ)*
          (if j=m-a+(n-b) ∧ i=(a : ℕ)+b then 1 else 0) =
      if i=(a : ℕ)+b then
        ((L*(m.choose a : ℝ)*(n.choose b : ℝ)*(-1 : ℝ)^(b : ℕ) : ℝ) : ℂ)
      else 0 := by
    by_cases hi : i=(a : ℕ)+b
    · have hj : j=m-a+(n-b) := by omega
      rw [if_pos ⟨hj, hi⟩, if_pos hi, mul_one]
      have hp : t^(a : ℕ)*t^(m-a)*(-t)^(b : ℕ)*t^(n-b) =
          t^(m+n)*(-1 : ℝ)^(b : ℕ) := by
        rw [neg_pow]
        calc
          _ = (t^(a : ℕ)*t^(m-a))*(t^(b : ℕ)*t^(n-b))*(-1 : ℝ)^(b : ℕ) := by ring
          _ = _ := by
            rw [← pow_add, ← pow_add, show (a : ℕ)+(m-a)=m by omega,
              show (b : ℕ)+(n-b)=n by omega, ← pow_add]
      rw [← hi, ← hj]
      apply congrArg Complex.ofReal
      dsimp only [L]
      calc
        _ = (m.choose a : ℝ)*(n.choose b : ℝ)*
            (t^(a : ℕ)*t^(m-a)*(-t)^(b : ℕ)*t^(n-b))*
            Real.sqrt (i.factorial : ℝ)*Real.sqrt (j.factorial : ℝ) /
              (Real.sqrt (m.factorial : ℝ)*Real.sqrt (n.factorial : ℝ)) := by ring
        _ = _ := by rw [hp]; ring
    · rw [if_neg hi, if_neg (by rintro ⟨_, h⟩; exact hi h), mul_zero]
  have hsum (b : Fin (n+1)) :
      (∑ a : Fin (m+1), if i=(a : ℕ)+b then
        ((L*(m.choose a : ℝ)*(n.choose b : ℝ)*(-1 : ℝ)^(b : ℕ) : ℝ) : ℂ)
      else 0) =
        ((L*(if (b : ℕ) ≤ i then (m.choose (i-b) : ℝ)*(n.choose b : ℝ) else 0)*
          (-1 : ℝ)^(b : ℕ) : ℝ) : ℂ) := by
    by_cases hbi : (b : ℕ) ≤ i
    · rw [if_pos hbi]
      by_cases him : i-b ≤ m
      · let a : Fin (m+1) := ⟨i-b, by omega⟩
        rw [Finset.sum_eq_single a]
        · rw [if_pos (by dsimp only [a]; omega)]
          push_cast
          ring
        · intro c _ hca
          rw [if_neg (by intro h; apply hca; apply Fin.ext; dsimp only [a]; omega)]
        · intro h
          exact (h (Finset.mem_univ a)).elim
      · have hm : m < i-b := Nat.lt_of_not_ge him
        rw [Nat.choose_eq_zero_of_lt hm]
        simp only [Nat.cast_zero, zero_mul, mul_zero, Complex.ofReal_zero]
        apply Finset.sum_eq_zero
        intro a _
        rw [if_neg (by intro h; omega)]
    · rw [if_neg hbi, mul_zero, zero_mul, Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg (by intro h; omega)]
  simp only [fockExpansion, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, fock_pair_coordinate, hterm]
  rw [Finset.sum_comm]
  simp only [hsum, ← Complex.ofReal_sum]
  apply congrArg Complex.ofReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change L * _ * _ = L * (_ * _)
  ring

private theorem balanced_two_photon_amplitude (m i j : ℕ) (hN : i+j=m+2) :
    fockExpansion (Real.sqrt (1/2)) (Real.sqrt (1/2)) m 2 j i =
      ((Real.sqrt (((i+j).choose i : ℝ)/2^(i+j)) *
        (((i : ℝ)-(j : ℝ))^2-((i : ℝ)+(j : ℝ))) /
          Real.sqrt (2*((i : ℝ)+(j : ℝ))*((i : ℝ)+(j : ℝ)-1)) : ℝ) : ℂ) := by
  let N := i+j
  let t := Real.sqrt (1/2 : ℝ)
  let L := t^N*Real.sqrt (i.factorial : ℝ)*Real.sqrt (j.factorial : ℝ) /
    (Real.sqrt (m.factorial : ℝ)*Real.sqrt 2)
  let D := ((i : ℝ)-(j : ℝ))^2-((i : ℝ)+(j : ℝ))
  have hf (a : ℕ) : (a.factorial : ℝ) ≠ 0 := by positivity
  have hNN : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hfact : ((N.choose i : ℕ) : ℝ)*(i.factorial : ℝ)*(j.factorial : ℝ) =
      (N : ℝ)*((N : ℝ)-1)*(m.factorial : ℝ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial (show i ≤ i+j by omega)
    rw [show i+j-i=j by omega] at hnat
    have h := congrArg (fun n : ℕ => (n : ℝ))
      hnat
    simp only [Nat.cast_mul] at h
    rw [hN, Nat.factorial_succ, Nat.factorial_succ] at h
    push_cast at h
    dsimp only [N]
    rw [hN]
    push_cast
    linear_combination h
  have hscalar : L*(m.factorial : ℝ)/((i.factorial : ℝ)*(j.factorial : ℝ)) =
      Real.sqrt ((N.choose i : ℝ)/2^N) /
        Real.sqrt (2*(N : ℝ)*((N : ℝ)-1)) := by
    have hden : 0 ≤ 2*(N : ℝ)*((N : ℝ)-1) :=
      mul_nonneg (by positivity) (by linarith)
    apply (sq_eq_sq₀ (by dsimp [L]; positivity) (by positivity)).mp
    have ht : t^2 = (1/2 : ℝ) := Real.sq_sqrt (by norm_num)
    calc
      _ = (m.factorial : ℝ)/(2^N*2*(i.factorial : ℝ)*(j.factorial : ℝ)) := by
        dsimp only [L]
        simp only [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        rw [pow_right_comm t N 2, ht]
        simp only [div_pow, one_pow]
        field_simp [hf]
        <;> ring
      _ = (N.choose i : ℝ)/(2^N*(2*(N : ℝ)*((N : ℝ)-1))) := by
        apply (div_eq_div_iff (by positivity) (by positivity)).mpr
        linear_combination -(2^N*2)*hfact
      _ = _ := by
        rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hden, div_div]
  have hbin : twoPhotonBinomial m i =
      (m.factorial : ℝ)*D/((i.factorial : ℝ)*(j.factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero (hf i) (hf j))).mpr
    simpa only [mul_assoc, D] using two_photon_binomial_factorial m i j hN
  rw [equal_parameter_fock_coordinate t m 2 i j hN]
  rw [← hN]
  norm_num only [Nat.factorial_two, Nat.cast_ofNat]
  change ((L*twoPhotonBinomial m i : ℝ) : ℂ) = _
  rw [hbin]
  apply congrArg Complex.ofReal
  calc
    _ = (L*(m.factorial : ℝ)/((i.factorial : ℝ)*(j.factorial : ℝ)))*D := by ring
    _ = _ := by
      rw [hscalar]
      dsimp only [N, D]
      push_cast
      ring

/-- The closed balanced two-photon coefficient for every completed input.
The difference of occupations is subtraction in Real, including i<j. -/
theorem balanced_two_photon_occupation_coefficient (a : Fock) (i j : ℕ)
    (hN : 2 ≤ i+j) (hHalf : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    beamSplitter (1/2) hHalf (tensor a (lp.single 2 2 (1 : ℂ))) j i =
      a (i+j-2) *
        ((Real.sqrt (((i+j).choose i : ℝ)/2^(i+j)) *
          (((i : ℝ)-(j : ℝ))^2-((i : ℝ)+(j : ℝ))) /
            Real.sqrt (2*((i : ℝ)+(j : ℝ))*((i : ℝ)+(j : ℝ)-1)) : ℝ) : ℂ) := by
  rw [occupation_coefficient_of_total (1/2) hHalf 2 j i hN a,
    show (1-(1/2) : ℝ) = 1/2 by norm_num,
    balanced_two_photon_amplitude (i+j-2) i j (by omega)]

#print axioms balanced_two_photon_occupation_coefficient

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
