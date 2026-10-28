/- GID: D5/S3/Observer/Linear/GainRayEndpoint
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayEndpoint
   mirror-E: none(waiver:whole-pure-M-endpoint-obstruction)
   anchors: []
   utility: none
   digest: The first and last coefficient rows impose incompatible endpoint signs below the exact readout threshold. -/

import D5.S3.Observer.Linear.GainRayJets
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
Native gain-ray endpoint identities.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Set
namespace D5.S3.Observer.Linear.GainRay

/-- A row of a universal pure-M coefficient identity, with its drift constraint. -/
def EndpointRow (d k : ℕ) (u v : ℝ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ 2 * d + 1 ∧ p.eval 1 = 0 ∧
    (∀ j ≤ d, jet 0 j p phi = if j = k then u else 0) ∧
    (∀ j ≤ d, jet 0 j p psi = if j = k then v else 0)

private theorem golden_distinct : phi ≠ psi :=
  ne_of_gt (lt_trans Real.goldenConj_neg Real.goldenRatio_pos)

private theorem jet_constant (j : ℕ) (c x : ℝ) :
    jet 0 j (C c) x = if j = 0 then c else 0 := by
  cases j with
  | zero => simp [jet]
  | succ j => simp [jet, pow_succ, Module.End.mul_apply, euler]

private theorem jet_subtract (j : ℕ) (p q : ℝ[X]) (x : ℝ) :
    jet 0 j (p-q) x = jet 0 j p x - jet 0 j q x := by simp [jet]

private theorem first_row_factor (d : ℕ) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d 0 u v p) :
    p.derivative = C p.derivative.leadingCoeff *
      ((X-C phi)^d * (X-C psi)^d) := by
  have ha : (X-C phi)^(d + 1) ∣ p-C u :=
    jets_root_dvd 0 phi Real.goldenRatio_ne_zero d (p-C u) (by
      intro j hj
      simp only [jet_subtract, jet_constant, h.2.2.1 j hj, sub_self])
  have hb : (X-C psi)^(d + 1) ∣ p-C v :=
    jets_root_dvd 0 psi Real.goldenConj_ne_zero d (p-C v) (by
      intro j hj
      simp only [jet_subtract, jet_constant, h.2.2.2 j hj, sub_self])
  have ha' : (X-C phi)^d ∣ p.derivative := by
    simpa using pow_sub_one_dvd_derivative_of_pow_dvd ha
  have hb' : (X-C psi)^d ∣ p.derivative := by
    simpa using pow_sub_one_dvd_derivative_of_pow_dvd hb
  have hcop := isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr golden_distinct))
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (((monic_X_sub_C phi).pow d).mul ((monic_X_sub_C psi).pow d))
    (hcop.pow.mul_dvd ha' hb')
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _))
    (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_pow,
    natDegree_X_sub_C, natDegree_X_sub_C]
  have hp := natDegree_derivative_le p
  have hh := h.1
  omega

private theorem first_row_reflection (d : ℕ) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d 0 u v p) : p.eval phi + p.eval psi = 2*p.eval (1/2) := by
  have hψ : psi = 1-phi := by linarith [Real.goldenRatio_add_goldenConj]
  have hr : (((X-C phi)^d * (X-C psi)^d : ℝ[X]).comp (1-X)) =
      (X-C phi)^d * (X-C psi)^d := by
    simp only [mul_comp, pow_comp, sub_comp, X_comp, C_comp]
    have ha : (1-X)-C phi = -(X-C psi) := by rw [hψ, C_sub, C_1]; ring
    have hb : (1-X)-C psi = -(X-C phi) := by rw [hψ, C_sub, C_1]; ring
    rw [ha, hb, neg_pow (X-C psi) d, neg_pow (X-C phi) d]
    have hs : (-1 : ℝ[X])^d * (-1)^d = 1 := by rw [← mul_pow]; simp
    calc _ = ((-1:ℝ[X])^d * (-1)^d) * ((X-C phi)^d * (X-C psi)^d) := by ac_rfl
         _ = _ := by rw [hs, one_mul]
  have hd : (p + p.comp (1-X)).derivative = 0 := by
    rw [derivative_add, derivative_comp_one_sub_X, first_row_factor d u v p h,
      mul_comp, C_comp, hr]
    simp
  have he := eq_C_of_derivative_eq_zero hd
  have ha := congrArg (fun q : ℝ[X] => q.eval phi) he
  have hb := congrArg (fun q : ℝ[X] => q.eval (1/2)) he
  simp only [eval_add, eval_comp, eval_sub, eval_one, eval_X, eval_C] at ha hb
  rw [← hψ] at ha
  norm_num at hb
  simp only [coeff_add] at ha
  linarith

private theorem density_identity (d : ℕ) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d 0 u v p) (x : ℝ) :
    p.derivative.eval x = (p.derivative.leadingCoeff * (-1)^d) *
      ((x-psi)^d * (phi-x)^d) := by
  have hf := first_row_factor d u v p h
  have he := congrArg (fun q : ℝ[X] => q.eval x) hf
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X] at he
  rw [he, show phi-x = -(x-phi) by ring, neg_pow (x-phi) d]
  have hs : (-1:ℝ)^d * (-1)^d = 1 := by rw [← mul_pow]; simp
  symm
  calc _ = p.derivative.leadingCoeff * ((x-phi)^d * (x-psi)^d) *
      ((-1:ℝ)^d * (-1)^d) := by ac_rfl
       _ = _ := by rw [hs, mul_one]

private theorem first_row_sign (d : ℕ) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d 0 u v p) : (u = 0 ∧ v = 0) ∨ u*(u+v) < 0 := by
  have hu : p.eval phi = u := by simpa [jet] using h.2.2.1 0 (by omega)
  have hv : p.eval psi = v := by simpa [jet] using h.2.2.2 0 (by omega)
  let c : ℝ := p.derivative.leadingCoeff * (-1)^d
  have hp : ∀ x ∈ Ioo psi phi, 0 < (x-psi)^d * (phi-x)^d := by
    intro x hx
    exact mul_pos (pow_pos (sub_pos.mpr hx.1) _) (pow_pos (sub_pos.mpr hx.2) _)
  by_cases hc : c = 0
  · left
    have hd : p.derivative = 0 := by
      apply Polynomial.funext
      intro x
      simp only [eval_zero]
      rw [density_identity d u v p h x]
      change c * _ = 0
      rw [hc, zero_mul]
    have he := eq_C_of_derivative_eq_zero hd
    have hval (x : ℝ) : p.eval x = 0 := by
      have hh := h.2.1
      rw [he, eval_C] at hh ⊢
      exact hh
    exact ⟨hu.symm.trans (hval phi), hv.symm.trans (hval psi)⟩
  · right
    have hmid : psi < (1/2:ℝ) := by linarith [Real.goldenConj_neg]
    have hright : (1:ℝ) < phi := Real.one_lt_goldenRatio
    have hψ1 : psi < (1:ℝ) := lt_trans Real.goldenConj_neg zero_lt_one
    have hφmid : (1/2:ℝ) < phi := by linarith
    have hsym := first_row_reflection d u v p h
    rcases lt_or_gt_of_ne hc with hc | hc
    · have hm : StrictAntiOn p.eval (Icc psi phi) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) p.continuous.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [p.deriv, density_identity d u v p h x]
        exact mul_neg_of_neg_of_pos hc (hp x hx)
      have hu0 : u < 0 := by
        have hh := hm ⟨le_of_lt hψ1, le_of_lt hright⟩ ⟨le_of_lt
          (lt_trans Real.goldenConj_neg Real.goldenRatio_pos), le_rfl⟩ hright
        simpa [hu, h.2.1] using hh
      have hm0 : 0 < p.eval (1/2) := by
        have hh := hm ⟨le_of_lt hmid, le_of_lt hφmid⟩
          ⟨le_of_lt hψ1, le_of_lt hright⟩ (by norm_num : (1/2:ℝ) < 1)
        simpa [h.2.1] using hh
      rw [hu, hv] at hsym
      exact mul_neg_of_neg_of_pos hu0 (by linarith)
    · have hm : StrictMonoOn p.eval (Icc psi phi) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _) p.continuous.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [p.deriv, density_identity d u v p h x]
        exact mul_pos hc (hp x hx)
      have hu0 : 0 < u := by
        have hh := hm ⟨le_of_lt hψ1, le_of_lt hright⟩ ⟨le_of_lt
          (lt_trans Real.goldenConj_neg Real.goldenRatio_pos), le_rfl⟩ hright
        simpa [hu, h.2.1] using hh
      have hm0 : p.eval (1/2) < 0 := by
        have hh := hm ⟨le_of_lt hmid, le_of_lt hφmid⟩
          ⟨le_of_lt hψ1, le_of_lt hright⟩ (by norm_num : (1/2:ℝ) < 1)
        simpa [h.2.1] using hh
      rw [hu, hv] at hsym
      exact mul_neg_of_pos_of_neg hu0 (by linarith)

private theorem last_row_factor (d : ℕ) (hd : 1 ≤ d) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d d u v p) :
    ∃ a : ℝ, p = ((X-C phi)^d * (X-C psi)^d) * (C a * (X-1)) := by
  have ha : (X-C phi)^d ∣ p := by
    have hh := jets_root_dvd 0 phi Real.goldenRatio_ne_zero (d-1) p (by
      intro j hj
      rw [h.2.2.1 j (by omega), if_neg (by omega)])
    simpa [Nat.sub_add_cancel hd] using hh
  have hb : (X-C psi)^d ∣ p := by
    have hh := jets_root_dvd 0 psi Real.goldenConj_ne_zero (d-1) p (by
      intro j hj
      rw [h.2.2.2 j (by omega), if_neg (by omega)])
    simpa [Nat.sub_add_cancel hd] using hh
  have hcop := isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr golden_distinct))
  obtain ⟨q, hq⟩ := hcop.pow.mul_dvd ha hb
  have hqdeg : q.natDegree ≤ 1 := by
    by_cases hz : q = 0
    · simp [hz]
    have hdeg : p.natDegree = 2 * d + q.natDegree := by
      rw [hq, natDegree_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (pow_ne_zero _ (X_sub_C_ne_zero _))) hz]
      simp [natDegree_mul, natDegree_pow, X_sub_C_ne_zero]
      omega
    have := h.1
    omega
  obtain ⟨a,b,hlin⟩ := exists_eq_X_add_C_of_natDegree_le_one hqdeg
  have hval : (1-phi)^d * (1-psi)^d * (a+b) = 0 := by
    have he := h.2.1
    rw [hq, hlin] at he
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_add,
      mul_one] using he
  have hab : b = -a := by
    have hne : (1-phi)^d * (1-psi)^d ≠ 0 := mul_ne_zero
      (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_lt Real.one_lt_goldenRatio)))
      (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt (lt_trans Real.goldenConj_neg zero_lt_one))))
    have hh := (mul_eq_zero.mp hval).resolve_left hne
    linarith
  refine ⟨a, ?_⟩
  rw [hq, hlin, hab, C_neg]
  ring

private theorem top_root_derivative (d : ℕ) (x : ℝ) (q : ℝ[X]) :
    (derivative^[d] ((X-C x)^d * q)).eval x = (d.factorial : ℝ) * q.eval x := by
  rw [iterate_derivative_mul, eval_finsetSum,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos d))]
  · simp [iterate_derivative_X_sub_pow_self]
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C,
      sub_self, zero_pow hb0, smul_zero, zero_mul, smul_zero]

private theorem last_row_values (d : ℕ) (hd : 1 ≤ d) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d d u v p) :
    ∃ a : ℝ,
      u = (d.factorial : ℝ) * phi^d * (phi-psi)^d * a * (phi-1) ∧
      v = (d.factorial : ℝ) * psi^d * (psi-phi)^d * a * (psi-1) := by
  obtain ⟨a,he⟩ := last_row_factor d hd u v p h
  have ha : ∀ j < d, (derivative^[j] p).eval phi = 0 := by
    intro j hj
    apply (jets_vanish_iff 0 phi Real.goldenRatio_ne_zero j p).mp _ j le_rfl
    intro k hk
    rw [h.2.2.1 k (by omega), if_neg (by omega)]
  have hb : ∀ j < d, (derivative^[j] p).eval psi = 0 := by
    intro j hj
    apply (jets_vanish_iff 0 psi Real.goldenConj_ne_zero j p).mp _ j le_rfl
    intro k hk
    rw [h.2.2.2 k (by omega), if_neg (by omega)]
  refine ⟨a, ?_, ?_⟩
  · have hj := h.2.2.1 d le_rfl
    rw [if_pos rfl, jet_leading 0 phi d p ha, he, mul_assoc, top_root_derivative] at hj
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_one] at hj
    rw [← hj]
    ring
  · have hj := h.2.2.2 d le_rfl
    have he' : p = (X-C psi)^d * ((X-C phi)^d * (C a * (X-1))) := by
      rw [he]; ring
    rw [if_pos rfl, jet_leading 0 psi d p hb, he', top_root_derivative] at hj
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_one] at hj
    rw [← hj]
    ring

private theorem last_row_sign (d : ℕ) (hd : 1 ≤ d) (u v : ℝ) (p : ℝ[X])
    (h : EndpointRow d d u v p) : 0 ≤ u*(u+v) := by
  obtain ⟨a,hu,hv⟩ := last_row_values d hd u v p h
  have hφψ : phi-1 = -psi := by linarith [Real.goldenRatio_add_goldenConj]
  have hψφ : psi-1 = -phi := by linarith [Real.goldenRatio_add_goldenConj]
  have hprod : psi^d * (psi-phi)^d = (-psi)^d * (phi-psi)^d := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  have hv' : v = (d.factorial : ℝ) * (phi-psi)^d * a * (-psi)^d * (-phi) := by
    rw [hv, hψφ]
    calc _ = (d.factorial:ℝ) * (psi^d * (psi-phi)^d) * a * (-phi) := by ring
         _ = _ := by rw [hprod]; ring
  rw [hφψ] at hu
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hq : 0 ≤ -psi := le_of_lt (neg_pos.mpr Real.goldenConj_neg)
  have hqφ : -psi ≤ phi := by linarith [Real.goldenRatio_add_goldenConj]
  have hp : (-psi)^k ≤ phi^k := pow_le_pow_left₀ hq hqφ _
  have hB : 0 ≤ phi^d * (-psi) - (-psi)^d * phi := by
    rw [hk, pow_succ, pow_succ]
    nlinarith [mul_nonneg (mul_nonneg Real.goldenRatio_pos.le hq) (sub_nonneg.mpr hp)]
  rw [hu, hv']
  have ht : 0 ≤ phi^d * (-psi) := mul_nonneg (pow_nonneg Real.goldenRatio_pos.le _) hq
  have hs := mul_nonneg (sq_nonneg ((d.factorial:ℝ) * (phi-psi)^d * a))
    (mul_nonneg ht hB)
  convert hs using 1 <;> ring

/-- All degrees d>=1, including the equality boundary in the last row at d=1. -/
theorem endpoint_jet_obstruction (d : ℕ) (hd : 1 ≤ d) (u v : ℝ) (f g : ℝ[X])
    (hf : EndpointRow d 0 u v f) (hg : EndpointRow d d u v g) : u = 0 ∧ v = 0 := by
  rcases first_row_sign d u v f hf with h | h
  · exact h
  · have hh := last_row_sign d hd u v g hg
    linarith

private theorem single_gain (d : ℕ) (j : Fin (d + 1)) (x : ℝ) :
    (gain d (Pi.single j 1)).eval x = x^j.val := by
  simp [gain, ofFn_eq_sum_monomial, eval_finsetSum, Pi.single_apply]

/-- The original auxiliary-source identity, on the literal initial-inclusive word.
It admits only the zero source functional through 2m reads. -/
theorem pureM_universal_obstruction (d : ℕ) (hd : 1 ≤ d) (n : ℕ)
    (hn : n + 1 ≤ 2 * (d + 1)) (C : Readout d (List.replicate n false))
    (ell : Mat →ₗ[ℝ] ℝ)
    (hδ : C.mulVec (fun _ => 1) = 0)
    (hid : ∀ (S : Mat) (β : Coeff d),
      C.mulVec (fun i => (gain d β).eval (i.val : ℝ) *
        Matrix.trace (acquisition ((List.replicate n false).take i.val) * S)) =
          ell S • β) : ell = 0 := by
  let u := ell spectralPlus
  let v := ell spectralMinus
  have hread (S : Mat) (i : Fin ((List.replicate n false).length+1)) :
      Matrix.trace (acquisition ((List.replicate n false).take i.val) * S) =
        alpha S * phi^i.val + eta S * psi^i.val := by
    have hi : i.val ≤ n := by have := i.isLt; simp at this; omega
    rw [List.take_replicate, min_eq_left hi, pureM_spectral]
  have hrow (k : Fin (d + 1)) :
      EndpointRow d k.val u v (ofFn ((List.replicate n false).length+1) (C k)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hdeg := ofFn_natDegree_lt
        (by simp : 1 ≤ (List.replicate n false).length+1) (C k)
      simp only [List.length_replicate] at hdeg
      omega
    · have hh := congrFun hδ k
      simpa [Matrix.mulVec, dotProduct, ofFn_eq_sum_monomial, eval_finsetSum] using hh
    · intro j hj
      let j' : Fin (d + 1) := ⟨j, by omega⟩
      have hh := congrFun (hid spectralPlus (Pi.single j' 1)) k
      simp only [single_gain, hread, spectral_basis_weights.1,
        spectral_basis_weights.2.1, one_mul, zero_mul, add_zero,
        Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hh
      rw [jet_ofFn]
      change (∑ i, C k i * ((i.val:ℝ)+0)^j * phi^i.val) = _
      have hkj : (k = j') ↔ j = k.val := by
        constructor
        · intro he; have := congrArg Fin.val he; simpa [j'] using this.symm
        · intro he; exact Fin.ext he.symm
      simpa [Matrix.mulVec, dotProduct, hkj, mul_assoc, add_zero] using hh
    · intro j hj
      let j' : Fin (d + 1) := ⟨j, by omega⟩
      have hh := congrFun (hid spectralMinus (Pi.single j' 1)) k
      simp only [single_gain, hread, spectral_basis_weights.2.2.1,
        spectral_basis_weights.2.2.2, zero_mul, one_mul, zero_add,
        Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hh
      rw [jet_ofFn]
      change (∑ i, C k i * ((i.val:ℝ)+0)^j * psi^i.val) = _
      have hkj : (k = j') ↔ j = k.val := by
        constructor
        · intro he; have := congrArg Fin.val he; simpa [j'] using this.symm
        · intro he; exact Fin.ext he.symm
      simpa [Matrix.mulVec, dotProduct, hkj, mul_assoc, add_zero] using hh
  have huv := endpoint_jet_obstruction d hd u v
    (ofFn _ (C ⟨0, by omega⟩)) (ofFn _ (C ⟨d, by omega⟩))
    (hrow ⟨0, by omega⟩) (hrow ⟨d, by omega⟩)
  ext S
  have hh := congrFun (hid S (Pi.single (⟨0, by omega⟩ : Fin (d + 1)) 1))
    (⟨0, by omega⟩ : Fin (d + 1))
  simp only [single_gain, pow_zero, one_mul, hread, Pi.smul_apply,
    smul_eq_mul, Pi.single_eq_same, mul_one] at hh
  have hplus : ∑ i, C ⟨0, by omega⟩ i * phi^i.val = u := by
    have he := (hrow ⟨0, by omega⟩).2.2.1 0 (by omega)
    simpa [jet_ofFn] using he
  have hminus : ∑ i, C ⟨0, by omega⟩ i * psi^i.val = v := by
    have he := (hrow ⟨0, by omega⟩).2.2.2 0 (by omega)
    simpa [jet_ofFn] using he
  change ell S = 0
  rw [← hh]
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  have he : (∑ i, C ⟨0, by omega⟩ i * (alpha S * phi^i.val)) +
      (∑ i, C ⟨0, by omega⟩ i * (eta S * psi^i.val)) =
      alpha S * u + eta S * v := by
    rw [← hplus, ← hminus, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [he, huv.1, huv.2]
  ring

#print axioms endpoint_jet_obstruction
#print axioms pureM_universal_obstruction

end D5.S3.Observer.Linear.GainRay
