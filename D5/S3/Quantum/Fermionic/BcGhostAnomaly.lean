/- GID: D5/S3/Quantum/Fermionic/BcGhostAnomaly
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostAnomaly
   mirror-E: none(waiver:algebraic-ghost-brst-anomaly)
   anchors: []
   utility: none
   digest: Mixed Virasoro anomaly of the actual normally ordered cubic ghost charge. -/

import D5.S3.Quantum.Fermionic.BcGhostBRST

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostVirasoro (L)
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

private theorem weighted_cc_finite (r : ℤ) (w : ℤ → ℂ) (v : Fock) :
    Function.HasFiniteSupport (fun p : ℤ => w p • (c p * c (r-p)) v) := by
  apply (cc_finite r v).subset
  intro p hp hn
  exact hp (by simp [hn])

private theorem L_cc (m p q : ℤ) :
    L m * (c p * c q) - (c p * c q) * L m =
      ((-2*m-p : ℤ) : ℂ) • (c (m+p) * c q) +
      ((-2*m-q : ℤ) : ℂ) • (c p * c (m+q)) := by
  calc
    _ = (L m * c p - c p * L m) * c q +
        c p * (L m * c q - c q * L m) := by noncomm_ring
    _ = _ := by
      rw [BcGhostVirasoro.ward_c, BcGhostVirasoro.ward_c]
      simp only [smul_mul_assoc, mul_smul_comm]

/-- Finite covariance of the pure-c quadratic under the actual Virasoro modes. -/
theorem R_covariance (m r : ℤ) :
    L m * R r - R r * L m = ((-2*m-r : ℤ) : ℂ) • R (m+r) := by
  apply LinearMap.ext
  intro v
  let f : ℤ → Fock := fun p =>
    ((1/2 : ℂ) * ((2*(p-m)-r : ℤ) : ℂ) * ((-m-p : ℤ) : ℂ)) •
      (c p * c (m+r-p)) v
  let g : ℤ → Fock := fun p =>
    ((1/2 : ℂ) * ((2*p-r : ℤ) : ℂ) * ((-2*m-r+p : ℤ) : ℂ)) •
      (c p * c (m+r-p)) v
  have hf : Function.HasFiniteSupport f := weighted_cc_finite (m+r) _ v
  have hg : Function.HasFiniteSupport g := weighted_cc_finite (m+r) _ v
  have hfs : Function.HasFiniteSupport (fun p : ℤ => f (m+p)) :=
    hf.fun_comp_of_injective (Equiv.addLeft m).injective
  have hv := rTerm_finite r v
  have hw := rTerm_finite r (L m v)
  have hmap := hv.fun_comp (map_zero (L m))
  change L m (∑ᶠ p : ℤ, rTerm r p v) -
      (∑ᶠ p : ℤ, rTerm r p (L m v)) = _
  rw [map_finsum (L m) hv, ← finsum_sub_distrib hmap hw]
  calc
    _ = ∑ᶠ p : ℤ, (f (m+p) + g p) := by
      apply finsum_congr
      intro p
      have h := LinearMap.congr_fun (L_cc m p (r-p)) v
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.mul_apply] at h
      simp only [rTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
      rw [← smul_sub, h, smul_add]
      simp only [smul_smul]
      dsimp only [f, g]
      rw [show m+r-(m+p) = r-p by omega, show m+r-p = m+(r-p) by omega]
      simp only [Module.End.mul_apply]
      congr 2 <;> (push_cast; ring)
    _ = (∑ᶠ p : ℤ, f (m+p)) + (∑ᶠ p : ℤ, g p) := finsum_add_distrib hfs hg
    _ = (∑ᶠ p : ℤ, f p) + (∑ᶠ p : ℤ, g p) := by
      congr 1
      exact finsum_comp_equiv (Equiv.addLeft m) (f := f)
    _ = ∑ᶠ p : ℤ, ((-2*m-r : ℤ) : ℂ) • rTerm (m+r) p v := by
      rw [← finsum_add_distrib hf hg]
      apply finsum_congr
      intro p
      dsimp only [f, g, rTerm]
      simp only [LinearMap.smul_apply, smul_smul, ← add_smul]
      congr 1
      push_cast
      ring
    _ = (((-2*m-r : ℤ) : ℂ) • R (m+r)) v := by
      rw [← smul_finsum' _ (rTerm_finite (m+r) v)]
      rfl

private theorem odd_product_three (A B C : Module.End ℂ Fock)
    (hA : parity*A+A*parity = 0) (hB : parity*B+B*parity = 0)
    (hC : parity*C+C*parity = 0) :
    parity*(A*B*C)+(A*B*C)*parity = 0 := by
  calc
    _ = (parity*A+A*parity)*B*C - A*(parity*B+B*parity)*C +
        A*B*(parity*C+C*parity) := by noncomm_ring
    _ = 0 := by rw [hA, hB, hC]; simp

private theorem cubic_odd (p q : ℤ) :
    parity * cubic p q + cubic p q * parity = 0 := by
  by_cases hk : -p-q ≤ -2
  · simpa only [cubic_eq, if_pos hk] using odd_product_three (b (-p-q)) (c p) (c q)
      (ghost_parity _).1 (ghost_parity _).2 (ghost_parity _).2
  · simpa only [cubic_eq, if_neg hk] using odd_product_three (c p) (c q) (b (-p-q))
      (ghost_parity _).2 (ghost_parity _).2 (ghost_parity _).1

/-- Oddness is proved for the actual pointwise cubic, using actual occupation parity. -/
theorem Qg_odd : parity * Qg + Qg * parity = 0 := by
  apply LinearMap.ext
  intro v
  have hv := cubicTerm_finite v
  have hw := cubicTerm_finite (parity v)
  have hmap := hv.fun_comp (map_zero parity)
  change parity (∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) +
      (∑ᶠ pq : ℤ × ℤ, cubicTerm pq (parity v)) = 0
  rw [map_finsum parity hv, ← finsum_add_distrib hmap hw]
  apply finsum_eq_zero_of_forall_eq_zero
  intro pq
  have h := LinearMap.congr_fun (cubic_odd pq.1 pq.2) v
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [cubicTerm, LinearMap.smul_apply, map_smul, ← smul_add, h, smul_zero]

private theorem L_even (r : ℤ) : parity * L r - L r * parity = 0 := by
  rw [← ward_b r]
  calc
    _ = (parity*Qg+Qg*parity)*b r - Qg*(parity*b r+b r*parity) +
        (parity*b r+b r*parity)*Qg - b r*(parity*Qg+Qg*parity) := by noncomm_ring
    _ = 0 := by rw [Qg_odd, (ghost_parity r).1]; simp

/-- An odd operator anticommuting with every actual ghost mode vanishes. -/
private theorem odd_anticommutant_zero (A : Module.End ℂ Fock)
    (hb : ∀ r : ℤ, A*b r+b r*A = 0)
    (hc : ∀ r : ℤ, A*c r+c r*A = 0)
    (hodd : parity*A+A*parity = 0) : A = 0 := by
  have hcomm (B : Module.End ℂ Fock) (hB : parity*B+B*parity = 0)
      (hAB : A*B+B*A = 0) : (A*parity)*B = B*(A*parity) := by
    apply sub_eq_zero.mp
    calc
      _ = A*(parity*B+B*parity)-(A*B+B*A)*parity := by noncomm_ring
      _ = 0 := by rw [hB, hAB]; simp
  obtain ⟨α, hα⟩ := scalar_commutant (A*parity)
    (fun r => hcomm (b r) (ghost_parity r).1 (hb r))
    (fun r => hcomm (c r) (ghost_parity r).2 (hc r))
  have he : A = parity*A*parity := by
    calc
      A = (A*parity)*parity := by rw [mul_assoc, parity_involution, mul_one]
      _ = parity*(A*parity) := by rw [hα]; simp [smul_mul_assoc, mul_smul_comm]
      _ = _ := by noncomm_ring
  have hh := congrArg (fun T : Module.End ℂ Fock => T*parity) hodd
  have hPAP : parity*A*parity+A = 0 := by
    simpa only [add_mul, zero_mul, mul_assoc, parity_involution, mul_one] using hh
  rw [← he] at hPAP
  have htwo : (2 : ℂ) • A = 0 := by simpa only [two_smul] using hPAP
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

def anomalyCoefficient (r : ℤ) : ℂ := (26/12 : ℂ) * ((r : ℂ)^3-r)

private def mixedDefect (r : ℤ) : Module.End ℂ Fock :=
  Qg*L r-L r*Qg-anomalyCoefficient r • c r

private theorem mixedDefect_b (r s : ℤ) : mixedDefect r*b s+b s*mixedDefect r = 0 := by
  have hj : (Qg*L r-L r*Qg)*b s+b s*(Qg*L r-L r*Qg) =
      Qg*(L r*b s-b s*L r)+(L r*b s-b s*L r)*Qg -
      (L r*(Qg*b s+b s*Qg)-(Qg*b s+b s*Qg)*L r) := by noncomm_ring
  unfold mixedDefect
  rw [show ∀ A B C : Module.End ℂ Fock,
    (A-B)*C+C*(A-B) = (A*C+C*A)-(B*C+C*B) by intros; noncomm_ring]
  rw [hj, BcGhostVirasoro.ward_b, ward_b s]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [ward_b (r+s), BcGhostVirasoro.virasoro,
    show c r*b s+b s*c r = b s*c r+c r*b s by abel, ghost_mixed_car]
  unfold anomalyCoefficient
  by_cases h : r+s = 0
  · simp only [h, show s+r = 0 by omega, if_true, smul_add, smul_smul]
    have he : (-26/12 : ℂ) * ((r : ℂ)^3-r) =
        -((26/12 : ℂ) * ((r : ℂ)^3-r)) := by ring
    rw [he, neg_smul]
    abel
  · simp only [h, show s+r ≠ 0 by omega, if_false, zero_smul, smul_zero, add_zero, sub_self]

private theorem mixedDefect_c (r s : ℤ) : mixedDefect r*c s+c s*mixedDefect r = 0 := by
  have hj : (Qg*L r-L r*Qg)*c s+c s*(Qg*L r-L r*Qg) =
      Qg*(L r*c s-c s*L r)+(L r*c s-c s*L r)*Qg -
      (L r*(Qg*c s+c s*Qg)-(Qg*c s+c s*Qg)*L r) := by noncomm_ring
  unfold mixedDefect
  rw [show ∀ A B C : Module.End ℂ Fock,
    (A-B)*C+C*(A-B) = (A*C+C*A)-(B*C+C*B) by intros; noncomm_ring]
  rw [hj, BcGhostVirasoro.ward_c, ward_c s]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [ward_c (r+s), R_covariance, ghost_c_car]
  simp

private theorem mixedDefect_odd (r : ℤ) :
    parity*mixedDefect r+mixedDefect r*parity = 0 := by
  unfold mixedDefect
  calc
    _ = (parity*Qg+Qg*parity)*L r - L r*(parity*Qg+Qg*parity) -
        Qg*(parity*L r-L r*parity)-(parity*L r-L r*parity)*Qg -
        anomalyCoefficient r • (parity*c r+c r*parity) := by
          simp only [smul_add, smul_mul_assoc, mul_smul_comm]
          noncomm_ring
    _ = 0 := by rw [Qg_odd, L_even, (ghost_parity r).2]; simp

/-- The mixed Virasoro anomaly, derived from actual Ward identities and c=-26. -/
theorem mixed_anomaly (r : ℤ) :
    Qg*L r-L r*Qg = ((26/12 : ℂ) * ((r : ℂ)^3-r)) • c r := by
  exact sub_eq_zero.mp (odd_anticommutant_zero (mixedDefect r)
    (mixedDefect_b r) (mixedDefect_c r) (mixedDefect_odd r))

end D5.S3.Quantum.Fermionic.BcGhostBRST
