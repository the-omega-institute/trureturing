/- GID: D5/S3/Quantum/Fermionic/BcGhostSquare
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostSquare
   mirror-E: none(waiver:algebraic-ghost-brst-square)
   anchors: []
   utility: none
   digest: Full integer ghost BRST square anomaly on the actual countable bc Fock. -/

import D5.S3.Quantum.Fermionic.BcGhostAnomaly
import D5.S3.Quantum.Fermionic.BcGhostJacobi

set_option backward.isDefEq.respectTransparency false

/-! The classical ghost-only square formula, with central charge minus twenty-six.
The scalar residual is fixed on the actual ghost vacuum. This argument makes
no assertion that a matter-tensor BRST charge kills arbitrary matter states.
-/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

def squareTerm (n : ℤ) : Module.End ℂ Fock :=
  ((-26/24 : ℂ) * ((n : ℂ)^3-n)) • (c (-n)*c n)

/-- All signed indices are included; local finiteness is on the actual input state. -/
theorem squareTerm_finite (v : Fock) :
    Function.HasFiniteSupport (fun n : ℤ => squareTerm n v) := by
  have h : Function.HasFiniteSupport (fun n : ℤ => (c (-n)*c n) v) := by
    simpa using (cc_finite 0 v).fun_comp_of_injective (Equiv.neg ℤ).injective
  apply h.subset
  intro n hn hz
  exact hn (by simp [squareTerm, hz])

/-- The full integer pure-c anomaly, not a cutoff or an operator-family finsum. -/
def squareAnomaly : Module.End ℂ Fock where
  toFun v := ∑ᶠ n : ℤ, squareTerm n v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (squareTerm_finite v) (squareTerm_finite w)
  map_smul' a v := by
    simp only [map_smul]
    exact (smul_finsum' a (squareTerm_finite v)).symm

private theorem cc_b (p q r : ℤ) :
    (c p*c q)*b r-b r*(c p*c q) =
      (if q+r = 0 then c p else 0)-(if p+r = 0 then c q else 0) := by
  calc
    _ = c p*(b r*c q+c q*b r)-(b r*c p+c p*b r)*c q := by noncomm_ring
    _ = _ := by
      rw [ghost_mixed_car, ghost_mixed_car]
      simp only [show r+q = 0 ↔ q+r = 0 by omega,
        show r+p = 0 ↔ p+r = 0 by omega]
      split_ifs <;> simp

private theorem cc_c (p q r : ℤ) :
    (c p*c q)*c r-c r*(c p*c q) = 0 := by
  calc
    _ = c p*(c q*c r+c r*c q)-(c p*c r+c r*c p)*c q := by noncomm_ring
    _ = 0 := by rw [ghost_c_car, ghost_c_car]; simp

private theorem squareAnomaly_b (r : ℤ) :
    squareAnomaly*b r-b r*squareAnomaly = anomalyCoefficient r • c r := by
  apply LinearMap.ext
  intro v
  have hv := squareTerm_finite v
  have hw := squareTerm_finite (b r v)
  have hmap := hv.fun_comp (map_zero (b r))
  change (∑ᶠ n : ℤ, squareTerm n (b r v)) - b r (∑ᶠ n : ℤ, squareTerm n v) = _
  rw [map_finsum (b r) hv, ← finsum_sub_distrib hw hmap]
  let f : ℤ → Fock := fun n =>
    if n = -r then ((-26/24 : ℂ) * (((-r : ℤ) : ℂ)^3-(-r : ℤ))) • c r v else 0
  let g : ℤ → Fock := fun n =>
    if n = r then ((-26/24 : ℂ) * ((r : ℂ)^3-r)) • c r v else 0
  have hf : Function.HasFiniteSupport f := by
    apply (Set.finite_singleton (-r)).subset
    intro n hn
    by_contra he
    simp only [Set.mem_singleton_iff] at he
    exact hn (by simp [f, he])
  have hg : Function.HasFiniteSupport g := by
    apply (Set.finite_singleton r).subset
    intro n hn
    by_contra he
    simp only [Set.mem_singleton_iff] at he
    exact hn (by simp [g, he])
  calc
    _ = ∑ᶠ n : ℤ, (f n-g n) := by
      apply finsum_congr
      intro n
      have h := LinearMap.congr_fun (cc_b (-n) n r) v
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      simp only [squareTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
      rw [← smul_sub, h, smul_sub]
      congr 1
      · by_cases hn : n = -r
        · subst n
          simp [f]
        · simp [f, hn, show n+r ≠ 0 by omega]
      · by_cases hn : n = r
        · subst n
          simp [g]
        · simp [g, hn, show -n+r ≠ 0 by omega]
    _ = (∑ᶠ n : ℤ, f n)-(∑ᶠ n : ℤ, g n) := finsum_sub_distrib hf hg
    _ = (anomalyCoefficient r • c r) v := by
      rw [finsum_eq_single f (-r) (fun n hn => by simp [f, hn]),
        finsum_eq_single g r (fun n hn => by simp [g, hn])]
      simp only [f, g, if_true, LinearMap.smul_apply, ← sub_smul]
      congr 1
      unfold anomalyCoefficient
      push_cast
      ring

private theorem squareAnomaly_c (r : ℤ) : squareAnomaly*c r-c r*squareAnomaly = 0 := by
  apply LinearMap.ext
  intro v
  have hv := squareTerm_finite v
  have hw := squareTerm_finite (c r v)
  have hmap := hv.fun_comp (map_zero (c r))
  change (∑ᶠ n : ℤ, squareTerm n (c r v)) - c r (∑ᶠ n : ℤ, squareTerm n v) = 0
  rw [map_finsum (c r) hv, ← finsum_sub_distrib hw hmap]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  have h := LinearMap.congr_fun (cc_c (-n) n r) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [squareTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
  rw [← smul_sub, h, smul_zero]

private theorem squareAnomaly_vacuum : squareAnomaly vacuum = 0 := by
  change (∑ᶠ n : ℤ, squareTerm n vacuum) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hp : 2 ≤ n
  · simp [squareTerm, Module.End.mul_apply, ghost_vacuum.2.1 n hp]
  by_cases hn : n ≤ -2
  · have hz := ghost_vacuum.2.1 (-n) (by omega)
    simp [squareTerm, c_swap (-n) n, Module.End.mul_apply, hz]
  have he : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases he with rfl | rfl | rfl <;> norm_num [squareTerm]

/-- The full cubic square is the classical all-integer c=-26 ghost anomaly. -/
theorem square_anomaly : Qg*Qg = squareAnomaly := by
  let D : Module.End ℂ Fock := Qg*Qg-squareAnomaly
  have hb (r : ℤ) : D*b r = b r*D := by
    apply sub_eq_zero.mp
    have hq : (Qg*Qg)*b r-b r*(Qg*Qg) =
        Qg*(Qg*b r+b r*Qg)-(Qg*b r+b r*Qg)*Qg := by noncomm_ring
    change (Qg*Qg-squareAnomaly)*b r-b r*(Qg*Qg-squareAnomaly) = 0
    rw [show ∀ A B C : Module.End ℂ Fock,
      (A-B)*C-C*(A-B) = (A*C-C*A)-(B*C-C*B) by intros; noncomm_ring]
    rw [hq, ward_b, mixed_anomaly, squareAnomaly_b]
    simp [anomalyCoefficient]
  have hc (r : ℤ) : D*c r = c r*D := by
    apply sub_eq_zero.mp
    have hq : (Qg*Qg)*c r-c r*(Qg*Qg) =
        Qg*(Qg*c r+c r*Qg)-(Qg*c r+c r*Qg)*Qg := by noncomm_ring
    change (Qg*Qg-squareAnomaly)*c r-c r*(Qg*Qg-squareAnomaly) = 0
    rw [show ∀ A B C : Module.End ℂ Fock,
      (A-B)*C-C*(A-B) = (A*C-C*A)-(B*C-C*B) by intros; noncomm_ring]
    rw [hq, ward_c, Qg_R, squareAnomaly_c, sub_self]
  obtain ⟨α, hα⟩ := scalar_commutant D hb hc
  have hv : D vacuum = 0 := by
    simp [D, Module.End.mul_apply, Qg_vacuum, squareAnomaly_vacuum]
  have hscalar : α = 0 := by
    have he : (α • (1 : Module.End ℂ Fock)) vacuum = 0 := by
      rw [← hα]
      exact hv
    have he0 := congrArg (fun v : Fock => v ∅) he
    simpa only [LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_apply,
      vacuum, ket, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Finsupp.zero_apply] using he0
  have hzero : D = 0 := by rw [hα, hscalar, zero_smul]
  exact sub_eq_zero.mp hzero

end D5.S3.Quantum.Fermionic.BcGhostBRST
