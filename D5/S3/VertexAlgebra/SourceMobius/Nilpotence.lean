/- GID: D5/S3/VertexAlgebra/SourceMobius/Nilpotence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/Nilpotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite oscillator-weight bound for the original positive Sugawara source mode. -/
import D5.S3.VertexAlgebra.SourceMobius.PositiveMode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

/-- The sharp product bound, without division or any grading hypothesis. -/
private theorem killed_mul {σ : Type*} (d : Derivation ℂ (MvPolynomial σ ℂ)
    (MvPolynomial σ ℂ)) : ∀ r s : ℕ, ∀ p q : MvPolynomial σ ℂ,
    (d.toLinearMap^(r+1)) p = 0 → (d.toLinearMap^(s+1)) q = 0 →
      (d.toLinearMap^(r+s+1)) (p*q) = 0 := by
  intro r
  induction r with
  | zero =>
    intro s
    induction s with
    | zero =>
      intro p q hp hq
      have hp' : d p = 0 := by simpa using hp
      have hq' : d q = 0 := by simpa using hq
      simpa [Derivation.leibniz, hp', hq']
    | succ s ih =>
      intro p q hp hq
      have hp' : d p = 0 := by simpa using hp
      have hq' : (d.toLinearMap^(s+1)) (d q) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, Derivation.coeFn_coe] using hq
      have hh := ih p (d q) hp hq'
      rw [show 0+(s+1)+1 = (s+1)+1 by omega, pow_succ, Module.End.mul_apply]
      change (d.toLinearMap^(s+1)) (d (p*q)) = 0
      simpa only [Derivation.leibniz, hp', smul_eq_mul, mul_zero, add_zero,
        Nat.zero_add] using hh
  | succ r outer =>
    intro s
    induction s with
    | zero =>
      intro p q hp hq
      have hq' : d q = 0 := by simpa using hq
      have hp' : (d.toLinearMap^(r+1)) (d p) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, Derivation.coeFn_coe] using hp
      have hh := outer 0 (d p) q hp' hq
      rw [show (r+1)+0+1 = (r+1)+1 by omega, pow_succ, Module.End.mul_apply]
      change (d.toLinearMap^(r+1)) (d (p*q)) = 0
      simpa only [Derivation.leibniz, hq', smul_eq_mul, mul_zero, zero_add,
        Nat.add_zero, mul_comm q (d p)] using hh
    | succ s inner =>
      intro p q hp hq
      have hp' : (d.toLinearMap^(r+1)) (d p) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, Derivation.coeFn_coe] using hp
      have hq' : (d.toLinearMap^(s+1)) (d q) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply, Derivation.coeFn_coe] using hq
      have hl := outer (s+1) (d p) q hp' hq
      have hr := inner p (d q) hp hq'
      rw [show (r+1)+(s+1)+1 = (r+s+2)+1 by omega, pow_succ, Module.End.mul_apply]
      change (d.toLinearMap^(r+s+2)) (d (p*q)) = 0
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add]
      rw [show r+s+2 = (r+1)+s+1 by omega, hr]
      rw [mul_comm q (d p), show (r+1)+s+1 = r+(s+1)+1 by omega, hl, add_zero]

private theorem variable_nilpotent (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (r : ℕ) :
    ((sectorL1 D a).toLinearMap^(r+2)) (X (i,r)) = 0 := by
  induction r with
  | zero => simp [pow_succ, Module.End.mul_apply, sectorL1, loweringVariable, mkDerivation_X]
  | succ r ih =>
    rw [show r+1+2 = (r+2)+1 by omega, pow_succ, Module.End.mul_apply]
    change ((sectorL1 D a).toLinearMap^(r+2)) (sectorL1 D a (X (i,r+1))) = 0
    rw [show sectorL1 D a (X (i,r+1)) = (r+2 : ℂ) • X (i,r) by
      simp [sectorL1, loweringVariable, mkDerivation_X], map_smul, ih, smul_zero]

/-- The original oscillator monomial is killed at weight plus one. -/
theorem sectorL1_monomial_bound (D : LatticeData) (a : Charge D)
    (m : Index D →₀ ℕ) (c : ℂ) :
    ((sectorL1 D a).toLinearMap ^ (m.weight (sourceWeight D) + 1)) (monomial m c) = 0 := by
  classical
  have power (x : Index D) (k : ℕ) :
      ((sectorL1 D a).toLinearMap ^ (k * sourceWeight D x + 1)) (X x ^ k) = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hv : ((sectorL1 D a).toLinearMap ^ (sourceWeight D x + 1)) (X x) = 0 :=
        variable_nilpotent D a x.1 x.2
      simpa [pow_succ, Nat.succ_mul] using
        killed_mul (sectorL1 D a) (k * sourceWeight D x) (sourceWeight D x)
          (X x ^ k) (X x) ih hv
  induction m using Finsupp.induction with
  | zero => simp
  | single_add x k m absent nonzero ih =>
    have hh := killed_mul (sectorL1 D a) (m.weight (sourceWeight D))
      (k * sourceWeight D x) (monomial m c) (X x ^ k) ih (power x k)
    simpa [add_comm (Finsupp.single x k) m, monomial_add_single,
      map_add, Finsupp.weight_single, nsmul_eq_mul] using hh

/-- Weighted total degree controls every finite polynomial, including zero. -/
theorem sectorL1_degree_bound (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    ((sectorL1 D a).toLinearMap ^ (weightedTotalDegree (sourceWeight D) p + 1)) p = 0 := by
  classical
  let N := weightedTotalDegree (sourceWeight D) p + 1
  change ((sectorL1 D a).toLinearMap ^ N) p = 0
  calc
    _ = ((sectorL1 D a).toLinearMap ^ N) (∑ m ∈ p.support, monomial m (p.coeff m)) :=
      congrArg _ p.as_sum
    _ = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro m hm
      exact Module.End.pow_map_zero_of_le
        (Nat.add_le_add_right (le_weightedTotalDegree (sourceWeight D) hm) 1)
        (sectorL1_monomial_bound D a m (p.coeff m))

theorem sugawara_pow_single (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (p : Oscillator D) (n : ℕ) :
    (sugawaraMode D H 1 ^ n) (Finsupp.single a p) =
      Finsupp.single a (((sectorL1 D a).toLinearMap^n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, sugawara_one_single D H hHG hGH,
      pow_succ', Module.End.mul_apply]
    rfl

/-- Finite charge support gives local nilpotence on every original source. -/
theorem sugawara_one_locally_nilpotent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (v : Carrier D) : ∃ n : ℕ, (sugawaraMode D H 1 ^ n) v = 0 := by
  classical
  induction v using Finsupp.induction with
  | zero => exact ⟨1, by simp⟩
  | single_add a p v absent nonzero ih =>
    obtain ⟨s,hs⟩ := ih
    let r := weightedTotalDegree (sourceWeight D) p + 1
    have hr : (sugawaraMode D H 1 ^ r) (Finsupp.single a p) = 0 := by
      rw [sugawara_pow_single D H hHG hGH, sectorL1_degree_bound, Finsupp.single_zero]
    refine ⟨r+s, ?_⟩
    rw [map_add, Module.End.pow_map_zero_of_le (show r ≤ r+s by omega) hr,
      Module.End.pow_map_zero_of_le (show s ≤ r+s by omega) hs, add_zero]

end D5.S3.VertexAlgebra.SourceMobius
