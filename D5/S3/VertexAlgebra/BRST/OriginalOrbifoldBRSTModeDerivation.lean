/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTModeDerivation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTModeDerivation
   mirror-E: none(waiver:algebraic-original-brst-mode-derivation)
   anchors: []
   utility: none
   digest: Original BRST and antighost commutators on every integer mode. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTSuperJacobi

/-!
The (r = 0) super-Borcherds identity gives the first two commutator formulas
for an odd field. The parity eigenspace decomposition extends them to
arbitrary states. The native BRST and antighost modes use the coefficient
identifications in `OriginalOrbifoldBRSTStateField`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTModeDerivation

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterVacuum)
open OriginalOrbifoldMatterTensorField (stressState)
open OriginalOrbifoldBRSTStateField (J Y b_modes current_zero_mode)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTFieldAxioms (parity_involution)
open OriginalOrbifoldBRSTSuperJacobi (homogeneous_borcherds)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev mode (a : State) (n : ℤ) (x : State) : State := ((Y a)[[n]]) x

private theorem mode_add_left (a c x : State) (n : ℤ) :
    mode (a + c) n x = mode a n x + mode c n x := by
  simp only [mode, map_add, Pi.add_apply, LinearMap.add_apply]

private theorem mode_smul_left (z : ℂ) (a x : State) (n : ℤ) :
    mode (z • a) n x = z • mode a n x := by
  simp only [mode, map_smul, Pi.smul_apply, LinearMap.smul_apply]

private theorem of_parity_eigenspaces (P : State → Prop)
    (add : ∀ u v, P u → P v → P (u + v))
    (homogeneous : ∀ u (k : ℕ), parity u = (-1 : ℂ) ^ k • u → P u) (a : State) :
    P a := by
  let evenPart := (2 : ℂ)⁻¹ • (a + parity a)
  let oddPart := (2 : ℂ)⁻¹ • (a - parity a)
  have square : parity (parity a) = a := LinearMap.congr_fun parity_involution a
  have evenEigen : parity evenPart = (-1 : ℂ) ^ 0 • evenPart := by
    dsimp only [evenPart]
    rw [map_smul, map_add, square, pow_zero, one_smul, add_comm (parity a) a]
  have oddEigen : parity oddPart = (-1 : ℂ) ^ 1 • oddPart := by
    dsimp only [oddPart]
    rw [map_smul, map_sub, square, pow_one]
    module
  have split : evenPart + oddPart = a := by
    dsimp only [evenPart, oddPart]
    module
  rw [← split]
  exact add _ _ (homogeneous _ 0 evenEigen) (homogeneous _ 1 oddEigen)

private theorem zero_binomial_sum (f : ℕ → State) :
    (∑ᶠ i : ℕ, integerBinomial 0 i • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem signed_zero_binomial_sum (f : ℕ → State) :
    (∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * integerBinomial 0 i) • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem odd_zero_mode (u : State) (hu : parity u = (-1 : ℂ) ^ 1 • u)
    (a x : State) (n : ℤ) :
    mode u 0 (mode a n x) = mode (mode u 0 a) n x + mode (parity a) n (mode u 0 x) := by
  apply of_parity_eigenspaces (fun v =>
    mode u 0 (mode v n x) = mode (mode u 0 v) n x + mode (parity v) n (mode u 0 x)) _ _ a
  · intro v w hv hw
    simp only [mode_add_left, map_add, hv, hw]
    abel
  · intro v k hv
    have law := (homogeneous_borcherds u v x 1 k hu hv 0 n 0).2.2.2
    dsimp only at law
    simp only [zero_binomial_sum, signed_zero_binomial_sum, Nat.cast_zero,
      zero_add, add_zero, sub_zero, epsilon, zpow_zero, one_mul] at law
    change mode u 0 (mode v n x) = mode (mode u 0 v) n x + mode (parity v) n (mode u 0 x)
    rw [hv, mode_smul_left]
    exact (eq_sub_iff_add_eq.mp law).symm

private theorem current_odd : parity J = (-1 : ℂ) ^ 1 • J := by
  have c_odd : CountableOccupationFock.parity (ket {1}) = (-1 : ℂ) ^ 1 • ket {1} := by
    simp [parity_ket]
  simp only [J, map_add, parity, TensorProduct.map_tmul, LinearMap.id_apply,
    c_odd, BcGhostConformalBRSTState.current_odd, TensorProduct.tmul_smul, smul_add]

private theorem antighost_odd :
    parity (matterVacuum ⊗ₜ[ℂ] ket {0}) =
      (-1 : ℂ) ^ 1 • (matterVacuum ⊗ₜ[ℂ] ket {0}) := by
  have ghost_odd : CountableOccupationFock.parity (ket {0}) = (-1 : ℂ) ^ 1 • ket {0} := by
    simp [parity_ket]
  simp only [parity, TensorProduct.map_tmul, LinearMap.id_apply,
    ghost_odd, TensorProduct.tmul_smul]

/-- The native BRST differential is a superderivation of every original integer mode. -/
theorem Q_mode (a x : State) (n : ℤ) :
    Q (((Y a)[[n]]) x) = ((Y (Q a))[[n]]) x + ((Y (parity a))[[n]]) (Q x) := by
  simpa only [mode, current_zero_mode] using odd_zero_mode J current_odd a x n

/-- The normalized antighost zero mode is native `b (-1)` and is an odd superderivation. -/
theorem b_minus_one_mode (a x : State) (n : ℤ) :
    b (-1) (((Y a)[[n]]) x) =
      ((Y (b (-1) a))[[n]]) x + ((Y (parity a))[[n]]) (b (-1) x) := by
  simpa only [mode, b_modes, zero_sub] using
    odd_zero_mode (matterVacuum ⊗ₜ[ℂ] ket {0}) antighost_odd a x n

private theorem one_binomial_sum (f : ℕ → State) :
    (∑ᶠ i : ℕ, integerBinomial 1 i • f i) = f 0 + f 1 := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, integerBinomial]
  · intro i hi
    by_contra hout
    have hi' : 1 < i := by simpa using hout
    have hz : Ring.choose (1 : ℤ) i = 0 := by
      simpa only [Nat.cast_one, Nat.cast_zero] using
        (Ring.choose_natCast (R := ℤ) 1 i).trans (congrArg (Nat.cast : ℕ → ℤ)
          (Nat.choose_eq_zero_of_lt hi'))
    exact hi (by simp [integerBinomial, hz])

private theorem odd_first_mode (u : State) (hu : parity u = (-1 : ℂ) ^ 1 • u)
    (a x : State) (n : ℤ) :
    mode u 1 (mode a n x) =
      mode (mode u 1 a) n x + mode (mode u 0 a) (1 + n) x +
        mode (parity a) n (mode u 1 x) := by
  apply of_parity_eigenspaces (fun v =>
    mode u 1 (mode v n x) =
      mode (mode u 1 v) n x + mode (mode u 0 v) (1 + n) x +
        mode (parity v) n (mode u 1 x)) _ _ a
  · intro v w hv hw
    simp only [mode_add_left, map_add, hv, hw]
    abel
  · intro v k hv
    have law := (homogeneous_borcherds u v x 1 k hu hv 1 n 0).2.2.2
    dsimp only at law
    simp only [one_binomial_sum, signed_zero_binomial_sum, Nat.cast_zero,
      Nat.cast_one, zero_add, add_zero, sub_zero, epsilon, zpow_zero, one_mul,
      show 1 + n - 1 = n by omega] at law
    change mode u 1 (mode v n x) =
      mode (mode u 1 v) n x + mode (mode u 0 v) (1 + n) x +
        mode (parity v) n (mode u 1 x)
    rw [hv, mode_smul_left]
    rw [add_comm (mode (mode u 1 v) n x)]
    exact (eq_sub_iff_add_eq.mp law).symm

/-- Native `b 0` is normalized antighost mode one. Its commutator has the
additional iterate from normalized mode zero of the antighost state. -/
theorem b_zero_mode (a x : State) (n : ℤ) :
    b 0 (((Y a)[[n]]) x) =
      ((Y (b 0 a))[[n]]) x + ((Y (b (-1) a))[[n + 1]]) x +
        ((Y (parity a))[[n]]) (b 0 x) := by
  simpa only [mode, b_modes, zero_sub, sub_self, add_comm 1 n] using
    odd_first_mode (matterVacuum ⊗ₜ[ℂ] ket {0}) antighost_odd a x n

#print axioms Q_mode
#print axioms b_minus_one_mode
#print axioms b_zero_mode

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTModeDerivation
