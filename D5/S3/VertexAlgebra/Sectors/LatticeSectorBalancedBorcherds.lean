/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coupled second-term cancellation with the original statewise cutoff. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldCommonSeries
import D5.S3.VertexAlgebra.FormalSeries.SupportedBalancedCollision

/-! The full integer Borcherds identity is summed across the u/t cross factor.
Its second term vanishes only after original u/t locality moves u onto w.
No cutoff for u on t_z w is assumed or chosen. The original lattice and
Carnahan/Bakalov--Kac/Matsuo--Nagatomo supplier attributions are retained.
proof_shape: content; consumed by actual_three_field_balanced_transport.
admission_basis: escape-witness
escape_witness: coupled locality cancels the full Jacobi second term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorBalancedBorcherds
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeAllStateReconstruction LatticeAllStateJacobi LatticeSectorIntertwiner
open LatticeSectorChannelTransport SupportedChannelSeries SupportedBalancedCollision
open UniformGradedLocalCorrelator
open StateFieldResidueReconstruction (integerBinomial epsilon)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

private def weight (k j : ℕ) : ℂ := ((-1 : ℂ) ^ j) * (k.choose j : ℂ)

private theorem cross_kills (D : LatticeData) (u t w : Carrier D) (k A : ℕ)
    (locality : (deltaEnd ^ k) (commutator (Y D u) (Y D t)) = 0)
    (cutoff : ∀ n : ℤ, (A : ℤ) ≤ n → mu D u n w = 0) (i : ℕ) (z : ℤ) :
    (∑ j ∈ Finset.range (k + 1), weight k j •
      mu D u ((A : ℤ) + k - j + i) (mu D t (z + j) w)) = 0 := by
  have h := congrArg (fun d : ℤ → ℤ → Module.End ℂ (Carrier D) =>
    d ((A : ℤ) + i) z w) locality
  rw [FieldDeltaBinomial.delta_binomial] at h
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.zero_apply,
    LinearMap.zero_apply, smul_sub, Finset.sum_sub_distrib] at h
  have vanish : (∑ j ∈ Finset.range (k + 1), weight k j •
      mu D t (z + j) (mu D u ((A : ℤ) + i + k - j) w)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≤ k := by simpa using Finset.mem_range.mp hj
    rw [cutoff _ (by omega)]
    simp [mu]
  change (∑ j ∈ Finset.range (k + 1), weight k j •
    mu D u ((A : ℤ) + i + k - j) (mu D t (z + j) w)) -
      (∑ j ∈ Finset.range (k + 1), weight k j •
        mu D t (z + j) (mu D u ((A : ℤ) + i + k - j) w)) = 0 at h
  rw [vanish, sub_zero] at h
  simpa only [show ∀ j : ℕ, (A : ℤ) + i + k - j = (A : ℤ) + k - j + i by
    intro j; omega] using h

private theorem coupled_borcherds (D : LatticeData) (u v t w : Carrier D)
    (k A : ℕ)
    (locality : (deltaEnd ^ k) (commutator (Y D u) (Y D t)) = 0)
    (cutoff : ∀ n : ℤ, (A : ℤ) ≤ n → mu D u n w = 0)
    (q r z : ℤ) :
    (∑ j ∈ Finset.range (k + 1), weight k j •
      ∑ᶠ h : ℕ, jacobiLeftTerm D ((A : ℤ) + k - j) q r
        u v (mu D t (z + j) w) h) =
    ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial r i) •
      ∑ j ∈ Finset.range (k + 1), weight k j •
        mu D u ((A : ℤ) + k - j + r - i)
          (mu D v (q + i) (mu D t (z + j) w)) := by
  classical
  let C (j : ℕ) := mu D t (z + j) w
  let first (j i : ℕ) := jacobiRightFirstTerm D ((A : ℤ) + k - j) q r u v (C j) i
  let second (j i : ℕ) := jacobiRightSecondTerm D ((A : ℤ) + k - j) q r u v (C j) i
  have bor (j : ℕ) := borcherds D u v (C j) ((A : ℤ) + k - j) q r
  have hf (j : ℕ) : Function.HasFiniteSupport (first j) := (bor j).2.1
  have hs (j : ℕ) : Function.HasFiniteSupport (second j) := (bor j).2.2.1
  have equation (j : ℕ) :
      (∑ᶠ h : ℕ, jacobiLeftTerm D ((A : ℤ) + k - j) q r u v (C j) h) =
        (∑ᶠ i : ℕ, first j i) - ∑ᶠ i : ℕ, second j i := by
    have h := (bor j).2.2.2
    simp_rw [smul_sub] at h
    exact h.trans (finsum_sub_distrib (hf j) (hs j))
  have killed (i : ℕ) :
      (∑ j ∈ Finset.range (k + 1), weight k j • second j i) = 0 := by
    let L : Carrier D →ₗ[ℂ] Carrier D := (Y D v)[[q + r - i]]
    have term (j : ℕ) : weight k j • second j i =
        ((((-1 : ℂ) ^ i) * integerBinomial r i) * epsilon r) •
          L (weight k j • mu D u ((A : ℤ) + k - j + i) (mu D t (z + j) w)) := by
      simp only [second, jacobiRightSecondTerm, C, map_smul, smul_smul]
      change _ • mu D v (q + r - i) _ = _ • mu D v (q + r - i) _
      congr 1
      ring
    simp_rw [term]
    rw [← Finset.smul_sum, ← map_sum, cross_kills D u t w k A locality cutoff i z,
      map_zero, smul_zero]
  change (∑ j ∈ Finset.range (k + 1), weight k j •
    ∑ᶠ h : ℕ, jacobiLeftTerm D ((A : ℤ) + k - j) q r u v (C j) h) = _
  simp_rw [equation, smul_sub]
  rw [Finset.sum_sub_distrib]
  have exchangeSecond :
      (∑ j ∈ Finset.range (k + 1), weight k j • ∑ᶠ i : ℕ, second j i) = 0 := by
    simp_rw [smul_finsum' _ (hs _)]
    rw [sum_finsum_comm _ (fun j i => weight k j • second j i)
      (fun j _ => (hs j).smul_right (fun _ => weight k j))]
    simp only [killed, finsum_zero]
  rw [exchangeSecond, sub_zero]
  simp_rw [smul_finsum' _ (hf _)]
  rw [sum_finsum_comm _ (fun j i => weight k j • first j i)
    (fun j _ => (hf j).smul_right (fun _ => weight k j))]
  apply finsum_congr
  intro i
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [first, jacobiRightFirstTerm, C, smul_smul]
  congr 1
  ring

/-- Actual ((u_s v)_x (t_z w)), in coefficient order [s,x,z]. -/
def balanced (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (s x z : ℤ) : Oscillator D :=
  canonical D (α + β) (γ + δ) (canonical D α β u (-s - 1) v) (-x - 1)
    (canonical D γ δ t (-z - 1) w)

/-- Finite expansion of (s+x)^a0 x^a1 z^a2 s^k
(s+x-z)^k (x-z)^k. Only polynomial factors are expanded. -/
def clearedBalanced (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : Oscillator D :=
  ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
    weight k j • (weight k l •
      clearIterate k (a 0 + k - j) (a 1 + k - l)
        (fun s x => balanced D α β γ δ u v t w s x (e 2 - a 2 - j - l))
        (e 0) (e 1))

set_option maxHeartbeats 2000000 in
private theorem fixed_q_borcherds (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k A B C l : ℕ) (hl : l ≤ k)
    (locality : (deltaEnd ^ k) (commutator
      (Y D (inclusion D α u)) (Y D (inclusion D γ t))) = 0)
    (cutoff : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D α δ u n w = 0)
    (s x z : ℤ) :
    (∑ j ∈ Finset.range (k + 1), weight k j •
      clearIterate k (A + k - j) (B + k - l)
        (fun s x => balanced D α β γ δ u v t w s x (z - C - j - l)) s x) =
    ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - s - 1) i) •
      ∑ j ∈ Finset.range (k + 1), weight k j •
        LatticeSectorThreeFieldCommonSeries.nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
          ![s - A - 2 * k + j + i, x - B - k + l - i, z - C - j - l] := by
  classical
  let U := inclusion D α u
  let V := inclusion D β v
  let T := inclusion D γ t
  let W := inclusion D δ w
  let P := projection D ((α + β) + (γ + δ))
  let q : ℤ := (B : ℤ) + k - l - x - 1
  let r : ℤ := (k : ℤ) - s - 1
  let z₀ : ℤ := (C : ℤ) + l - z - 1
  let Cj (j : ℕ) := mu D T (z₀ + j) W
  have cutoff' (n : ℤ) (hn : (A : ℤ) ≤ n) : mu D U n W = 0 := by
    change ((Y D (inclusion D α u))[[n]]) (inclusion D δ w) = 0
    rw [← inclusion_canonical, cutoff n hn, map_zero]
  have h := coupled_borcherds D U V T W k A locality cutoff' q r z₀
  have bor (j : ℕ) := borcherds D U V (Cj j) ((A : ℤ) + k - j) q r
  have finite : Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * integerBinomial r i) •
        ∑ j ∈ Finset.range (k + 1), weight k j •
          mu D U ((A : ℤ) + k - j + r - i) (mu D V (q + i) (Cj j))) := by
    have f := Function.HasFiniteSupport.sum
      (fun j : ℕ => (bor j).2.1.smul_right (fun _ => weight k j))
      (Finset.range (k + 1))
    convert f using 1
    funext i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact smul_comm _ _ _
  have projected := congrArg P h
  rw [map_sum, map_finsum P finite] at projected
  simp only [map_smul, map_sum] at projected
  have left (j : ℕ) (hj : j ≤ k) :
      P (∑ᶠ h : ℕ, jacobiLeftTerm D ((A : ℤ) + k - j) q r U V (Cj j) h) =
        clearIterate k (A + k - j) (B + k - l)
          (fun s x => balanced D α β γ δ u v t w s x (z - C - j - l)) s x := by
    rw [map_finsum P (bor j).1]
    have term (h : ℕ) :
        P (jacobiLeftTerm D ((A : ℤ) + k - j) q r U V (Cj j) h) =
          integerBinomial ((A + k - j : ℕ) : ℤ) h •
            balanced D α β γ δ u v t w (s - k - h)
              (x - (B + k - l : ℕ) - (A + k - j : ℕ) + h) (z - C - j - l) := by
      simp only [jacobiLeftTerm, mu, U, V, T, W, P, Cj, q, r, z₀,
        inclusion, Finsupp.lsingle_apply, ← single_canonical, projection,
        Finsupp.lapply_apply, Finsupp.smul_apply]
      rw [Finsupp.single_eq_same]
      have hp : (A : ℤ) + k - j = ((A + k - j : ℕ) : ℤ) := by omega
      rw [hp]
      unfold balanced
      rw [show (k : ℤ) - s - 1 + h = -(s - k - h) - 1 by omega,
        show ((A + k - j : ℕ) : ℤ) + ((B : ℤ) + k - l - x - 1) - h =
          -(x - (B + k - l : ℕ) - (A + k - j : ℕ) + h) - 1 by omega,
        show (C : ℤ) + l - z - 1 + j = -(z - C - j - l) - 1 by omega]
    simp_rw [term]
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
    apply finsum_eq_sum_of_support_subset
    intro h hh
    by_contra hout
    have bound : A + k - j < h := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    exact hh (by simp [Nat.choose_eq_zero_of_lt bound])
  have first (j i : ℕ) :
      P (mu D U ((A : ℤ) + k - j + r - i) (mu D V (q + i) (Cj j))) =
        LatticeSectorThreeFieldCommonSeries.nestedCanonical D ![α, β, γ] ![u, v, t] δ w 0 1 2
          ![s - A - 2 * k + j + i, x - B - k + l - i, z - C - j - l] := by
    simp only [mu, U, V, T, W, P, Cj, q, r, z₀,
      inclusion, Finsupp.lsingle_apply, ← single_canonical, projection,
      Finsupp.lapply_apply]
    rw [show α + (β + (γ + δ)) = (α + β) + (γ + δ) by abel,
      Finsupp.single_eq_same]
    unfold LatticeSectorThreeFieldCommonSeries.nestedCanonical
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [show (A : ℤ) + k - j + ((k : ℤ) - s - 1) - i =
        -(s - A - 2 * k + j + i) - 1 by omega,
      show (B : ℤ) + k - l - x - 1 + i = -(x - B - k + l - i) - 1 by omega,
      show (C : ℤ) + l - z - 1 + j = -(z - C - j - l) - 1 by omega]
    rfl
  simp_rw [first] at projected
  rw [← projected]
  apply Finset.sum_congr rfl
  intro j hj
  rw [left j (by simpa using Finset.mem_range.mp hj)]

end
end D5.S3.VertexAlgebra.LatticeSectorBalancedBorcherds
