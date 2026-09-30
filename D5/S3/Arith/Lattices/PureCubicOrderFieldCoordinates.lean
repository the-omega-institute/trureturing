/- GID: D5/S3/Arith/Lattices/PureCubicOrderFieldCoordinates
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicOrderFieldCoordinates
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual pure-cubic order coordinates satisfy two divisibility conditions. -/

import D5.S3.Arith.Lattices.PureCubicMixedMaximality
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates

open Module

/-- In the actual maximal integral basis, membership in the displayed cubic
order is exactly divisibility of the second and third coordinates. -/
theorem pure_cubic_order_field_coordinates
    {K : Type*} [Field K] [NumberField K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hmpos : 0 < m) (hnpos : 0 < n) (hcpos : 0 < c)
    (hmsq : Squarefree m) (hnsq : Squarefree n) (hcop : IsCoprime m n)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k) :
    let gamma : K :=
      (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3
    let theta : K := (c : K) * pb.gen
    let beta : K := (1 + theta + theta ^ 2) / 3
    (∀ z : K, IsIntegral ℤ z ↔ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen + (s : K) * gamma) ∧
    (∀ u r s : ℤ,
      (∃ x y t : ℤ,
        (u : K) + (r : K) * pb.gen + (s : K) * gamma =
          (x : K) + (y : K) * theta + (t : K) * beta) ↔
        c ∣ r ∧ c ^ 2 * n ∣ s) := by
  dsimp
  let gamma : K :=
    (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3
  let theta : K := (c : K) * pb.gen
  let beta : K := (1 + theta + theta ^ 2) / 3
  change (∀ z : K, IsIntegral ℤ z ↔ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen + (s : K) * gamma) ∧
    (∀ u r s : ℤ,
      (∃ x y t : ℤ,
        (u : K) + (r : K) * pb.gen + (s : K) * gamma =
          (x : K) + (y : K) * theta + (t : K) * beta) ↔
        c ∣ r ∧ c ^ 2 * n ∣ s)
  have hmax :=
    D5.S3.Arith.Lattices.PureCubicMixedMaximality.pure_cubic_mixed_maximality_and_discriminant
      pb h3 m n c a k v hmpos hnpos hmsq hnsq hcop hv hroot hcubic hcv
  have hbsource :=
    D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices
      pb h3 m n c a k v (ne_of_gt hmpos) (ne_of_gt hnpos)
      hv hroot hcubic hcv
  obtain ⟨_, b, _, hb, _, _⟩ := hbsource.2.2.2
  have hb0 : b 0 = (1 : K) := by simpa using congrFun hb 0
  have hb1 : b 1 = pb.gen := by simpa using congrFun hb 1
  have hb2 : b 2 = gamma := by simpa [gamma] using congrFun hb 2
  have huniq (u r s u' r' s' : ℤ)
      (heq : (u : K) + (r : K) * pb.gen + (s : K) * gamma =
        (u' : K) + (r' : K) * pb.gen + (s' : K) * gamma) :
      u = u' ∧ r = r' ∧ s = s' := by
    have heq' : (u : ℚ) • b 0 + (r : ℚ) • b 1 + (s : ℚ) • b 2 =
        (u' : ℚ) • b 0 + (r' : ℚ) • b 1 + (s' : ℚ) • b 2 := by
      simpa [hb0, hb1, hb2, Algebra.smul_def] using heq
    have heqrepr := congrArg b.repr heq'
    have hu := congrArg (fun f : Fin 3 →₀ ℚ => f 0) heqrepr
    have hr := congrArg (fun f : Fin 3 →₀ ℚ => f 1) heqrepr
    have hs := congrArg (fun f : Fin 3 →₀ ℚ => f 2) heqrepr
    simp [map_add, map_smul, Basis.repr_self] at hu hr hs
    exact ⟨by exact_mod_cast hu, by exact_mod_cast hr, by exact_mod_cast hs⟩
  have hnK : (n : K) ≠ 0 := by exact_mod_cast ne_of_gt hnpos
  have hcvK : (c : K) ^ 2 * (n : K) = (v : K) + 3 * (k : K) := by
    exact_mod_cast hcv
  have hvSqK : (v : K) ^ 2 = 1 := by
    rcases hv with hv | hv <;> rw [hv] <;> norm_num
  have hgammaBeta : gamma = beta - (k : K) * (pb.gen ^ 2 / (n : K)) := by
    dsimp [gamma, beta, theta]
    field_simp [hnK]
    linear_combination -(pb.gen ^ 2) * hcvK
  have hq : pb.gen ^ 2 / (n : K) =
      (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
    calc
      pb.gen ^ 2 / (n : K) =
          (v : K) ^ 2 * (pb.gen ^ 2 / (n : K)) := by rw [hvSqK]; ring
      _ = (v : K) * (3 * gamma - 1 - (c : K) * pb.gen) := by
        dsimp [gamma]
        field_simp [hnK]
        ring
  have hcoef : ((v * c ^ 2 * n : ℤ) : K) =
      1 + 3 * (k : K) * (v : K) := by
    calc
      ((v * c ^ 2 * n : ℤ) : K) =
          (v : K) * ((c : K) ^ 2 * (n : K)) := by push_cast; ring
      _ = (v : K) * ((v : K) + 3 * (k : K)) := by rw [hcvK]
      _ = (v : K) ^ 2 + 3 * (k : K) * (v : K) := by ring
      _ = 1 + 3 * (k : K) * (v : K) := by rw [hvSqK]
  have hbeta : beta =
      (-(k * v) : ℤ) + (-(k * v * c) : ℤ) * pb.gen +
        ((v * c ^ 2 * n : ℤ) : K) * gamma := by
    have hbetaGamma : beta = gamma + (k : K) *
        (pb.gen ^ 2 / (n : K)) := (eq_sub_iff_add_eq.mp hgammaBeta).symm
    rw [hbetaGamma, hq, hcoef]
    push_cast
    ring
  refine ⟨hmax.1, ?_⟩
  intro u r s
  constructor
  · rintro ⟨x, y, t, heq⟩
    have heq' : (u : K) + (r : K) * pb.gen + (s : K) * gamma =
        ((x - k * v * t : ℤ) : K) +
          ((c * y - k * v * c * t : ℤ) : K) * pb.gen +
          ((v * c ^ 2 * n * t : ℤ) : K) * gamma := by
      rw [heq, hbeta]
      push_cast
      ring
    obtain ⟨_, hr, hs⟩ := huniq u r s
      (x - k * v * t) (c * y - k * v * c * t) (v * c ^ 2 * n * t) heq'
    constructor
    · refine ⟨y - k * v * t, ?_⟩
      rw [hr]
      ring
    · refine ⟨v * t, ?_⟩
      rw [hs]
      ring
  · rintro ⟨⟨y, hy⟩, ⟨t, ht⟩⟩
    refine ⟨u + k * t, y + k * t, v * t, ?_⟩
    rw [hy, ht, hbeta]
    push_cast
    rcases hv with hv | hv <;> rw [hv] <;> norm_num <;> ring

#print axioms pure_cubic_order_field_coordinates

end D5.S3.Arith.Lattices.PureCubicOrderFieldCoordinates
