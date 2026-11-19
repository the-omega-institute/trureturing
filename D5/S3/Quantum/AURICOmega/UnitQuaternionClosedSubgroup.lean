/- GID: D5/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/UnitQuaternionClosedSubgroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A closed noncommutative subgroup of unit quaternions with close-reading chains is all. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
import D5.S3.Quantum.AURICOmega.UnitQuaternionPolar
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Sequences

/-! Closed chain-connected noncommutative subgroups of the unit quaternions.

A closed subgroup `H` of the unit quaternions that contains two noncommuting elements, and in
which any two elements are joined for every `ε > 0` by a chain in `H` whose consecutive readings
exceed `1 - ε`, is the whole group. An axis of `H` is a square root `a` of `-1` such that every
`cos t + sin t • a` lies in `H`.

* Small nontrivial elements: a chain from `1` to an element other than `1` has a step from `1`
  to an element other than `1`, so `H` has elements other than `1` with reading against `1`
  arbitrarily close to one.
* A first axis: write such elements as `cos θ + sin θ • n` with `n` a unit imaginary quaternion
  and `θ` tending to zero; the `n` accumulate at some `a` by compactness of the unit imaginary
  sphere, and along a subsequence the powers with exponent `⌊t / θ⌋` converge to
  `cos t + sin t • a` for `t ≥ 0`, which therefore lies in the closed subgroup `H`. Negative `t`
  come from inverses.
* A second axis off the poles: conjugation by a unit quaternion `p` sends the first axis to `i`.
  Elements of `H` commuting with the first axis would commute with each other, so some element
  of `H` does not; a chain from `1` to it, at threshold one half, has a step from an element
  commuting with the axis to one that does not. The quotient `g` of that step does not commute
  with the axis and has reading against `1` above one half, so its conjugate by `p` has positive
  real part. The conjugate of the axis by `g` is an axis whose image under conjugation by `p`
  has height strictly between `-1` and `1`.
* All axes, through their images under conjugation by `p`: these images contain `i`, are closed
  under negation, and are closed under conjugation of one image by `cos s + sin s • b` for
  another image `b`. Conjugating `i` by `cos s + sin s • b`, for `b` of height `α`, reaches every
  height in `[2 α ^ 2 - 1, 1]`, by a formula in the double angle `2 s`; iterating from a height in
  `[0, 1)` reaches height zero and then every height, and rotation about `i` acts transitively on
  each circle of latitude, so every square root of `-1` is an axis.
* Conclusion: every unit quaternion is `cos θ + sin θ • n` with `n` a unit imaginary quaternion,
  hence lies in `H`. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
open D5.S3.Quantum.AURICOmega.UnitQuaternionPolar

/-- The quaternion `cos t + sin t • a`. -/
private def cs (a : ℍ[ℝ]) (t : ℝ) : ℍ[ℝ] := ((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • a

/-- Conjugation `b ↦ u * b * star u` by `u = cos s + sin s • a`. -/
private def rot (a : ℍ[ℝ]) (s : ℝ) (b : ℍ[ℝ]) : ℍ[ℝ] := cs a s * b * star (cs a s)

/-- A square root of `-1` is a pure imaginary quaternion of norm one, in coordinates. -/
private lemma re_eq_zero_of_mul_self {c : ℍ[ℝ]} (h : c * c = -1) :
    c.re = 0 ∧ c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2 = 1 := by
  have h0 := congrArg (fun q : ℍ[ℝ] => q.re) h
  have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
  have h2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h
  have h3 := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
    neg_zero] at h0 h1 h2 h3
  have hsq : c.re ^ 2 * (1 + c.re ^ 2) = 0 := by
    linear_combination (c.re * c.imI / 2) * h1 + (c.re * c.imJ / 2) * h2 +
      (c.re * c.imK / 2) * h3 + c.re ^ 2 * h0
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp hsq with h' | h'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
    · nlinarith [sq_nonneg c.re]
  refine ⟨hre, ?_⟩
  rw [hre] at h0
  linear_combination -h0

/-- A pure imaginary quaternion of norm one squares to `-1`. -/
private lemma mul_self_of_norm {c : ℍ[ℝ]} (hre : c.re = 0) (hn : ‖c‖ = 1) : c * c = -1 := by
  rw [← sq, Quaternion.sq_eq_neg_normSq.mpr hre, Quaternion.normSq_eq_norm_mul_self, hn,
    mul_one, Quaternion.coe_one]

/-- A square root of `-1` has norm square one. -/
private lemma normSq_of_mul_self {c : ℍ[ℝ]} (h : c * c = -1) : Quaternion.normSq c = 1 := by
  obtain ⟨h0, h1⟩ := re_eq_zero_of_mul_self h
  rw [Quaternion.normSq_def']
  change c.re ^ 2 + c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2 = 1
  rw [h0]
  linear_combination h1

/-- `cos t + sin t • a` has norm square one when `a * a = -1`. -/
private lemma normSq_cs {a : ℍ[ℝ]} (ha : a * a = -1) (t : ℝ) : Quaternion.normSq (cs a t) = 1 := by
  obtain ⟨h0, h1⟩ := re_eq_zero_of_mul_self ha
  rw [Quaternion.normSq_def']
  change (cs a t).re ^ 2 + (cs a t).imI ^ 2 + (cs a t).imJ ^ 2 + (cs a t).imK ^ 2 = 1
  simp only [cs, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe, smul_eq_mul,
    h0]
  linear_combination Real.sin t ^ 2 * h1 + Real.sin_sq_add_cos_sq t

/-- A quaternion of norm square one is unitary. -/
private lemma mem_unitary_of_normSq {u : ℍ[ℝ]} (h : Quaternion.normSq u = 1) :
    u ∈ unitary ℍ[ℝ] := by
  have h' : ((Quaternion.normSq u : ℝ) : ℍ[ℝ]) = 1 := by rw [h, Quaternion.coe_one]
  exact Unitary.mem_iff.mpr ⟨(Quaternion.star_mul_self u).trans h',
    (Quaternion.self_mul_star u).trans h'⟩

/-- The conjugate of `cos t + sin t • a` is `cos (-t) + sin (-t) • a` when `a * a = -1`. -/
private lemma star_cs {a : ℍ[ℝ]} (ha : a * a = -1) (t : ℝ) : star (cs a t) = cs a (-t) := by
  have hs : star a = -a := Quaternion.star_eq_neg.mpr (re_eq_zero_of_mul_self ha).1
  rw [cs, cs, star_add, Quaternion.star_coe, Quaternion.star_smul, hs, Real.cos_neg,
    Real.sin_neg, neg_smul, smul_neg]

/-- A star algebra automorphism maps `cos t + sin t • a` to `cos t + sin t • ψ a`. -/
private lemma map_cs (ψ : ℍ[ℝ] ≃⋆ₐ[ℝ] ℍ[ℝ]) (a : ℍ[ℝ]) (t : ℝ) : ψ (cs a t) = cs (ψ a) t := by
  rw [cs, cs, map_add, map_smul, ← congrFun Quaternion.algebraMap_def, AlgHomClass.commutes]

/-- The reading against `1` is half of one plus the real part. -/
private lemma kappa_one_left (u : unitary ℍ[ℝ]) :
    quaternionModel.kappa 1 u = (1 + (u : ℍ[ℝ]).re) / 2 := by
  change (1 + ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (u : ℍ[ℝ])⟫_ℝ) / 2 = _
  rw [Quaternion.inner_def, OneMemClass.coe_one, one_mul, Quaternion.re_star]

/-- Height of the image of `i` under conjugation by `cos s + sin s • a`, for `a * a = -1`. -/
private lemma imI_rot_i {a : ℍ[ℝ]} (ha : a * a = -1) (s : ℝ) :
    (rot a s ⟨0, 1, 0, 0⟩).imI = Real.cos (2 * s) + a.imI ^ 2 * (1 - Real.cos (2 * s)) := by
  obtain ⟨h0, h1⟩ := re_eq_zero_of_mul_self ha
  simp only [rot, cs, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul, Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe,
    Quaternion.imK_coe, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, smul_eq_mul, h0, Real.cos_two_mul]
  linear_combination (2 * a.imI ^ 2 - 1) * Real.sin_sq_add_cos_sq s - Real.sin s ^ 2 * h1

/-- Two plane vectors of equal length differ by a rotation: the quotient of the corresponding
complex numbers has norm one, hence is `exp (φ * I)`. -/
private lemma exists_rotation_plane {x y x' y' : ℝ} (h : x ^ 2 + y ^ 2 = x' ^ 2 + y' ^ 2) :
    ∃ φ : ℝ, Real.cos φ * x - Real.sin φ * y = x' ∧ Real.sin φ * x + Real.cos φ * y = y' := by
  have hn : ‖(⟨x', y'⟩ : ℂ)‖ = ‖(⟨x, y⟩ : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def, Complex.normSq_mk, Complex.normSq_mk, ← sq, ← sq,
      ← sq, ← sq, h]
  by_cases hz : (⟨x, y⟩ : ℂ) = 0
  · have hz' : (⟨x', y'⟩ : ℂ) = 0 := norm_eq_zero.mp (by rw [hn, hz, norm_zero])
    obtain ⟨hx, hy⟩ : x = 0 ∧ y = 0 := Complex.ext_iff.mp hz
    obtain ⟨hx', hy'⟩ : x' = 0 ∧ y' = 0 := Complex.ext_iff.mp hz'
    refine ⟨0, ?_, ?_⟩
    · rw [hx, hy, hx']
      ring
    · rw [hx, hy, hy']
      ring
  · obtain ⟨φ, hφ⟩ := (Complex.norm_eq_one_iff ((⟨x', y'⟩ : ℂ) / ⟨x, y⟩)).mp (by
      rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hz)])
    have hw : Complex.exp (φ * Complex.I) * ⟨x, y⟩ = ⟨x', y'⟩ := by
      rw [hφ, div_mul_cancel₀ _ hz]
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hre
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at him
    exact ⟨φ, hre, by linarith⟩

/-- Rotation about `i` is transitive on each circle of latitude of the unit imaginary sphere. -/
private lemma exists_rot_i_eq {b c : ℍ[ℝ]} (hb : b * b = -1) (hc : c * c = -1)
    (h1 : b.imI = c.imI) : ∃ s : ℝ, rot ⟨0, 1, 0, 0⟩ s b = c := by
  obtain ⟨hb0, hbn⟩ := re_eq_zero_of_mul_self hb
  obtain ⟨hc0, hcn⟩ := re_eq_zero_of_mul_self hc
  obtain ⟨φ, h2, h3⟩ := exists_rotation_plane (x := b.imJ) (y := b.imK) (x' := c.imJ)
    (y' := c.imK) (by rw [h1] at hbn; linarith)
  have hcos : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hsin : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hp := Real.sin_sq_add_cos_sq (φ / 2)
  refine ⟨φ / 2, ?_⟩
  ext <;> simp only [rot, cs, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
    Quaternion.imK_smul, Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe,
    Quaternion.imK_coe, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, smul_eq_mul, hb0, hc0]
  · ring
  · linear_combination h1 + b.imI * hp
  · linear_combination h2 - b.imJ * hcos - b.imJ * hp + b.imK * hsin
  · linear_combination h3 - b.imK * hcos - b.imK * hp - b.imJ * hsin

/-- A set of square roots of `-1` that contains `i` and a point off the poles `±i`, and is closed
under negation and under conjugation of a member by `cos s + sin s • a` for a member `a`,
contains every square root of `-1`. Conjugating `i` by `cos s + sin s • a` reaches every height
in `[2 α ^ 2 - 1, 1]` where `α` is the height of `a`; iterating reaches height zero, and from
there every height; rotation about `i` then fills each circle of latitude. -/
private lemma mem_of_mul_self_eq_neg_one (B : Set ℍ[ℝ]) (hi : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) ∈ B)
    (hunit : ∀ b ∈ B, b * b = -1) (hneg : ∀ b ∈ B, -b ∈ B)
    (hrot : ∀ a ∈ B, ∀ b ∈ B, ∀ s : ℝ, rot a s b ∈ B)
    (h0 : ∃ b ∈ B, b.imI ^ 2 < 1) (c : ℍ[ℝ]) (hc : c * c = -1) : c ∈ B := by
  have hstep : ∀ a ∈ B, a.imI ^ 2 < 1 → ∀ h : ℝ, 2 * a.imI ^ 2 - 1 ≤ h → h ≤ 1 →
      ∃ b ∈ B, b.imI = h := by
    intro a ha hα h hh1 hh2
    have hden : 0 < 1 - a.imI ^ 2 := by linarith
    have hC1 : -1 ≤ (h - a.imI ^ 2) / (1 - a.imI ^ 2) := by
      rw [le_div_iff₀ hden]; linarith
    have hC2 : (h - a.imI ^ 2) / (1 - a.imI ^ 2) ≤ 1 := by
      rw [div_le_iff₀ hden]; linarith
    refine ⟨rot a (Real.arccos ((h - a.imI ^ 2) / (1 - a.imI ^ 2)) / 2) ⟨0, 1, 0, 0⟩,
      hrot a ha _ hi _, ?_⟩
    have hmul : (h - a.imI ^ 2) / (1 - a.imI ^ 2) * (1 - a.imI ^ 2) = h - a.imI ^ 2 :=
      div_mul_cancel₀ _ hden.ne'
    rw [imI_rot_i (hunit a ha), show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring,
      Real.cos_arccos hC1 hC2]
    linear_combination hmul
  have hfill : ∀ a ∈ B, a.imI = 0 → c ∈ B := by
    intro a ha ha0
    obtain ⟨-, hcn⟩ := re_eq_zero_of_mul_self hc
    obtain ⟨b, hb, hbh⟩ := hstep a ha (by rw [ha0]; norm_num) c.imI
      (by rw [ha0]; nlinarith [sq_nonneg c.imJ, sq_nonneg c.imK, sq_nonneg (c.imI + 1)])
      (by nlinarith [sq_nonneg c.imJ, sq_nonneg c.imK, sq_nonneg (c.imI - 1)])
    obtain ⟨s, hs⟩ := exists_rot_i_eq (hunit b hb) hc hbh
    rw [← hs]
    exact hrot _ hi b hb s
  obtain ⟨b₀, hb₀, hb₀h⟩ := h0
  obtain ⟨a₀, ha₀, ha₀0, ha₀1⟩ : ∃ a ∈ B, 0 ≤ a.imI ∧ a.imI < 1 := by
    rcases le_or_gt 0 b₀.imI with h | h
    · exact ⟨b₀, hb₀, h, by nlinarith⟩
    · refine ⟨-b₀, hneg b₀ hb₀, ?_, ?_⟩ <;> rw [Quaternion.imI_neg] <;> nlinarith
  have hdesc : ∀ N : ℕ, ∀ a ∈ B, 0 ≤ a.imI → a.imI ≤ a₀.imI →
      a.imI ≤ N * (1 - a₀.imI) → c ∈ B := by
    intro N
    induction N with
    | zero =>
      intro a ha h0 _ hN
      rw [Nat.cast_zero, zero_mul] at hN
      exact hfill a ha (le_antisymm hN h0)
    | succ N ih =>
      intro a ha h0 h1 hN
      have hα : a.imI ^ 2 < 1 := by nlinarith
      have hprod : 0 ≤ (1 - a.imI) * a.imI := mul_nonneg (by linarith) h0
      rcases le_or_gt (2 * a.imI ^ 2 - 1) 0 with hle | hpos
      · obtain ⟨b, hb, hb0⟩ := hstep a ha hα 0 hle zero_le_one
        exact hfill b hb hb0
      · obtain ⟨b, hb, hbh⟩ := hstep a ha hα (2 * a.imI ^ 2 - 1) le_rfl (by linarith)
        refine ih b hb (by rw [hbh]; exact hpos.le) (by rw [hbh]; nlinarith) ?_
        rw [hbh]
        rw [Nat.cast_succ] at hN
        nlinarith
  obtain ⟨N, hN⟩ := exists_nat_ge (a₀.imI / (1 - a₀.imI))
  exact hdesc N a₀ ha₀ ha₀0 le_rfl (by rwa [div_le_iff₀ (by linarith)] at hN)

/-- `a` is an axis of `H`: `a * a = -1` and every `cos t + sin t • a` lies in `H`. -/
private def IsAxis (H : Subgroup (unitary ℍ[ℝ])) (a : ℍ[ℝ]) : Prop :=
  a * a = -1 ∧ ∀ t : ℝ, ∃ u ∈ H, (u : ℍ[ℝ]) = cs a t

/-- Conjugating an axis by an element of `H` gives an axis. -/
private lemma isAxis_conj {H : Subgroup (unitary ℍ[ℝ])} {a : ℍ[ℝ]} (ha : IsAxis H a)
    {g : unitary ℍ[ℝ]} (hg : g ∈ H) : IsAxis H ((g : ℍ[ℝ]) * a * star (g : ℍ[ℝ])) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ[ℝ] ≃⋆ₐ[ℝ] ℍ[ℝ], ∀ x, ψ x = (g : ℍ[ℝ]) * x * star (g : ℍ[ℝ]) :=
    ⟨Unitary.conjStarAlgAut ℝ ℍ[ℝ] g, fun x => rfl⟩
  refine ⟨?_, fun t => ?_⟩
  · rw [← hψ, ← map_mul, ha.1, map_neg, map_one]
  · obtain ⟨u, hu, hut⟩ := ha.2 t
    refine ⟨g * u * g⁻¹, H.mul_mem (H.mul_mem hg hu) (H.inv_mem hg), ?_⟩
    rw [← hψ, ← map_cs, ← hut, hψ]
    rfl

/-- The negative of an axis is an axis. -/
private lemma isAxis_neg {H : Subgroup (unitary ℍ[ℝ])} {a : ℍ[ℝ]} (ha : IsAxis H a) :
    IsAxis H (-a) := by
  refine ⟨by rw [neg_mul_neg, ha.1], fun t => ?_⟩
  obtain ⟨u, hu, hut⟩ := ha.2 (-t)
  refine ⟨u, hu, ?_⟩
  rw [hut, cs, cs, Real.cos_neg, Real.sin_neg, neg_smul, smul_neg]

/-- A chain inside `H` from a point with property `P` to a point without it has a step from a
point with `P` to a point without `P`. -/
private lemma exists_step {H : Subgroup (unitary ℍ[ℝ])} {ε : ℝ} (P : unitary ℍ[ℝ] → Prop)
    {x y : unitary ℍ[ℝ]} (hx : x ∈ H)
    (hxy : Relation.ReflTransGen
      (fun a b : unitary ℍ[ℝ] => b ∈ H ∧ 1 - ε < quaternionModel.kappa a b) x y)
    (hPx : P x) (hPy : ¬ P y) :
    ∃ a ∈ H, ∃ b ∈ H, P a ∧ ¬ P b ∧ 1 - ε < quaternionModel.kappa a b := by
  suffices h : y ∈ H ∧
      (¬ P y → ∃ a ∈ H, ∃ b ∈ H, P a ∧ ¬ P b ∧ 1 - ε < quaternionModel.kappa a b) from
    h.2 hPy
  clear hPy
  induction hxy with
  | refl => exact ⟨hx, fun h => absurd hPx h⟩
  | @tail b c _ hbc ih =>
    refine ⟨hbc.1, fun hPc => ?_⟩
    by_cases hPb : P b
    · exact ⟨b, ih.1, c, hbc.1, hPb, hPc, hbc.2⟩
    · exact ih.2 hPb

/-- A quaternion commutes with `i` exactly when its `j` and `k` coordinates vanish. -/
private lemma mul_i_eq_i_mul_iff (x : ℍ[ℝ]) :
    x * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * x ↔ x.imJ = 0 ∧ x.imK = 0 := by
  constructor
  · intro h
    have hJ := congrArg (fun q : ℍ[ℝ] => q.imJ) h
    have hK := congrArg (fun q : ℍ[ℝ] => q.imK) h
    simp only [Quaternion.imJ_mul, Quaternion.imK_mul] at hJ hK
    constructor <;> linarith
  · rintro ⟨hJ, hK⟩
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, hJ, hK] <;> ring

/-- Two quaternions commuting with `i` commute with each other. -/
private lemma mul_comm_of_mul_i {x y : ℍ[ℝ]} (hx : x * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * x)
    (hy : y * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * y) : x * y = y * x := by
  obtain ⟨hx2, hx3⟩ := (mul_i_eq_i_mul_iff x).mp hx
  obtain ⟨hy2, hy3⟩ := (mul_i_eq_i_mul_iff y).mp hy
  ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hx2, hx3, hy2, hy3] <;> ring

/-- Height of the conjugate `G * i * star G`. -/
private lemma imI_mul_i_mul_star (G : ℍ[ℝ]) :
    (G * ⟨0, 1, 0, 0⟩ * star G).imI = G.re ^ 2 + G.imI ^ 2 - G.imJ ^ 2 - G.imK ^ 2 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- The coordinates of a unit quaternion have squares summing to one. -/
private lemma sq_add_sq_coe_unitary (u : unitary ℍ[ℝ]) :
    (u : ℍ[ℝ]).re ^ 2 + (u : ℍ[ℝ]).imI ^ 2 + (u : ℍ[ℝ]).imJ ^ 2 + (u : ℍ[ℝ]).imK ^ 2 = 1 := by
  have h : Quaternion.normSq (u : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  rwa [Quaternion.normSq_def'] at h

/-- A closed subgroup with elements other than `1` of reading against `1` arbitrarily close to
one has an axis. The polar angles of such elements tend to zero, their unit imaginary parts
accumulate at some `n` by compactness of the unit sphere, and the powers with exponent
`⌊t / θ⌋` converge to `cos t + sin t • n`. -/
private lemma exists_isAxis (H : Subgroup (unitary ℍ[ℝ]))
    (hclosed : IsClosed (H : Set (unitary ℍ[ℝ])))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ h ∈ H, h ≠ 1 ∧ 1 - ε < quaternionModel.kappa 1 h) :
    ∃ n : ℍ[ℝ], IsAxis H n := by
  choose h hH hne hk using fun k : ℕ => hsmall (1 / ((k : ℝ) + 1)) (by positivity)
  have hle : ∀ k, (h k : ℍ[ℝ]).re ≤ 1 := fun k => by
    nlinarith [sq_add_sq_coe_unitary (h k), sq_nonneg (h k : ℍ[ℝ]).imI,
      sq_nonneg (h k : ℍ[ℝ]).imJ, sq_nonneg (h k : ℍ[ℝ]).imK, sq_nonneg ((h k : ℍ[ℝ]).re - 1)]
  have hlt : ∀ k, (h k : ℍ[ℝ]).re < 1 := fun k => by
    refine lt_of_le_of_ne (hle k) fun h1 => hne k (Subtype.ext ?_)
    have hc := sq_add_sq_coe_unitary (h k)
    rw [h1] at hc
    have hI : (h k : ℍ[ℝ]).imI = 0 := by
      nlinarith [sq_nonneg (h k : ℍ[ℝ]).imI, sq_nonneg (h k : ℍ[ℝ]).imJ,
        sq_nonneg (h k : ℍ[ℝ]).imK]
    have hJ : (h k : ℍ[ℝ]).imJ = 0 := by
      nlinarith [sq_nonneg (h k : ℍ[ℝ]).imI, sq_nonneg (h k : ℍ[ℝ]).imJ,
        sq_nonneg (h k : ℍ[ℝ]).imK]
    have hK : (h k : ℍ[ℝ]).imK = 0 := by
      nlinarith [sq_nonneg (h k : ℍ[ℝ]).imI, sq_nonneg (h k : ℍ[ℝ]).imJ,
        sq_nonneg (h k : ℍ[ℝ]).imK]
    ext
    · exact h1
    · exact hI
    · exact hJ
    · exact hK
  have hlow : ∀ k : ℕ, 1 - 2 * (1 / ((k : ℝ) + 1)) ≤ (h k : ℍ[ℝ]).re := fun k => by
    have := hk k
    rw [kappa_one_left] at this
    linarith
  have hre : Filter.Tendsto (fun k => (h k : ℍ[ℝ]).re) Filter.atTop (nhds 1) := by
    have hl := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).const_sub 1
    rw [mul_zero, sub_zero] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hle
  set θ : ℕ → ℝ := fun k => Real.arccos (h k : ℍ[ℝ]).re
  have hθ : Filter.Tendsto θ Filter.atTop (nhds 0) := by
    have := (Real.continuous_arccos.tendsto 1).comp hre
    rwa [Real.arccos_one] at this
  have hθpos : ∀ k, 0 < θ k := fun k => Real.arccos_pos.mpr (hlt k)
  choose n hn0 hn1 hpol using fun k =>
    exists_eq_cos_arccos_add_sin_smul (h k : ℍ[ℝ]) (CStarRing.norm_coe_unitary (h k))
  have hpol' : ∀ k, (h k : ℍ[ℝ]) = cs (n k) (θ k) := hpol
  have hK : IsCompact (Metric.sphere (0 : ℍ[ℝ]) 1 ∩ {q | q.re = 0}) :=
    (isCompact_sphere 0 1).inter_right (isClosed_eq Quaternion.continuous_re continuous_const)
  obtain ⟨a, ⟨ha1, ha0⟩, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq fun k => ⟨mem_sphere_zero_iff_norm.mpr (hn1 k), hn0 k⟩
  have haa : a * a = -1 := mul_self_of_norm ha0 (mem_sphere_zero_iff_norm.mp ha1)
  have hθφ : Filter.Tendsto (fun k => θ (φ k)) Filter.atTop (nhds 0) :=
    hθ.comp hφ.tendsto_atTop
  have hpos : ∀ t : ℝ, 0 ≤ t → ∃ u ∈ H, (u : ℍ[ℝ]) = cs a t := by
    intro t ht
    have hup : ∀ k, (⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k) ≤ t := fun k => by
      have := Nat.floor_le (div_nonneg ht (hθpos (φ k)).le)
      calc (⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k) ≤ t / θ (φ k) * θ (φ k) :=
            mul_le_mul_of_nonneg_right this (hθpos _).le
        _ = t := div_mul_cancel₀ t (hθpos _).ne'
    have hlo : ∀ k, t - θ (φ k) ≤ (⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k) := fun k => by
      have := Nat.lt_floor_add_one (t / θ (φ k))
      rw [div_lt_iff₀ (hθpos _)] at this
      linarith
    have hm : Filter.Tendsto (fun k => (⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k)) Filter.atTop
        (nhds t) := by
      have hl := (tendsto_const_nhds (x := t)).sub hθφ
      rw [sub_zero] at hl
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hup
    have hcoe : ∀ k, ((h (φ k) ^ ⌊t / θ (φ k)⌋₊ : unitary ℍ[ℝ]) : ℍ[ℝ]) =
        cs (n (φ k)) ((⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k)) := fun k => by
      rw [SubmonoidClass.coe_pow, hpol' (φ k)]
      exact cos_add_sin_smul_pow (n (φ k)) (hn0 _) (hn1 _) (θ (φ k)) _
    have hlim' : Filter.Tendsto (fun k => cs (n (φ k)) ((⌊t / θ (φ k)⌋₊ : ℝ) * θ (φ k)))
        Filter.atTop (nhds (cs a t)) :=
      ((Quaternion.continuous_coe.tendsto _).comp
        ((Real.continuous_cos.tendsto t).comp hm)).add
        (((Real.continuous_sin.tendsto t).comp hm).smul hlim)
    have htend : Filter.Tendsto (fun k => h (φ k) ^ ⌊t / θ (φ k)⌋₊) Filter.atTop
        (nhds ⟨cs a t, mem_unitary_of_normSq (normSq_cs haa t)⟩) := by
      rw [tendsto_subtype_rng]
      exact hlim'.congr fun k => (hcoe k).symm
    exact ⟨_, hclosed.mem_of_tendsto htend
      (Filter.Eventually.of_forall fun k => H.pow_mem (hH (φ k)) _), rfl⟩
  refine ⟨a, haa, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact hpos t ht
  · obtain ⟨u, hu, hut⟩ := hpos (-t) (by linarith)
    refine ⟨u⁻¹, H.inv_mem hu, ?_⟩
    rw [show ((u⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) = star (u : ℍ[ℝ]) from rfl, hut, star_cs haa,
      neg_neg]

/-- A closed subgroup of the unit quaternions that is noncommutative and in which any two
elements are joined, for every `ε > 0`, by a chain of elements of the subgroup with consecutive
readings above `1 - ε`, is the whole group. -/
theorem eq_top_of_isClosed_of_chainConnected (H : Subgroup (unitary ℍ[ℝ]))
    (hclosed : IsClosed (H : Set (unitary ℍ[ℝ])))
    (hchain : ∀ ε : ℝ, 0 < ε → ∀ x ∈ H, ∀ y ∈ H,
      Relation.ReflTransGen
        (fun a b : unitary ℍ[ℝ] => b ∈ H ∧ 1 - ε < quaternionModel.kappa a b) x y)
    (hnc : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x) : H = ⊤ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxy (by rw [one_mul, mul_one])
  obtain ⟨n, hn⟩ := exists_isAxis H hclosed fun ε hε => by
    obtain ⟨a, -, b, hb, ha1, hb1, hab⟩ :=
      exists_step (fun g => g = 1) H.one_mem (hchain ε hε 1 H.one_mem x hx) rfl hx1
    obtain rfl : a = 1 := ha1
    exact ⟨b, hb, hb1, hab⟩
  obtain ⟨nU, hnU⟩ : ∃ nU : unitary ℍ[ℝ], (nU : ℍ[ℝ]) = n :=
    ⟨⟨n, mem_unitary_of_normSq (normSq_of_mul_self hn.1)⟩, rfl⟩
  obtain ⟨p, q, hpq, hpn⟩ := exists_mul_mul_eq_of_kappa_eq 1 nU 1 unitI (by
    rw [kappa_one_left, kappa_one_left, hnU, (re_eq_zero_of_mul_self hn.1).1]
    rfl)
  rw [mul_one] at hpq
  obtain rfl : q = p⁻¹ := eq_inv_of_mul_eq_one_right hpq
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ[ℝ] ≃⋆ₐ[ℝ] ℍ[ℝ], ∀ z, ψ z = (p : ℍ[ℝ]) * z * star (p : ℍ[ℝ]) :=
    ⟨Unitary.conjStarAlgAut ℝ ℍ[ℝ] p, fun z => rfl⟩
  have hψn : ψ n = ⟨0, 1, 0, 0⟩ := by
    rw [hψ, ← hnU]
    exact congrArg Subtype.val hpn
  have hcomm : ∀ g : unitary ℍ[ℝ],
      Commute g nU ↔ ψ g * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * ψ g := by
    intro g
    rw [← hψn, ← map_mul, ← map_mul, EmbeddingLike.apply_eq_iff_eq, ← hnU, commute_iff_eq,
      Subtype.ext_iff]
    rfl
  obtain ⟨g₀, hg₀H, hg₀⟩ : ∃ g ∈ H, ¬ Commute g nU := by
    by_contra hall
    push Not at hall
    refine hxy (Subtype.ext (ψ.injective ?_))
    change ψ ((x : ℍ[ℝ]) * y) = ψ ((y : ℍ[ℝ]) * x)
    rw [map_mul, map_mul]
    exact mul_comm_of_mul_i ((hcomm x).mp (hall x hx)) ((hcomm y).mp (hall y hy))
  obtain ⟨a, haH, b, hbH, hPa, hPb, hab⟩ := exists_step (fun g => Commute g nU) H.one_mem
    (hchain (1 / 2) (by norm_num) 1 H.one_mem g₀ hg₀H) (Commute.one_left nU) hg₀
  have hgH : a⁻¹ * b ∈ H := H.mul_mem (H.inv_mem haH) hbH
  have hgc : ¬ Commute (a⁻¹ * b) nU := fun hc => hPb (by
    have := (hPa : Commute a nU).mul_left hc
    rwa [mul_inv_cancel_left] at this)
  have hgk : 1 - 1 / 2 < quaternionModel.kappa 1 (a⁻¹ * b) := by
    have := kappa_mul_mul a⁻¹ 1 a b
    rw [inv_mul_cancel, mul_one, mul_one] at this
    rw [this]
    exact hab
  set g := a⁻¹ * b
  have hGeq : ψ (g : ℍ[ℝ]) = ((p * g * p⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) := hψ g
  have hGre : 0 < (ψ (g : ℍ[ℝ])).re := by
    have h1 := kappa_mul_mul p p⁻¹ 1 g
    rw [mul_one, mul_inv_cancel, kappa_one_left] at h1
    rw [← h1] at hgk
    rw [hGeq]
    linarith
  have hGn := sq_add_sq_coe_unitary (p * g * p⁻¹)
  rw [← hGeq] at hGn
  have hGJK : 0 < (ψ g).imJ ^ 2 + (ψ g).imK ^ 2 := by
    by_contra hle
    push Not at hle
    refine hgc ((hcomm g).mpr ((mul_i_eq_i_mul_iff _).mpr ⟨?_, ?_⟩)) <;>
      nlinarith [sq_nonneg (ψ g).imJ, sq_nonneg (ψ g).imK]
  have hn' : IsAxis H ((g : ℍ[ℝ]) * n * star (g : ℍ[ℝ])) := isAxis_conj hn hgH
  have hb₀ : (ψ ((g : ℍ[ℝ]) * n * star (g : ℍ[ℝ]))).imI ^ 2 < 1 := by
    rw [map_mul, map_mul, map_star, hψn, imI_mul_i_mul_star]
    have hG0 : 0 < (ψ g).re ^ 2 := by positivity
    nlinarith
  have hall : ∀ c : ℍ[ℝ], c * c = -1 → IsAxis H c := by
    intro c hc
    have h := mem_of_mul_self_eq_neg_one {b | IsAxis H (ψ.symm b)}
      (by
        change IsAxis H (ψ.symm ⟨0, 1, 0, 0⟩)
        rw [← hψn, ψ.symm_apply_apply]
        exact hn)
      (fun b hb => by
        rw [← ψ.apply_symm_apply b, ← map_mul, (hb : IsAxis H (ψ.symm b)).1, map_neg,
          map_one])
      (fun b hb => by
        change IsAxis H (ψ.symm (-b))
        rw [map_neg]
        exact isAxis_neg hb)
      (fun a ha b hb s => by
        change IsAxis H (ψ.symm (rot a s b))
        obtain ⟨u, hu, hut⟩ := (ha : IsAxis H (ψ.symm a)).2 s
        rw [rot, map_mul, map_mul, map_star, map_cs, ← hut]
        exact isAxis_conj hb hu)
      ⟨_, (by
        change IsAxis H (ψ.symm (ψ ((g : ℍ[ℝ]) * n * star (g : ℍ[ℝ]))))
        rw [ψ.symm_apply_apply]
        exact hn'), hb₀⟩
      (ψ c) (by rw [← map_mul, hc, map_neg, map_one])
    change IsAxis H (ψ.symm (ψ c)) at h
    rwa [ψ.symm_apply_apply] at h
  rw [eq_top_iff]
  intro u _
  obtain ⟨m, hm0, hm1, hpol⟩ :=
    exists_eq_cos_arccos_add_sin_smul (u : ℍ[ℝ]) (CStarRing.norm_coe_unitary u)
  obtain ⟨v, hv, hvu⟩ := (hall m (mul_self_of_norm hm0 hm1)).2 (Real.arccos (u : ℍ[ℝ]).re)
  have hvu' : v = u := Subtype.ext (hvu.trans hpol.symm)
  rwa [hvu'] at hv

end D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
