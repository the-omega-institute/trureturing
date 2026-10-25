/- GID: D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The always-failing purification policy minimizes buffer availability. -/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound

/-- Index `k` denotes `k+1` generated links. -/
def weight (n : ℕ) (pg : ℝ) (k : Fin n) : ℝ :=
  (n.choose (k.val + 1) : ℝ) * pg ^ (k.val + 1) * (1 - pg) ^ (n - (k.val + 1))

def aggregate {n : ℕ} (pg : ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ k, a k * weight n pg k

/-- Success probability and unnormalized output fidelity satisfy Appendix C. -/
def admissible {n : ℕ} (a b c d : Fin n → ℝ) : Prop :=
  ∀ k f, (1 / 4 : ℝ) ≤ f → f ≤ 1 →
    (0 ≤ c k * (f - 1 / 4) + d k ∧ c k * (f - 1 / 4) + d k ≤ 1) ∧
    (0 ≤ a k * (f - 1 / 4) + b k ∧
      a k * (f - 1 / 4) + b k ≤ (3 / 4) * (c k * (f - 1 / 4) + d k))

/-- Theorem 1's formula, with `gam` denoting the source's noise parameter. -/
def availability (n : ℕ) (pg pc q gam fnew : ℝ) (a b c d : Fin n → ℝ) : ℝ :=
  let p := pc + q * (1 - (1 - pg) ^ n) * (1 - pc)
  let x := Real.exp gam - (1 - q + q * (1 - pg) ^ n) * (1 - pc)
  let ta := q * (1 - pc) * aggregate pg a / x
  let tb := q * (1 - pc) * aggregate pg b / p
  let tc := q * (1 - pc) * aggregate pg c / x
  let td := q * (1 - pc) * aggregate pg d / p
  let tgen := 1 / (1 - (1 - pg) ^ n)
  let tocc := (1 - ta + tc * (fnew - 1 / 4)) /
    (((1 - ta) * (1 - td) - tb * tc) * p)
  tocc / (tgen + tocc)

def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (pg pc gam fnew : ℝ),
    0 < pg → pg ≤ 1 → 0 < pc → pc ≤ 1 → 0 ≤ gam → 1 / 4 < fnew → fnew ≤ 1 →
    ∀ (a b c d : Fin n → ℝ), admissible a b c d → ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
    availability n pg pc 1 gam fnew 0 0 0 0 ≤
      availability n pg pc q gam fnew a b c d

private lemma generation_mass (n : ℕ) (pg : ℝ) (hn : 1 ≤ n)
    (hp : 0 < pg) (hp1 : pg ≤ 1) :
    (∑ k : Fin n, weight n pg k) = 1 - (1 - pg) ^ n ∧
      0 < 1 - (1 - pg) ^ n ∧ 1 - (1 - pg) ^ n ≤ 1 := by
  sorry

private lemma aggregate_endpoints {n : ℕ} (pg : ℝ) (hp : 0 ≤ pg) (hp1 : pg ≤ 1)
    (a b c d : Fin n → ℝ) (ha : admissible a b c d)
    (hs : (∑ k : Fin n, weight n pg k) = 1 - (1 - pg) ^ n) :
    let g := 1 - (1 - pg) ^ n
    let aa := aggregate pg a
    let bb := aggregate pg b
    let cc := aggregate pg c
    let dd := aggregate pg d
    (0 ≤ dd ∧ dd ≤ g) ∧ (0 ≤ (3 / 4) * cc + dd ∧ (3 / 4) * cc + dd ≤ g) ∧
    (0 ≤ bb ∧ bb ≤ (3 / 4) * dd) ∧
    (0 ≤ (3 / 4) * aa + bb ∧ (3 / 4) * aa + bb ≤ (3 / 4) * ((3 / 4) * cc + dd)) := by
  sorry

private lemma two_state_mass (u v w z ell mu h : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hmu : 0 < mu) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hl0 : ell ≤ u + w) (hl1 : ell ≤ v + z)
    (hc0 : u + w ≤ 1 - mu) (hc1 : v + z ≤ 1 - mu) :
    let det := (1 - u) * (1 - z) - v * w
    let num := (1 - z + w) * h + (v + 1 - u) * (1 - h)
    0 < det ∧ det ≤ (1 - ell) * num := by
  sorry

private lemma scalar_mass (g mu q e h a b c d : ℝ)
    (hg : 0 < g) (hg1 : g ≤ 1) (hm : 0 < mu) (hm1 : mu ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (he : 1 ≤ e) (hh : 0 ≤ h) (hh1 : h ≤ 3 / 4)
    (hd : 0 ≤ d ∧ d ≤ g) (hc : 0 ≤ (3 / 4) * c + d ∧ (3 / 4) * c + d ≤ g)
    (hb : 0 ≤ b ∧ b ≤ (3 / 4) * d)
    (ha : 0 ≤ (3 / 4) * a + b ∧ (3 / 4) * a + b ≤ (3 / 4) * ((3 / 4) * c + d)) :
    let t := q * (1 - mu)
    let p := mu + q * g * (1 - mu)
    let x := e - (1 - q * g) * (1 - mu)
    let det := (x - t * a) * (p - t * d) - t ^ 2 * b * c
    0 < x ∧ 0 < p ∧ 0 < det ∧ 1 ≤ p * ((x - t * a + t * c * h) / det) := by
  sorry

private lemma policy_bound (n : ℕ) (pg pc q gam fnew : ℝ)
    (a b c d : Fin n → ℝ) (hn : 1 ≤ n) (hp : 0 < pg) (hp1 : pg ≤ 1)
    (hm : 0 < pc) (hm1 : pc ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (he : 0 ≤ gam) (hf : 1 / 4 < fnew) (hf1 : fnew ≤ 1)
    (ha : admissible a b c d) :
    (1 - (1 - pg) ^ n) / (pc + (2 - pc) * (1 - (1 - pg) ^ n)) ≤
      availability n pg pc q gam fnew a b c d := by
  have hg := generation_mass n pg hn hp hp1
  have hab := aggregate_endpoints pg hp.le hp1 a b c d ha hg.1
  have hexp : 1 ≤ Real.exp gam := Real.one_le_exp he
  have hs := scalar_mass (1 - (1 - pg) ^ n) pc q (Real.exp gam) (fnew - 1 / 4)
    (aggregate pg a) (aggregate pg b) (aggregate pg c) (aggregate pg d)
    hg.2.1 hg.2.2 hm hm1 hq hq1 hexp (by linarith) (by linarith)
    hab.1 hab.2.1 hab.2.2.1 hab.2.2.2
  sorry

private lemma failing_value (n : ℕ) (pg pc gam fnew : ℝ)
    (hg : 0 < 1 - (1 - pg) ^ n) (hm : 0 < pc) :
    availability n pg pc 1 gam fnew 0 0 0 0 =
      (1 - (1 - pg) ^ n) / (pc + (2 - pc) * (1 - (1 - pg) ^ n)) := by
  sorry

theorem result : claim := by
  intro n hn pg pc gam fnew hp hp1 hm hm1 he hf hf1 a b c d ha q hq hq1
  have hg := generation_mass n pg hn hp hp1
  rw [failing_value n pg pc gam fnew hg.2.1 hm]
  exact policy_bound n pg pc q gam fnew a b c d hn hp hp1 hm hm1 hq hq1 he hf hf1 ha

end D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
