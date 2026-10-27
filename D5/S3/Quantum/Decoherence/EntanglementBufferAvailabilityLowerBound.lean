/- GID: D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The always-failing purification policy minimizes buffer availability. -/

import D5.S3.AnalyticClosure.BinomialLocalGaussian
import D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity

/-! Availability bound for the discrete-time entanglement-buffer formula. -/

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound

open D5.S3.AnalyticClosure.BinomialLocalGaussian (binomialMass)
open D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity (det_pos_of_dominant)

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
  let ta := q * (1 - pc) * (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) / x
  let tb := q * (1 - pc) * (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) / p
  let tc := q * (1 - pc) * (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) / x
  let td := q * (1 - pc) * (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) / p
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
    (∑ k : Fin n, binomialMass pg n (k.val + 1)) = 1 - (1 - pg) ^ n ∧
      0 < 1 - (1 - pg) ^ n ∧ 1 - (1 - pg) ^ n ≤ 1 := by
  have hb := add_pow pg (1 - pg) n
  rw [show pg + (1 - pg) = 1 by ring, one_pow, Finset.sum_range_succ'] at hb
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    one_mul] at hb
  have hs : (∑ k : Fin n, binomialMass pg n (k.val + 1)) =
      ∑ k ∈ Finset.range n, pg ^ (k + 1) * (1 - pg) ^ (n - (k + 1)) *
        (n.choose (k + 1) : ℝ) := by
    unfold binomialMass
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  refine ⟨by linarith, ?_, ?_⟩
  · have := pow_lt_one₀ (by linarith : 0 ≤ 1 - pg)
      (by linarith : 1 - pg < 1) (Nat.ne_zero_of_lt hn)
    linarith
  · have := pow_nonneg (by linarith : 0 ≤ 1 - pg) n
    linarith

private lemma aggregate_endpoints {n : ℕ} (pg : ℝ) (hp : 0 ≤ pg) (hp1 : pg ≤ 1)
    (a b c d : Fin n → ℝ) (ha : admissible a b c d)
    (hs : (∑ k : Fin n, binomialMass pg n (k.val + 1)) = 1 - (1 - pg) ^ n) :
    let g := 1 - (1 - pg) ^ n
    let aa := (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    let bb := (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    let cc := (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    let dd := (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    (0 ≤ dd ∧ dd ≤ g) ∧ (0 ≤ (3 / 4) * cc + dd ∧ (3 / 4) * cc + dd ≤ g) ∧
    (0 ≤ bb ∧ bb ≤ (3 / 4) * dd) ∧
    (0 ≤ (3 / 4) * aa + bb ∧ (3 / 4) * aa + bb ≤ (3 / 4) * ((3 / 4) * cc + dd)) := by
  have hw (k : Fin n) : 0 ≤ binomialMass pg n (k.val + 1) := by
    exact ProbabilityTheory.binomial_nonneg (n := n) (k := k.val + 1)
      (p := ⟨pg, hp, hp1⟩)
  have lin (u v : Fin n → ℝ) (r : ℝ) :
      (∑ k, (u k * r + v k) * binomialMass pg n (k.val + 1)) =
        (u ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * r +
          (v ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) := by
    simpa only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm r] using
      (add_dotProduct (r • u) v (fun k => binomialMass pg n (k.val + 1))).trans
        (congrArg (· + (v ⬝ᵥ fun k => binomialMass pg n (k.val + 1)))
          (smul_dotProduct r u (fun k => binomialMass pg n (k.val + 1))))
  have h (f : ℝ) (hf : 1 / 4 ≤ f) (hf1 : f ≤ 1) :
      (0 ≤ (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
          (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) ∧
        (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
          (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) ≤ 1 - (1 - pg) ^ n) ∧
      (0 ≤ (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
          (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) ∧
        (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
          (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) ≤
          (3 / 4) * ((c ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
            (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1)))) := by
    have h0 := Finset.sum_nonneg (s := Finset.univ)
      (fun k _ => mul_nonneg (ha k f hf hf1).1.1 (hw k))
    have h1 := Finset.sum_le_sum (s := Finset.univ)
      (fun k _ => mul_le_mul_of_nonneg_right (ha k f hf hf1).1.2 (hw k))
    have h2 := Finset.sum_nonneg (s := Finset.univ)
      (fun k _ => mul_nonneg (ha k f hf hf1).2.1 (hw k))
    have h3 := Finset.sum_le_sum (s := Finset.univ)
      (fun k _ => mul_le_mul_of_nonneg_right (ha k f hf hf1).2.2 (hw k))
    simp only [one_mul, lin, hs] at h0 h1 h2
    have hi : (∑ k, 3 / 4 * (c k * (f - 1 / 4) + d k) * binomialMass pg n (k.val + 1)) =
        3 / 4 * ((c ⬝ᵥ fun k => binomialMass pg n (k.val + 1)) * (f - 1 / 4) +
          (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1))) := by
      rw [← lin, Finset.mul_sum]
      simp only [mul_assoc]
    rw [lin, hi] at h3
    exact ⟨⟨h0, h1⟩, h2, h3⟩
  have h0 := h (1 / 4) (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) le_rfl
  dsimp only
  norm_num at h0 h1
  exact ⟨h0.1, by constructor <;> linarith [h1.1.1, h1.1.2],
    h0.2, by constructor <;> linarith [h1.2.1, h1.2.2]⟩

private lemma two_state_mass (u v w z ell mu h : ℝ)
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hmu : 0 < mu) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hl0 : ell ≤ u + w) (hl1 : ell ≤ v + z)
    (hc0 : u + w ≤ 1 - mu) (hc1 : v + z ≤ 1 - mu) :
    let det := (1 - u) * (1 - z) - v * w
    let num := (1 - z + w) * h + (v + 1 - u) * (1 - h)
    0 < det ∧ det ≤ (1 - ell) * num := by
  dsimp only
  have hz1 : 0 < 1 - z := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hd : 0 < (1 - u) * (1 - z) - v * w := by
    have hd := det_pos_of_dominant !![1 - u, -w; -v, 1 - z]
        (by intro i; fin_cases i <;> simp <;> linarith)
        (by intro i; fin_cases i <;>
            simp [Fin.sum_univ_two, Real.norm_eq_abs, abs_of_nonneg hv, abs_of_nonneg hw] <;>
            linarith)
    simpa [Matrix.det_fin_two, mul_comm] using hd
  have hy0 : 0 ≤ (1 - z) * h + v * (1 - h) :=
    add_nonneg (mul_nonneg hz1.le hh) (mul_nonneg hv (sub_nonneg.mpr hh1))
  have hy1 : 0 ≤ w * h + (1 - u) * (1 - h) :=
    add_nonneg (mul_nonneg hw hh) (mul_nonneg hu1.le (sub_nonneg.mpr hh1))
  refine ⟨hd, ?_⟩
  have h0 := mul_nonneg (sub_nonneg.mpr hl0) hy0
  have h1 := mul_nonneg (sub_nonneg.mpr hl1) hy1
  nlinarith only [h0, h1]

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
  dsimp only
  let t := q * (1 - mu)
  let ell := (1 - q * g) * (1 - mu)
  let p := mu + q * g * (1 - mu)
  let r := 1 / e
  let u := (ell + t * (a + 4 / 3 * b)) * r + t * (4 / 3 * b) * (1 - r)
  let v := t * (4 / 3 * b)
  let w := t * (d + 3 / 4 * c - a - 4 / 3 * b) * r +
    (ell + t * (d - 4 / 3 * b)) * (1 - r)
  let z := ell + t * (d - 4 / 3 * b)
  let det := (1 - u) * (1 - z) - v * w
  let num := (1 - z + w) * (4 / 3 * h) + (v + 1 - u) * (1 - 4 / 3 * h)
  have hep : 0 < e := by linarith
  have hr : 0 ≤ r := (div_pos zero_lt_one hep).le
  have hr1 : r ≤ 1 := (div_le_one hep).mpr he
  have ht : 0 ≤ t := mul_nonneg hq (sub_nonneg.mpr hm1)
  have hqg : q * g ≤ 1 := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hg1)]
  have hl : 0 ≤ ell := mul_nonneg (sub_nonneg.mpr hqg) (sub_nonneg.mpr hm1)
  have hp : 0 < p := by
    dsimp [p]
    exact add_pos_of_pos_of_nonneg hm (mul_nonneg (mul_nonneg hq hg.le)
      (sub_nonneg.mpr hm1))
  have hpell : p = 1 - ell := by dsimp [p, ell]; ring
  have htell : ell + t * g = 1 - mu := by dsimp [ell, t]; ring
  have ha1 : 0 ≤ d + 3 / 4 * c - a - 4 / 3 * b := by linarith [ha.2]
  have hb1 : 0 ≤ d - 4 / 3 * b := by linarith [hb.2]
  have hv : 0 ≤ v := mul_nonneg ht (mul_nonneg (by norm_num) hb.1)
  have hw : 0 ≤ w :=
    add_nonneg (mul_nonneg (mul_nonneg ht ha1) hr)
      (mul_nonneg (add_nonneg hl (mul_nonneg ht hb1)) (sub_nonneg.mpr hr1))
  have hm0 : 0 ≤ r * (3 / 4 * c + d) + (1 - r) * d :=
    add_nonneg (mul_nonneg hr hc.1) (mul_nonneg (sub_nonneg.mpr hr1) hd.1)
  have hm1' : r * (3 / 4 * c + d) + (1 - r) * d ≤ g := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hc.2),
      mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hd.2)]
  have hc0 : u + w = ell + t * (r * (3 / 4 * c + d) + (1 - r) * d) := by
    dsimp [u, w]; ring
  have hc1 : v + z = ell + t * d := by dsimp [v, z]; ring
  have hmasses := two_state_mass u v w z ell mu (4 / 3 * h) hv hw hm
    (mul_nonneg (by norm_num) hh) (by linarith only [hh1])
    (by rw [hc0]; exact le_add_of_nonneg_right (mul_nonneg ht hm0))
    (by rw [hc1]; exact le_add_of_nonneg_right (mul_nonneg ht hd.1))
    (by rw [hc0, ← htell]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm1' ht))
    (by rw [hc1, ← htell]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hd.2 ht))
  change 0 < det ∧ det ≤ (1 - ell) * num at hmasses
  have hid : e * det =
      (e - ell - t * a) * (p - t * d) - t ^ 2 * b * c := by
    rw [hpell]
    dsimp only [det, u, v, w, z, r]
    field_simp [hep.ne']
    ring
  have hin : e * num = e - ell - t * a + t * c * h := by
    dsimp only [num, u, v, w, z, r]
    field_simp [hep.ne']
    ring
  have hdpos : 0 < (e - ell - t * a) * (p - t * d) - t ^ 2 * b * c := by
    rw [← hid]
    exact mul_pos hep hmasses.1
  refine ⟨by change 0 < e - ell; linarith, hp, hdpos, ?_⟩
  have hbound : (e - ell - t * a) * (p - t * d) - t ^ 2 * b * c ≤
      p * (e - ell - t * a + t * c * h) := calc
    _ = e * det := hid.symm
    _ ≤ e * ((1 - ell) * num) := mul_le_mul_of_nonneg_left hmasses.2 hep.le
    _ = p * (e * num) := by rw [hpell, mul_left_comm e (1 - ell)]
    _ = _ := by rw [hin]
  change 1 ≤ p * ((e - ell - t * a + t * c * h) /
    ((e - ell - t * a) * (p - t * d) - t ^ 2 * b * c))
  rw [← mul_div_assoc, le_div_iff₀ hdpos, one_mul]
  exact hbound

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
    (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
    hg.2.1 hg.2.2 hm hm1 hq hq1 hexp (by linarith) (by linarith)
    hab.1 hab.2.1 hab.2.2.1 hab.2.2.2
  let g := 1 - (1 - pg) ^ n
  let t := q * (1 - pc)
  let p := pc + q * g * (1 - pc)
  let x := Real.exp gam - (1 - q + q * (1 - pg) ^ n) * (1 - pc)
  let aa := (a ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
  let bb := (b ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
  let cc := (c ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
  let dd := (d ⬝ᵥ fun k => binomialMass pg n (k.val + 1))
  let det := (x - t * aa) * (p - t * dd) - t ^ 2 * bb * cc
  let num := x - t * aa + t * cc * (fnew - 1 / 4)
  let s := num / det
  have hxeq : Real.exp gam - (1 - q * g) * (1 - pc) = x := by
    dsimp [g, x]; ring
  rw [hxeq] at hs
  change 0 < x ∧ 0 < p ∧ 0 < det ∧ 1 ≤ p * s at hs
  have hsp : 0 < s := by nlinarith only [hs.2.1, hs.2.2.2]
  have hdeltaeq : (1 - t * aa / x) * (1 - t * dd / p) -
      (t * bb / p) * (t * cc / x) = det / (x * p) := by
    dsimp only [det]
    field_simp (disch := first | exact hs.1.ne' | exact hs.2.1.ne' | norm_num)
  have hdelta : 0 < (1 - t * aa / x) * (1 - t * dd / p) -
      (t * bb / p) * (t * cc / x) := by
    rw [hdeltaeq]
    exact div_pos hs.2.2.1 (mul_pos hs.1 hs.2.1)
  have hocc : (1 - t * aa / x + t * cc / x * (fnew - 1 / 4)) /
      (((1 - t * aa / x) * (1 - t * dd / p) - (t * bb / p) * (t * cc / x)) * p) = s := by
    apply (div_eq_iff (mul_pos hdelta hs.2.1).ne').mpr
    rw [hdeltaeq]
    dsimp only [s, num]
    field_simp (disch := first | exact hs.1.ne' | exact hs.2.1.ne' | exact hs.2.2.1.ne' | norm_num)
  have hform : availability n pg pc q gam fnew a b c d = s / (1 / g + s) := by
    unfold availability
    change ((1 - t * aa / x + t * cc / x * (fnew - 1 / 4)) /
      (((1 - t * aa / x) * (1 - t * dd / p) - (t * bb / p) * (t * cc / x)) * p)) /
        (1 / g + (1 - t * aa / x + t * cc / x * (fnew - 1 / 4)) /
          (((1 - t * aa / x) * (1 - t * dd / p) - (t * bb / p) * (t * cc / x)) * p)) = _
    rw [hocc]
  have hpmax : p ≤ pc + (1 - pc) * g := by
    dsimp only [p]
    nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hq1) hg.2.1.le)
      (sub_nonneg.mpr hm1)]
  have hmass : 1 ≤ s * (pc + (1 - pc) * g) := by
    have ht := mul_le_mul_of_nonneg_right hpmax hsp.le
    nlinarith only [ht, hs.2.2.2]
  have hden : 0 < pc + (2 - pc) * g :=
    add_pos hm (mul_pos (by linarith only [hm1]) hg.2.1)
  rw [hform]
  apply (div_le_div_iff₀ hden (add_pos (div_pos zero_lt_one hg.2.1) hsp)).mpr
  have hid : g * (1 / g + s) = 1 + g * s := by
    rw [mul_add, mul_one_div, div_self hg.2.1.ne']
  rw [hid]
  nlinarith only [hmass]

private lemma failing_value (n : ℕ) (pg pc gam fnew : ℝ)
    (hg : 0 < 1 - (1 - pg) ^ n) (hm : 0 < pc) (hm1 : pc ≤ 1) :
    availability n pg pc 1 gam fnew 0 0 0 0 =
      (1 - (1 - pg) ^ n) / (pc + (2 - pc) * (1 - (1 - pg) ^ n)) := by
  let g := 1 - (1 - pg) ^ n
  let p := pc + g * (1 - pc)
  have hp : 0 < p := add_pos_of_pos_of_nonneg hm
    (mul_nonneg hg.le (sub_nonneg.mpr hm1))
  unfold availability dotProduct
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, zero_div,
    sub_zero, one_mul, mul_one, add_zero]
  change (1 / p) / (1 / g + 1 / p) = g / (pc + (2 - pc) * g)
  have hid : pc + (2 - pc) * g = g + p := by dsimp [p]; ring
  rw [hid]
  have hg0 : g ≠ 0 := hg.ne'
  have hgp : g + p ≠ 0 := (add_pos (show 0 < g from hg) hp).ne'
  field_simp (disch := first | exact hg0 | exact hp.ne' | exact hgp | norm_num)
  rw [add_comm p g, div_self hgp]

theorem result : claim := by
  intro n hn pg pc gam fnew hp hp1 hm hm1 he hf hf1 a b c d ha q hq hq1
  have hg := generation_mass n pg hn hp hp1
  rw [failing_value n pg pc gam fnew hg.2.1 hm hm1]
  exact policy_bound n pg pc q gam fnew a b c d hn hp hp1 hm hm1 hq hq1 he hf hf1 ha

end D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
