/- GID: D5/S3/Zeros/GRH/New/Curve/LiveSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/LiveSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.LiveSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/LiveSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Data.AdmissibleData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Divisibility of the chain of theta lifts at each prime (see
New.Columns.LocalStatement).

This file: Names for asked divisibility, gain, loss, short and served primes. Coupling count and
exponent of the jet divisibility theorem; weights of the data. The sum of p^{−e} over e ≥ 1,
e odd or p = d, is
(1/(p−1) − ρ_p)/ω_p for non-split p, ω_p = (1 − (p/d))/2, ρ_p = `nonsplitWeight`. -/

noncomputable section

namespace Data

variable {P} (D : Data P) (p : ℕ) (τ h)

/-- The ask at p: ((1 − (p/d))/2)·∑ (y/p^e − w(−p^e σ))⁺ over e ≥ 1 with e
odd or p = d, where w = `Data.nominalWeight`. -/
def localAsk (y : ℝ) σ := (1 - chiK P.d p) / 2 * ∑' e, ite (0 < e ∧ (Odd e ∨ p = P.d))
    (y / p ^ e - D.nominalWeight (D.placeOfInt (-p ^ e) * σ))⁺ 0

/-- The forced divisibility F(p) = ∑_σ ask_p(w(σ), σ), the sum over infinite places σ, with w =
`Data.nominalWeight`. -/
def forcedPart := ∑ σ, D.localAsk p (D.nominalWeight σ) σ

/-- The divisibility asked of the chain of lifts at p: gain(p) = m(∑_τ ask_p(a, τ) + k·F(p)), τ
over the tops; see `Data.localAsk`, `Data.forcedPart`. -/
def gain := D.m * (∑ τ ∈ D.tops, D.localAsk p D.a τ + D.k * D.forcedPart p)

/-- The natural number p satisfies p < x₁ and χ_K(p) ≠ 1; for prime p, this says that p is below
x₁ and inert or ramified in K. -/
abbrev IsSmallNonsplit := p < D.x₁ ∧ chiK P.d p ≠ 1

/-- p is short if p ≡ ±1 modulo m. -/
def IsShortPrime := D.m ∣ p - 1 ∨ D.m ∣ p + 1

/-- The unit of allowed loss at p: fa(log b)²/p, multiplied by m if p is short, that is, p ≡ ±1
modulo m. -/
def loss := D.f * D.logB ^ 2 * (D.a / p * ite (D.IsShortPrime p) D.m 1)

/-- The least natural number 𝔯 with m ≤ p^𝔯 (for p > 1). -/
def ceilLogM := p.clog D.m

/-- The natural number δ_p = 𝔯f(n_m + 𝔯), with 𝔯 = `Data.ceilLogM` p, f the number of infinite
places of E and n_m the last rank. -/
def deltaP := D.ceilLogM p * D.f * (D.n D.m + D.ceilLogM p)

/-- The natural number j_p = ⌈2mfa/p⌉, with f the number of infinite places of E. -/
def jetCeil := ⌈(D.m * (2 * D.f * D.a / p) : ℝ)⌉₊

/-- The order o₀ of the class modulo N₀ of the infinite place named by −p; for p prime to N₁,
the order of −p in (ℤ/N₀)^×. -/
def o₀ := orderOf (P.placeClass ⟨_, rfl⟩ (D.placeOfInt (-p)))

/-- p is served if (p|d) = −1, p is not short, and the order o₀ of −p modulo N₀ is odd and at most
𝔯 = `Data.ceilLogM` p; so −p^e ≡ 1 modulo N₀ for some odd e ≤ 𝔯. -/
def IsServed := chiK P.d p = -1 ∧ ¬D.IsShortPrime p ∧ Odd (D.o₀ p) ∧ D.o₀ p ≤ D.ceilLogM p

/-- A collision outside ev: e ≥ 1, e is odd or p = d, and both τ and its product with the place
named by −p^e are tops not in ev. -/
def IsCollision ev τ e := (0 < e ∧ (Odd e ∨ p = P.d)) ∧ τ ∈ D.tops \ ev ∧
  D.placeOfInt (-p ^ e) * τ ∈ D.tops \ ev

/-- The sum of a/p^e over all pairs (τ, e) that are collisions outside ev (`Data.IsCollision`). -/
def collisionSum ev := ∑ τ, ∑' e, ite (D.IsCollision p ev τ e) (D.a / p ^ e : ℝ) 0

/-- The number min(t_σ/p^e, r_σ' + t_σ') + r_σ/p^e + min(B_σ/p^e, B_σ'): t counts columns of
height one (0 on ev), r the other columns of height < n', B their boxes. -/
def _root_.couplingCount {Φ} (p : ℕ) (κ : Φ → ℕ → ℕ) n' (ev : Finset Φ) σ σ' e :=
  let t σ := ∑ h ∈ .range n', ite (h = 1 ∧ σ ∉ ev) (κ σ h) 0
  let r σ := ∑ h ∈ .range n', ite (h = 1) 0 (κ σ h)
  let B σ := ∑ h ∈ .range n', h * ite (h = 1) 0 (κ σ h)
  (t σ / p ^ e : ℝ) ⊓ (r σ' + t σ') + r σ / p ^ e + (B σ / p ^ e : ℝ) ⊓ B σ'

/-- The number of columns of height h at τ: a for h = 1 at tops, w_1(τ) − ⌊(k+t+1)/2⌋ for h = k,
𝗁 − (t+1) for h > k, h ≡ k mod t+1, else 0. -/
def κ := ite (h = 1) (ite (τ ∈ D.tops) D.a 0) (ite (h = D.k) (D.w 1 τ - (D.k + D.t + 1) / 2)
    (ite (D.k < h ∧ D.t + 1 ∣ h - D.k) (D.h - (D.t + 1)) 0))

lemma κ_le a : ite (h = 1) a (D.κ τ h) ≤ ite (h = 1) a 0 + ite (h = D.k) (D.w 1 τ) 0 + D.h := by
  grind [κ]

/-- The determinant exponent of the weight at stage j and place τ: 0 for j = 0, else ⌊𝗇_{j−1}/2⌋
− w_j(τ). -/
def lastEntry j τ := ite (j = 0) 0 (D.n (j - 1) / 2 - D.w j τ : ℤ)

/-- The number h₂ − ⌊(t+1)/2⌋ if h ≥ k and h ≡ k mod t+1, else 0: the columns of height h that
keep their height under branching to Y_m. -/
def keptColumns := ite (D.k ≤ h ∧ D.t + 1 ∣ h - D.k) D.reducedHalfGap 0

/-- Columns of height h at τ of the weight on Y_m: c(h) + (κ_τ(h+1) − c(h+1)), c = `keptColumns`. -/
def columnsY := D.keptColumns h + (D.κ τ (h + 1) - D.keptColumns (h + 1))

/-- If (p/d) ≠ 1, the sum of p^{−e} over the e ≥ 1 with e odd or p = d is (1/(p − 1) − ρ_p)/ω_p,
where ω_p = (1 − (p/d))/2 and ρ_p is `nonsplitWeight`. -/
lemma _root_.hasSum_live_inv_pow {d p : ℕ} [Fact d.Prime] [Fact p.Prime] (h : chiK d p ≠ 1) c :
    HasSum (fun e ↦ ite (0 < e ∧ (Odd e ∨ p = d)) (c / p ^ e : ℝ) 0)
    (2 / (1 - chiK d p) * c * (1 / (p - 1) - nonsplitWeight d p)) := by
    convert! (((@hasSum_geometric_of_abs_lt_one p⁻¹ _).sub (@hasSum_geometric_of_abs_lt_one
  (chiK d p / p) _)).div_const 2).mul_left _ using 2 <;> obtain ⟨⟨⟨⟨⟩⟩⟩ | _⟩ := chiK_cases d p,
  @Padic.norm_p_lt_one p <;>
  simp_all [nonsplitWeight, neg_one_pow_eq_ite, ↓div_pow, zero_pow_eq] <;> grind [NeZero.natCast_ne]
