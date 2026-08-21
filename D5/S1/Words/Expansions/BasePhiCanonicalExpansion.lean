/- GID: D5/S1/Words/Expansions/BasePhiCanonicalExpansion
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiCanonicalExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical finite two-sided base-phi expansions exist uniquely for natural numbers. -/

import D5.S1.Words.Expansions.BasePhiCarryTransducer
import D5.S1.Words.Expansions.BasePhiNegativeBridge
import D5.S1.Digit.Carry.Successor
import D5.S1.Scale.Fibonacci

namespace D5.S1.Words.Expansions.BasePhiCanonicalExpansion

noncomputable section

open D5.S0.Carrier
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiNegativeBridge
open D5.S1.Words.Expansions.BasePhiNegative
open Real

local instance (priority := low) (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Translate every occupied exponent by the same integral offset. -/
noncomputable def shiftDigits (K : Int) (digits : Int →₀ Nat) : Int →₀ Nat :=
  Finsupp.equivCongrLeft (Equiv.addRight K) digits

@[simp] theorem shiftDigits_apply (K i : Int) (digits : Int →₀ Nat) :
    shiftDigits K digits i = digits (i - K) := by
  rfl

@[simp] theorem shiftDigits_zero (K : Int) :
    shiftDigits K (0 : Int →₀ Nat) = 0 := by
  ext i
  simp

theorem shiftDigits_add (K : Int) (digits₁ digits₂ : Int →₀ Nat) :
    shiftDigits K (digits₁ + digits₂) =
      shiftDigits K digits₁ + shiftDigits K digits₂ := by
  ext i
  simp

theorem shiftDigits_single (K i : Int) (coefficient : Nat) :
    shiftDigits K (Finsupp.single i coefficient) =
      Finsupp.single (i + K) coefficient := by
  rw [shiftDigits, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_single]
  rfl

theorem shiftDigits_injective (K : Int) :
    Function.Injective (shiftDigits K) :=
  (Finsupp.equivCongrLeft (Equiv.addRight K)).injective

private theorem basePhiValue_eq_sum (digits : Int →₀ Nat) :
    basePhiValue digits = digits.sum (fun i coefficient =>
      (coefficient : GoldenInt) *
        (((phiUnit ^ i : GoldenIntˣ) : GoldenInt))) := by
  rfl

private theorem basePhiValue_add (digits₁ digits₂ : Int →₀ Nat) :
    basePhiValue (digits₁ + digits₂) =
      basePhiValue digits₁ + basePhiValue digits₂ := by
  classical
  rw [basePhiValue_eq_sum, basePhiValue_eq_sum, basePhiValue_eq_sum]
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i coefficient₁ coefficient₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem basePhiValue_single (i : Int) (coefficient : Nat) :
    basePhiValue (Finsupp.single i coefficient) =
      (coefficient : GoldenInt) *
        (((phiUnit ^ i : GoldenIntˣ) : GoldenInt)) := by
  classical
  rw [basePhiValue_eq_sum, Finsupp.sum_single_index]
  simp

/-- Translating exponents multiplies the represented value by the matching golden unit. -/
theorem shiftDigits_eval (K : Int) (digits : Int →₀ Nat) :
    basePhiValue (shiftDigits K digits) =
      (((phiUnit ^ K : GoldenIntˣ) : GoldenInt)) * basePhiValue digits := by
  induction digits using Finsupp.induction with
  | zero => simp [basePhiValue]
  | single_add i coefficient digits _ _ inductionHypothesis =>
      rw [shiftDigits_add, shiftDigits_single, basePhiValue_add,
        basePhiValue_single, basePhiValue_add, basePhiValue_single,
        inductionHypothesis, add_comm i K, zpow_add]
      simp only [Units.val_mul]
      ring

theorem shiftDigits_binary (K : Int) {digits : Int →₀ Nat}
    (binary : ∀ i : Int, digits i ≤ 1) :
    ∀ i : Int, shiftDigits K digits i ≤ 1 := by
  intro i
  rw [shiftDigits_apply]
  exact binary (i - K)

theorem shiftDigits_canonical (K : Int) {digits : Int →₀ Nat}
    (canonical : ∀ i : Int, digits i = 1 → digits (i + 1) = 0) :
    ∀ i : Int, shiftDigits K digits i = 1 →
      shiftDigits K digits (i + 1) = 0 := by
  intro i hi
  rw [shiftDigits_apply] at hi ⊢
  have := canonical (i - K) hi
  rw [show i + 1 - K = (i - K) + 1 by omega]
  exact this

/-- The canonical embedding of nonnegative exponents into integral exponents. -/
def intOfNatEmbedding : Nat ↪ Int :=
  ⟨fun n => (n : Int), Int.ofNat_injective⟩

/-- Lift a finite nonnegative digit word to integral exponents. -/
noncomputable def natLift (digits : RawDigits) : Int →₀ Nat :=
  Finsupp.embDomain intOfNatEmbedding digits

/-- Read the nonnegative part of an integral-exponent digit word. -/
noncomputable def natView (digits : Int →₀ Nat) : RawDigits :=
  Finsupp.comapDomain intOfNatEmbedding digits
    intOfNatEmbedding.injective.injOn

@[simp] theorem natLift_apply (digits : RawDigits) (n : Nat) :
    natLift digits (n : Int) = digits n := by
  exact Finsupp.embDomain_apply_self intOfNatEmbedding digits n

@[simp] theorem natView_apply (digits : Int →₀ Nat) (n : Nat) :
    natView digits n = digits (n : Int) := by
  rfl

@[simp] theorem natView_natLift (digits : RawDigits) :
    natView (natLift digits) = digits := by
  exact Finsupp.comapDomain_embDomain intOfNatEmbedding digits

theorem natLift_add (digits₁ digits₂ : RawDigits) :
    natLift (digits₁ + digits₂) = natLift digits₁ + natLift digits₂ := by
  rw [natLift, natLift, natLift, Finsupp.embDomain_eq_mapDomain,
    Finsupp.mapDomain_add, ← Finsupp.embDomain_eq_mapDomain,
    ← Finsupp.embDomain_eq_mapDomain]

theorem natLift_single (i coefficient : Nat) :
    natLift (Finsupp.single i coefficient) =
      Finsupp.single (i : Int) coefficient := by
  exact Finsupp.embDomain_single intOfNatEmbedding i coefficient

theorem natLift_natView_of_nonnegative_support {digits : Int →₀ Nat}
    (nonnegative : ∀ i ∈ digits.support, 0 ≤ i) :
    natLift (natView digits) = digits := by
  apply Finsupp.embDomain_comapDomain
  intro i hi
  refine ⟨i.toNat, ?_⟩
  exact Int.toNat_of_nonneg (nonnegative i hi)

/-- One offset makes both finite supports nonnegative. -/
theorem commonShift_natView (digits₁ digits₂ : Int →₀ Nat) :
    ∃ (K : Nat) (view₁ view₂ : RawDigits),
      natLift view₁ = shiftDigits (K : Int) digits₁ ∧
      natLift view₂ = shiftDigits (K : Int) digits₂ := by
  let K := digits₁.support.sup (fun i => (-i).toNat) +
    digits₂.support.sup (fun i => (-i).toNat)
  have lower₁ : ∀ i ∈ digits₁.support, 0 ≤ i + (K : Int) := by
    intro i hi
    by_cases hi0 : 0 ≤ i
    · positivity
    · have hsup : (-i).toNat ≤ digits₁.support.sup (fun j => (-j).toNat) :=
        Finset.le_sup (f := fun j => (-j).toNat) hi
      have hK : (-i).toNat ≤ K := by
        dsimp [K]
        omega
      have hcast : ((-i).toNat : Int) = -i :=
        Int.toNat_of_nonneg (by omega)
      have hKcast : ((-i).toNat : Int) ≤ (K : Int) := by
        exact_mod_cast hK
      omega
  have lower₂ : ∀ i ∈ digits₂.support, 0 ≤ i + (K : Int) := by
    intro i hi
    by_cases hi0 : 0 ≤ i
    · positivity
    · have hsup : (-i).toNat ≤ digits₂.support.sup (fun j => (-j).toNat) :=
        Finset.le_sup (f := fun j => (-j).toNat) hi
      have hK : (-i).toNat ≤ K := by
        dsimp [K]
        omega
      have hcast : ((-i).toNat : Int) = -i :=
        Int.toNat_of_nonneg (by omega)
      have hKcast : ((-i).toNat : Int) ≤ (K : Int) := by
        exact_mod_cast hK
      omega
  have shifted₁ : ∀ i ∈ (shiftDigits (K : Int) digits₁).support, 0 ≤ i := by
    intro i hi
    have hsource : i - (K : Int) ∈ digits₁.support := by
      rw [Finsupp.mem_support_iff] at hi ⊢
      simpa using hi
    have := lower₁ (i - (K : Int)) hsource
    simpa [sub_add_cancel] using this
  have shifted₂ : ∀ i ∈ (shiftDigits (K : Int) digits₂).support, 0 ≤ i := by
    intro i hi
    have hsource : i - (K : Int) ∈ digits₂.support := by
      rw [Finsupp.mem_support_iff] at hi ⊢
      simpa using hi
    have := lower₂ (i - (K : Int)) hsource
    simpa [sub_add_cancel] using this
  refine ⟨K, natView (shiftDigits (K : Int) digits₁),
    natView (shiftDigits (K : Int) digits₂), ?_, ?_⟩
  · exact natLift_natView_of_nonnegative_support shifted₁
  · exact natLift_natView_of_nonnegative_support shifted₂

/-- The additive Fibonacci readout `a + b phi ↦ a + 2b`. -/
def goldenReadout : GoldenInt →+ Int where
  toFun x := x.a + 2 * x.b
  map_zero' := by simp
  map_add' x y := by simp; ring

@[simp] theorem goldenReadout_apply (x : GoldenInt) :
    goldenReadout x = x.a + 2 * x.b := rfl

/-- On nonnegative golden powers, the additive readout is the shifted Fibonacci weight. -/
theorem goldenReadout_phiPow : ∀ n : Nat,
    goldenReadout (phi ^ n) = (Nat.fib (n + 2) : Int)
  | 0 => by norm_num [goldenReadout]
  | n + 1 => by
      rw [golden_phi_pow_eq_fib_pair]
      change (Nat.fib n : Int) + 2 * (Nat.fib (n + 1) : Int) =
        (Nat.fib (n + 1 + 2) : Int)
      rw [show n + 1 + 2 = (n + 1) + 2 by omega,
        Nat.fib_add_two, Nat.fib_add_two]
      push_cast
      ring

private theorem goldenReadout_nat_mul (coefficient : Nat) (x : GoldenInt) :
    goldenReadout ((coefficient : GoldenInt) * x) =
      (coefficient : Int) * goldenReadout x := by
  simp only [goldenReadout_apply, a_mul, b_mul, a_natCast, b_natCast]
  ring

/-- The readout of a nonnegative digit word is its exact Fibonacci value. -/
theorem goldenReadout_natDigits (digits : RawDigits) :
    goldenReadout (basePhiValue (natLift digits)) = (rawValue digits : Int) := by
  induction digits using Finsupp.induction with
  | zero => simp [natLift, basePhiValue, rawValue]
  | single_add i coefficient digits _ _ inductionHypothesis =>
      rw [natLift_add, natLift_single, basePhiValue_add, basePhiValue_single,
        map_add, goldenReadout_nat_mul]
      have power : (((phiUnit ^ (i : Int) : GoldenIntˣ) : GoldenInt)) = phi ^ i := by
        simp
      rw [power, goldenReadout_phiPow, inductionHypothesis,
        rawValue_add, rawValue_single]
      simp only [D5.S0.Conventions.wValue]
      push_cast
      ring

theorem canonicalRaw_natView {digits : Int →₀ Nat}
    (binary : ∀ i : Int, digits i ≤ 1)
    (canonical : ∀ i : Int, digits i = 1 → digits (i + 1) = 0) :
    CanonicalRaw (natView digits) := by
  constructor
  · intro i
    rw [natView_apply]
    exact binary (i : Int)
  · intro i hi
    rw [natView_apply] at hi ⊢
    simpa using canonical (i : Int) hi

/-- Canonical nonnegative base-phi words are injective, independently of existence. -/
theorem nonnegative_basePhi_injective {digits₁ digits₂ : RawDigits}
    (canonical₁ : CanonicalRaw digits₁) (canonical₂ : CanonicalRaw digits₂)
    (value : basePhiValue (natLift digits₁) =
      basePhiValue (natLift digits₂)) :
    digits₁ = digits₂ := by
  have readout := congrArg goldenReadout value
  rw [goldenReadout_natDigits, goldenReadout_natDigits] at readout
  apply canonicalRaw_unique canonical₁ canonical₂
  exact_mod_cast readout

/-- Canonical finite two-sided base-phi words are injective. -/
theorem bilateral_basePhi_injective {digits₁ digits₂ : Int →₀ Nat}
    (binary₁ : ∀ i : Int, digits₁ i ≤ 1)
    (canonical₁ : ∀ i : Int, digits₁ i = 1 → digits₁ (i + 1) = 0)
    (binary₂ : ∀ i : Int, digits₂ i ≤ 1)
    (canonical₂ : ∀ i : Int, digits₂ i = 1 → digits₂ (i + 1) = 0)
    (value : basePhiValue digits₁ = basePhiValue digits₂) :
    digits₁ = digits₂ := by
  obtain ⟨K, view₁, view₂, lift₁, lift₂⟩ := commonShift_natView digits₁ digits₂
  have shiftedValue :
      basePhiValue (shiftDigits (K : Int) digits₁) =
        basePhiValue (shiftDigits (K : Int) digits₂) := by
    rw [shiftDigits_eval, shiftDigits_eval, value]
  have viewValue : basePhiValue (natLift view₁) = basePhiValue (natLift view₂) := by
    rw [lift₁, lift₂]
    exact shiftedValue
  have viewEq : view₁ = view₂ := nonnegative_basePhi_injective
    (by
      have : view₁ = natView (shiftDigits (K : Int) digits₁) := by
        rw [← lift₁, natView_natLift]
      rw [this]
      exact canonicalRaw_natView
        (shiftDigits_binary (K : Int) binary₁)
        (shiftDigits_canonical (K : Int) canonical₁))
    (by
      have : view₂ = natView (shiftDigits (K : Int) digits₂) := by
        rw [← lift₂, natView_natLift]
      rw [this]
      exact canonicalRaw_natView
        (shiftDigits_binary (K : Int) binary₂)
        (shiftDigits_canonical (K : Int) canonical₂))
    viewValue
  apply shiftDigits_injective (K : Int)
  rw [← lift₁, ← lift₂, viewEq]

/-- At most one canonical two-sided digit word has any prescribed golden value. -/
theorem atMostOne_canonicalExpansion (x : GoldenInt) :
    Set.Subsingleton {digits : Int →₀ Nat |
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = x} := by
  intro digits₁ member₁ digits₂ member₂
  exact bilateral_basePhi_injective
    member₁.1 member₁.2.1 member₂.1 member₂.2.1
    (member₁.2.2.trans member₂.2.2.symm)

private theorem embedding_conj_phi_pow (K : Nat) :
    embedding (conj (phi ^ K)) = goldenConj ^ K := by
  rw [show conj (phi ^ K) = (conj phi) ^ K by
    exact conjEquiv.map_pow phi K, conj_phi]
  rw [map_pow]
  rw [map_sub, map_one, embedding_phi, Real.one_sub_goldenConj]

private theorem embedding_conj_nat_mul_phi_pow (N K : Nat) :
    embedding (conj ((N : GoldenInt) * phi ^ K)) =
      (N : ℝ) * goldenConj ^ K := by
  rw [conj_mul, map_mul, embedding_conj_phi_pow]
  simp

private theorem goldenConj_lt_neg_half : goldenConj < -(1 / 2 : ℝ) := by
  have hneg : goldenConj < 0 := Real.goldenConj_neg
  have hsq : goldenConj ^ 2 = goldenConj + 1 := Real.goldenConj_sq
  nlinarith [sq_nonneg (goldenConj + (1 / 2 : ℝ))]

private theorem goldenConj_fourth_window :
    0 ≤ goldenConj ^ 4 ∧ goldenConj ^ 4 < (1 / 4 : ℝ) := by
  have hlow : -1 < goldenConj := neg_one_lt_goldenConj
  have hhalf : goldenConj < -(1 / 2 : ℝ) := goldenConj_lt_neg_half
  have hsq : goldenConj ^ 2 = goldenConj + 1 := Real.goldenConj_sq
  constructor
  · positivity
  · nlinarith [sq_nonneg (goldenConj + 1)]

private theorem nat_succ_le_four_pow : ∀ N : Nat, N + 1 ≤ 4 ^ N
  | 0 => by simp
  | N + 1 => by
      calc
        N + 1 + 1 ≤ 4 * (N + 1) := by omega
        _ ≤ 4 * 4 ^ N := Nat.mul_le_mul_left 4 (nat_succ_le_four_pow N)
        _ = 4 ^ (N + 1) := by simp [pow_succ, Nat.mul_comm]

private theorem nat_mul_quarter_pow_lt (N : Nat) :
    (N : ℝ) * (1 / 4 : ℝ) ^ (N + 1) < 1 / 4 := by
  cases N with
  | zero => norm_num
  | succ N =>
      have hN : N + 1 ≤ 4 ^ N := nat_succ_le_four_pow N
      have hN' : ((N + 1 : Nat) : ℝ) ≤ (4 : ℝ) ^ N := by exact_mod_cast hN
      have hpow : (1 / 4 : ℝ) ^ (N + 2) < (1 / 4 : ℝ) ^ (N + 1) := by
        rw [pow_succ]
        have h := mul_lt_mul_of_pos_left
          (show (1 / 4 : ℝ) < 1 by norm_num)
          (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) (N + 1))
        simpa [mul_comm] using h
      calc
        ((N + 1 : Nat) : ℝ) * (1 / 4 : ℝ) ^ (N + 2) ≤
            (4 : ℝ) ^ N * (1 / 4 : ℝ) ^ (N + 2) := by
              exact mul_le_mul_of_nonneg_right hN' (by positivity)
        _ < (4 : ℝ) ^ N * (1 / 4 : ℝ) ^ (N + 1) := by
              exact mul_lt_mul_of_pos_left hpow (by positivity)
        _ = 1 / 4 := by
              rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
                inv_pow, pow_succ]
              field_simp

private theorem goldenConj_shift_small (N : Nat) :
    0 ≤ (N : ℝ) * goldenConj ^ (4 * (N + 1)) ∧
      (N : ℝ) * goldenConj ^ (4 * (N + 1)) < 1 / 4 := by
  have hr := goldenConj_fourth_window
  have hpow : goldenConj ^ (4 * (N + 1)) =
      (goldenConj ^ 4) ^ (N + 1) := by rw [pow_mul]
  rw [hpow]
  constructor
  · positivity
  · have hp : (goldenConj ^ 4) ^ (N + 1) < (1 / 4 : ℝ) ^ (N + 1) := by
      apply pow_lt_pow_left₀ hr.2 (by positivity)
      omega
    have hN : (N : ℝ) ≤ (4 : ℝ) ^ N := by
      have := nat_succ_le_four_pow N
      exact_mod_cast (Nat.le_trans (Nat.le_succ N) this)
    calc
      (N : ℝ) * (goldenConj ^ 4) ^ (N + 1) ≤
          (4 : ℝ) ^ N * (goldenConj ^ 4) ^ (N + 1) := by
            exact mul_le_mul_of_nonneg_right hN (by positivity)
      _ < (4 : ℝ) ^ N * (1 / 4 : ℝ) ^ (N + 1) := by
            exact mul_lt_mul_of_pos_left hp (by positivity)
      _ = 1 / 4 := by
            rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
              inv_pow]
            field_simp
            rw [pow_succ]

private theorem betaGolden_high_shift (N : Nat) :
    betaGolden (N * Nat.fib (4 * (N + 1))) =
      (N : GoldenInt) * phi ^ (4 * (N + 1)) := by
  let K : Nat := 4 * (N + 1)
  let v : Nat := N * Nat.fib K
  have hb : (betaGolden v).b = ((N : GoldenInt) * phi ^ K).b := by
    rw [betaGolden_b, b_mul, a_natCast, b_natCast, phi_pow_b]
    dsimp [v]
    ring
  let delta : GoldenInt := betaGolden v - (N : GoldenInt) * phi ^ K
  have hdelta_b : delta.b = 0 := by
    dsimp [delta]
    rw [sub_eq_add_neg, b_add, b_neg, hb]
    ring
  have hdelta_conj : conj delta = delta := by
    apply GoldenInt.ext
    · simp [conj, hdelta_b]
    · simp [conj, hdelta_b]
  have hreal : (delta.a : ℝ) =
      betaContraction v - (N : ℝ) * goldenConj ^ K := by
    calc
      (delta.a : ℝ) = embedding delta := by
        simp [embedding_apply, hdelta_b]
      _ = embedding (conj delta) := by rw [hdelta_conj]
      _ = embedding (conj (betaGolden v)) -
          embedding (conj ((N : GoldenInt) * phi ^ K)) := by
        rw [show conj delta =
            conj (betaGolden v) - conj ((N : GoldenInt) * phi ^ K) by
              dsimp [delta]
              exact conjEquiv.map_sub _ _]
        rw [map_sub]
      _ = betaContraction v - (N : ℝ) * goldenConj ^ K := by
        rw [show betaContraction v = embedding (conj (betaGolden v)) by rfl,
          embedding_conj_nat_mul_phi_pow]
  have hsmall : 0 ≤ (N : ℝ) * goldenConj ^ K ∧
      (N : ℝ) * goldenConj ^ K < 1 / 4 := by
    dsimp [K]
    exact goldenConj_shift_small N
  have hwindow := betaContraction_mem_window v
  have hlower : (-1 : ℝ) < -goldenConj ^ 2 - 1 / 4 := by
    have hneg : goldenConj < 0 := Real.goldenConj_neg
    have hlow : -1 < goldenConj := neg_one_lt_goldenConj
    nlinarith [Real.goldenConj_sq, sq_nonneg (goldenConj + 1)]
  have ha_lo : (-1 : ℝ) < delta.a := by
    rw [hreal]
    nlinarith [hwindow.1, hsmall.2]
  have ha_hi : (delta.a : ℝ) < 1 := by
    rw [hreal]
    have hneg : goldenConj < 0 := Real.goldenConj_neg
    have hlow : -1 < goldenConj := neg_one_lt_goldenConj
    nlinarith [hwindow.2, hsmall.1]
  have ha_zero : delta.a = 0 := by
    have hazi : (-1 : ℤ) < delta.a := by exact_mod_cast ha_lo
    have hazi' : delta.a < (1 : ℤ) := by exact_mod_cast ha_hi
    omega
  have : delta = 0 := by
    apply GoldenInt.ext
    · exact_mod_cast ha_zero
    · exact hdelta_b
  exact sub_eq_zero.mp this

noncomputable def rawPhiLift (digits : RawDigits) : Int →₀ Nat :=
  shiftDigits 2 (natLift digits)

private theorem betaDigits_add_local (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

private theorem betaDigits_single_local (i coefficient : Nat) :
    betaDigits (Finsupp.single i coefficient) =
      (coefficient : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

private theorem phiUnit_natPower : ∀ n : Nat,
    (((phiUnit ^ (n : Int) : GoldenIntˣ) : GoldenInt)) = phi ^ n
  | 0 => by simp
  | n + 1 => by
      rw [zpow_natCast]
      simp [coe_phiUnit]

private theorem rawPhiLift_value (digits : RawDigits) :
    basePhiValue (rawPhiLift digits) = betaDigits digits := by
  induction digits using Finsupp.induction with
  | zero => simp [rawPhiLift, betaDigits, natLift, basePhiValue]
  | single_add i coefficient digits _ _ inductionHypothesis =>
      have ih' : basePhiValue (shiftDigits 2 (natLift digits)) = betaDigits digits := by
        simpa [rawPhiLift] using inductionHypothesis
      rw [rawPhiLift, natLift_add, natLift_single, shiftDigits_add, basePhiValue_add,
        shiftDigits_single, basePhiValue_single, ih',
        betaDigits_add_local, betaDigits_single_local]
      have power :
          (((phiUnit ^ ((i : Int) + 2) : GoldenIntˣ) : GoldenInt)) =
            phi ^ (i + 2) := by
        rw [show (i : Int) + 2 = ((i + 2 : Nat) : Int) by omega]
        exact phiUnit_natPower (i + 2)
      rw [power]

private theorem natLift_zero_of_neg (digits : RawDigits) {i : Int}
    (hi : i < 0) : natLift digits i = 0 := by
  rw [natLift, Finsupp.embDomain_apply]
  split
  · rename_i h
    obtain ⟨n, hn⟩ := h
    have hnonneg : (0 : Int) ≤ intOfNatEmbedding n := by
      change (0 : Int) ≤ (n : Int)
      exact_mod_cast Nat.zero_le n
    exfalso
    omega
  · rfl

private theorem natLift_binary {digits : RawDigits}
    (binary : ∀ i, digits i ≤ 1) :
    ∀ i : Int, natLift digits i ≤ 1 := by
  intro i
  by_cases hi : 0 ≤ i
  · have hindex : i = (i.toNat : Int) := (Int.toNat_of_nonneg hi).symm
    rw [hindex, natLift_apply]
    exact binary i.toNat
  · have hzero : natLift digits i = 0 := by
      exact natLift_zero_of_neg digits (lt_of_not_ge hi)
    rw [hzero]
    omega

private theorem natLift_canonical {digits : RawDigits}
    (canonical : CanonicalRaw digits) :
    ∀ i : Int, natLift digits i = 1 → natLift digits (i + 1) = 0 := by
  intro i hi
  by_cases hnonneg : 0 ≤ i
  · have hindex : i = (i.toNat : Int) := (Int.toNat_of_nonneg hnonneg).symm
    have hcanon := canonical.2 i.toNat
    rw [hindex, natLift_apply] at hi
    rw [show i + 1 = ((i.toNat + 1 : Nat) : Int) by
      rw [hindex]
      simp, natLift_apply]
    exact hcanon hi
  · have hzero : natLift digits i = 0 := by
      exact natLift_zero_of_neg digits (lt_of_not_ge hnonneg)
    omega

private theorem rawPhiLift_binary {digits : RawDigits}
    (binary : ∀ i, digits i ≤ 1) :
    ∀ i : Int, rawPhiLift digits i ≤ 1 := by
  exact shiftDigits_binary 2 (natLift_binary binary)

private theorem rawPhiLift_canonical {digits : RawDigits}
    (canonical : CanonicalRaw digits) :
    ∀ i : Int, rawPhiLift digits i = 1 → rawPhiLift digits (i + 1) = 0 := by
  exact shiftDigits_canonical 2 (natLift_canonical canonical)

private theorem unit_shift_cancel (N K : Nat) :
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) *
        ((N : GoldenInt) * phi ^ K) = (N : GoldenInt) := by
  have hunit :
      (phiUnit ^ (-(K : Int)) : GoldenIntˣ) *
          (phiUnit ^ (K : Int) : GoldenIntˣ) = 1 := by
    rw [← zpow_add]
    simp
  rw [← phiUnit_natPower K]
  calc
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) *
          ((N : GoldenInt) *
            (((phiUnit ^ (K : Int) : GoldenIntˣ) : GoldenInt))) =
        (N : GoldenInt) *
          (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) *
            (phiUnit ^ (K : Int) : GoldenIntˣ) : GoldenIntˣ)) := by
              simp only [Units.val_mul]
              ring
    _ = (N : GoldenInt) := by rw [hunit]; simp

noncomputable def constructedDigits (N : Nat) : Int →₀ Nat :=
  let K : Nat := 4 * (N + 1)
  shiftDigits (-(K : Int))
    (rawPhiLift (toRaw (Z (N * Nat.fib K))))

private theorem constructedDigits_binary (N : Nat) :
    ∀ i : Int, constructedDigits N i ≤ 1 := by
  intro i
  dsimp [constructedDigits]
  apply shiftDigits_binary
  exact rawPhiLift_binary (canonicalRaw_toRaw (Z _)).1

private theorem constructedDigits_canonical (N : Nat) :
    ∀ i : Int, constructedDigits N i = 1 →
      constructedDigits N (i + 1) = 0 := by
  intro i hi
  dsimp [constructedDigits] at hi ⊢
  exact shiftDigits_canonical (-(4 * (N + 1) : Int))
    (rawPhiLift_canonical (canonicalRaw_toRaw (Z _))) i hi

private theorem constructedDigits_value (N : Nat) :
    basePhiValue (constructedDigits N) = (N : GoldenInt) := by
  let K : Nat := 4 * (N + 1)
  let v : Nat := N * Nat.fib K
  dsimp [constructedDigits, K, v]
  rw [shiftDigits_eval, rawPhiLift_value]
  change (((phiUnit ^ (-(K : Int) : Int) : GoldenIntˣ) : GoldenInt)) *
      betaGolden v = (N : GoldenInt)
  rw [betaGolden_high_shift]
  exact unit_shift_cancel N K

theorem basePhiExpansion_exists (N : Nat) :
    ∃ digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : GoldenInt) := by
  refine ⟨constructedDigits N, constructedDigits_binary N,
    constructedDigits_canonical N, constructedDigits_value N⟩

theorem basePhiExpansion_existsUnique :
    ∀ N : Nat, ∃! digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : GoldenInt) := by
  intro N
  obtain ⟨digits, binary, canonical, value⟩ := basePhiExpansion_exists N
  refine ⟨digits, ⟨binary, canonical, value⟩, ?_⟩
  intro other otherSpec
  exact bilateral_basePhi_injective
    otherSpec.1 otherSpec.2.1 binary canonical
    (otherSpec.2.2.trans value.symm)

theorem canonical_two_sided_digits_unique :
    ∀ N : Nat, ∃! digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : GoldenInt) :=
  basePhiExpansion_existsUnique

theorem canonical_base_phi_digits_exists_unique :
    ∀ N : Nat, ∃! digits : Int →₀ Nat,
      (∀ i : Int, digits i ≤ 1) ∧
      (∀ i : Int, digits i = 1 → digits (i + 1) = 0) ∧
      basePhiValue digits = (N : GoldenInt) :=
  canonical_two_sided_digits_unique

end


end D5.S1.Words.Expansions.BasePhiCanonicalExpansion
