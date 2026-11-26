/- GID: D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D
   generality: I
   mirror-B: D5/B/S3/Quantum/Gauge/ChiralAnomalyRigidity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact factorization of the one-generation chiral anomaly equations. -/

import D5.S3.Quantum.Gauge.FiniteSpectralTripleSM
import Mathlib.Tactic.LinearCombination

/-!
Charges are ordered as the left-handed quark doublet, the two conjugate quark
singlets, the left-handed lepton doublet, the conjugate charged lepton, and,
when present, the conjugate neutrino. The labeled five-species locus is the
union of three lines through zero. With a neutrino it is a union of planes,
one of which consists of the Yukawa-compatible charges.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D

variable {K : Type*} [Field K]

/-- Mixed color, mixed weak, mixed gravitational and cubic abelian cancellation. -/
def anomaly5 (y : Fin 5 → K) : Prop :=
  2 * y 0 + y 1 + y 2 = 0 ∧
  3 * y 0 + y 3 = 0 ∧
  6 * y 0 + 3 * y 1 + 3 * y 2 + 2 * y 3 + y 4 = 0 ∧
  6 * y 0 ^ 3 + 3 * y 1 ^ 3 + 3 * y 2 ^ 3 + 2 * y 3 ^ 3 + y 4 ^ 3 = 0

/-- The additional singlet contributes to the gravitational and cubic equations. -/
def anomaly6 (y : Fin 6 → K) : Prop :=
  2 * y 0 + y 1 + y 2 = 0 ∧
  3 * y 0 + y 3 = 0 ∧
  6 * y 0 + 3 * y 1 + 3 * y 2 + 2 * y 3 + y 4 + y 5 = 0 ∧
  6 * y 0 ^ 3 + 3 * y 1 ^ 3 + 3 * y 2 ^ 3 + 2 * y 3 ^ 3 +
    y 4 ^ 3 + y 5 ^ 3 = 0

/-- The four Yukawa charge equations for Higgs charge `h`. -/
def yukawa (y : Fin 6 → K) (h : K) : Prop :=
  y 0 + y 1 = -h ∧ y 0 + y 2 = h ∧ y 3 + y 4 = h ∧ y 3 + y 5 = -h

def sm5 : Fin 5 → K := ![1, -4, 2, -3, 6]
def sm5Swap : Fin 5 → K := ![1, 2, -4, -3, 6]
def trivial5 : Fin 5 → K := ![0, -1, 1, 0, 0]

theorem anomaly5_linear_normal_form (y : Fin 5 → K) (hy : anomaly5 y) :
    y 3 = -3 * y 0 ∧ y 4 = 6 * y 0 ∧ y 1 = -y 2 - 2 * y 0 := by
  obtain ⟨hC, hW, hG, _⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hW
  · linear_combination hG - 3 * hC - 2 * hW
  · linear_combination hC

theorem anomaly5_cubic_factor (q d : K) :
    6 * q ^ 3 + 3 * (-d - 2 * q) ^ 3 + 3 * d ^ 3 + 2 * (-3 * q) ^ 3 + (6 * q) ^ 3 =
      18 * q * (-d + 2 * q) * (d + 4 * q) := by ring

variable [CharZero K]

theorem anomaly5_classification (y : Fin 5 → K) : anomaly5 y ↔
    (∃ t : K, y = t • sm5) ∨ (∃ t : K, y = t • sm5Swap) ∨
    (∃ t : K, y = t • trivial5) := by
  constructor
  · intro hy
    obtain ⟨hL, hE, hU⟩ := anomaly5_linear_normal_form y hy
    have hc := hy.2.2.2
    rw [hL, hE, hU, anomaly5_cubic_factor] at hc
    have h18 : (18 : K) ≠ 0 := by norm_num
    simp only [mul_eq_zero, h18, false_or] at hc
    rcases hc with (hq | hd) | hd
    · right
      right
      refine ⟨y 2, ?_⟩
      funext i
      fin_cases i <;> simp [trivial5, hq, hL, hE, hU]
    · have hd' : y 2 = 2 * y 0 := by linear_combination -hd
      left
      refine ⟨y 0, ?_⟩
      funext i
      fin_cases i <;> simp [sm5, hL, hE, hU, hd'] <;> ring
    · have hd' : y 2 = -4 * y 0 := by linear_combination hd
      right
      left
      refine ⟨y 0, ?_⟩
      funext i
      fin_cases i <;> simp [sm5Swap, hL, hE, hU, hd'] <;> ring
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      simp [anomaly5, sm5, sm5Swap, trivial5, Pi.smul_apply, smul_eq_mul] <;>
      (repeat' constructor) <;> ring

/-- On a nonzero solution exactly one of the three labeled directions applies. -/
theorem anomaly5_projective_unique (y : Fin 5 → K) (hy : y ≠ 0) :
    anomaly5 y ↔
      ∃! b : Fin 3, ∃ t : K, y = t • (![sm5, sm5Swap, trivial5] : Fin 3 → (Fin 5 → K)) b := by
  let v : Fin 3 → (Fin 5 → K) := ![sm5, sm5Swap, trivial5]
  change anomaly5 y ↔ ∃! b : Fin 3, ∃ t : K, y = t • v b
  have hv : anomaly5 y ↔ ∃ b : Fin 3, ∃ t : K, y = t • v b := by
    rw [anomaly5_classification, Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_one]
    rfl
  rw [hv]
  constructor
  · rintro ⟨a, t, ht⟩
    refine ⟨a, ⟨t, ht⟩, ?_⟩
    rintro b ⟨s, hs⟩
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hy (by simpa using ht)
    have h0 := congrFun (ht.symm.trans hs) 0
    have h2 := congrFun (ht.symm.trans hs) 2
    fin_cases a <;> fin_cases b <;>
      norm_num [v, sm5, sm5Swap, trivial5, Pi.smul_apply, smul_eq_mul] at h0 h2 ⊢
    all_goals apply (ht0 _).elim
    · linear_combination (h2 + 4 * h0) / 6
    · exact h0
    · linear_combination (2 * h0 - h2) / 6
    · exact h0
    · simpa [← h0] using h2
    · simpa [← h0] using h2
  · rintro ⟨b, hb, _⟩
    exact ⟨b, hb⟩

/-- Exchange the up and down singlet charges. -/
def swapUD (y : Fin 5 → K) : Fin 5 → K := ![y 0, y 2, y 1, y 3, y 4]

theorem anomaly5_orbit_classification (y : Fin 5 → K) : anomaly5 y ↔
    (∃ t : K, y = t • sm5 ∨ swapUD y = t • sm5) ∨
    (∃ t : K, y = t • trivial5) := by
  have hswap : ∀ t : K, swapUD y = t • sm5 ↔ y = t • sm5Swap := by
    intro t
    rw [funext_iff, funext_iff]
    constructor <;> intro he
    all_goals
      simp [Fin.forall_fin_succ, swapUD, sm5, sm5Swap] at he ⊢
      tauto
  simp only [hswap, exists_or, anomaly5_classification, or_assoc]

omit [CharZero K] in
theorem anomaly6_cubic_factor (q d nu : K) :
    6 * q ^ 3 + 3 * (-d - 2 * q) ^ 3 + 3 * d ^ 3 + 2 * (-3 * q) ^ 3 +
      (6 * q - nu) ^ 3 + nu ^ 3 =
      18 * q * (-d - nu + 2 * q) * (d - nu + 4 * q) := by ring

/-- Three free linear coordinates, with a product of three linear forms as the cubic constraint. -/
theorem anomaly6_factorization (y : Fin 6 → K) :
    anomaly6 y ↔
      y 1 = -y 2 - 2 * y 0 ∧ y 3 = -3 * y 0 ∧ y 4 = 6 * y 0 - y 5 ∧
      (y 0 = 0 ∨ y 2 + y 5 = 2 * y 0 ∨ y 5 = y 2 + 4 * y 0) := by
  have h18 : (18 : K) ≠ 0 := by norm_num
  have hbranch : 18 * y 0 * (-y 2 - y 5 + 2 * y 0) * (y 2 - y 5 + 4 * y 0) = 0 ↔
      y 0 = 0 ∨ y 2 + y 5 = 2 * y 0 ∨ y 5 = y 2 + 4 * y 0 := by
    simp only [mul_eq_zero, h18, false_or, or_assoc]
    have h₁ : -y 2 - y 5 + 2 * y 0 = 0 ↔ y 2 + y 5 = 2 * y 0 := by
      constructor <;> intro h <;> linear_combination -h
    have h₂ : y 2 - y 5 + 4 * y 0 = 0 ↔ y 5 = y 2 + 4 * y 0 := by
      constructor <;> intro h <;> linear_combination -h
    rw [h₁, h₂]
  constructor
  · rintro ⟨hC, hW, hG, hY⟩
    have hu : y 1 = -y 2 - 2 * y 0 := by linear_combination hC
    have hl : y 3 = -3 * y 0 := by linear_combination hW
    have he : y 4 = 6 * y 0 - y 5 := by linear_combination hG - 3 * hC - 2 * hW
    rw [hu, hl, he, anomaly6_cubic_factor] at hY
    exact ⟨hu, hl, he, hbranch.mp hY⟩
  · rintro ⟨hu, hl, he, hb⟩
    unfold anomaly6
    rw [hu, hl, he, anomaly6_cubic_factor]
    exact ⟨by ring, by ring, by ring, hbranch.mpr hb⟩

def yukawaCharges (q h : K) : Fin 6 → K :=
  ![q, -h - q, h - q, -3 * q, h + 3 * q, 3 * q - h]

theorem anomaly6_yukawa_normal_form (y : Fin 6 → K) (h : K) :
    anomaly6 y ∧ yukawa y h ↔ ∃ q : K, y = yukawaCharges q h := by
  constructor
  · rintro ⟨ha, hu, hd, he, hn⟩
    have hl := (anomaly6_factorization y).mp ha |>.2.1
    refine ⟨y 0, ?_⟩
    rw [funext_iff]
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    change y 0 = y 0 ∧ y 1 = -h - y 0 ∧ y 2 = h - y 0 ∧ y 3 = -3 * y 0 ∧
      y 4 = h + 3 * y 0 ∧ y 5 = 3 * y 0 - h
    exact ⟨rfl, by linear_combination hu, by linear_combination hd, hl,
      by linear_combination he - hl, by linear_combination hn - hl⟩
  · rintro ⟨q, rfl⟩
    rw [anomaly6_factorization]
    change ((-h - q = -(h - q) - 2 * q) ∧ -3 * q = -3 * q ∧
      h + 3 * q = 6 * q - (3 * q - h) ∧
      (q = 0 ∨ h - q + (3 * q - h) = 2 * q ∨ 3 * q - h = h - q + 4 * q)) ∧
      (q + (-h - q) = -h ∧ q + (h - q) = h ∧
        -3 * q + (h + 3 * q) = h ∧ -3 * q + (3 * q - h) = -h)
    exact ⟨⟨by ring, rfl, by ring, Or.inr (Or.inl (by ring))⟩,
      by ring, by ring, by ring, by ring⟩

open FiniteSpectralTripleSM in
/-- In all-left-handed order, the spectral-triple charges have Higgs charge one half. -/
theorem spectral_triple_hypercharge_compatibility :
    ![hypercharge .QL, hypercharge .uc, hypercharge .dc, hypercharge .LL,
      hypercharge .ec, hypercharge .nuc] = yukawaCharges (1 / 6 : ℚ) (1 / 2) := by
  obtain ⟨hq, hu, hd, hl, he, hn⟩ := hypercharge_table
  rw [hq, hu, hd, hl, he, hn]
  norm_num [yukawaCharges]

/-- One weak lepton doublet and one weak quark doublet per color. -/
def doubletCount (nc : ℕ) : ℕ := nc + 1

theorem witten_parity (nc : ℕ) : Even (doubletCount nc) ↔ Odd nc := by
  exact Nat.even_add_one.trans Nat.not_even_iff_odd

theorem sm_witten_even : Even (doubletCount 3) := by
  rw [witten_parity]
  decide

end D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D
