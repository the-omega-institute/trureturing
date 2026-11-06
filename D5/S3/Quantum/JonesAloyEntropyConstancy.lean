/- GID: D5/S3/Quantum/JonesAloyEntropyConstancy
   generality: G
   mirror-B: D5/B/S3/Quantum/JonesAloyEntropyConstancy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Refute entropy constancy on fixed-difference quantum correlation lines. -/

/-
admission_basis: open-problem-resolution (#23268; Refuted)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25630
The uniform analytic family, its entropy estimates and consumed algebraic facts
are not finite enumeration, a checker, a numerical reduction or an isolated
certified instance. The public result has no utility-based registration exemption.
Direct frozen dependencies (declaration statement_id, not module pins):
F1: D5/S3/Quantum/CloningMachine.binaryEntropyBits;
  statement_id: sha256:688128ab90010a81f7deda9f09bce484b31dd0c87b4be4eba0ee15f631995292
F2: D5/S3/Quantum/CloningMachine.machineReducedState._proof_2;
  statement_id: sha256:d5fe3322d971dc1c2b0ef6a814eeeb0cdec6553d0d5422db330c7c1de2f069bb
F2 is a compiler-shared normalization proof in the frozen owner.
cos_tangent_strict: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: sin_sq_tangent_strict
sin_sq_tangent_strict: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: support_bound
sin_sq_chord: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: support_bound
support_bound: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: boundary_support
family_parameters: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: boundary_support
bits_eq_nats: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: bits_one_sub, bits_upper, entropy_gap
bits_one_sub: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: entropy_gap, entropy_boundary, entropy_antidiagonal
bits_upper: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: entropy_gap
entropy_gap: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: roof_separation
fidelity_boundary: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: boundary_support, boundary_mem
fidelity_antidiagonal: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: antidiagonal_mem, midpoint_mem
boundary_support: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: boundary_objective
boundary_mem: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: roof_separation, result
antidiagonal_mem: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: midpoint_feasible
midpoint_mem: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: roof_separation
entropy_boundary: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: boundary_objective, midpoint_objective
entropy_antidiagonal: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: midpoint_objective
boundary_objective: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: roof_separation
corners_mem: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: midpoint_feasible
midpoint_feasible: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: roof_separation
midpoint_objective: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: roof_separation
roof_separation: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: result
result: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F2; consumers: none (settling result)
The source's binary-entropy coordinate map and midpoint are inlined in the
public formulas; proofs reuse binaryEntropyBits and normalize the midpoint.
The source uses bits, nonnegative unbounded branch energies and exact mean energy.
The public claim includes existence of an attained-minimum function; its negation
does not independently establish existence. Interior persistence and physical
operator realizations are outside this theorem.
-/

import D5.S3.Quantum.CloningMachine

/-! Binding definitions for arXiv:2506.14526v3, Appendix E(ii), after Lemma 3.
Time separation and Planck's constant are one. Input probabilities are both one half.
Energy labels are nonnegative and unbounded, with the exact mean-energy equality.
The source's minimum is specified by IsLeast; claim includes existence of this object.
-/

namespace D5.S3.Quantum.JonesAloyEntropyConstancy

open scoped BigOperators

/-- Equation (9), with time separation one. -/
noncomputable def gamma (e : ℝ) : ℝ :=
  if e < Real.pi / 2 then Real.cos e else 0

/-- Equation (8); the two square-root factors remain separate as in the source. -/
noncomputable def fidelityExpression (C : (ℝ × ℝ)) : ℝ :=
  (Real.sqrt (1 + C.1) * Real.sqrt (1 + C.2) +
    Real.sqrt (1 - C.1) * Real.sqrt (1 - C.2)) / 2

/-- The source's characterized correlation set, including the correlation square. -/
def quantumSet (e : ℝ) : Set (ℝ × ℝ) :=
  {C | -1 ≤ C.1 ∧ C.1 ≤ 1 ∧ -1 ≤ C.2 ∧ C.2 ≤ 1 ∧
    gamma e ≤ fidelityExpression C}

/-- H(C) with p(x) = 1/2 for both inputs. -/
noncomputable def entropy (C : (ℝ × ℝ)) : ℝ :=
  (D5.S3.Quantum.CloningMachine.binaryEntropyBits ((1 + C.1) / 2) +
    D5.S3.Quantum.CloningMachine.binaryEntropyBits ((1 + C.2) / 2)) / 2

/-- A finite ensemble; its number of hidden variables is unrestricted. -/
structure Ensemble (n : ℕ) where
  weight : Fin n → ℝ
  corr : Fin n → (ℝ × ℝ)
  energy : Fin n → ℝ

/-- Equation (27), with probability normalization and nonnegative energy labels. -/
def Feasible {n : ℕ} (A : Ensemble n) (C : (ℝ × ℝ)) (E : ℝ) : Prop :=
  (∀ i : Fin n, 0 ≤ A.weight i) ∧
  (∑ i : Fin n, A.weight i) = 1 ∧
  (∀ i : Fin n, 0 ≤ A.energy i) ∧
  (∀ i : Fin n, A.corr i ∈ quantumSet (A.energy i)) ∧
  (∑ i : Fin n, A.weight i * (A.corr i).1) = C.1 ∧
  (∑ i : Fin n, A.weight i * (A.corr i).2) = C.2 ∧
  (∑ i : Fin n, A.weight i * A.energy i) = E

/-- All objective values of the source's optimization, over every finite ensemble. -/
def entropyValues (C : (ℝ × ℝ)) (E : ℝ) : Set ℝ :=
  {z | ∃ (n : ℕ) (A : Ensemble n), Feasible A C E ∧
    z = ∑ i : Fin n, A.weight i * entropy (A.corr i)}

/-- Literal minimum specification, rather than a default value for an empty infimum. -/
def IsSourceRoof (HStar : (ℝ × ℝ) → ℝ → ℝ) : Prop :=
  ∀ (E : ℝ), 0 ≤ E → ∀ (C : (ℝ × ℝ)), C ∈ quantumSet E →
    IsLeast (entropyValues C E) (HStar C E)

/-- The conjectured equality after Lemma 3 (journal Lemma E3), with existence explicit. -/
def claim : Prop :=
  (∃ HStar : (ℝ × ℝ) → ℝ → ℝ, IsSourceRoof HStar) ∧
  ∀ HStar : (ℝ × ℝ) → ℝ → ℝ, IsSourceRoof HStar →
    ∀ E : ℝ, 0 ≤ E → E ≤ Real.pi / 2 →
      ∀ C : (ℝ × ℝ), C ∈ quantumSet E →
        HStar C E = HStar ((C.1 - C.2) / 2, -(C.1 - C.2) / 2) E

end D5.S3.Quantum.JonesAloyEntropyConstancy

namespace D5.S3.Quantum.JonesAloyEntropyConstancy
open Real Set
open scoped BigOperators

-- A strict tangent estimate for the concave part of sin².
private theorem cos_tangent_strict {x y : ℝ}
    (hx : x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hne : y ≠ x) :
    Real.cos y < Real.cos x - Real.sin x * (y - x) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hsl := strictConcaveOn_cos_Icc.lt_slope_of_hasDerivAt hy hx h
      (Real.hasDerivAt_cos x)
    rw [slope_def_field] at hsl
    have hmul := (lt_div_iff₀ (sub_pos.mpr h)).mp hsl
    nlinarith
  · have hsl := strictConcaveOn_cos_Icc.slope_lt_of_hasDerivAt hx hy h
      (Real.hasDerivAt_cos x)
    rw [slope_def_field] at hsl
    have hmul := (div_lt_iff₀ (sub_pos.mpr h)).mp hsl
    nlinarith

-- The strict tangent of sin² on its upper half.
private theorem sin_sq_tangent_strict {E e : ℝ}
    (hE : Real.pi / 4 < E) (hE' : E < Real.pi / 2)
    (he : Real.pi / 4 ≤ e) (he' : e ≤ Real.pi / 2) (hne : e ≠ E) :
    Real.sin e ^ 2 < Real.sin E ^ 2 +
      2 * Real.sin E * Real.cos E * (e - E) := by
  have hx : 2 * E - Real.pi ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hy : 2 * e - Real.pi ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hh := cos_tangent_strict hx hy (by intro h; apply hne; linarith)
  rw [Real.cos_sub_pi, Real.cos_sub_pi, Real.sin_sub_pi,
    Real.sin_two_mul, Real.cos_two_mul, Real.cos_two_mul] at hh
  have h1 := Real.sin_sq_add_cos_sq e
  have h2 := Real.sin_sq_add_cos_sq E
  nlinarith


private theorem sin_sq_chord {e : ℝ} (he : 0 ≤ e) (he' : e ≤ Real.pi / 4) :
    Real.sin e ^ 2 ≤ 2 * e / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let t := 4 * e / Real.pi
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_one hpi).2; linarith
  have hh := strictConcaveOn_cos_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith)
    (show Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith)
    (show 0 ≤ 1 - t by linarith) ht0 (by ring : (1 - t) + t = 1)
  have ha : (1 - t) • (0 : ℝ) + t • (Real.pi / 2) = 2 * e := by
    simp only [smul_eq_mul]; dsimp [t]; field_simp <;> ring
  rw [ha, Real.cos_zero, Real.cos_pi_div_two, smul_eq_mul, smul_eq_mul] at hh
  rw [Real.cos_two_mul] at hh
  have hs := Real.sin_sq_add_cos_sq e
  dsimp [t] at hh
  have hratio : 4 * e / Real.pi = 2 * (2 * e / Real.pi) := by ring
  rw [hratio] at hh
  nlinarith

-- Uniform strict support, including energies above the speed-limit threshold.
private theorem support_bound {E s c p e : ℝ}
    (hE : Real.pi / 4 < E) (hE' : E < Real.pi / 2)
    (hs : Real.sin E = s) (hc : Real.cos E = c)
    (hsc : 0 < 2 * s * c) (hzero : 0 < s ^ 2 - 2 * s * c * E)
    (he : 0 ≤ e) (hp : p ≤ 1)
    (hquant : e < Real.pi / 2 → p ≤ Real.sin e ^ 2) :
    p ≤ s ^ 2 + 2 * s * c * (e - E) ∧
    (p = s ^ 2 + 2 * s * c * (e - E) → p = s ^ 2) := by
  have hh : (1 / 2 : ℝ) < s ^ 2 + 2 * s * c * (Real.pi / 4 - E) := by
    have ht := sin_sq_tangent_strict hE hE' (le_refl (Real.pi / 4))
      (by linarith [Real.pi_pos]) (ne_of_lt hE)
    rw [hs, hc, Real.sin_pi_div_four] at ht
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  by_cases hl : e < Real.pi / 4
  · have hp' := hquant (by linarith)
    have hch := sin_sq_chord he hl.le
    have hpi := Real.pi_pos
    have ht0 : 0 ≤ 4 * e / Real.pi := by positivity
    have ht1 : 0 < 1 - 4 * e / Real.pi := by
      have := (div_lt_one hpi).2 (show 4 * e < Real.pi by linarith)
      linarith
    have hmix := add_pos_of_pos_of_nonneg (mul_pos ht1 hzero)
      (mul_nonneg ht0 (le_of_lt (sub_pos.mpr hh)))
    have hidentity :
        (1 - 4 * e / Real.pi) * (s ^ 2 - 2 * s * c * E) +
        (4 * e / Real.pi) *
          (s ^ 2 + 2 * s * c * (Real.pi / 4 - E) - 1 / 2) =
        s ^ 2 + 2 * s * c * (e - E) - 2 * e / Real.pi := by
      field_simp <;> ring
    rw [hidentity] at hmix
    have hpstrict : p < s ^ 2 + 2 * s * c * (e - E) := by linarith
    exact ⟨hpstrict.le, fun heq => False.elim (hpstrict.ne heq)⟩
  · have hl : Real.pi / 4 ≤ e := le_of_not_gt hl
    by_cases hhigh : Real.pi / 2 ≤ e
    · have hh := sin_sq_tangent_strict hE hE' (by linarith [Real.pi_pos])
        (le_refl (Real.pi / 2)) (ne_of_gt hE')
      rw [hs, hc, Real.sin_pi_div_two] at hh
      have hmul := mul_nonneg hsc.le (sub_nonneg.mpr hhigh)
      have hpstrict : p < s ^ 2 + 2 * s * c * (e - E) := by nlinarith
      exact ⟨hpstrict.le, fun heq => False.elim (hpstrict.ne heq)⟩
    · have hhigh : e < Real.pi / 2 := lt_of_not_ge hhigh
      have hp' := hquant hhigh
      by_cases heq : e = E
      · subst e
        rw [hs] at hp'
        simpa using (show p ≤ s ^ 2 ∧ (p = s ^ 2 → p = s ^ 2) from ⟨hp', id⟩)
      · have hh := sin_sq_tangent_strict hE hE' hl hhigh.le heq
        rw [hs, hc] at hh
        have hpstrict := hp'.trans_lt hh
        exact ⟨hpstrict.le, fun heq => False.elim (hpstrict.ne heq)⟩

private theorem family_parameters {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    0 < s ∧ 0 < Real.sqrt (1 - s ^ 2) ∧
    Real.sqrt (1 - s ^ 2) ≤ 7 / 25 ∧
    Real.pi / 4 < Real.arcsin s ∧ Real.arcsin s < Real.pi / 2 ∧
    Real.sin (Real.arcsin s) = s ∧
    Real.cos (Real.arcsin s) = Real.sqrt (1 - s ^ 2) ∧
    0 < s ^ 2 - 2 * s * Real.sqrt (1 - s ^ 2) * Real.arcsin s := by
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hlow : (576 / 625 : ℝ) ≤ s ^ 2 := by nlinarith
  have hc0 : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hcsq := Real.sq_sqrt (show 0 ≤ 1 - s ^ 2 by linarith)
  have hc1 : Real.sqrt (1 - s ^ 2) ≤ 7 / 25 := by nlinarith
  have he0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 hs0.le
  have he1 : Real.arcsin s < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hs'
  have hsmall : Real.sin (Real.pi / 4) < s := by
    rw [Real.sin_pi_div_four]
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have he : Real.pi / 4 < Real.arcsin s :=
    (Real.lt_arcsin_iff_sin_lt
      (show Real.pi / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos]) ⟨by linarith, hs'.le⟩).2 hsmall
  have hEbound : Real.arcsin s < 8 / 5 := by linarith [Real.pi_lt_d2]
  have hprod : 2 * Real.sqrt (1 - s ^ 2) * Real.arcsin s ≤ 112 / 125 := by
    have hh := mul_le_mul hc1 (le_of_lt hEbound) he0 (by norm_num : (0 : ℝ) ≤ 7 / 25)
    nlinarith
  refine ⟨hs0, hc0, hc1, he, he1, Real.sin_arcsin (by linarith) hs'.le,
    Real.cos_arcsin s, ?_⟩
  have hh := mul_pos hs0 (show 0 < s - 2 * Real.sqrt (1 - s ^ 2) * Real.arcsin s by linarith)
  nlinarith

local notation "b" => D5.S3.Quantum.CloningMachine.binaryEntropyBits

private theorem bits_eq_nats (p : ℝ) : b p = Real.binEntropy p / Real.log 2 := by
  simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb,
    Real.binEntropy, Real.log_inv]
  ring

private theorem bits_one_sub (p : ℝ) : b (1 - p) = b p := by
  rw [bits_eq_nats, bits_eq_nats, Real.binEntropy_one_sub]

private theorem bits_upper {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    b a ≤ a * (-Real.log a / Real.log 2 + 3 / 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hsmall : -(1 - a) * Real.log (1 - a) ≤ a := by
    simpa only [Real.negMulLog, sub_sub_cancel] using
      (Real.negMulLog_le_one_sub_self (sub_nonneg.mpr ha'.le))
  rw [bits_eq_nats, Real.binEntropy, Real.log_inv, Real.log_inv]
  apply (div_le_iff₀ hl2).2
  have hid : a * (-Real.log a / Real.log 2 + 3 / 2) * Real.log 2 =
      -a * Real.log a + (3 / 2) * a * Real.log 2 := by
    field_simp <;> ring
  rw [hid]
  have hp := mul_nonneg ha.le (show 0 ≤ (3 / 2) * Real.log 2 - 1 by linarith)
  nlinarith

private theorem entropy_gap {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    s * b ((1 + s) / 2) + 7 * ((1 - s) / 2) ^ 2 < b (s ^ 2) / 2 := by
  let a := (1 - s) / 2
  let L := -Real.log a / Real.log 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : a ≤ 1 / 50 := by dsimp [a]; linarith
  have ha1 : a < 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hl2
  have hlogpow : Real.log (1 / 2048 : ℝ) = -11 * Real.log 2 := by
    rw [show (1 / 2048 : ℝ) = ((2 : ℝ) ^ 11)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    ring
  have hpow : a ^ 2 < (1 / 2048 : ℝ) := by nlinarith
  have hlog := Real.log_lt_log (sq_pos_of_pos ha) hpow
  rw [Real.log_pow, hlogpow] at hlog
  norm_num at hlog
  have hL : (11 / 2 : ℝ) < L := by
    dsimp [L]
    apply (lt_div_iff₀ hl2).2
    nlinarith
  let x := 1 - s ^ 2
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hx1 : x < 1 := by dsimp [x]; nlinarith
  have hx : x = 4 * a * (1 - a) := by dsimp [x, a]; ring
  have hxa : x ≤ 4 * a := by rw [hx]; nlinarith
  have hlogx := Real.log_le_log hx0 hxa
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt ha), Real.log_four_eq] at hlogx
  have hn : 0 ≤ -(1 - x) * Real.log (1 - x) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (Real.log_nonpos (by linarith) (by linarith))
  have hxbits : b (s ^ 2) = b x := by
    rw [← bits_one_sub (s ^ 2)]
  have hbits : b x * Real.log 2 = -x * Real.log x - (1 - x) * Real.log (1 - x) := by
    rw [bits_eq_nats, div_mul_cancel₀ _ hl2ne]
    simp only [Real.binEntropy, Real.log_inv]
    ring
  have hprod := mul_le_mul_of_nonpos_left hlogx (show -x ≤ 0 by linarith)
  have hlowmul : -x / 2 * (Real.log a + 2 * Real.log 2) ≤ b x / 2 * Real.log 2 := by
    nlinarith [hbits]
  have hid : 2 * a * (1 - a) * (L - 2) * Real.log 2 =
      -x / 2 * (Real.log a + 2 * Real.log 2) := by
    rw [hx]; dsimp [L]; field_simp <;> ring
  have hlow : 2 * a * (1 - a) * (L - 2) ≤ b (s ^ 2) / 2 := by
    rw [hxbits]
    apply (mul_le_mul_iff_left₀ hl2).mp
    nlinarith [hid, hlowmul]
  have hu := bits_upper ha ha1
  change b a ≤ a * (L + 3 / 2) at hu
  have hsym : b ((1 + s) / 2) = b a := by
    rw [← bits_one_sub ((1 + s) / 2)]
    congr 1; dsimp [a]; ring
  have hm := mul_le_mul_of_nonneg_left hu hs0.le
  have hsa : s = 1 - 2 * a := by dsimp [a]; ring
  have hstrict : s * (a * (L + 3 / 2)) + 7 * a ^ 2 <
      2 * a * (1 - a) * (L - 2) := by
    rw [hsa]
    have hh := mul_pos ha (show 0 < L - 11 / 2 by linarith)
    nlinarith
  rw [hsym]
  change s * b a + 7 * a ^ 2 < b (s ^ 2) / 2
  linarith

private theorem fidelity_boundary (p : ℝ) :
    fidelityExpression (1, 1 - 2 * p) = Real.sqrt (1 - p) := by
  unfold fidelityExpression
  dsimp
  rw [show 1 + (1 - 2 * p) = 2 * (1 - p) by ring]
  norm_num only [add_self_div_two, sub_self, Real.sqrt_zero, zero_mul, add_zero,
    show (1 + 1 : ℝ) = 2 by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    exact Real.mul_self_sqrt (by norm_num)
  rw [h2]
  ring

private theorem fidelity_antidiagonal {t : ℝ} (ht : -1 ≤ t) :
    fidelityExpression (t, -t) = Real.sqrt (1 - t ^ 2) := by
  unfold fidelityExpression
  dsimp
  rw [show 1 + -t = 1 - t by ring, show 1 - -t = 1 + t by ring]
  rw [mul_comm (Real.sqrt (1 - t)) (Real.sqrt (1 + t))]
  rw [← Real.sqrt_mul (show 0 ≤ 1 + t by linarith)]
  rw [show (1 + t) * (1 - t) = 1 - t ^ 2 by ring]
  ring

private theorem boundary_support {s p e : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1)
    (he : 0 ≤ e) (hQ : (1, 1 - 2 * p) ∈ quantumSet e) :
    p ≤ s ^ 2 + 2 * s * Real.sqrt (1 - s ^ 2) * (e - Real.arcsin s) ∧
    (p = s ^ 2 + 2 * s * Real.sqrt (1 - s ^ 2) * (e - Real.arcsin s) → p = s ^ 2) := by
  obtain ⟨hs0, hc0, hc1, hE, hE', hsin, hcos, hz⟩ := family_parameters hs hs'
  obtain ⟨h00, h01, h10, h11, hF⟩ := hQ
  have hp1 : p ≤ 1 := by dsimp at h10; linarith
  apply support_bound hE hE' hsin hcos (by positivity) hz he hp1
  intro he'
  rw [gamma, if_pos he', fidelity_boundary] at hF
  have hcs : 0 ≤ Real.cos e := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], he'.le⟩
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - p by linarith)
  have hsn := Real.sqrt_nonneg (1 - p)
  have htrig := Real.sin_sq_add_cos_sq e
  nlinarith

private theorem boundary_mem {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    (1, 1 - 2 * s ^ 2) ∈ quantumSet (Real.arcsin s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  refine ⟨by norm_num, by norm_num, by dsimp; nlinarith, by dsimp; nlinarith, ?_⟩
  rw [gamma, if_pos (Real.arcsin_lt_pi_div_two.2 hs'), fidelity_boundary, Real.cos_arcsin]

private theorem antidiagonal_mem {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    (s, -s) ∈ quantumSet (Real.arcsin s) := by
  refine ⟨by dsimp; linarith, hs'.le, by dsimp; linarith, by dsimp; linarith, ?_⟩
  rw [gamma, if_pos (Real.arcsin_lt_pi_div_two.2 hs'),
    fidelity_antidiagonal (by linarith), Real.cos_arcsin]

private theorem midpoint_mem {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    (s ^ 2, -(s ^ 2)) ∈ quantumSet (Real.arcsin s) := by
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 < 1 := by nlinarith
  refine ⟨by dsimp; nlinarith, by dsimp; nlinarith,
    by dsimp; nlinarith, by dsimp; nlinarith, ?_⟩
  rw [gamma, if_pos (Real.arcsin_lt_pi_div_two.2 hs'),
    fidelity_antidiagonal (by nlinarith), Real.cos_arcsin]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (s ^ 2)]

private theorem entropy_boundary (s : ℝ) : entropy (1, 1 - 2 * s ^ 2) = b (s ^ 2) / 2 := by
  have hb1 : b 1 = 0 := by
    simp [D5.S3.Quantum.CloningMachine.binaryEntropyBits]
  change (b ((1 + 1) / 2) + b ((1 + (1 - 2 * s ^ 2)) / 2)) / 2 = _
  rw [show ((1 + 1 : ℝ) / 2) = 1 by norm_num, hb1,
    show (1 + (1 - 2 * s ^ 2)) / 2 = 1 - s ^ 2 by ring, bits_one_sub]
  ring

private theorem entropy_antidiagonal (s : ℝ) : entropy (s, -s) = b ((1 + s) / 2) := by
  change (b ((1 + s) / 2) + b ((1 + -s) / 2)) / 2 = _
  rw [show (1 + -s) / 2 = 1 - (1 + s) / 2 by ring, bits_one_sub]
  ring

-- Saturation of an extremal coordinate followed by saturation of strict energy support.
private theorem boundary_objective {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1)
    {n : ℕ} {A : Ensemble n}
    (hA : Feasible A (1, 1 - 2 * s ^ 2) (Real.arcsin s)) :
    (∑ i : Fin n, A.weight i * entropy (A.corr i)) = b (s ^ 2) / 2 := by
  obtain ⟨hw0, hw, he0, hQ, hC0, hC1, hE⟩ := hA
  dsimp only [Prod.fst, Prod.snd] at hC0 hC1
  have hslack : (∑ i : Fin n, A.weight i * (1 - (A.corr i).1)) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hw, hC0]
    ring
  have hnonneg : ∀ i : Fin n, 0 ≤ A.weight i * (1 - (A.corr i).1) := by
    intro i
    exact mul_nonneg (hw0 i) (sub_nonneg.mpr (hQ i).2.1)
  have hsat : ∀ i : Fin n, 0 < A.weight i → (A.corr i).1 = 1 := by
    intro i hi
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hslack i (Finset.mem_univ i)
    have hh := (mul_eq_zero.mp hh).resolve_left (ne_of_gt hi)
    linarith
  let p : Fin n → ℝ := fun i => (1 - (A.corr i).2) / 2
  have hpmean : (∑ i : Fin n, A.weight i * p i) = s ^ 2 := by
    simp only [p, ← mul_div_assoc, mul_sub, mul_one]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hw, hC1]
    ring
  let k := 2 * s * Real.sqrt (1 - s ^ 2)
  have hsupport : ∀ i : Fin n, 0 < A.weight i →
      p i ≤ s ^ 2 + k * (A.energy i - Real.arcsin s) ∧
      (p i = s ^ 2 + k * (A.energy i - Real.arcsin s) → p i = s ^ 2) := by
    intro i hi
    have hc : A.corr i = (1, 1 - 2 * p i) := by
      apply Prod.ext
      · exact hsat i hi
      · dsimp [p]; ring
    exact boundary_support hs hs' (he0 i) (hc ▸ hQ i)
  have hnonneg2 : ∀ i : Fin n,
      0 ≤ A.weight i * (s ^ 2 + k * (A.energy i - Real.arcsin s) - p i) := by
    intro i
    rcases eq_or_lt_of_le (hw0 i) with hi | hi
    · rw [← hi]; simp
    · exact mul_nonneg (hw0 i) (sub_nonneg.mpr (hsupport i hi).1)
  have hslack2 : (∑ i : Fin n,
      A.weight i * (s ^ 2 + k * (A.energy i - Real.arcsin s) - p i)) = 0 := by
    calc
      _ = ∑ i : Fin n, ((s ^ 2 - k * Real.arcsin s) * A.weight i +
          k * (A.weight i * A.energy i) - A.weight i * p i) := by
        apply Finset.sum_congr rfl; intro i _; ring
      _ = (s ^ 2 - k * Real.arcsin s) * (∑ i : Fin n, A.weight i) +
          k * (∑ i : Fin n, A.weight i * A.energy i) -
          (∑ i : Fin n, A.weight i * p i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by rw [hw, hE, hpmean]; ring
  have hrigid : ∀ i : Fin n, 0 < A.weight i → A.corr i = (1, 1 - 2 * s ^ 2) := by
    intro i hi
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg2 j)).mp hslack2 i (Finset.mem_univ i)
    have hh := (mul_eq_zero.mp hh).resolve_left (ne_of_gt hi)
    have hp := (hsupport i hi).2 (by linarith)
    apply Prod.ext
    · exact hsat i hi
    · dsimp [p] at hp; dsimp; linarith
  calc
    _ = ∑ i : Fin n, A.weight i * (b (s ^ 2) / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_or_lt_of_le (hw0 i) with hi | hi
      · rw [← hi]; simp
      · rw [hrigid i hi, entropy_boundary]
    _ = b (s ^ 2) / 2 := by rw [← Finset.sum_mul, hw, one_mul]

private noncomputable def midpointEnsemble (s : ℝ) : Ensemble 3 where
  weight := ![s, (1 - s) / 2, (1 - s) / 2]
  corr := ![(s, -s), (1, 1), (-1, -1)]
  energy := fun _ => Real.arcsin s

private theorem corners_mem (e : ℝ) :
    (1, 1) ∈ quantumSet e ∧ (-1, -1) ∈ quantumSet e := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    exact Real.mul_self_sqrt (by norm_num)
  have hg : gamma e ≤ 1 := by
    unfold gamma
    split
    · exact Real.cos_le_one e
    · norm_num
  constructor <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩ <;>
    simpa [fidelityExpression, h2] using hg

private theorem midpoint_feasible {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    Feasible (midpointEnsemble s) (s ^ 2, -(s ^ 2)) (Real.arcsin s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [midpointEnsemble] <;> linarith
  · simp [midpointEnsemble, Fin.sum_univ_three]; ring
  · intro i; exact Real.arcsin_nonneg.2 (by linarith)
  · intro i
    fin_cases i
    · exact antidiagonal_mem hs hs'
    · exact (corners_mem (Real.arcsin s)).1
    · exact (corners_mem (Real.arcsin s)).2
  · simp [midpointEnsemble, Fin.sum_univ_three]; ring
  · simp [midpointEnsemble, Fin.sum_univ_three]; ring
  · simp [midpointEnsemble, Fin.sum_univ_three]; ring

private theorem midpoint_objective (s : ℝ) :
    (∑ i : Fin 3, (midpointEnsemble s).weight i * entropy ((midpointEnsemble s).corr i)) =
      s * b ((1 + s) / 2) := by
  have hp : entropy (1, 1) = 0 := by
    simpa [D5.S3.Quantum.CloningMachine.binaryEntropyBits] using entropy_boundary (0 : ℝ)
  have hn : entropy (-1, -1) = 0 := by
    norm_num [entropy, D5.S3.Quantum.CloningMachine.binaryEntropyBits]
  simp [midpointEnsemble, Fin.sum_univ_three, hp, hn, entropy_antidiagonal]

private theorem roof_separation {HStar : (ℝ × ℝ) → ℝ → ℝ} (hR : IsSourceRoof HStar)
    {s : ℝ} (hs : (24 / 25 : ℝ) ≤ s) (hs' : s < 1) :
    HStar (s ^ 2, -(s ^ 2)) (Real.arcsin s) + 7 * ((1 - s) / 2) ^ 2 <
      HStar (1, 1 - 2 * s ^ 2) (Real.arcsin s) := by
  have hE : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 (by linarith)
  have hb := hR (Real.arcsin s) hE (1, 1 - 2 * s ^ 2) (boundary_mem hs hs')
  have hB : HStar (1, 1 - 2 * s ^ 2) (Real.arcsin s) = b (s ^ 2) / 2 := by
    obtain ⟨n, A, hA, hz⟩ := hb.1
    rw [hz, boundary_objective hs hs' hA]
  have hm := hR (Real.arcsin s) hE (s ^ 2, -(s ^ 2)) (midpoint_mem hs hs')
  have hval : s * b ((1 + s) / 2) ∈ entropyValues (s ^ 2, -(s ^ 2)) (Real.arcsin s) := by
    exact ⟨3, midpointEnsemble s, midpoint_feasible hs hs', (midpoint_objective s).symm⟩
  have hM := hm.2 hval
  rw [hB]
  linarith [entropy_gap hs hs']

theorem result : ¬ D5.S3.Quantum.JonesAloyEntropyConstancy.claim := by
  rintro ⟨⟨HStar, hR⟩, hconst⟩
  let s : ℝ := 24 / 25
  have hs : (24 / 25 : ℝ) ≤ s := le_refl _
  have hs' : s < 1 := by norm_num [s]
  have hE : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 (by norm_num [s])
  have hE' : Real.arcsin s ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  have hneq := roof_separation hR hs hs'
  have heq := hconst HStar hR (Real.arcsin s) hE hE'
    (1, 1 - 2 * s ^ 2) (boundary_mem hs hs')
  have hmid : (((1 : ℝ) - (1 - 2 * s ^ 2)) / 2, -((1 : ℝ) - (1 - 2 * s ^ 2)) / 2) = (s ^ 2, -(s ^ 2)) := by
    apply Prod.ext <;> dsimp <;> ring
  rw [hmid] at heq
  rw [heq] at hneq
  nlinarith [sq_nonneg ((1 - s) / 2)]

end D5.S3.Quantum.JonesAloyEntropyConstancy
