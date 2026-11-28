/- GID: D5/S3/Quantum/Gauge/E6TrinificationUnification4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/E6TrinificationUnification4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exceptional roots, chiral E6 weights, trinification and the invariant cubic. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D
import D5.S3.Quantum.Gauge.GaugeUnificationRG4D
import OmegaMath.LinearAlgebra.SpinorWeights5
import OmegaMath.LinearAlgebra.RootSystem.ExceptionalSix
import OmegaMath.LinearAlgebra.Matrix.CyclicMatrixCubic

/-! The 27 left-handed states branch as 16 with qPsi charge 1, a vector with
qPsi charge -2, and a singlet with qPsi charge 4. The vector is a fundamental
5 with qChi charge -2 and its dual with qChi charge 2. Trinification coordinates
are ordered Q, L, Qc. Each charge and color identification is explicit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators InnerProductSpace
open OmegaMath
namespace D5.S3.Quantum.Gauge.E6TrinificationUnification4D

open SU5SO10GrandUnification4D (hyperchargeWeights weakWeights)


abbrev E6Rep27 := Fin 16 ⊕ ((Fin 5 ⊕ Fin 5) ⊕ Unit)
abbrev Entry := (Fin 3 × Fin 3) ⊕ ((Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3))

def spinor (i : Fin 16) : E6Rep27 := .inl i
def fundamental (i : Fin 5) : E6Rep27 := .inr (.inl (.inl i))
def antifundamental (i : Fin 5) : E6Rep27 := .inr (.inl (.inr i))
def neutral : E6Rep27 := .inr (.inr ())

/-- The spinor summand uses the actual five occupation coordinates. -/
def cartanWeight (h : Fin 5 → ℝ) : E6Rep27 → ℝ
  | .inl i => SpinorWeights5.cartan h (SpinorWeights5.evenWeight i).1
  | .inr (.inl (.inl i)) => h i
  | .inr (.inl (.inr i)) => -h i
  | .inr (.inr _) => 0

def Y : E6Rep27 → ℝ := cartanWeight hyperchargeWeights
def T3 : E6Rep27 → ℝ := cartanWeight weakWeights
def Q (s : E6Rep27) : ℝ := T3 s + Y s

def qPsi : E6Rep27 → ℝ
  | .inl _ => 1
  | .inr (.inl _) => -2
  | .inr (.inr _) => 4

def qChi : E6Rep27 → ℝ
  | .inl i => SpinorWeights5.xCharge (SpinorWeights5.evenWeight i).1
  | .inr (.inl (.inl _)) => -2
  | .inr (.inl (.inr _)) => 2
  | .inr (.inr _) => 0

def bMinusL (s : E6Rep27) : ℝ := (qChi s + 4 * Y s) / 5

theorem state_card :
    Fintype.card E6Rep27 = 27 ∧ ∀ s, qPsi s ∈ ({1, -2, 4} : Set ℝ) := by
  refine ⟨by decide, ?_⟩
  rintro (i | ((i | i) | u)) <;> simp [qPsi]

private theorem spinor_y (i : Fin 16) :
    Y (.inl i) = ![0, 1/6, 1/6, 1/6, 1/6, 1/6, 1/6,
      -2/3, -2/3, -2/3, 1/3, 1/3, 1/3, -1/2, -1/2, 1] i := by
  have h := congrFun
    (SpinorWeights5.so10_su5_cartan_restriction hyperchargeWeights
      (by norm_num [hyperchargeWeights, Fin.sum_univ_succ])) i
  norm_num [Y, cartanWeight, hyperchargeWeights] at h ⊢
  exact h

private theorem spinor_t3 (i : Fin 16) :
    T3 (.inl i) = ![0, 1/2, -1/2, 1/2, -1/2, 1/2, -1/2,
      0, 0, 0, 0, 0, 0, 1/2, -1/2, 0] i := by
  have h := congrFun
    (SpinorWeights5.so10_su5_cartan_restriction weakWeights
      (by norm_num [weakWeights, Fin.sum_univ_succ])) i
  norm_num [T3, cartanWeight, weakWeights] at h ⊢
  exact h

private theorem occupation_counts :
    (fun i : Fin 16 => SpinorWeights5.count (SpinorWeights5.evenWeight i).1) =
      ![0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 2] := by decide

private theorem spinor_chi (i : Fin 16) :
    qChi (.inl i) = ![5, 1, 1, 1, 1, 1, 1, 1, 1, 1, -3, -3, -3, -3, -3, 1] i := by
  change 5 - 2 * (SpinorWeights5.count (SpinorWeights5.evenWeight i).1 : ℝ) = _
  rw [congrFun occupation_counts i]
  fin_cases i <;> norm_num

/-- The spinor hypercharge and weak actions are the neighboring SM enumeration. -/
theorem spinor_sm_bridge :
    (fun i : Fin 16 => Y (spinor i)) = Fin.cons 0 GaugeUnificationRG4D.sm15Y ∧
    (fun i : Fin 16 => T3 (spinor i)) = Fin.cons 0 GaugeUnificationRG4D.sm15T3 := by
  constructor
  · change (fun i => SpinorWeights5.cartan hyperchargeWeights (SpinorWeights5.evenWeight i).1) = _
    rw [SU5SO10GrandUnification4D.so10_su5_fermion_branching _
      (by norm_num [hyperchargeWeights, Fin.sum_univ_succ]),
      SU5SO10GrandUnification4D.su5_bar5_plus_10_matches_sm_hypercharges.1]
  · change (fun i => SpinorWeights5.cartan weakWeights (SpinorWeights5.evenWeight i).1) = _
    rw [SU5SO10GrandUnification4D.so10_su5_fermion_branching _
      (by norm_num [weakWeights, Fin.sum_univ_succ]),
      SU5SO10GrandUnification4D.su5_bar5_plus_10_matches_sm_hypercharges.2.1]

theorem spinor_occupation_bridge (i : Fin 16) :
    Y (spinor i) = SpinorWeights5.hypercharge (SpinorWeights5.evenWeight i).1 ∧
    T3 (spinor i) = SpinorWeights5.t3L (SpinorWeights5.evenWeight i).1 ∧
    Q (spinor i) = SpinorWeights5.electricCharge (SpinorWeights5.evenWeight i).1 ∧
    qChi (spinor i) = SpinorWeights5.xCharge (SpinorWeights5.evenWeight i).1 ∧
    bMinusL (spinor i) = SpinorWeights5.bMinusL (SpinorWeights5.evenWeight i).1 := by
  have hy : Y (spinor i) = SpinorWeights5.hypercharge (SpinorWeights5.evenWeight i).1 := by
    change SpinorWeights5.cartan hyperchargeWeights _ = _
    rw [SpinorWeights5.cartan_eq_occupation_shift]
    norm_num [hyperchargeWeights, Fin.sum_univ_succ,
      SpinorWeights5.hypercharge, SpinorWeights5.hyperchargeCoefficients]
  have ht : T3 (spinor i) = SpinorWeights5.t3L (SpinorWeights5.evenWeight i).1 := by
    change SpinorWeights5.cartan weakWeights _ = _
    simp [SpinorWeights5.cartan, weakWeights, SpinorWeights5.t3L, Fin.sum_univ_succ]
    ring
  refine ⟨hy, ht, ?_, rfl, ?_⟩
  · have hy0 : ∑ j, hyperchargeWeights j = 0 := by
      norm_num [hyperchargeWeights, Fin.sum_univ_succ]
    have ht0 : ∑ j, weakWeights j = 0 := by
      norm_num [weakWeights, Fin.sum_univ_succ]
    change SpinorWeights5.cartan weakWeights _ +
      SpinorWeights5.cartan hyperchargeWeights _ = _
    simp only [SpinorWeights5.cartan_eq_occupation_shift, hy0, ht0,
      zero_div, sub_zero]
    change SpinorWeights5.occupationAction SpinorWeights5.weakCoefficients _ +
      SpinorWeights5.occupationAction
        SpinorWeights5.hyperchargeCoefficients _ = _
    simp [SpinorWeights5.electricCharge, SpinorWeights5.occupationAction,
      Finset.sum_add_distrib, add_comm]
  · simp only [bMinusL, hy, SpinorWeights5.bMinusL]
    rfl

/-- A finite trace formula retaining the spinor, fundamental, dual and singlet blocks. -/
private theorem trace_expand (f : ℝ → ℝ → ℝ → ℝ → ℝ) :
    (∑ s : E6Rep27, f (Y s) (T3 s) (qPsi s) (qChi s)) =
      (∑ i : Fin 16, f
        (![0, 1/6, 1/6, 1/6, 1/6, 1/6, 1/6, -2/3, -2/3, -2/3,
          1/3, 1/3, 1/3, -1/2, -1/2, 1] i)
        (![0, 1/2, -1/2, 1/2, -1/2, 1/2, -1/2, 0, 0, 0, 0, 0, 0, 1/2, -1/2, 0] i)
        1 (![5, 1, 1, 1, 1, 1, 1, 1, 1, 1, -3, -3, -3, -3, -3, 1] i)) +
      ((∑ i : Fin 5, f (hyperchargeWeights i) (weakWeights i) (-2) (-2)) +
       (∑ i : Fin 5, f (-hyperchargeWeights i) (-weakWeights i) (-2) 2) +
       f 0 0 4 0) := by
  simp only [Fintype.sum_sum_type]
  simp only [spinor_y, spinor_t3, spinor_chi]
  simp [Y, T3, cartanWeight, qPsi, qChi]

theorem linear_traces :
    (∑ s : E6Rep27, Y s) = 0 ∧ (∑ s : E6Rep27, T3 s) = 0 ∧
    (∑ s : E6Rep27, Q s) = 0 ∧ (∑ s : E6Rep27, qPsi s) = 0 ∧
    (∑ s : E6Rep27, qChi s) = 0 ∧ (∑ s : E6Rep27, bMinusL s) = 0 := by
  have h (a b c d : ℝ) :
      (∑ s : E6Rep27, (a * Y s + b * T3 s + c * qPsi s + d * qChi s)) = 0 := by
    change (∑ s : E6Rep27, (fun y t p x => a*y+b*t+c*p+d*x)
      (Y s) (T3 s) (qPsi s) (qChi s)) = 0
    rw [trace_expand (fun y t p x => a*y+b*t+c*p+d*x)]
    norm_num [hyperchargeWeights, weakWeights, Fin.sum_univ_succ]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using h 1 0 0 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using h 0 1 0 0
  · simpa only [Q, one_mul, zero_mul, mul_zero, zero_add, add_zero, add_comm] using h 1 1 0 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using h 0 0 1 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using h 0 0 0 1
  · convert h (4/5) 0 0 (1/5) using 1
    apply Finset.sum_congr rfl
    intro s _
    dsimp [bMinusL]
    ring

theorem trace_pairing (a b c d e f g h : ℝ) :
    (∑ s : E6Rep27, (a*Y s+b*T3 s+c*qPsi s+d*qChi s) *
      (e*Y s+f*T3 s+g*qPsi s+h*qChi s)) = 5*a*e+3*b*f+72*c*g+120*d*h := by
  rw [trace_expand (fun y t p x =>
    (a*y+b*t+c*p+d*x)*(e*y+f*t+g*p+h*x))]
  norm_num [hyperchargeWeights,
    weakWeights, Fin.sum_univ_succ]
  ring

theorem pairwise_orthogonality :
    (∑ s : E6Rep27, Y s * T3 s) = 0 ∧
    (∑ s : E6Rep27, Y s * qPsi s) = 0 ∧
    (∑ s : E6Rep27, Y s * qChi s) = 0 ∧
    (∑ s : E6Rep27, T3 s * qPsi s) = 0 ∧
    (∑ s : E6Rep27, T3 s * qChi s) = 0 ∧
    (∑ s : E6Rep27, qPsi s * qChi s) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 1 0 0 0 0 1 0 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 1 0 0 0 0 0 1 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 1 0 0 0 0 0 0 1
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 1 0 0 0 0 1 0
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 1 0 0 0 0 0 1
  · simpa only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 0 1 0 0 0 0 1

theorem quadratic_traces :
    (∑ s : E6Rep27, (T3 s)^2) = 3 ∧ (∑ s : E6Rep27, (Y s)^2) = 5 ∧
    (∑ s : E6Rep27, (Q s)^2) = 8 ∧ (∑ s : E6Rep27, (qPsi s)^2) = 72 ∧
    (∑ s : E6Rep27, (qChi s)^2) = 120 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_two, one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 1 0 0 0 1 0 0
  · simpa only [pow_two, one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 1 0 0 0 1 0 0 0
  · have h := trace_pairing 1 1 0 0 1 1 0 0
    norm_num only [one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] at h
    simpa only [Q, pow_two, add_comm] using h
  · simpa only [pow_two, one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 0 1 0 0 0 1 0
  · simpa only [pow_two, one_mul, zero_mul, mul_zero, mul_one, zero_add, add_zero] using
      trace_pairing 0 0 0 1 0 0 0 1

theorem weinberg_trace_ratio :
    (∑ s : E6Rep27, (T3 s)^2) / (∑ s : E6Rep27, (Q s)^2) = 3/8 := by
  norm_num [quadratic_traces.1, quadratic_traces.2.2.1]

/-- All cubic abelian anomalies vanish, including every polarized mixed coefficient. -/
theorem universal_abelian_cubic (a b c d : ℝ) :
    (∑ s : E6Rep27, (a * Y s + b * T3 s + c * qPsi s + d * qChi s)^3) = 0 := by
  change (∑ s : E6Rep27, (fun y t p x => (a*y+b*t+c*p+d*x)^3)
    (Y s) (T3 s) (qPsi s) (qChi s)) = 0
  rw [trace_expand (fun y t p x => (a*y+b*t+c*p+d*x)^3)]
  norm_num [hyperchargeWeights, weakWeights, Fin.sum_univ_succ]
  ring

/-- Every trilinear mixed abelian anomaly, with repeated generators allowed. -/
theorem mixed_abelian_cubic (a b c d e f g h i j k l : ℝ) :
    (∑ s : E6Rep27,
      (a*Y s+b*T3 s+c*qPsi s+d*qChi s) *
      (e*Y s+f*T3 s+g*qPsi s+h*qChi s) *
      (i*Y s+j*T3 s+k*qPsi s+l*qChi s)) = 0 := by
  change (∑ s : E6Rep27, (fun y t p x =>
    (a*y+b*t+c*p+d*x)*(e*y+f*t+g*p+h*x)*(i*y+j*t+k*p+l*x))
    (Y s) (T3 s) (qPsi s) (qChi s)) = 0
  rw [trace_expand (fun y t p x =>
    (a*y+b*t+c*p+d*x)*(e*y+f*t+g*p+h*x)*(i*y+j*t+k*p+l*x))]
  norm_num [hyperchargeWeights, weakWeights, Fin.sum_univ_succ]
  ring

inductive ColorSector where
  | triplet | antitriplet | singlet
  deriving DecidableEq

def colorSector : E6Rep27 → ColorSector
  | .inl i => ![.singlet, .triplet, .triplet, .triplet, .triplet, .triplet, .triplet,
      .antitriplet, .antitriplet, .antitriplet, .antitriplet, .antitriplet,
      .antitriplet, .singlet, .singlet, .singlet] i
  | .inr (.inl (.inl i)) => if i.val < 3 then .triplet else .singlet
  | .inr (.inl (.inr i)) => if i.val < 3 then .antitriplet else .singlet
  | .inr (.inr _) => .singlet

def colorLabel : E6Rep27 → Option (Fin 3)
  | .inl i => ![none, some 0, some 0, some 1, some 1, some 2, some 2,
      some 2, some 1, some 0, some 0, some 1, some 2, none, none, none] i
  | .inr (.inl (.inl i)) | .inr (.inl (.inr i)) =>
      if h : i.val < 3 then some ⟨i.val, h⟩ else none
  | .inr (.inr _) => none

/-- Each colored component contributes one third of the multiplet Dynkin index. -/
def colorIndex (s : E6Rep27) : ℝ := if colorSector s = .singlet then 0 else 1/6

def colorCubic (s : E6Rep27) : ℝ := match colorSector s with
  | .triplet => 1/3
  | .antitriplet => -1/3
  | .singlet => 0

theorem color_content :
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .triplet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .antitriplet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .singlet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .triplet).card / 3 = 3 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .antitriplet).card / 3 = 3 := by
  decide

theorem color_anomalies :
    (∑ s : E6Rep27, colorCubic s) = 0 ∧
    ∀ a b c d : ℝ,
      (∑ s : E6Rep27, colorIndex s * (a*Y s+b*T3 s+c*qPsi s+d*qChi s)) = 0 := by
  constructor
  · norm_num [Fintype.sum_sum_type, colorCubic, colorSector, Fin.sum_univ_succ]
  · intro a b c d
    simp only [Fintype.sum_sum_type]
    simp only [spinor_y, spinor_t3, spinor_chi]
    norm_num [colorIndex, colorSector, qPsi, Y, T3, qChi, cartanWeight,
      hyperchargeWeights, weakWeights, Fin.sum_univ_succ]
    ring

/-- Diagonal generators on the left and right trinification factors. -/
def HL : Fin 3 → ℝ := ![-1/6, -1/6, 1/3]
def HR : Fin 3 → ℝ := ![-2/3, 1/3, 1/3]
def T3L : Fin 3 → ℝ := ![1/2, -1/2, 0]

def entryY : Entry → ℝ
  | .inl (_, j) => -HL j
  | .inr (.inl (i, j)) => HL i - HR j
  | .inr (.inr (i, _)) => HR i

def entryT3 : Entry → ℝ
  | .inl (_, j) => -T3L j
  | .inr (.inl (i, _)) => T3L i
  | .inr (.inr _) => 0

def entryCartan (left right : Fin 3 → ℝ) : Entry → ℝ
  | .inl (_, j) => -left j
  | .inr (.inl (i, j)) => left i - right j
  | .inr (.inr (i, _)) => right i

def entryPsi : Entry → ℝ := entryCartan ![-1, -1, 2] ![1, 1, -2]
def entryChi : Entry → ℝ := entryCartan ![-1, -1, 2] ![1, -3, 2]
def entryBMinusL (e : Entry) : ℝ := (entryChi e + 4 * entryY e) / 5

def entryColorSector : Entry → ColorSector
  | .inl _ => .triplet
  | .inr (.inl _) => .singlet
  | .inr (.inr _) => .antitriplet

def entryColorLabel : Entry → Option (Fin 3)
  | .inl (i, _) => some i
  | .inr (.inl _) => none
  | .inr (.inr (_, j)) => some j

def toEntry : E6Rep27 → Entry
  | .inl i => ![.inr (.inl (2, 1)),
      .inl (0, 1), .inl (0, 0), .inl (1, 1), .inl (1, 0), .inl (2, 1), .inl (2, 0),
      .inr (.inr (0, 2)), .inr (.inr (0, 1)), .inr (.inr (0, 0)),
      .inr (.inr (1, 0)), .inr (.inr (1, 1)), .inr (.inr (1, 2)),
      .inr (.inl (0, 2)), .inr (.inl (1, 2)), .inr (.inl (2, 0))] i
  | .inr (.inl (.inl i)) =>
      ![.inl (0, 2), .inl (1, 2), .inl (2, 2), .inr (.inl (0, 0)), .inr (.inl (1, 0))] i
  | .inr (.inl (.inr i)) => ![.inr (.inr (2, 0)), .inr (.inr (2, 1)),
      .inr (.inr (2, 2)), .inr (.inl (1, 1)), .inr (.inl (0, 1))] i
  | .inr (.inr _) => .inr (.inl (2, 2))

def fromEntry : Entry → E6Rep27
  | .inl (i, j) =>
      ![![spinor 2, spinor 1, fundamental 0], ![spinor 4, spinor 3, fundamental 1],
        ![spinor 6, spinor 5, fundamental 2]] i j
  | .inr (.inl (i, j)) =>
      ![![fundamental 3, antifundamental 4, spinor 13],
        ![fundamental 4, antifundamental 3, spinor 14], ![spinor 15, spinor 0, neutral]] i j
  | .inr (.inr (i, j)) => ![![spinor 9, spinor 8, spinor 7],
      ![spinor 10, spinor 11, spinor 12],
      ![antifundamental 0, antifundamental 1, antifundamental 2]] i j

/-- An explicit inverse pair identifies every one of the 27 entries. -/
def e6_27_equiv_trinif : E6Rep27 ≃ Entry where
  toFun := toEntry
  invFun := fromEntry
  left_inv := by decide
  right_inv := by decide

theorem trinification_weights (s : E6Rep27) :
    entryY (e6_27_equiv_trinif s) = Y s ∧
    entryT3 (e6_27_equiv_trinif s) = T3 s ∧
    entryT3 (e6_27_equiv_trinif s) + entryY (e6_27_equiv_trinif s) = Q s := by
  have h : entryY (toEntry s) = Y s ∧ entryT3 (toEntry s) = T3 s := by
    rcases s with i | ((i | i) | u)
    · rw [spinor_y, spinor_t3]
      fin_cases i <;> norm_num [toEntry, entryY, entryT3, HL, HR, T3L]
    · fin_cases i <;> norm_num [toEntry, entryY, entryT3, HL, HR, T3L,
        Y, T3, cartanWeight, hyperchargeWeights, weakWeights]
    · fin_cases i <;> norm_num [toEntry, entryY, entryT3, HL, HR, T3L,
        Y, T3, cartanWeight, hyperchargeWeights, weakWeights]
    · cases u
      norm_num [toEntry, entryY, entryT3, HL, HR, T3L, Y, T3, cartanWeight]
  exact ⟨h.1, h.2, by change entryT3 (toEntry s) + entryY (toEntry s) = _; rw [h.1, h.2]; rfl⟩

theorem trinification_extra_charges (s : E6Rep27) :
    entryPsi (e6_27_equiv_trinif s) = qPsi s ∧
    entryChi (e6_27_equiv_trinif s) = qChi s ∧
    entryBMinusL (e6_27_equiv_trinif s) = bMinusL s := by
  have h : entryPsi (toEntry s) = qPsi s ∧ entryChi (toEntry s) = qChi s := by
    rcases s with i | ((i | i) | u)
    · rw [spinor_chi]
      fin_cases i <;> norm_num [toEntry, entryPsi, entryChi, entryCartan, qPsi]
    · fin_cases i <;> norm_num [toEntry, entryPsi, entryChi, entryCartan, qPsi, qChi]
    · fin_cases i <;> norm_num [toEntry, entryPsi, entryChi, entryCartan, qPsi, qChi]
    · cases u
      norm_num [toEntry, entryPsi, entryChi, entryCartan, qPsi, qChi]
  refine ⟨h.1, h.2, ?_⟩
  exact congrArg₂ (fun x y : ℝ => (x + 4 * y) / 5)
    h.2 (trinification_weights s).1

theorem trinification_color (s : E6Rep27) :
    entryColorSector (e6_27_equiv_trinif s) = colorSector s ∧
    entryColorLabel (e6_27_equiv_trinif s) = colorLabel s := by
  revert s
  decide

abbrev E6Ambient := OmegaMath.ExceptionalSix.Ambient

noncomputable abbrev e6Roots := OmegaMath.ExceptionalSix.roots
abbrev H6 := OmegaMath.ExceptionalSix.rankSix
noncomputable abbrev e6SimpleRoot := OmegaMath.ExceptionalSix.simple
abbrev e6Cartan := OmegaMath.ExceptionalSix.cartan

theorem e6Roots_card : e6Roots.card = 72 := OmegaMath.ExceptionalSix.card_roots

theorem e6Roots_in_rank6_subspace :
    (∀ α ∈ e6Roots, α ∈ H6) ∧ Module.finrank ℝ H6 = 6 :=
  OmegaMath.ExceptionalSix.roots_rank_six

theorem e6_lie_algebra_dimension : Module.finrank ℝ H6 + e6Roots.card = 78 := by
  rw [e6Roots_in_rank6_subspace.2, e6Roots_card]

theorem e6Roots_simply_laced {α : E6Ambient} (hα : α ∈ e6Roots) :
    ⟪α, α⟫_ℝ = 2 :=
  OmegaMath.ExceptionalSix.root_norm hα

theorem e6Roots_crystallographic_inner_products {α β : E6Ambient}
    (hα : α ∈ e6Roots) (hβ : β ∈ e6Roots) :
    ⟪α, β⟫_ℝ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪α, β⟫_ℝ = 2 ↔ α = β) ∧ (⟪α, β⟫_ℝ = -2 ↔ α = -β) :=
  OmegaMath.ExceptionalSix.root_products hα hβ

theorem e6Roots_weyl_reflection_closed {α β : E6Ambient}
    (hα : α ∈ e6Roots) (hβ : β ∈ e6Roots) :
    β - ⟪α, β⟫_ℝ • α ∈ e6Roots ∧ -α ∈ e6Roots := by
  refine ⟨OmegaMath.ExceptionalSix.root_reflection hα hβ, ?_⟩
  have h := OmegaMath.ExceptionalSix.root_reflection hα hα
  rw [e6Roots_simply_laced hα, two_smul] at h
  simpa [sub_add_eq_sub_sub] using h

theorem e6_dynkin_simple_roots :
    (∀ i, e6SimpleRoot i ∈ e6Roots) ∧
    (∀ i j, ⟪e6SimpleRoot i, e6SimpleRoot j⟫_ℝ = (e6Cartan i j : ℝ)) ∧
    e6Cartan.det = 3 ∧
    LinearIndependent ℝ e6SimpleRoot ∧
    (∀ α ∈ e6Roots, ∃ c : Fin 6 → ℤ, α = ∑ i, (c i : ℝ) • e6SimpleRoot i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0))) :=
  OmegaMath.ExceptionalSix.simple_system

theorem e6_root_span : Submodule.span ℝ (e6Roots : Set E6Ambient) = H6 := by
  have hsub : Submodule.span ℝ (Set.range e6SimpleRoot) ≤
      Submodule.span ℝ (e6Roots : Set E6Ambient) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact e6_dynkin_simple_roots.1 i)
  apply Submodule.eq_of_le_of_finrank_le
    (Submodule.span_le.mpr e6Roots_in_rank6_subspace.1)
  rw [e6Roots_in_rank6_subspace.2, ← Fintype.card_fin 6,
    ← finrank_span_eq_card e6_dynkin_simple_roots.2.2.2.1]
  exact Submodule.finrank_mono hsub

theorem trinification_diagonal_generators :
    Matrix.trace (Matrix.diagonal HL) = 0 ∧
    Matrix.trace (Matrix.diagonal HR) = 0 ∧
    Matrix.trace (Matrix.diagonal T3L) = 0 ∧ HR = HL - T3L := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [HL, Matrix.trace_diagonal, Fin.sum_univ_three]
  · norm_num [HR, Matrix.trace_diagonal, Fin.sum_univ_three]
  · norm_num [T3L, Matrix.trace_diagonal, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> norm_num [HL, HR, T3L]

abbrev Trinif27 := OmegaMath.CyclicMatrixCubic.Triple ℂ
abbrev TrinifGroup := OmegaMath.CyclicMatrixCubic.Group ℂ

def matrixEntry (x : Trinif27) : Entry → ℂ
  | .inl (i, j) => x.1 i j
  | .inr (.inl (i, j)) => x.2.1 i j
  | .inr (.inr (i, j)) => x.2.2 i j

theorem trinif_dimension :
    Module.finrank ℂ Trinif27 = 27 ∧
    ∀ x y : Trinif27, (∀ s : E6Rep27,
      matrixEntry x (e6_27_equiv_trinif s) = matrixEntry y (e6_27_equiv_trinif s)) ↔ x = y := by
  refine ⟨?_, ?_⟩
  · norm_num [Trinif27, OmegaMath.CyclicMatrixCubic.Triple, Module.finrank_prod,
      Module.finrank_matrix]
  · intro x y
    constructor
    · intro h
      have allEntries (e : Entry) : matrixEntry x e = matrixEntry y e := by
        obtain ⟨s, rfl⟩ := e6_27_equiv_trinif.surjective e
        exact h s
      refine Prod.ext (Matrix.ext fun i j => allEntries (.inl (i, j))) (Prod.ext ?_ ?_)
      · exact Matrix.ext fun i j => allEntries (.inr (.inl (i, j)))
      · exact Matrix.ext fun i j => allEntries (.inr (.inr (i, j)))
    · rintro rfl _
      rfl

def cyc (x : Trinif27) : Trinif27 := OmegaMath.CyclicMatrixCubic.rotate x

theorem trinif_cyclic_equivariance (g : TrinifGroup) (x : Trinif27) :
    cyc (g • x) = OmegaMath.CyclicMatrixCubic.rotateGroup g • cyc x ∧
    cyc (cyc (cyc x)) = x :=
  OmegaMath.CyclicMatrixCubic.rotation_intertwines g x

theorem trinif_action_kernel (g : TrinifGroup) :
    (∀ x : Trinif27, g • x = x) ↔
      ∃ z : ℂ, z ^ 3 = 1 ∧ (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z ∧
        (g.2.1 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z ∧
        (g.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) z :=
  OmegaMath.CyclicMatrixCubic.action_kernel g

theorem trinif_cartan_cubic_anomaly (a b c : Fin 3 → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) :
    (∑ x : OmegaMath.CyclicMatrixCubic.Entry,
      OmegaMath.CyclicMatrixCubic.differenceWeight a b c x ^ 3) = 0 :=
  OmegaMath.CyclicMatrixCubic.total_cubic_trace a b c ha hb hc

abbrev TrinifMatrix := Matrix (Fin 3) (Fin 3) ℂ

noncomputable def freudenthalCubic (Q L Qc : TrinifMatrix) : ℂ :=
  OmegaMath.CyclicMatrixCubic.cubic Q L Qc

theorem freudenthalCubic_sl3_cubed_invariant (Q L Qc a b c : TrinifMatrix)
    (ha : a.det = 1) (hb : b.det = 1) (hc : c.det = 1) :
    freudenthalCubic (a * Q * b⁻¹) (b * L * c⁻¹) (c * Qc * a⁻¹) =
      freudenthalCubic Q L Qc :=
  OmegaMath.CyclicMatrixCubic.cubic_plain_matrices Q L Qc a b c ha hb hc

theorem freudenthalCubic_z3_cyclic_invariant (Q L Qc : TrinifMatrix) :
    freudenthalCubic L Qc Q = freudenthalCubic Q L Qc :=
  OmegaMath.CyclicMatrixCubic.cubic_rotate Q L Qc

theorem freudenthalCubic_homogeneous_degree_3 (z : ℂ) (Q L Qc : TrinifMatrix) :
    freudenthalCubic (z • Q) (z • L) (z • Qc) = z ^ 3 * freudenthalCubic Q L Qc :=
  OmegaMath.CyclicMatrixCubic.cubic_scale z Q L Qc

abbrev E6CubicGroup : Subgroup (Trinif27 ≃ₗ[ℂ] Trinif27) :=
  OmegaMath.CyclicMatrixCubic.stabilizer

def trinifInCubicGroup : TrinifGroup →* E6CubicGroup :=
  OmegaMath.CyclicMatrixCubic.toStabilizer

def rotationInCubicGroup : E6CubicGroup :=
  OmegaMath.CyclicMatrixCubic.rotationInStabilizer

theorem trinif_cubic_stabilizer (g : TrinifGroup) :
    rotationInCubicGroup * trinifInCubicGroup g =
      trinifInCubicGroup (OmegaMath.CyclicMatrixCubic.rotateGroup g) * rotationInCubicGroup ∧
    rotationInCubicGroup ^ 3 = 1 ∧ rotationInCubicGroup ≠ 1 := by
  have h := OmegaMath.CyclicMatrixCubic.stabilizer_rotation g
  refine ⟨h.1, h.2, ?_⟩
  intro he
  have h₁ := congrArg (fun a : E6CubicGroup => (a.val ((1, 0, 0) : Trinif27)).1 0 0) he
  change (0 : ℂ) = (1 : TrinifMatrix) 0 0 at h₁
  simp at h₁

/-- The two quark couplings occupy right indices zero and one.
In the lepton block the weak rows are zero and one, and the singlet row is two. -/
theorem freudenthalCubic_contains_sm_yukawa (Q L Qc : TrinifMatrix) :
    freudenthalCubic Q L Qc =
      Q.det + Qc.det
      - (∑ i : Fin 3, (Q i 0 * L 0 0 + Q i 1 * L 1 0) * Qc 0 i)
      - (∑ i : Fin 3, (Q i 0 * L 0 1 + Q i 1 * L 1 1) * Qc 1 i)
      - (∑ i : Fin 3, (
        (Q i 0 * L 0 2 + Q i 1 * L 1 2 + Q i 2 * L 2 2) * Qc 2 i +
        Q i 2 * (L 2 0 * Qc 0 i + L 2 1 * Qc 1 i)))
      + (L 0 1 * L 1 2 - L 0 2 * L 1 1) * L 2 0
      + (L 0 2 * L 1 0 - L 0 0 * L 1 2) * L 2 1
      + (L 0 0 * L 1 1 - L 0 1 * L 1 0) * L 2 2 := by
  simp only [freudenthalCubic, OmegaMath.CyclicMatrixCubic.cubic, Matrix.det_fin_three,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  ring

end D5.S3.Quantum.Gauge.E6TrinificationUnification4D
