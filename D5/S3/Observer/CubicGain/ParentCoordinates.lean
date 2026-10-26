/- GID: D5/S3/Observer/CubicGain/ParentCoordinates
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/ParentCoordinates
   mirror-E: none(waiver:whole-world-algebraic-correspondence)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Literal chronological matrix readings and one cubic gain give the zero-safe full parent coordinates. -/

import D5.S3.Observer.CubicGain.StrictDriftVector
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The gain is represented by its four original samples, with no degree restriction
beyond degree at most three. The polynomial uniqueness argument is Mathlib's. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Observer.CubicGain

abbrev Gain := Fin 4 → ℝ
abbrev Coordinates := ℝ × ℝ × ℝ
abbrev World := ℝ × ℝ × ℝ × Gain

/-- One whole real gain, represented in fixed-node Lagrange coordinates. -/
def gain (a : Gain) (s : ℝ) : ℝ :=
  -a 0*(s-1)*(s-2)*(s-3)/6 + a 1*s*(s-2)*(s-3)/2 -
    a 2*s*(s-1)*(s-3)/2 + a 3*s*(s-1)*(s-2)/6

def gainPoly (a : Gain) : Polynomial ℝ :=
  let X := Polynomial.X
  Polynomial.C (-a 0/6)*(X-1)*(X-2)*(X-3) +
  Polynomial.C (a 1/2)*X*(X-2)*(X-3) -
  Polynomial.C (a 2/2)*X*(X-1)*(X-3) +
  Polynomial.C (a 3/6)*X*(X-1)*(X-2)

theorem gainPoly_eval (a : Gain) (s : ℝ) : (gainPoly a).eval s = gain a s := by
  simp [gainPoly, gain]
  ring

theorem gain_samples (a : Gain) (i : Fin 4) : gain a (i : ℕ) = a i := by
  fin_cases i <;> norm_num [gain] <;> ring

theorem gainPoly_degree (a : Gain) : (gainPoly a).degree < 4 := by
  have h : (gainPoly a).degree ≤ 3 := by dsimp [gainPoly]; compute_degree
  exact lt_of_le_of_lt h (by norm_num)

/-- Every real polynomial of degree at most three is this one whole gain.
No exact-degree or nonzero-sample premise is used. -/
theorem polynomial_representation (g : Polynomial ℝ) (hg : g.degree ≤ 3) :
    g = gainPoly (fun i : Fin 4 => g.eval (i : ℕ)) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := Finset.univ) (v := fun i : Fin 4 => (i : ℝ))
  · intro i _ j _ hij
    exact Fin.ext (Nat.cast_injective hij)
  · simpa using lt_of_le_of_lt hg (show (3 : WithBot ℕ) < 4 by norm_num)
  · simpa using gainPoly_degree (fun i : Fin 4 => g.eval (i : ℕ))
  · intro i _
    rw [gainPoly_eval, gain_samples]

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def sourceMatrix (r b : ℝ) : Mat := !![r,b; r*(1-r)/b,1-r]
def actionJ : Mat := !![0,1; 1,0]
def actionM : Mat := !![0,1; 1,1]

/-- The product is formed by chronological left multiplication. -/
def chronological (i : ℕ) : Mat :=
  ([actionJ,actionM,actionJ,actionM,actionM,actionM].take i).foldl
    (fun Q E => E * Q) 1

def traceAt (r b : ℝ) (i : ℕ) : ℝ :=
  Matrix.trace (chronological i * sourceMatrix r b)

def literalRead (W : World) (i : ℕ) : ℝ :=
  W.2.2.1 + gain W.2.2.2 i * traceAt W.1 W.2.1 i

def history : Fin 5 → ℝ := ![0,24,147/5,24,18]

def LiteralParent (W : World) : Prop :=
  0 < W.1 ∧ W.1 < 1 ∧ 0 < W.2.1 ∧
    ∀ i : Fin 5, literalRead W i = history i

def parentB (b : ℝ) : ℝ := 6/(1+b)-2/(1+2*b)
def parentEq (C : Coordinates) : ℝ :=
  C.2.2 * parentLambda C.1 C.2.1 + (24/5)*(C.2.1-1/8)*parentB C.2.1

def StrictParent (C : Coordinates) : Prop :=
  0 < C.1 ∧ C.1 < 1 ∧ 0 < C.2.1 ∧ parentEq C = 0

def parentGain (C : Coordinates) : Gain :=
  ![-24-C.2.2, -C.2.2/sourceJ C.1 C.2.1,
    (27/5-C.2.2)/(1+C.2.1), -C.2.2/sourceN C.1 C.2.1]

def parentWorld (C : Coordinates) : World :=
  (C.1,C.2.1,24+C.2.2,parentGain C)

def worldCoordinates (W : World) : Coordinates := (W.1,W.2.1,W.2.2.1-24)

def fifthResponse (C : Coordinates) : ℝ :=
  24+(1+2*C.2.1+sourceN C.1 C.2.1)*(96-108/(1+C.2.1)) +
    C.2.2*fifthDrift C.1 C.2.1

def sixthDrift (r b : ℝ) : ℝ :=
  1+(2*(1+2*b)+sourceN r b)*(10-36/sourceJ r b+45/(1+b)-20/sourceN r b)

def sixthResponse (C : Coordinates) : ℝ :=
  24+(2*(1+2*C.2.1)+sourceN C.1 C.2.1)*(240-243/(1+C.2.1)) +
    C.2.2*sixthDrift C.1 C.2.1

def response (C : Coordinates) : ℝ × ℝ := (fifthResponse C,sixthResponse C)

theorem literal_traces (r b : ℝ) :
    (fun i : Fin 7 => traceAt r b i) =
      ![1,sourceJ r b,1+b,sourceN r b,1+2*b,
        1+2*b+sourceN r b,2*(1+2*b)+sourceN r b] := by
  ext i
  fin_cases i <;>
    norm_num [traceAt, chronological, sourceMatrix, actionJ, actionM,
      Matrix.mul_apply, Matrix.trace, sourceN, sourceJ, Fin.sum_univ_two]
  all_goals ring

theorem source_positivity (r b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 < b) :
    0 < sourceJ r b ∧ 0 < sourceN r b ∧ 0 < 1+b ∧ 0 < 1+2*b := by
  have h : 0 ≤ r*(1-r)/b := div_nonneg (mul_nonneg hr (by linarith)) hb.le
  dsimp [sourceJ,sourceN]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> positivity

/-- All late readings use the same gain and the same drift as the parent. -/
theorem actual_m_responses (C : Coordinates) :
    literalRead (parentWorld C) 5 = fifthResponse C ∧
    literalRead (parentWorld C) 6 = sixthResponse C := by
  have h5 := congrFun (literal_traces C.1 C.2.1) (5 : Fin 7)
  have h6 := congrFun (literal_traces C.1 C.2.1) (6 : Fin 7)
  norm_num at h5 h6
  constructor
  · change 24+C.2.2+gain (parentGain C) 5*traceAt C.1 C.2.1 5 = _
    rw [h5]
    norm_num [gain,parentGain,fifthResponse,fifthDrift]
    ring
  · change 24+C.2.2+gain (parentGain C) 6*traceAt C.1 C.2.1 6 = _
    rw [h6]
    norm_num [gain,parentGain,sixthResponse,sixthDrift]
    ring

/-- A literal parent gain cannot be the zero polynomial, even if samples vanish. -/
theorem parent_gain_nonzero (W : World) (hW : LiteralParent W) : gainPoly W.2.2.2 ≠ 0 := by
  intro hz
  have h0 := hW.2.2.2 (0 : Fin 5)
  have h1 := hW.2.2.2 (1 : Fin 5)
  have e0 : gain W.2.2.2 0 = 0 := by rw [← gainPoly_eval,hz]; simp
  have e1 : gain W.2.2.2 1 = 0 := by rw [← gainPoly_eval,hz]; simp
  norm_num [literalRead,history,e0,e1] at h0 h1
  linarith

theorem fourth_residual (r b d : ℝ)
    (hj : sourceJ r b ≠ 0) (hn : sourceN r b ≠ 0)
    (ht : 1+b ≠ 0) (hu : 1+2*b ≠ 0) :
    d+gain (parentGain (r,b,d-24)) 4*(1+2*b)-18 =
      (1+2*b)*parentEq (r,b,d-24) := by
  unfold parentGain gain parentEq parentLambda parentB
  dsimp
  field_simp [hj,hn,ht,hu]
  <;> ring

/-- Exact equivalence of all five literal original rows with the full parent equation. -/
theorem parent_world_iff (W : World) :
    LiteralParent W ↔ StrictParent (worldCoordinates W) ∧
      parentWorld (worldCoordinates W) = W := by
  obtain ⟨r,b,d,a⟩ := W
  have traces := literal_traces r b
  have htr : ∀ i : Fin 5, traceAt r b i =
      (![1,sourceJ r b,1+b,sourceN r b,1+2*b] : Fin 5 → ℝ) i := by
    intro i
    fin_cases i
    · simpa using congrFun traces (0 : Fin 7)
    · simpa using congrFun traces (1 : Fin 7)
    · simpa using congrFun traces (2 : Fin 7)
    · simpa using congrFun traces (3 : Fin 7)
    · simpa using congrFun traces (4 : Fin 7)
  simp only [LiteralParent,StrictParent,worldCoordinates,parentWorld,Prod.mk.injEq]
  constructor
  · rintro ⟨hr,hr1,hb,hrows⟩
    obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
    have row0 := hrows 0
    have row1 := hrows 1
    have row2 := hrows 2
    have row3 := hrows 3
    have row4 := hrows 4
    have ht0 := htr 0
    have ht1 := htr 1
    have ht2 := htr 2
    have ht3 := htr 3
    have ht4 := htr 4
    norm_num at ht0 ht1 ht2 ht3 ht4
    norm_num [literalRead,history,gain,ht0,ht1,ht2,ht3,ht4] at row0 row1 row2 row3
    ring_nf at row0 row1 row2 row3
    have ha : a = parentGain (r,b,d-24) := by
      ext i
      fin_cases i <;> norm_num [parentGain]
      · linarith
      · apply (eq_div_iff (ne_of_gt hj)).mpr; linarith
      · apply (eq_div_iff (ne_of_gt ht)).mpr; linarith
      · apply (eq_div_iff (ne_of_gt hn)).mpr; linarith
    have hp : parentEq (r,b,d-24) = 0 := by
      have heq := fourth_residual r b d (ne_of_gt hj) (ne_of_gt hn) (ne_of_gt ht) (ne_of_gt hu)
      norm_num [literalRead,history,ha,ht4] at row4
      have hmul : (1+2*b)*parentEq (r,b,d-24)=0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hu)
    exact ⟨⟨hr,hr1,hb,hp⟩,trivial,trivial,by ring,ha.symm⟩
  · rintro ⟨⟨hr,hr1,hb,hp⟩,_,_,hd,ha⟩
    obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
    refine ⟨hr,hr1,hb,?_⟩
    intro i
    change d+gain a (i : ℕ)*traceAt r b i=history i
    rw [← ha,htr]
    fin_cases i
    · norm_num [history,parentGain,gain]; ring
    · norm_num [history,parentGain,gain]
      field_simp [ne_of_gt hj]; ring
    · norm_num [history,parentGain,gain]
      field_simp [ne_of_gt ht]; ring
    · norm_num [history,parentGain,gain]
      field_simp [ne_of_gt hn]; ring
    · have heq := fourth_residual r b d (ne_of_gt hj) (ne_of_gt hn) (ne_of_gt ht) (ne_of_gt hu)
      rw [hp,mul_zero] at heq
      norm_num [history,parentGain,gain] at heq ⊢
      linarith

#print axioms polynomial_representation
#print axioms actual_m_responses
#print axioms parent_world_iff

end D5.S3.Observer.CubicGain
