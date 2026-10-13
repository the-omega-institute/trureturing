import D5.S3.Geometry.Hyperideal.CFMP125FourAngleScalarTransient
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! Static candidate, not kernel checked. Exact native four-angle positive
right inverse on B4, retaining the six original edge occurrences. The canonical
source revision is 3c802974035773edc38eba4d7c0c3a0a019ab730 and mathlib is
pinned to db584cd6d46c92f209a44c0f1c829460d327499d. -/

set_option autoImplicit false
noncomputable section
namespace FourAngleNative
open FourAngleScalar
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (rad numerator cosine)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

/-- Strict four-angle domain with two independent axial coordinates. -/
def B4 (u : Quad) : Prop :=
  0 < u.r ∧ 0 < u.o ∧ 0 < u.a ∧ 0 < u.b ∧
    u.r + u.a + u.b < Real.pi ∧ u.o + u.a + u.b < Real.pi

/-- Actual six-slot order (12,13,14,34,24,23). -/
def J (z : Quad) : Fin 6 → ℝ := ![z.r,z.a,z.b,z.o,z.a,z.b]

def angleCos (u : Quad) : Quad :=
  ⟨Real.cos u.r, Real.cos u.o, Real.cos u.a, Real.cos u.b⟩

def Psi (u : Quad) : Quad :=
  let w := T (angleCos u)
  ⟨Real.arcosh w.r, Real.arcosh w.o, Real.arcosh w.a, Real.arcosh w.b⟩

/-- Cosine lengths after the coordinatewise positive part. -/
def lengthCos (q : Quad) : Fin 6 → ℝ :=
  fun i => Real.cosh (max (J q i) 0)

/-- Four-angle field extracted from the actual original extendedAngle. -/
def theta (q : Quad) : Quad :=
  ⟨extendedAngle (lengthCos q) 0, extendedAngle (lengthCos q) 3,
    extendedAngle (lengthCos q) 1, extendedAngle (lengthCos q) 2⟩

private theorem triangle_gap (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hsum : x+y+z < Real.pi) :
    0 < Real.sin y * Real.sin z ∧
    Real.sin y * Real.sin z < Real.cos x + Real.cos y * Real.cos z := by
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith : y < Real.pi)
  have hsz := Real.sin_pos_of_pos_of_lt_pi hz (by linarith : z < Real.pi)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hx.le
    (by linarith : Real.pi-(y+z) ≤ Real.pi)
    (by linarith : x < Real.pi-(y+z))
  rw [Real.cos_pi_sub, Real.cos_add] at hc
  exact ⟨mul_pos hsy hsz, by linarith⟩

/-- All positivity premises are derived from exactly B4. -/
private theorem b4_branch (u : Quad) (hu : B4 u) :
    0 < d (angleCos u) ∧ 0 < e (angleCos u) ∧ 0 < K (angleCos u) ∧
    1 < (T (angleCos u)).r ∧ 1 < (T (angleCos u)).o ∧
    1 < (T (angleCos u)).a ∧ 1 < (T (angleCos u)).b := by
  obtain ⟨hr,ho,ha,hb,hrsum,hosum⟩ := hu
  have hrpi : u.r < Real.pi := by linarith
  have hopi : u.o < Real.pi := by linarith
  have hapi : u.a < Real.pi := by linarith
  have hbpi : u.b < Real.pi := by linarith
  have cr := Real.mapsTo_cos_Ioo ⟨hr,hrpi⟩
  have co := Real.mapsTo_cos_Ioo ⟨ho,hopi⟩
  have cab := Real.mapsTo_cos_Ioo
    (show u.a+u.b ∈ Set.Ioo 0 Real.pi from ⟨by linarith, by linarith⟩)
  have gr := triangle_gap u.r u.a u.b hr ha hb hrsum
  have go := triangle_gap u.o u.a u.b ho ha hb hosum
  have gba := triangle_gap u.b u.a u.o hb ha ho (by linarith)
  have gab := triangle_gap u.a u.b u.o ha hb ho (by linarith)
  have sa : Real.sin u.a^2 = 1-Real.cos u.a^2 := by
    nlinarith [Real.sin_sq_add_cos_sq u.a]
  have sb : Real.sin u.b^2 = 1-Real.cos u.b^2 := by
    nlinarith [Real.sin_sq_add_cos_sq u.b]
  have hp2 : (Real.sin u.a * Real.sin u.b)^2 =
      (1-Real.cos u.a^2)*(1-Real.cos u.b^2) := by
    rw [mul_pow, sa, sb]
  have ht : Real.sin u.a * Real.sin u.b - Real.cos u.a * Real.cos u.b =
      -Real.cos (u.a+u.b) := by rw [Real.cos_add]; ring
  apply positive_branch (angleCos u) (Real.sin u.a * Real.sin u.b)
  · exact gr.1
  · exact hp2
  · exact gr.2
  · exact go.2
  · exact cr.2
  · exact co
  · change -1 < Real.sin u.a * Real.sin u.b - Real.cos u.a * Real.cos u.b ∧
      Real.sin u.a * Real.sin u.b - Real.cos u.a * Real.cos u.b < 1
    rw [ht]
    constructor <;> linarith [cab.1,cab.2]
  · change 0 < 1-Real.cos u.a^2
    rw [← sa]
    exact sq_pos_of_ne_zero (Real.sin_pos_of_pos_of_lt_pi ha hapi).ne'
  · change 0 < 1-Real.cos u.b^2
    rw [← sb]
    exact sq_pos_of_ne_zero (Real.sin_pos_of_pos_of_lt_pi hb hbpi).ne'
  · exact gba.1.trans gba.2
  · exact gab.1.trans gab.2

/-- Occurrence-by-occurrence bridge, using the canonical frame in all six cases. -/
private theorem rawCos_J (z : Quad) (hd : 0 < d z) (he : 0 < e z) :
    rawCos (J z) = J (T z) := by
  have hn : ∀ i : Fin 6, rawNum (J z) i = J ⟨Nr z,No z,Na z,Nb z⟩ i := by
    intro i
    fin_cases i <;> simp only [rawNum, frame, J, numerator, Nr, No, Na, Nb, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk] <;> norm_num <;> ring
  have hl : ∀ i : Fin 6, leftRad (J z) i = ![d z,e z,e z,e z,e z,e z] i := by
    intro i
    fin_cases i <;> simp only [leftRad, frame, J, rad, d, e, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk] <;> norm_num <;> ring
  have hr : ∀ i : Fin 6, rightRad (J z) i = ![d z,d z,d z,e z,d z,d z] i := by
    intro i
    fin_cases i <;> simp only [rightRad, frame, J, rad, d, e, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk] <;> norm_num <;> ring
  have hdd : Real.sqrt (d z) * Real.sqrt (d z) = d z := Real.mul_self_sqrt hd.le
  have hee : Real.sqrt (e z) * Real.sqrt (e z) = e z := Real.mul_self_sqrt he.le
  have hed : Real.sqrt (e z) * Real.sqrt (d z) = Real.sqrt (d z*e z) := by
    rw [Real.sqrt_mul hd.le]
    ring
  funext i
  change rawNum (J z) i / Real.sqrt (leftRad (J z) i) /
    Real.sqrt (rightRad (J z) i) = _
  rw [hn, hl, hr]
  fin_cases i <;> dsimp [J, T]
  · rw [div_div, hdd]
  · rw [div_div, hed]
  · rw [div_div, hed]
  · rw [div_div, hee]
  · rw [div_div, hed]
  · rw [div_div, hed]

/-- Exact positive right inverse. All six source occurrences are returned,
followed by the four-coordinate field in the original order (rho,omega,alpha,beta).
This declaration is an uncompiled candidate; validation belongs to the root task. -/
theorem native_positive_right_inverse (u : Quad) (hu : B4 u) :
    (0 < (Psi u).r ∧ 0 < (Psi u).o ∧ 0 < (Psi u).a ∧ 0 < (Psi u).b) ∧
    (∀ i : Fin 6, extendedAngle (lengthCos (Psi u)) i = J u i) ∧
    theta (Psi u) = u := by
  obtain ⟨hd,he,hk,hr,ho,ha,hb⟩ := b4_branch u hu
  have hpr : 0 < (Psi u).r := Real.arcosh_pos hr
  have hpo : 0 < (Psi u).o := Real.arcosh_pos ho
  have hpa : 0 < (Psi u).a := Real.arcosh_pos ha
  have hpb : 0 < (Psi u).b := Real.arcosh_pos hb
  have hl : lengthCos (Psi u) = J (T (angleCos u)) := by
    funext i
    have hpos : 0 ≤ J (Psi u) i := by
      fin_cases i <;> dsimp [J]
      all_goals first | exact hpr.le | exact hpo.le | exact hpa.le | exact hpb.le
    change Real.cosh (max (J (Psi u) i) 0) = _
    rw [max_eq_left hpos]
    fin_cases i <;> dsimp [J, Psi]
    · exact Real.cosh_arcosh hr.le
    · exact Real.cosh_arcosh ha.le
    · exact Real.cosh_arcosh hb.le
    · exact Real.cosh_arcosh ho.le
    · exact Real.cosh_arcosh ha.le
    · exact Real.cosh_arcosh hb.le
  obtain ⟨hdw,hew,hinv⟩ := transform_involution (angleCos u) hd he hk.ne'
  have hc : rawCos (lengthCos (Psi u)) = J (angleCos u) := by
    rw [hl, rawCos_J (T (angleCos u)) hdw hew, hinv]
  obtain ⟨ur,uo,ua,ub,ursum,uosum⟩ := hu
  have hui : ∀ i : Fin 6, 0 ≤ J u i ∧ J u i ≤ Real.pi := by
    intro i
    fin_cases i <;> dsimp [J] <;> constructor <;> linarith
  have hjc : ∀ i : Fin 6, J (angleCos u) i = Real.cos (J u i) := by
    intro i
    fin_cases i <;> rfl
  have hang : ∀ i : Fin 6, extendedAngle (lengthCos (Psi u)) i = J u i := by
    intro i
    unfold extendedAngle
    rw [congrFun hc i, hjc]
    rw [min_eq_left (Real.cos_le_one _), max_eq_right (Real.neg_one_le_cos _)]
    exact Real.arccos_cos (hui i).1 (hui i).2
  refine ⟨⟨hpr,hpo,hpa,hpb⟩, hang, ?_⟩
  apply Quad.ext
  · exact hang 0
  · exact hang 3
  · exact hang 1
  · exact hang 2

end FourAngleNative

#print axioms FourAngleScalar.transform_involution
#print axioms FourAngleScalar.positive_branch
#print axioms FourAngleNative.native_positive_right_inverse
#check FourAngleNative.native_positive_right_inverse
