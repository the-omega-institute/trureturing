/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Positive polynomial certificates and exact rational Gram data for three levels. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
import D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfThreeLevelSupplier

universe u


/- All subsequent declarations are consumed preparation on this exact path.
The scalar normalization g removes square roots until Gram realization. -/
private def q (a b : ℝ) : ℝ := a^2+a*b+b^2
private def aux (a b : ℝ) : ℝ := 4*a^2+7*a*b+4*b^2
private def g (a b : ℝ) : ℝ := 3*(a+b)/(2*q a b)
private def psi (a b c : ℝ) : ℝ :=
  (2*c/3)*g a c*g c b + 3*c^3*(a*b+c*(a+b))/(q a b*q a c*q b c)
private def lam (a b : ℝ) : ℝ :=
  -a*(a-b)*(2*a^2+3*a*b+2*b^2)/(q a b*aux a b)
private def mu (a b : ℝ) : ℝ :=
  a*(8*a^3+19*a^2*b+15*a*b^2+3*b^3)/(q a b*aux a b)
private def pairF (a b : ℝ) : ℝ :=
  8*a^4+45*a^3*b+69*a^2*b^2+45*a*b^3+8*b^4
private def delta (a b c : ℝ) : ℝ :=
  -3*a*(a-b)*(a-c)*(a^2-b*c)*(b-c)^2*(2*a^2+3*a*b+3*a*c+2*b*c)/
    (q a b*q a c*aux a b*aux a c*q b c)

private theorem q_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < q a b := by
  unfold q
  positivity
private theorem aux_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < aux a b := by
  unfold aux
  positivity
private theorem g_symm (a b : ℝ) : g a b = g b a := by
  unfold g q
  congr 1 <;> ring
private theorem g_self {a : ℝ} (ha : 0 < a) : g a a = 1/a := by
  unfold g q
  field_simp [ha.ne'] <;> ring

/-- Coefficients are natural numerals; evaluation produces explicit kernel
arithmetic. Python only prints these numerals and does not justify a theorem. -/
private abbrev Term := ℕ × ℕ × ℕ × ℕ
private def monomial (t : Term) (a b c : ℝ) : ℝ :=
  (t.1 : ℝ) * a^t.2.1 * b^t.2.2.1 * c^t.2.2.2
private def evalTerms (ts : List Term) (a b c : ℝ) : ℝ :=
  (ts.map (fun t => monomial t a b c)).sum

private theorem monomial_pos (t : Term) (ht : 0 < t.1)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < monomial t a b c := by
  unfold monomial
  exact mul_pos (mul_pos (mul_pos (by exact_mod_cast ht)
    (pow_pos ha _)) (pow_pos hb _)) (pow_pos hc _)

private theorem evalTerms_pos (ts : List Term) (ht : ∀ t ∈ ts, 0 < t.1)
    (hne : ts ≠ []) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < evalTerms ts a b c := by
  unfold evalTerms
  apply List.sum_pos
  · intro x hx
    obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hx
    exact monomial_pos t (ht t htmem) ha hb hc
  · exact fun h => hne (List.map_eq_nil_iff.mp h)

private def hTerms : List Term :=
[
  (4, 4, 2, 0),
  (7, 4, 1, 1),
  (4, 4, 0, 2),
  (7, 3, 3, 0),
  (26, 3, 2, 1),
  (26, 3, 1, 2),
  (7, 3, 0, 3),
  (4, 2, 4, 0),
  (26, 2, 3, 1),
  (48, 2, 2, 2),
  (26, 2, 1, 3),
  (4, 2, 0, 4),
  (7, 1, 4, 1),
  (26, 1, 3, 2),
  (26, 1, 2, 3),
  (7, 1, 1, 4),
  (4, 0, 4, 2),
  (7, 0, 3, 3),
  (4, 0, 2, 4)
  ]
private def hPoly (a b c : ℝ) : ℝ := evalTerms hTerms a b c
private theorem hPoly_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < hPoly a b c := by
  apply evalTerms_pos hTerms _ _ ha hb hc
  · norm_num [hTerms]
  · simp [hTerms]
private theorem hPoly_identity (a b c : ℝ) :
    hPoly a b c = 4*(a+b+c)^2*(a*b+a*c+b*c)^2 -
      (a*b+a*c+b*c)^3 - (a+b+c)^3*a*b*c := by
  simp only [hPoly, hTerms, evalTerms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, monomial]
  ring

private def vTerms : List Term :=
[
  (512, 12, 2, 0),
  (896, 12, 1, 1),
  (512, 12, 0, 2),
  (3776, 11, 3, 0),
  (10124, 11, 2, 1),
  (9416, 11, 1, 2),
  (2652, 11, 0, 3),
  (9968, 10, 4, 0),
  (42848, 10, 3, 1),
  (61340, 10, 2, 2),
  (34704, 10, 1, 3),
  (6132, 10, 0, 4),
  (13488, 9, 5, 0),
  (88023, 9, 4, 1),
  (192984, 9, 3, 2),
  (176645, 9, 2, 3),
  (67520, 9, 1, 4),
  (8039, 9, 0, 5),
  (9968, 8, 6, 0),
  (100379, 8, 5, 1),
  (328895, 8, 4, 2),
  (460631, 8, 3, 3),
  (291998, 8, 2, 4),
  (78230, 8, 1, 5),
  (6240, 8, 0, 6),
  (3776, 7, 7, 0),
  (64583, 7, 6, 1),
  (324785, 7, 5, 2),
  (678605, 7, 4, 3),
  (659366, 7, 3, 4),
  (296576, 7, 2, 5),
  (54774, 7, 1, 6),
  (2688, 7, 0, 7),
  (512, 6, 8, 0),
  (21584, 6, 7, 1),
  (184229, 6, 6, 2),
  (590343, 6, 5, 3),
  (855768, 6, 4, 4),
  (590343, 6, 3, 5),
  (184229, 6, 2, 6),
  (21584, 6, 1, 7),
  (512, 6, 0, 8),
  (2688, 5, 8, 1),
  (54774, 5, 7, 2),
  (296576, 5, 6, 3),
  (659366, 5, 5, 4),
  (678605, 5, 4, 5),
  (324785, 5, 3, 6),
  (64583, 5, 2, 7),
  (3776, 5, 1, 8),
  (6240, 4, 8, 2),
  (78230, 4, 7, 3),
  (291998, 4, 6, 4),
  (460631, 4, 5, 5),
  (328895, 4, 4, 6),
  (100379, 4, 3, 7),
  (9968, 4, 2, 8),
  (8039, 3, 8, 3),
  (67520, 3, 7, 4),
  (176645, 3, 6, 5),
  (192984, 3, 5, 6),
  (88023, 3, 4, 7),
  (13488, 3, 3, 8),
  (6132, 2, 8, 4),
  (34704, 2, 7, 5),
  (61340, 2, 6, 6),
  (42848, 2, 5, 7),
  (9968, 2, 4, 8),
  (2652, 1, 8, 5),
  (9416, 1, 7, 6),
  (10124, 1, 6, 7),
  (3776, 1, 5, 8),
  (512, 0, 8, 6),
  (896, 0, 7, 7),
  (512, 0, 6, 8)
  ]
private def vPoly (a b c : ℝ) : ℝ := evalTerms vTerms a b c
private theorem vPoly_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < vPoly a b c := by
  apply evalTerms_pos vTerms _ _ ha hb hc
  · norm_num [vTerms]
  · simp [vTerms]
private theorem vPoly_identity (a b c : ℝ) :
    vPoly a b c = pairF a b*(aux a c)^2*hPoly a b c -
      9*a*c*q a b*(a^2-b*c)^2*(b-c)^2*(2*a^2+3*a*b+3*a*c+2*b*c)^2 := by
  rw [hPoly_identity]
  simp only [vPoly, vTerms, evalTerms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, monomial, pairF, aux, q]
  ring

/-- Distinct permutations occur once, including repeated exponent patterns. -/
private def symMonomial (r s t : ℕ) (a b c : ℝ) : ℝ :=
  if r = s ∧ s = t then a^r*b^s*c^t
  else if r = s then a^r*b^s*c^t+a^r*b^t*c^s+a^t*b^r*c^s
  else if s = t then a^r*b^s*c^t+a^s*b^r*c^t+a^s*b^t*c^r
  else if r = t then a^r*b^s*c^t+a^r*b^t*c^s+a^s*b^r*c^t
  else a^r*b^s*c^t+a^r*b^t*c^s+a^s*b^r*c^t+
    a^s*b^t*c^r+a^t*b^r*c^s+a^t*b^s*c^r
private theorem symMonomial_pos (r s t : ℕ) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < symMonomial r s t a b c := by
  unfold symMonomial
  split_ifs <;> positivity

/-- The 162 supplied permutation orbits, not the larger sorted-chamber table. -/
private def coreOrbits : List Term :=
[
  (4294967296, 34, 17, 0),
  (70330089472, 34, 16, 1),
  (533515468800, 34, 15, 2),
  (2520139169792, 34, 14, 3),
  (8358274793472, 34, 13, 4),
  (20740411752448, 34, 12, 5),
  (39977919971328, 34, 11, 6),
  (61244355117056, 34, 10, 7),
  (75569638670336, 34, 9, 8),
  (70330089472, 33, 18, 0),
  (1226078945280, 33, 17, 1),
  (9992543404032, 33, 16, 2),
  (50940900016128, 33, 15, 3),
  (182863140028416, 33, 14, 4),
  (492382998282240, 33, 13, 5),
  (1032875588616192, 33, 12, 6),
  (1728509857837056, 33, 11, 7),
  (2341718738657280, 33, 10, 8),
  (2588921009655808, 33, 9, 9),
  (533515468800, 32, 19, 0),
  (9992543404032, 32, 18, 1),
  (87961584795648, 32, 17, 2),
  (485463275864064, 32, 16, 3),
  (1889061682593792, 32, 15, 4),
  (5520212733542400, 32, 14, 5),
  (12586444223880192, 32, 13, 6),
  (22946613300753408, 32, 12, 7),
  (33979801315067904, 32, 11, 8),
  (41257875618447360, 32, 10, 9),
  (2520139169792, 31, 20, 0),
  (50940900016128, 31, 19, 1),
  (485463275864064, 31, 18, 2),
  (2904316668313600, 31, 17, 3),
  (12256819252314112, 31, 16, 4),
  (38860446570559488, 31, 15, 5),
  (96202391889653760, 31, 14, 6),
  (190678645188790016, 31, 13, 7),
  (307639697016748544, 31, 12, 8),
  (408307515954310144, 31, 11, 9),
  (448429947406946304, 31, 10, 10),
  (8358274793472, 30, 21, 0),
  (182863140028416, 30, 20, 1),
  (1889061682593792, 30, 19, 2),
  (12256819252314112, 30, 18, 3),
  (56099055634865152, 30, 17, 4),
  (192886433961773824, 30, 16, 5),
  (517935149024467200, 30, 15, 6),
  (1114232758341828800, 30, 14, 7),
  (1953828735438706496, 30, 13, 8),
  (2824715539493912192, 30, 12, 9),
  (3390716076286162944, 30, 11, 10),
  (20740411752448, 29, 22, 0),
  (492382998282240, 29, 21, 1),
  (5520212733542400, 29, 20, 2),
  (38860446570559488, 29, 19, 3),
  (192886433961773824, 29, 18, 4),
  (718900027767905280, 29, 17, 5),
  (2092027549620311232, 29, 16, 6),
  (4878374210878300032, 29, 15, 7),
  (9279443998483095936, 29, 14, 8),
  (14574480082881736432, 29, 13, 9),
  (19051848770025958560, 29, 12, 10),
  (20821281108672117456, 29, 11, 11),
  (39977919971328, 28, 23, 0),
  (1032875588616192, 28, 22, 1),
  (12586444223880192, 28, 21, 2),
  (96202391889653760, 28, 20, 3),
  (517935149024467200, 28, 19, 4),
  (2092027549620311232, 28, 18, 5),
  (6593774950792326336, 28, 17, 6),
  (16650098943993244656, 28, 16, 7),
  (34305338608729496112, 28, 15, 8),
  (58414874734073342592, 28, 14, 9),
  (82924144908761237952, 28, 13, 10),
  (98671665250449542448, 28, 12, 11),
  (61244355117056, 27, 24, 0),
  (1728509857837056, 27, 23, 1),
  (22946613300753408, 27, 22, 2),
  (190678645188790016, 27, 21, 3),
  (1114232758341828800, 27, 20, 4),
  (4878374210878300032, 27, 19, 5),
  (16650098943993244656, 27, 18, 6),
  (45500002224550349920, 27, 17, 7),
  (101439369437941628096, 27, 16, 8),
  (186980420636763516244, 27, 15, 9),
  (287635909711243624848, 27, 14, 10),
  (371573191230585858016, 27, 13, 11),
  (404523553495972543304, 27, 12, 12),
  (75569638670336, 26, 25, 0),
  (2341718738657280, 26, 24, 1),
  (33979801315067904, 26, 23, 2),
  (307639697016748544, 26, 22, 3),
  (1953828735438706496, 26, 21, 4),
  (9279443998483095936, 26, 20, 5),
  (34305338608729496112, 26, 19, 6),
  (101439369437941628096, 26, 18, 7),
  (244571800818382515288, 26, 17, 8),
  (487505545858055939420, 26, 16, 9),
  (811415994140546377332, 26, 15, 10),
  (1135504870086917902800, 26, 14, 11),
  (1341851035274707858256, 26, 13, 12),
  (2588921009655808, 25, 25, 1),
  (41257875618447360, 25, 24, 2),
  (408307515954310144, 25, 23, 3),
  (2824715539493912192, 25, 22, 4),
  (14574480082881736432, 25, 21, 5),
  (58414874734073342592, 25, 20, 6),
  (186980420636763516244, 25, 19, 7),
  (487505545858055939420, 25, 18, 8),
  (1050305812308427489808, 25, 17, 9),
  (1889565833127630154360, 25, 16, 10),
  (2860052948051966538843, 25, 15, 11),
  (3660503274037058850562, 25, 14, 12),
  (3973062038450329216673, 25, 13, 13),
  (448429947406946304, 24, 24, 3),
  (3390716076286162944, 24, 23, 4),
  (19051848770025958560, 24, 22, 5),
  (82924144908761237952, 24, 21, 6),
  (287635909711243624848, 24, 20, 7),
  (811415994140546377332, 24, 19, 8),
  (1889565833127630154360, 24, 18, 9),
  (3672776280233386988382, 24, 17, 10),
  (6006859584502965350106, 24, 16, 11),
  (8313476881815275395860, 24, 15, 12),
  (9771662658576700596156, 24, 14, 13),
  (20821281108672117456, 23, 23, 5),
  (98671665250449542448, 23, 22, 6),
  (371573191230585858016, 23, 21, 7),
  (1135504870086917902800, 23, 20, 8),
  (2860052948051966538843, 23, 19, 9),
  (6006859584502965350106, 23, 18, 10),
  (10611233486110726741650, 23, 17, 11),
  (15865367342746639241134, 23, 16, 12),
  (20162624612928664597179, 23, 15, 13),
  (21833774714025477525834, 23, 14, 14),
  (404523553495972543304, 22, 22, 7),
  (1341851035274707858256, 22, 21, 8),
  (3660503274037058850562, 22, 20, 9),
  (8313476881815275395860, 22, 19, 10),
  (15865367342746639241134, 22, 18, 11),
  (25616701808599580721764, 22, 17, 12),
  (35165322380483721887138, 22, 16, 13),
  (41169840544536244656840, 22, 15, 14),
  (3973062038450329216673, 21, 21, 9),
  (9771662658576700596156, 21, 20, 10),
  (20162624612928664597179, 21, 19, 11),
  (35165322380483721887138, 21, 18, 12),
  (52125538366476985919570, 21, 17, 13),
  (65914500514548898519828, 21, 16, 14),
  (71261326594270423474743, 21, 15, 15),
  (21833774714025477525834, 20, 20, 11),
  (41169840544536244656840, 20, 19, 12),
  (65914500514548898519828, 20, 18, 13),
  (89998109701312645386966, 20, 17, 14),
  (105089627595272037892470, 20, 16, 15),
  (71261326594270423474743, 19, 19, 13),
  (105089627595272037892470, 19, 18, 14),
  (132494812024759900084278, 19, 17, 15),
  (143103055414254861651568, 19, 16, 16),
  (143103055414254861651568, 18, 18, 15),
  (166881697410333773484038, 18, 17, 16),
  (180184790931642907020288, 17, 17, 17)
  ]
private def orbitEval (ts : List Term) (a b c : ℝ) : ℝ :=
  (ts.map (fun t => (t.1 : ℝ)*symMonomial t.2.1 t.2.2.1 t.2.2.2 a b c)).sum
private def positiveCore (a b c : ℝ) : ℝ := orbitEval coreOrbits a b c
private theorem orbitEval_pos (ts : List Term) (ht : ∀ t ∈ ts, 0 < t.1)
    (hne : ts ≠ []) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < orbitEval ts a b c := by
  unfold orbitEval
  apply List.sum_pos
  · intro x hx
    obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hx
    exact mul_pos (by exact_mod_cast ht t htmem) (symMonomial_pos _ _ _ ha hb hc)
  · exact fun h => hne (List.map_eq_nil_iff.mp h)

private theorem positiveCore_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 0 < positiveCore a b c := by
  apply orbitEval_pos coreOrbits _ _ ha hb hc
  · decide
  · decide

private def gapDen (a b c : ℝ) : ℝ :=
  64*(hPoly a b c)^2*(q a b)^4*(aux a b)^4*
    (q a c)^4*(aux a c)^4*(q b c)^4*(aux b c)^4
private def coreGap (a b c : ℝ) : ℝ :=
  a*b*c*(a-b)^2*(a-c)^2*(b-c)^2*positiveCore a b c/gapDen a b c
private theorem gapDen_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 0 < gapDen a b c := by
  have := hPoly_pos ha hb hc
  have := q_pos ha hb
  have := q_pos ha hc
  have := q_pos hb hc
  have := aux_pos ha hb
  have := aux_pos ha hc
  have := aux_pos hb hc
  unfold gapDen
  positivity
private theorem coreGap_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 0 < coreGap a b c := by
  have hab' := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hac' := sq_pos_of_ne_zero (sub_ne_zero.mpr hac)
  have hbc' := sq_pos_of_ne_zero (sub_ne_zero.mpr hbc)
  have hp := positiveCore_pos ha hb hc
  unfold coreGap
  exact div_pos (by positivity) (gapDen_pos ha hb hc)

private def residualC (a b c : ℝ) : ℝ :=
  a*(a-b)^2*vPoly a b c/(4*(q a b)^3*aux a b*(aux a c)^2*hPoly a b c)
private theorem residualC_pos {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) :
    0 < residualC a b c := by
  have hab' := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hv := vPoly_pos ha hb hc
  have hh := hPoly_pos ha hb hc
  have hq := q_pos ha hb
  have hu := aux_pos ha hb
  have hu' := aux_pos ha hc
  unfold residualC
  positivity

private def left (j : Fin 3) : Fin 3 := ![1,0,0] j
private def right (j : Fin 3) : Fin 3 := ![2,2,1] j
private def third (i j : Fin 3) : Fin 3 :=
  if i = 0 then (if j = 1 then 2 else 1)
  else if i = 1 then (if j = 0 then 2 else 0)
  else (if j = 0 then 1 else 0)
private theorem column_indices (j : Fin 3) :
    left j ≠ j ∧ right j ≠ j ∧ left j ≠ right j ∧
      third (left j) j = right j ∧ third (right j) j = left j := by
  fin_cases j <;> decide

private def baseG (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => g (p i) (p j)
private def detG (p : Fin 3 → ℝ) : ℝ :=
  1/(p 0*p 1*p 2)+2*g (p 0) (p 1)*g (p 0) (p 2)*g (p 1) (p 2)-
    (g (p 1) (p 2))^2/p 0-(g (p 0) (p 2))^2/p 1-(g (p 0) (p 1))^2/p 2
/-- Explicit cofactors of the coefficient Gram, not a substitute for a
Sylvester operator. Distinct labels are required only when proving its laws. -/
private def dualG (p : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x := g (p 0) (p 1)
  let y := g (p 0) (p 2)
  let z := g (p 1) (p 2)
  (detG p)⁻¹ • !![1/(p 1*p 2)-z^2, y*z-x/p 2, x*z-y/p 1;
    y*z-x/p 2, 1/(p 0*p 2)-y^2, x*y-z/p 0;
    x*z-y/p 1, x*y-z/p 0, 1/(p 0*p 1)-x^2]
private def projectionCross (p : Fin 3 → ℝ) (i j k : Fin 3) : ℝ :=
  lam (p i) (p j)*lam (p k) (p j)*g (p i) (p k)+
  lam (p i) (p j)*mu (p k) (p j)*g (p i) (p j)+
  mu (p i) (p j)*lam (p k) (p j)*g (p j) (p k)+
  mu (p i) (p j)*mu (p k) (p j)/p j+
  delta (p i) (p j) (p k)*lam (p k) (p j)/2+
  delta (p k) (p j) (p i)*lam (p i) (p j)/2+
  delta (p i) (p j) (p k)*delta (p k) (p j) (p i)*dualG p i k/4
private def residualE (p : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  p j*residualC (p i) (p j) (p (third i j))
private def columnA (p : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  residualE p (left j) j*residualE p (right j) j
private def residualT (p : Fin 3 → ℝ) : ℝ := ∑ j, columnA p j
private def canonicalK (p : Fin 3 → ℝ) : ℝ :=
  4-p 0*p 1*p 2*g (p 0) (p 1)*g (p 1) (p 2)*g (p 2) (p 0)-
    ∑ j, p j*projectionCross p (left j) j (right j)
private def residualY (p : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  canonicalK p*columnA p j/residualT p

/-- A signed numerator is only an algebraic intermediate. No sign claim is
made for it; positivity comes from the separate degree-51 core. -/
private abbrev SignedTerm := ℤ × ℕ × ℕ × ℕ
private def kNumeratorTerms : List SignedTerm :=
[
  (122880, 1, 19, 10),
  (835584, 2, 19, 9),
  (2608512, 3, 19, 8),
  (5038656, 4, 19, 7),
  (6816768, 5, 19, 6),
  (6816768, 6, 19, 5),
  (5038656, 7, 19, 4),
  (2608512, 8, 19, 3),
  (835584, 9, 19, 2),
  (122880, 10, 19, 1),
  (835584, 1, 18, 11),
  (6876288, 2, 18, 10),
  (25054368, 3, 18, 9),
  (55358160, 4, 18, 8),
  (84896016, 5, 18, 7),
  (97126368, 6, 18, 6),
  (84896016, 7, 18, 5),
  (55358160, 8, 18, 4),
  (25054368, 9, 18, 3),
  (6876288, 10, 18, 2),
  (835584, 11, 18, 1),
  (2608512, 1, 17, 12),
  (25054368, 2, 17, 11),
  (104572824, 3, 17, 10),
  (259951044, 4, 17, 9),
  (443430300, 5, 17, 8),
  (565820652, 6, 17, 7),
  (565820652, 7, 17, 6),
  (443430300, 8, 17, 5),
  (259951044, 9, 17, 4),
  (104572824, 10, 17, 3),
  (25054368, 11, 17, 2),
  (2608512, 12, 17, 1),
  (5038656, 1, 16, 13),
  (55358160, 2, 16, 12),
  (259951044, 3, 16, 11),
  (713716590, 4, 16, 10),
  (1322150148, 5, 16, 9),
  (1822190454, 6, 16, 8),
  (2008196946, 7, 16, 7),
  (1822190454, 8, 16, 6),
  (1322150148, 9, 16, 5),
  (713716590, 10, 16, 4),
  (259951044, 11, 16, 3),
  (55358160, 12, 16, 2),
  (5038656, 13, 16, 1),
  (6816768, 1, 15, 14),
  (84896016, 2, 15, 13),
  (443430300, 3, 15, 12),
  (1322150148, 4, 15, 11),
  (2583832176, 5, 15, 10),
  (3664213485, 6, 15, 9),
  (4182658782, 7, 15, 8),
  (4182658782, 8, 15, 7),
  (3664213485, 9, 15, 6),
  (2583832176, 10, 15, 5),
  (1322150148, 11, 15, 4),
  (443430300, 12, 15, 3),
  (84896016, 13, 15, 2),
  (6816768, 14, 15, 1),
  (6816768, 1, 14, 15),
  (97126368, 2, 14, 14),
  (565820652, 3, 14, 13),
  (1822190454, 4, 14, 12),
  (3664213485, 5, 14, 11),
  (4975617354, 6, 14, 10),
  (5095482042, 7, 14, 9),
  (4874838204, 8, 14, 8),
  (5095482042, 9, 14, 7),
  (4975617354, 10, 14, 6),
  (3664213485, 11, 14, 5),
  (1822190454, 12, 14, 4),
  (565820652, 13, 14, 3),
  (97126368, 14, 14, 2),
  (6816768, 15, 14, 1),
  (5038656, 1, 13, 16),
  (84896016, 2, 13, 15),
  (565820652, 3, 13, 14),
  (2008196946, 4, 13, 13),
  (4182658782, 5, 13, 12),
  (5095482042, 6, 13, 11),
  (3063945648, 7, 13, 10),
  (115183008, 8, 13, 9),
  (115183008, 9, 13, 8),
  (3063945648, 10, 13, 7),
  (5095482042, 11, 13, 6),
  (4182658782, 12, 13, 5),
  (2008196946, 13, 13, 4),
  (565820652, 14, 13, 3),
  (84896016, 15, 13, 2),
  (5038656, 16, 13, 1),
  (2608512, 1, 12, 17),
  (55358160, 2, 12, 16),
  (443430300, 3, 12, 15),
  (1822190454, 4, 12, 14),
  (4182658782, 5, 12, 13),
  (4874838204, 6, 12, 12),
  (115183008, 7, 12, 11),
  (-8627151906, 8, 12, 10),
  (-13237360878, 9, 12, 9),
  (-8627151906, 10, 12, 8),
  (115183008, 11, 12, 7),
  (4874838204, 12, 12, 6),
  (4182658782, 13, 12, 5),
  (1822190454, 14, 12, 4),
  (443430300, 15, 12, 3),
  (55358160, 16, 12, 2),
  (2608512, 17, 12, 1),
  (835584, 1, 11, 18),
  (25054368, 2, 11, 17),
  (259951044, 3, 11, 16),
  (1322150148, 4, 11, 15),
  (3664213485, 5, 11, 14),
  (5095482042, 6, 11, 13),
  (115183008, 7, 11, 12),
  (-13237360878, 8, 11, 11),
  (-26071649076, 9, 11, 10),
  (-26071649076, 10, 11, 9),
  (-13237360878, 11, 11, 8),
  (115183008, 12, 11, 7),
  (5095482042, 13, 11, 6),
  (3664213485, 14, 11, 5),
  (1322150148, 15, 11, 4),
  (259951044, 16, 11, 3),
  (25054368, 17, 11, 2),
  (835584, 18, 11, 1),
  (122880, 1, 10, 19),
  (6876288, 2, 10, 18),
  (104572824, 3, 10, 17),
  (713716590, 4, 10, 16),
  (2583832176, 5, 10, 15),
  (4975617354, 6, 10, 14),
  (3063945648, 7, 10, 13),
  (-8627151906, 8, 10, 12),
  (-26071649076, 9, 10, 11),
  (-34776356256, 10, 10, 10),
  (-26071649076, 11, 10, 9),
  (-8627151906, 12, 10, 8),
  (3063945648, 13, 10, 7),
  (4975617354, 14, 10, 6),
  (2583832176, 15, 10, 5),
  (713716590, 16, 10, 4),
  (104572824, 17, 10, 3),
  (6876288, 18, 10, 2),
  (122880, 19, 10, 1),
  (835584, 2, 9, 19),
  (25054368, 3, 9, 18),
  (259951044, 4, 9, 17),
  (1322150148, 5, 9, 16),
  (3664213485, 6, 9, 15),
  (5095482042, 7, 9, 14),
  (115183008, 8, 9, 13),
  (-13237360878, 9, 9, 12),
  (-26071649076, 10, 9, 11),
  (-26071649076, 11, 9, 10),
  (-13237360878, 12, 9, 9),
  (115183008, 13, 9, 8),
  (5095482042, 14, 9, 7),
  (3664213485, 15, 9, 6),
  (1322150148, 16, 9, 5),
  (259951044, 17, 9, 4),
  (25054368, 18, 9, 3),
  (835584, 19, 9, 2),
  (2608512, 3, 8, 19),
  (55358160, 4, 8, 18),
  (443430300, 5, 8, 17),
  (1822190454, 6, 8, 16),
  (4182658782, 7, 8, 15),
  (4874838204, 8, 8, 14),
  (115183008, 9, 8, 13),
  (-8627151906, 10, 8, 12),
  (-13237360878, 11, 8, 11),
  (-8627151906, 12, 8, 10),
  (115183008, 13, 8, 9),
  (4874838204, 14, 8, 8),
  (4182658782, 15, 8, 7),
  (1822190454, 16, 8, 6),
  (443430300, 17, 8, 5),
  (55358160, 18, 8, 4),
  (2608512, 19, 8, 3),
  (5038656, 4, 7, 19),
  (84896016, 5, 7, 18),
  (565820652, 6, 7, 17),
  (2008196946, 7, 7, 16),
  (4182658782, 8, 7, 15),
  (5095482042, 9, 7, 14),
  (3063945648, 10, 7, 13),
  (115183008, 11, 7, 12),
  (115183008, 12, 7, 11),
  (3063945648, 13, 7, 10),
  (5095482042, 14, 7, 9),
  (4182658782, 15, 7, 8),
  (2008196946, 16, 7, 7),
  (565820652, 17, 7, 6),
  (84896016, 18, 7, 5),
  (5038656, 19, 7, 4),
  (6816768, 5, 6, 19),
  (97126368, 6, 6, 18),
  (565820652, 7, 6, 17),
  (1822190454, 8, 6, 16),
  (3664213485, 9, 6, 15),
  (4975617354, 10, 6, 14),
  (5095482042, 11, 6, 13),
  (4874838204, 12, 6, 12),
  (5095482042, 13, 6, 11),
  (4975617354, 14, 6, 10),
  (3664213485, 15, 6, 9),
  (1822190454, 16, 6, 8),
  (565820652, 17, 6, 7),
  (97126368, 18, 6, 6),
  (6816768, 19, 6, 5),
  (6816768, 6, 5, 19),
  (84896016, 7, 5, 18),
  (443430300, 8, 5, 17),
  (1322150148, 9, 5, 16),
  (2583832176, 10, 5, 15),
  (3664213485, 11, 5, 14),
  (4182658782, 12, 5, 13),
  (4182658782, 13, 5, 12),
  (3664213485, 14, 5, 11),
  (2583832176, 15, 5, 10),
  (1322150148, 16, 5, 9),
  (443430300, 17, 5, 8),
  (84896016, 18, 5, 7),
  (6816768, 19, 5, 6),
  (5038656, 7, 4, 19),
  (55358160, 8, 4, 18),
  (259951044, 9, 4, 17),
  (713716590, 10, 4, 16),
  (1322150148, 11, 4, 15),
  (1822190454, 12, 4, 14),
  (2008196946, 13, 4, 13),
  (1822190454, 14, 4, 12),
  (1322150148, 15, 4, 11),
  (713716590, 16, 4, 10),
  (259951044, 17, 4, 9),
  (55358160, 18, 4, 8),
  (5038656, 19, 4, 7),
  (2608512, 8, 3, 19),
  (25054368, 9, 3, 18),
  (104572824, 10, 3, 17),
  (259951044, 11, 3, 16),
  (443430300, 12, 3, 15),
  (565820652, 13, 3, 14),
  (565820652, 14, 3, 13),
  (443430300, 15, 3, 12),
  (259951044, 16, 3, 11),
  (104572824, 17, 3, 10),
  (25054368, 18, 3, 9),
  (2608512, 19, 3, 8),
  (835584, 9, 2, 19),
  (6876288, 10, 2, 18),
  (25054368, 11, 2, 17),
  (55358160, 12, 2, 16),
  (84896016, 13, 2, 15),
  (97126368, 14, 2, 14),
  (84896016, 15, 2, 13),
  (55358160, 16, 2, 12),
  (25054368, 17, 2, 11),
  (6876288, 18, 2, 10),
  (835584, 19, 2, 9),
  (122880, 10, 1, 19),
  (835584, 11, 1, 18),
  (2608512, 12, 1, 17),
  (5038656, 13, 1, 16),
  (6816768, 14, 1, 15),
  (6816768, 15, 1, 14),
  (5038656, 16, 1, 13),
  (2608512, 17, 1, 12),
  (835584, 18, 1, 11),
  (122880, 19, 1, 10)
  ]
private def kNumerator (a b c : ℝ) : ℝ :=
  (kNumeratorTerms.map (fun t => (t.1 : ℝ)*a^t.2.1*b^t.2.2.1*c^t.2.2.2)).sum
private def kDenominator (a b c : ℝ) : ℝ :=
  8*hPoly a b c*(q a b)^2*(aux a b)^2*(q a c)^2*(aux a c)^2*
    (q b c)^2*(aux b c)^2
private def columnNumerator (a b c : ℝ) : ℝ :=
  4*a*b^2*c*(a-b)^2*(c-b)^2*vPoly a b c*vPoly c b a*
    q a b*q c b*(q a c)^4*(aux a b)^3*(aux c b)^3
private def tNumerator (a b c : ℝ) : ℝ :=
  columnNumerator b a c+columnNumerator a b c+columnNumerator a c b
private theorem denominator_square (a b c : ℝ) :
    (kDenominator a b c)^2 = gapDen a b c := by
  unfold kDenominator gapDen
  ring

set_option maxHeartbeats 16000000 in
/-- Exact degree-60 polynomial identity, with every signed and positive
coefficient present in source. The source generator is not proof authority;
the coefficient arithmetic is handled by the ring proof. -/
private theorem polynomial_gap (a b c : ℝ) :
    tNumerator a b c-(kNumerator a b c)^2 =
      a*b*c*(a-b)^2*(a-c)^2*(b-c)^2*positiveCore a b c := by
  dsimp only [tNumerator, columnNumerator, vPoly, vTerms, evalTerms,
    kNumerator, kNumeratorTerms, positiveCore, orbitEval, coreOrbits,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, monomial,
    symMonomial, q, aux]
  norm_num
  ring

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
