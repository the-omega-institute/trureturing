/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelSupplier
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Candidate positive-core, residual and ordered-square source for the original three-level supplier. -/

import D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
import D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! Three-level balanced CFC supplier and positive-definite Sylvester rigidity.
The coefficient construction has three base coordinates and six residual
coordinates, independent of the finite matrix dimension. Positive labels may
coincide and level fibers may be empty. Source-selection binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/23103. -/

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

/-- Exact supplier proposition, retaining the actual CFC factorial derivatives.
`level` need not be surjective and `p` need not be injective. The finite carrier
is arbitrary and may be empty. This is a proposition definition, not a theorem. -/
def ThreeLevelSupplierTarget : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ∀ (S : Matrix n n ℂ), S.PosSemidef →
    ∀ (Z : Matrix n n ℂ), Z.IsHermitian →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P^3 + t • (CFC.rpow P (3/2 : ℝ) * S *
        CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re

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

private theorem q_symm (a b : ℝ) : q a b = q b a := by unfold q; ring
private theorem aux_symm (a b : ℝ) : aux a b = aux b a := by unfold aux; ring

private theorem detG_formula (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    detG p = (p 0-p 1)^2*(p 0-p 2)^2*(p 1-p 2)^2*hPoly (p 0) (p 1) (p 2)/
      (4*p 0*p 1*p 2*(q (p 0) (p 1))^2*(q (p 0) (p 2))^2*(q (p 1) (p 2))^2) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have h01 := (q_pos (hp 0) (hp 1)).ne'
  have h02 := (q_pos (hp 0) (hp 2)).ne'
  have h12 := (q_pos (hp 1) (hp 2)).ne'
  rw [hPoly_identity]
  unfold detG g q at *
  field_simp [h0, h1, h2, h01, h02, h12] <;> ring

set_option maxHeartbeats 16000000 in
/-- Rational denominator clearing against the signed degree-30 numerator.
All facts used here are scalar facts or numerical coefficient data;
there is no spectral, jet, or supplier hypothesis. -/
private theorem canonicalK_clear (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    canonicalK p*kDenominator (p 0) (p 1) (p 2) = kNumerator (p 0) (p 1) (p 2) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have h01 : p 0-p 1 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have h02 : p 0-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h))
  have h12 : p 1-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h))
  have hq01 := (q_pos (hp 0) (hp 1)).ne'
  have hq02 := (q_pos (hp 0) (hp 2)).ne'
  have hq12 := (q_pos (hp 1) (hp 2)).ne'
  have hu01 := (aux_pos (hp 0) (hp 1)).ne'
  have hu02 := (aux_pos (hp 0) (hp 2)).ne'
  have hu12 := (aux_pos (hp 1) (hp 2)).ne'
  have hH := (hPoly_pos (hp 0) (hp 1) (hp 2)).ne'
  simp only [canonicalK, Fin.sum_univ_three, projectionCross]
  norm_num [left, right, third, dualG]
  rw [detG_formula p hp]
  simp only [kDenominator, kNumerator, kNumeratorTerms,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  field_simp [h0, h1, h2, h01, h02, h12, hq01, hq02, hq12,
    hu01, hu02, hu12, hH]
  simp only [hPoly_identity]
  unfold lam mu delta g q aux at *
  field_simp [h0, h1, h2, h01, h02, h12, hq01, hq02, hq12,
    hu01, hu02, hu12] <;> ring

private theorem residualT_clear (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    residualT p*gapDen (p 0) (p 1) (p 2) = tNumerator (p 0) (p 1) (p 2) := by
  have hH := (hPoly_pos (hp 0) (hp 1) (hp 2)).ne'
  have hq01 := (q_pos (hp 0) (hp 1)).ne'
  have hq02 := (q_pos (hp 0) (hp 2)).ne'
  have hq12 := (q_pos (hp 1) (hp 2)).ne'
  have hu01 := (aux_pos (hp 0) (hp 1)).ne'
  have hu02 := (aux_pos (hp 0) (hp 2)).ne'
  have hu12 := (aux_pos (hp 1) (hp 2)).ne'
  have hh10 : hPoly (p 1) (p 0) (p 2) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh20 : hPoly (p 2) (p 0) (p 1) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh21 : hPoly (p 2) (p 1) (p 0) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh02 : hPoly (p 0) (p 2) (p 1) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  have hh12 : hPoly (p 1) (p 2) (p 0) = hPoly (p 0) (p 1) (p 2) := by
    simp only [hPoly_identity]; ring
  simp only [residualT, columnA, residualE, Fin.sum_univ_three]
  norm_num [left, right, third]
  simp only [residualC, gapDen, tNumerator, columnNumerator,
    hh10, hh20, hh21, hh02, hh12]
  simp only [q_symm, aux_symm] at hq01 hq02 hq12 hu01 hu02 hu12 ⊢
  field_simp [hH, hq01, hq02, hq12, hu01, hu02, hu12] <;> ring

/-- Exact identity linking the positive core to the original rational budgets. -/
private theorem canonical_gap_identity (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    residualT p-(canonicalK p)^2 = coreGap (p 0) (p 1) (p 2) := by
  have hD := (gapDen_pos (hp 0) (hp 1) (hp 2)).ne'
  have hB : kDenominator (p 0) (p 1) (p 2) ≠ 0 := by
    intro hzero
    have he := denominator_square (p 0) (p 1) (p 2)
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at he
    exact hD he.symm
  have hK : canonicalK p =
      kNumerator (p 0) (p 1) (p 2)/kDenominator (p 0) (p 1) (p 2) :=
    (eq_div_iff hB).mpr (canonicalK_clear p hp hinj)
  have hT : residualT p =
      tNumerator (p 0) (p 1) (p 2)/gapDen (p 0) (p 1) (p 2) :=
    (eq_div_iff hD).mpr (residualT_clear p hp)
  unfold coreGap
  rw [hT, hK, ← denominator_square, div_pow, ← sub_div, polynomial_gap]

private theorem residualE_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    0 < residualE p i j := by
  exact mul_pos (hp j) (residualC_pos (hp i) (hp j) (hp _) (fun h => hij (hinj h)))
private theorem columnA_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (j : Fin 3) : 0 < columnA p j := by
  exact mul_pos (residualE_pos p hp hinj _ _ (column_indices j).1)
    (residualE_pos p hp hinj _ _ (column_indices j).2.1)

private theorem canonical_gap_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : (canonicalK p)^2 < residualT p := by
  have h01 : p 0 ≠ p 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : p 0 ≠ p 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : p 1 ≠ p 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hpos := coreGap_pos (hp 0) (hp 1) (hp 2) h01 h02 h12
  rw [← canonical_gap_identity p hp hinj] at hpos
  exact sub_pos.mp hpos

private theorem detG_pos (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : 0 < detG p := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h01 : p 0-p 1 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have h02 : p 0-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h))
  have h12 : p 1-p 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h))
  have hs01 := sq_pos_of_ne_zero h01
  have hs02 := sq_pos_of_ne_zero h02
  have hs12 := sq_pos_of_ne_zero h12
  have hH := hPoly_pos (hp 0) (hp 1) (hp 2)
  have hq01 := q_pos (hp 0) (hp 1)
  have hq02 := q_pos (hp 0) (hp 2)
  have hq12 := q_pos (hp 1) (hp 2)
  rw [detG_formula p hp]
  positivity

private theorem pair_schur_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < 1/b-a*(g a b)^2 := by
  have hq := (q_pos ha hb).ne'
  have he : 1/b-a*(g a b)^2 = (a-b)^2*aux a b/(4*b*(q a b)^2) := by
    unfold g q aux at *
    field_simp [hb.ne', hq] <;> ring
  have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hu := aux_pos ha hb
  have hqp := q_pos ha hb
  rw [he]
  positivity

/-- Explicit rational LDL completion of the three-by-three base quadratic
form. Square roots have not entered the scalar algebra. The ambient matrix
carrier in the ultimate supplier is unrestricted. -/
private theorem baseG_posDef (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : (baseG p).PosDef := by
  let d0 : ℝ := 1/p 0
  let d1 : ℝ := 1/p 1-p 0*(g (p 0) (p 1))^2
  let d2 : ℝ := detG p/(d0*d1)
  have hd0 : 0 < d0 := one_div_pos.mpr (hp 0)
  have hd1 : 0 < d1 := pair_schur_pos (hp 0) (hp 1)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have hd2 : 0 < d2 := div_pos (detG_pos p hp hinj) (mul_pos hd0 hd1)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [baseG, Matrix.conjTranspose_apply, star_trivial]
    exact g_symm _ _
  · intro x hx
    let y0 := x 0+p 0*g (p 0) (p 1)*x 1+p 0*g (p 0) (p 2)*x 2
    let y1 := x 1+(g (p 1) (p 2)-p 0*g (p 0) (p 1)*g (p 0) (p 2))/d1*x 2
    have hid : star x ⬝ᵥ (baseG p*ᵥ x) = d0*y0^2+d1*y1^2+d2*(x 2)^2 := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply,
        star_trivial, baseG]
      simp only [g_self (hp 0), g_self (hp 1), g_self (hp 2), g_symm]
      dsimp only [y0, y1, d2]
      field_simp [hd0.ne', hd1.ne']
      dsimp only [d0, d1]
      unfold detG
      try simp only [g_symm]
      have hn0 := (hp 0).ne'
      have hn1 := (hp 1).ne'
      have hn2 := (hp 2).ne'
      field_simp [hn0, hn1, hn2] <;> ring
    rw [hid]
    have hn0 : 0 ≤ d0*y0^2 := mul_nonneg hd0.le (sq_nonneg _)
    have hn1 : 0 ≤ d1*y1^2 := mul_nonneg hd1.le (sq_nonneg _)
    have hn2 : 0 ≤ d2*(x 2)^2 := mul_nonneg hd2.le (sq_nonneg _)
    by_contra hnot
    have hle := le_of_not_gt hnot
    have hz0 : d0*y0^2 = 0 := by linarith
    have hz1 : d1*y1^2 = 0 := by linarith
    have hz2 : d2*(x 2)^2 = 0 := by linarith
    have hy0 : y0 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz0).resolve_left hd0.ne')
    have hy1 : y1 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left hd1.ne')
    have hx2 : x 2 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_left hd2.ne')
    have hx1 : x 1 = 0 := by simpa only [y1, hx2, mul_zero, add_zero] using hy1
    have hx0 : x 0 = 0 := by simpa only [y0, hx1, hx2, mul_zero, add_zero] using hy0
    apply hx
    funext i
    fin_cases i <;> assumption

private theorem baseG_dual (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) : baseG p*dualG p = 1 := by
  have hd := (detG_pos p hp hinj).ne'
  have hn0 := (hp 0).ne'
  have hn1 := (hp 1).ne'
  have hn2 := (hp 2).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.mk_zero, Fin.mk_one, show (⟨2, by decide⟩ : Fin 3) = 2 from rfl,
      baseG, dualG, Matrix.mul_apply, Fin.sum_univ_three,
      g_self (hp 0), g_self (hp 1), g_self (hp 2), g_symm]
  all_goals
    field_simp [hd, hn0, hn1, hn2]
    unfold detG
    try simp only [g_symm (p 1) (p 0), g_symm (p 2) (p 0), g_symm (p 2) (p 1)]
    field_simp [hn0, hn1, hn2] <;> ring

/-- The residual allocation works for every three positive budgets, for either
sign of K. Its proof is elementary ordered-field arithmetic. -/
private theorem residual_allocation (A : Fin 3 → ℝ) (hA : ∀ j, 0 < A j)
    (K : ℝ) (hgap : K^2 < ∑ j, A j) :
    (∑ j, K*A j/(∑ k, A k)) = K ∧
      ∀ j, 0 < A j-(K*A j/(∑ k, A k))^2 := by
  let T := ∑ j, A j
  have hT : 0 < T := Finset.sum_pos (fun j _ => hA j) Finset.univ_nonempty
  have hj (j : Fin 3) : A j < T := by
    rw [show T = A 0+A 1+A 2 from Fin.sum_univ_three A]
    fin_cases j
    · change A 0 < A 0+A 1+A 2
      linarith [hA 1, hA 2]
    · change A 1 < A 0+A 1+A 2
      linarith [hA 0, hA 2]
    · change A 2 < A 0+A 1+A 2
      linarith [hA 0, hA 1]
  constructor
  · rw [← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ K hT.ne'
  · intro j
    change 0 < A j-(K*A j/T)^2
    have hnum : 0 < T*(T-A j)+A j*(T-K^2) :=
      add_pos (mul_pos hT (sub_pos.mpr (hj j)))
        (mul_pos (hA j) (sub_pos.mpr hgap))
    have he : A j-(K*A j/T)^2 =
        A j*(T*(T-A j)+A j*(T-K^2))/T^2 := by
      field_simp
      ring
    rw [he]
    exact div_pos (mul_pos (hA j) hnum) (sq_pos_of_pos hT)

private theorem canonical_residual_blocks (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    (∑ j, residualY p j) = canonicalK p ∧
      ∀ j, 0 < residualE p (left j) j*residualE p (right j) j-(residualY p j)^2 := by
  simpa only [residualY, columnA, residualT] using
    residual_allocation (columnA p) (columnA_pos p hp hinj)
      (canonicalK p) (canonical_gap_pos p hp hinj)

/-- Explicit residual pair, including negative y. No absolute value or complex
phase is silently discarded. This is used in each of three orthogonal columns. -/
private def residualFirst (r : ℝ) : Fin 2 → ℝ := ![Real.sqrt r, 0]
private def residualSecond (r s y : ℝ) : Fin 2 → ℝ :=
  ![y/Real.sqrt r, Real.sqrt (s-y^2/r)]
private theorem residual_pair (r s y : ℝ) (hr : 0 < r) (hdet : 0 < r*s-y^2) :
    (∑ a, residualFirst r a*residualFirst r a) = r ∧
    (∑ a, residualFirst r a*residualSecond r s y a) = y ∧
    (∑ a, residualSecond r s y a*residualSecond r s y a) = s := by
  have hsqrt := Real.sqrt_pos.mpr hr
  have hsquare := Real.sq_sqrt hr.le
  have hrad : 0 < s-y^2/r := by
    apply (div_pos hdet hr).trans_eq
    field_simp [hr.ne'] <;> ring
  have hradSquare := Real.sq_sqrt hrad.le
  simp only [residualFirst, residualSecond, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hsquare]
  · field_simp [hsqrt.ne']
  · rw [← pow_two, ← pow_two, div_pow, hsquare, hradSquare]
    field_simp [hr.ne'] <;> ring

/-- Standard finite PSD Gram realization, reusing CFC.sqrt rather than
reimplementing spectral theory or introducing an assumed Gram formula. -/
private theorem gram_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    ∀ i j, (∑ a, CFC.sqrt G a i*CFC.sqrt G a j) = G i j := by
  let R := CFC.sqrt G
  have hR : R.IsHermitian := (CFC.sqrt_nonneg G).posSemidef.isHermitian
  have hsq : R*R = G := by simpa only [pow_two] using CFC.sq_sqrt G hG.nonneg
  intro i j
  have he := congrArg (fun M : Matrix ι ι ℝ => M i j) (show Rᴴ*R = G by rw [hR.eq, hsq])
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial] using he

/-- Nine coefficient coordinates: three base coordinates and six independent
residual coordinates. This bound is unrelated to the carrier dimension. -/
private abbrev Coeff := Fin 3 ⊕ (Fin 3 × Fin 2)
private def baseCoordinates (p : Fin 3 → ℝ) (i a : Fin 3) : ℝ :=
  CFC.sqrt (baseG p) a i
private def dualCoordinates (p : Fin 3 → ℝ) (i a : Fin 3) : ℝ :=
  ∑ k, dualG p k i*baseCoordinates p k a
private def correctedCoordinates (p : Fin 3 → ℝ) (i j a : Fin 3) : ℝ :=
  lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a
private def v (p : Fin 3 → ℝ) (i : Fin 3) : Coeff → ℝ
  | .inl a => Real.sqrt (p i)*baseCoordinates p i a
  | .inr _ => 0
private def m (p : Fin 3 → ℝ) (i j : Fin 3) : Coeff → ℝ
  | .inl a => if i = j then v p i (.inl a)
      else Real.sqrt (p j)*correctedCoordinates p i j a
  | .inr (col,a) => if i = j then 0 else if col = j then
      if i = left j then residualFirst (residualE p (left j) j) a
      else residualSecond (residualE p (left j) j) (residualE p (right j) j)
        (residualY p j) a
      else 0
private def dot (x y : Coeff → ℝ) : ℝ := ∑ a, x a*y a
private def tau (a b : ℝ) : ℝ := Real.sqrt (a*b)*g a b
private def beta (a b c : ℝ) : ℝ := Real.sqrt (a*b)*psi a b c

private theorem baseCoordinates_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    (∑ a, baseCoordinates p i a*baseCoordinates p j a) = g (p i) (p j) := by
  simpa only [baseCoordinates, baseG] using
    gram_realization (baseG p) (baseG_posDef p hp hinj).posSemidef i j

private theorem base_dual_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    (∑ a, baseCoordinates p i a*dualCoordinates p j a) = if i = j then 1 else 0 := by
  calc
    _ = ∑ k, dualG p k j*(∑ a, baseCoordinates p i a*baseCoordinates p k a) := by
      simp only [dualCoordinates, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ k, baseG p i k*dualG p k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [baseCoordinates_gram p hp hinj]
      dsimp only [baseG]
      ring
    _ = if i = j then 1 else 0 := by
      change (baseG p*dualG p) i j = _
      rw [baseG_dual p hp hinj]
      rfl

private theorem m_diagonal (p : Fin 3 → ℝ) (i : Fin 3) : m p i i = v p i := by
  funext a
  cases a with
  | inl a => simp only [m, ite_true]
  | inr a =>
    rcases a with ⟨col, a⟩
    simp only [m, v, ite_true]

private theorem v_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot (v p i) (v p j) = tau (p i) (p j) := by
  simp only [dot, Fintype.sum_sum_type, v, mul_zero, Finset.sum_const_zero, add_zero, tau]
  calc
    _ = Real.sqrt (p i)*Real.sqrt (p j)*
        (∑ a, baseCoordinates p i a*baseCoordinates p j a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [baseCoordinates_gram p hp hinj, Real.sqrt_mul (hp i).le]

/- The coefficient proofs below use only finite bilinear algebra after the
single CFC Gram realization above. In particular no square-root entry is
expanded, and the dual-dual contribution is retained. -/
private def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ a, x a*y a

private theorem dot3_comm (x y : Fin 3 → ℝ) : dot3 x y = dot3 y x := by
  unfold dot3
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem dot3_add_left (x y z : Fin 3 → ℝ) :
    dot3 (fun a => x a+y a) z = dot3 x z+dot3 y z := by
  simp only [dot3, add_mul, Finset.sum_add_distrib]

private theorem dot3_add_right (x y z : Fin 3 → ℝ) :
    dot3 x (fun a => y a+z a) = dot3 x y+dot3 x z := by
  simp only [dot3, mul_add, Finset.sum_add_distrib]

private theorem dot3_scale_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dot3 (fun a => r*x a) y = r*dot3 x y := by
  simp only [dot3, mul_assoc, Finset.mul_sum]

private theorem dot3_scale_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dot3 x (fun a => r*y a) = r*dot3 x y := by
  rw [dot3_comm, dot3_scale_left, dot3_comm y x]

private theorem dualG_symm (p : Fin 3 → ℝ) (i j : Fin 3) :
    dualG p i j = dualG p j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem dual_base_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot3 (dualCoordinates p i) (baseCoordinates p j) = if i = j then 1 else 0 := by
  rw [dot3_comm]
  simpa only [dot3, eq_comm] using base_dual_coordinates p hp hinj j i

private theorem dual_dual_coordinates (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) :
    dot3 (dualCoordinates p i) (dualCoordinates p j) = dualG p i j := by
  calc
    _ = ∑ k, dualG p k i*(∑ a,
        baseCoordinates p k a*dualCoordinates p j a) := by
      change (∑ a, (∑ k, dualG p k i*baseCoordinates p k a)*
        dualCoordinates p j a) = _
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = dualG p j i := by
      simp only [base_dual_coordinates p hp hinj]
      simp
    _ = dualG p i j := dualG_symm p j i

private theorem corrected_base (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (h i j : Fin 3) :
    dot3 (baseCoordinates p h) (correctedCoordinates p i j) =
      lam (p i) (p j)*g (p h) (p i)+
      mu (p i) (p j)*g (p h) (p j)+
      delta (p i) (p j) (p (third i j))/2*(if h = third i j then 1 else 0) := by
  change dot3 (baseCoordinates p h) (fun a =>
    lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a) = _
  simp only [dot3_add_right, dot3_scale_right]
  simp only [dot3, baseCoordinates_gram p hp hinj,
    base_dual_coordinates p hp hinj]

/-- The full nine-term product includes the dual-dual term even when one
of the two defects vanishes. No division by a defect is used. -/
private theorem corrected_pair (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k l : Fin 3) :
    dot3 (correctedCoordinates p i j) (correctedCoordinates p k l) =
      lam (p i) (p j)*lam (p k) (p l)*g (p i) (p k)+
      lam (p i) (p j)*mu (p k) (p l)*g (p i) (p l)+
      lam (p i) (p j)*(delta (p k) (p l) (p (third k l))/2)*
        (if i = third k l then 1 else 0)+
      mu (p i) (p j)*lam (p k) (p l)*g (p j) (p k)+
      mu (p i) (p j)*mu (p k) (p l)*g (p j) (p l)+
      mu (p i) (p j)*(delta (p k) (p l) (p (third k l))/2)*
        (if j = third k l then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*lam (p k) (p l)*
        (if third i j = k then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*mu (p k) (p l)*
        (if third i j = l then 1 else 0)+
      (delta (p i) (p j) (p (third i j))/2)*
        (delta (p k) (p l) (p (third k l))/2)*
        dualG p (third i j) (third k l) := by
  change dot3 (fun a =>
    lam (p i) (p j)*baseCoordinates p i a+
    mu (p i) (p j)*baseCoordinates p j a+
    (delta (p i) (p j) (p (third i j))/2)*dualCoordinates p (third i j) a)
    (fun a => lam (p k) (p l)*baseCoordinates p k a+
    mu (p k) (p l)*baseCoordinates p l a+
    (delta (p k) (p l) (p (third k l))/2)*dualCoordinates p (third k l) a) = _
  simp only [dot3_add_left, dot3_add_right, dot3_scale_left, dot3_scale_right,
    dual_base_coordinates p hp hinj, dual_dual_coordinates p hp hinj]
  simp only [dot3, baseCoordinates_gram p hp hinj,
    base_dual_coordinates p hp hinj]
  ring

private theorem third_properties (i j : Fin 3) (hij : i ≠ j) :
    third i j ≠ i ∧ third i j ≠ j ∧ third j i = third i j := by
  fin_cases i <;> fin_cases j <;> simp_all [third]

private theorem third_eq (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : third i j = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [third]

private theorem off_column_cases (i j : Fin 3) (hij : i ≠ j) :
    i = left j ∨ i = right j := by
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

private theorem dot_comm (x y : Coeff → ℝ) : dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem tau_symm (a b : ℝ) : tau a b = tau b a := by
  unfold tau
  rw [mul_comm b a, g_symm b a]

private theorem tau_self {a : ℝ} (ha : 0 < a) : tau a a = 1 := by
  rw [tau, Real.sqrt_mul_self ha.le, g_self ha]
  field_simp [ha.ne']

private theorem tau_triangle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    tau a b*tau b c*tau c a = a*b*c*g a b*g b c*g c a := by
  calc
    _ = (Real.sqrt a*Real.sqrt a)*(Real.sqrt b*Real.sqrt b)*
        (Real.sqrt c*Real.sqrt c)*g a b*g b c*g c a := by
      simp only [tau, Real.sqrt_mul ha.le, Real.sqrt_mul hb.le,
        Real.sqrt_mul hc.le]
      ring
    _ = _ := by rw [Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb.le,
      Real.mul_self_sqrt hc.le]

/-- Normalized endpoint projection, including the actual diagonal row. -/
private def rowProjection (p : Fin 3 → ℝ) (i k j : Fin 3) : ℝ :=
  if k = j then g (p i) (p j) else
    lam (p k) (p j)*g (p i) (p k)+mu (p k) (p j)*g (p i) (p j)+
      delta (p k) (p j) (p (third k j))/2*(if i = third k j then 1 else 0)

private theorem v_m_projection (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) :
    dot (v p i) (m p k j) =
      Real.sqrt (p i)*Real.sqrt (p j)*rowProjection p i k j := by
  by_cases hkj : k = j
  · subst k
    rw [m_diagonal, v_gram p hp hinj]
    simp only [ite_true, ite_false, rowProjection, if_pos rfl, tau, Real.sqrt_mul (hp i).le]
  · have he : dot (v p i) (m p k j) =
        Real.sqrt (p i)*Real.sqrt (p j)*
          dot3 (baseCoordinates p i) (correctedCoordinates p k j) := by
      simp only [ite_true, ite_false, dot, Fintype.sum_sum_type, v, m, if_neg hkj, zero_mul,
        Finset.sum_const_zero, add_zero, dot3]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he, corrected_base p hp hinj]
    simp only [ite_true, ite_false, rowProjection, if_neg hkj]

set_option maxHeartbeats 16000000 in
/-- Twenty-seven compact rational identities, with arbitrary positive p.
The case split is on the three finite indices, never on sampled labels. -/
private theorem rowProjection_balance (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (i j k : Fin 3) :
    rowProjection p i k j+rowProjection p j k i = 2*psi (p i) (p j) (p k) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have hq (r s : Fin 3) : (p r)^2+p r*p s+(p s)^2 ≠ 0 :=
    (q_pos (hp r) (hp s)).ne'
  have hu (r s : Fin 3) : 4*(p r)^2+7*p r*p s+4*(p s)^2 ≠ 0 :=
    (aux_pos (hp r) (hp s)).ne'
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [rowProjection, third]
  all_goals
    simp only [lam, mu, delta, psi, g, q, aux]
    field_simp [h0, h1, h2, hq 0 0, hq 0 1, hq 0 2,
      hq 1 0, hq 1 1, hq 1 2, hq 2 0, hq 2 1, hq 2 2,
      hu 0 1, hu 0 2, hu 1 0, hu 1 2, hu 2 0, hu 2 1] <;> ring

private theorem mixed_moment (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3) :
    (dot (v p i) (m p k j)+dot (m p k i) (v p j))/2 =
      beta (p i) (p j) (p k) := by
  rw [dot_comm (m p k i) (v p j), v_m_projection p hp hinj,
    v_m_projection p hp hinj]
  have hb := rowProjection_balance p hp i j k
  unfold beta
  rw [Real.sqrt_mul (hp i).le]
  calc
    _ = (Real.sqrt (p i)*Real.sqrt (p j))*
        (rowProjection p i k j+rowProjection p j k i)/2 := by ring
    _ = _ := by rw [hb]; ring

private def pairR (a b : ℝ) : ℝ :=
  a*(a-b)^2*pairF a b/(4*(q a b)^3*aux a b)

private theorem pairR_budget {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b*((lam a b)^2/a+2*lam a b*mu a b*g a b+(mu a b)^2/b+pairR a b) =
      4-a*b*(g a b)^2-2*a*psi a a b := by
  have hq := (q_pos ha hb).ne'
  have hqa := (q_pos ha ha).ne'
  have hqb := (q_pos hb hb).ne'
  have hqr := (q_pos hb ha).ne'
  have hu := (aux_pos ha hb).ne'
  unfold pairR pairF lam mu psi g q aux at *
  field_simp [ha.ne', hb.ne', hq, hqa, hqb, hqr, hu] <;> ring

set_option maxHeartbeats 16000000 in
/-- The diagonal cofactor for the missing third level. Its proof uses the
already supplied determinant formula, not another CFC computation. -/
private theorem dual_diagonal (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    dualG p (third i j) (third i j) =
      p (third i j)*(q (p i) (p (third i j)))^2*
        (q (p j) (p (third i j)))^2*aux (p i) (p j)/
      ((p i-p (third i j))^2*(p j-p (third i j))^2*
        hPoly (p i) (p j) (p (third i j))) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have hd (r s : Fin 3) (hrs : r ≠ s) : p r-p s ≠ 0 :=
    sub_ne_zero.mpr (fun h => hrs (hinj h))
  have hq (r s : Fin 3) : (p r)^2+p r*p s+(p s)^2 ≠ 0 :=
    (q_pos (hp r) (hp s)).ne'
  have hH (r s t : Fin 3) :
      4*(p r+p s+p t)^2*(p r*p s+p r*p t+p s*p t)^2-
        (p r*p s+p r*p t+p s*p t)^3-(p r+p s+p t)^3*p r*p s*p t ≠ 0 := by
    rw [← hPoly_identity]
    exact (hPoly_pos (hp r) (hp s) (hp t)).ne'
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    norm_num [third, dualG]
    rw [detG_formula p hp]
    simp only [hPoly_identity]
    unfold g q aux
    field_simp [h0, h1, h2, hq 0 1, hq 0 2, hq 1 0,
      hq 1 2, hq 2 0, hq 2 1,
      hd 0 1 (by decide), hd 0 2 (by decide), hd 1 0 (by decide),
      hd 1 2 (by decide), hd 2 0 (by decide), hd 2 1 (by decide),
      hH 0 1 2, hH 0 2 1, hH 1 0 2, hH 1 2 0, hH 2 0 1, hH 2 1 0] <;> ring

private theorem residualC_budget {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a ≠ c) (hbc : b ≠ c) :
    residualC a b c+(delta a b c)^2/4*
      (c*(q a c)^2*(q b c)^2*aux a b/
        ((a-c)^2*(b-c)^2*hPoly a b c)) = pairR a b := by
  have hq := (q_pos ha hb).ne'
  have hqc := (q_pos ha hc).ne'
  have hqbc := (q_pos hb hc).ne'
  have hu := (aux_pos ha hb).ne'
  have huc := (aux_pos ha hc).ne'
  have hH := (hPoly_pos ha hb hc).ne'
  have hdac := sub_ne_zero.mpr hac
  have hdbc := sub_ne_zero.mpr hbc
  unfold residualC pairR delta
  rw [vPoly_identity]
  field_simp [hq, hqc, hqbc, hu, huc, hH, hdac, hdbc] <;> ring

private def edgeResidual (p : Fin 3 → ℝ) (i j : Fin 3) : Fin 2 → ℝ :=
  if i = left j then residualFirst (residualE p (left j) j)
  else residualSecond (residualE p (left j) j) (residualE p (right j) j)
    (residualY p j)

private theorem edgeResidual_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) :
    (∑ a, edgeResidual p i j a*edgeResidual p k j a) =
      if i = k then residualE p i j else residualY p j := by
  have hidx := column_indices j
  have hpair := residual_pair (residualE p (left j) j)
    (residualE p (right j) j) (residualY p j)
    (residualE_pos p hp hinj _ _ hidx.1)
    ((canonical_residual_blocks p hp hinj).2 j)
  rcases off_column_cases i j hij with rfl | rfl <;>
    rcases off_column_cases k j hkj with rfl | rfl
  · simpa only [ite_true, ite_false, edgeResidual, if_pos rfl] using hpair.1
  · simpa only [ite_true, ite_false, edgeResidual, if_pos rfl, if_neg hidx.2.2.1,
      if_neg (Ne.symm hidx.2.2.1)] using hpair.2.1
  · simp only [ite_true, ite_false, edgeResidual, if_pos rfl, if_neg hidx.2.2.1,
      if_neg (Ne.symm hidx.2.2.1)]
    calc
      _ = ∑ a, residualFirst (residualE p (left j) j) a*
          residualSecond (residualE p (left j) j) (residualE p (right j) j)
            (residualY p j) a := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := hpair.2.1
  · simpa only [ite_true, ite_false, edgeResidual, if_neg (Ne.symm hidx.2.2.1), if_pos rfl]
      using hpair.2.2

private theorem same_column_gram (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k j : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) :
    dot (m p i j) (m p k j) =
      p j*dot3 (correctedCoordinates p i j) (correctedCoordinates p k j)+
        (if i = k then residualE p i j else residualY p j) := by
  have hbase : (∑ a : Fin 3, m p i j (.inl a)*m p k j (.inl a)) =
      p j*dot3 (correctedCoordinates p i j) (correctedCoordinates p k j) := by
    simp only [ite_true, ite_false, m, if_neg hij, if_neg hkj, dot3]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (Real.sqrt (p j)*Real.sqrt (p j))*
          (correctedCoordinates p i j a*correctedCoordinates p k j a) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (hp j).le]
  have hres : (∑ a : Fin 3 × Fin 2, m p i j (.inr a)*m p k j (.inr a)) =
      ∑ a, edgeResidual p i j a*edgeResidual p k j a := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ col : Fin 3, ∑ a : Fin 2,
          if col = j then edgeResidual p i j a*edgeResidual p k j a else 0 := by
        apply Finset.sum_congr rfl
        intro col _
        apply Finset.sum_congr rfl
        intro a _
        by_cases hcol : col = j <;>
          by_cases hi : i = left j <;> by_cases hk : k = left j <;>
          simp [m, hij, hkj, hcol, hi, hk, edgeResidual, (column_indices j).1]
      _ = _ := by rw [Finset.sum_comm]; simp
  rw [dot, Fintype.sum_sum_type, hbase, hres, edgeResidual_gram p hp hinj i k j hij hkj]

private theorem tau_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (tau a b)^2 = a*b*(g a b)^2 := by
  rw [tau, mul_pow, Real.sq_sqrt (mul_pos ha hb).le]

private theorem beta_diagonal {a b : ℝ} (ha : 0 < a) : beta a a b = a*psi a a b := by
  rw [beta, Real.sqrt_mul_self ha.le]

private theorem m_norm (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    dot (m p i j) (m p i j) =
      4-(tau (p i) (p j))^2-2*beta (p i) (p i) (p j) := by
  have ht := third_properties i j hij
  have hcorr : dot3 (correctedCoordinates p i j) (correctedCoordinates p i j) =
      (lam (p i) (p j))^2/p i+
      2*lam (p i) (p j)*mu (p i) (p j)*g (p i) (p j)+
      (mu (p i) (p j))^2/p j+
      (delta (p i) (p j) (p (third i j)))^2/4*
        dualG p (third i j) (third i j) := by
    rw [corrected_pair p hp hinj]
    simp only [ite_true, ite_false, if_neg ht.1, if_neg ht.2.1, if_neg (Ne.symm ht.1),
      if_neg (Ne.symm ht.2.1), g_self (hp i), g_self (hp j),
      mul_zero, zero_mul, add_zero, zero_add]
    rw [g_symm (p j) (p i)]
    ring
  have hC : residualC (p i) (p j) (p (third i j))+
      (delta (p i) (p j) (p (third i j)))^2/4*
        dualG p (third i j) (third i j) = pairR (p i) (p j) := by
    rw [dual_diagonal p hp hinj i j hij]
    exact residualC_budget (hp i) (hp j) (hp (third i j))
      (fun h => ht.1 (hinj h).symm) (fun h => ht.2.1 (hinj h).symm)
  have hb := pairR_budget (hp i) (hp j)
  rw [same_column_gram p hp hinj i i j hij hij, if_pos rfl, hcorr,
    tau_square (hp i) (hp j), beta_diagonal (hp i)]
  dsimp only [residualE]
  linear_combination hb + (p j)*hC

private theorem corrected_cross (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dot3 (correctedCoordinates p i j) (correctedCoordinates p k j) =
      projectionCross p i j k := by
  have ht := third_eq i j k hij hik hjk
  have ht' := third_eq k j i (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij)
  rw [corrected_pair p hp hinj, ht, ht']
  simp only [ite_true, ite_false, if_pos rfl, if_neg hij, if_neg (Ne.symm hij),
    if_neg hjk, if_neg (Ne.symm hjk), g_self (hp j),
    mul_zero, zero_mul, mul_one, add_zero, zero_add]
  rw [dualG_symm p k i]
  unfold projectionCross
  ring

private theorem m_column_cross (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dot (m p i j) (m p k j) = p j*projectionCross p i j k+residualY p j := by
  rw [same_column_gram p hp hinj i k j hij (Ne.symm hjk), if_neg hik,
    corrected_cross p hp hinj i j k hij hik hjk]

private theorem canonical_cycle (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) :
    dot (m p 1 0) (m p 2 0)+dot (m p 2 1) (m p 0 1)+
      dot (m p 0 2) (m p 1 2) =
        4-tau (p 0) (p 1)*tau (p 1) (p 2)*tau (p 2) (p 0) := by
  rw [dot_comm (m p 2 1) (m p 0 1)]
  rw [m_column_cross p hp hinj 1 0 2 (by decide) (by decide) (by decide),
    m_column_cross p hp hinj 0 1 2 (by decide) (by decide) (by decide),
    m_column_cross p hp hinj 0 2 1 (by decide) (by decide) (by decide),
    tau_triangle (hp 0) (hp 1) (hp 2)]
  have hY := (canonical_residual_blocks p hp hinj).1
  simp only [canonicalK, Fin.sum_univ_three] at hY
  norm_num [left, right] at hY
  linarith only [hY]

private theorem repeated_cycle (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i k : Fin 3) (hik : i ≠ k) :
    2*dot (v p i) (m p k i)+dot (m p i k) (m p i k) =
      4-(tau (p i) (p k))^2 := by
  have hm := mixed_moment p hp hinj i i k
  rw [dot_comm (m p k i) (v p i)] at hm
  rw [m_norm p hp hinj i k hik]
  linarith only [hm]

/-- All 27 cyclic coefficient laws. Repeated levels use the exact row norm;
the six distinct triples consume canonicalK without expanding its numerator. -/
private theorem cyclic_moment (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j k : Fin 3) :
    dot (m p j i) (m p k i)+dot (m p k j) (m p i j)+
      dot (m p i k) (m p j k) =
        4-tau (p i) (p j)*tau (p j) (p k)*tau (p k) (p i) := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp only [m_diagonal, v_gram p hp hinj, tau_self (hp i)]
      norm_num
    · have hr := repeated_cycle p hp hinj i k hik
      simp only [m_diagonal, tau_self (hp i), one_mul]
      rw [dot_comm (m p k i) (v p i), tau_symm (p k) (p i)]
      nlinarith only [hr]
  · by_cases hik : i = k
    · subst k
      have hr := repeated_cycle p hp hinj i j hij
      simp only [m_diagonal, tau_self (hp i), mul_one]
      rw [dot_comm (m p j i) (v p i), tau_symm (p j) (p i)]
      nlinarith only [hr]
    · by_cases hjk : j = k
      · subst k
        have hr := repeated_cycle p hp hinj j i (Ne.symm hij)
        simp only [m_diagonal, tau_self (hp j), mul_one]
        rw [dot_comm (m p i j) (v p j), tau_symm (p i) (p j)]
        nlinarith only [hr]
      · have hc := canonical_cycle p hp hinj
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          first
          | exact (hij rfl).elim
          | exact (hik rfl).elim
          | exact (hjk rfl).elim
          | (simp only [Fin.mk_zero, Fin.mk_one,
              show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] at hc ⊢ <;>
              simp only [dot_comm (m p 2 0) (m p 1 0),
              dot_comm (m p 2 1) (m p 0 1), dot_comm (m p 1 2) (m p 0 2),
              tau_symm (p 1) (p 0), tau_symm (p 2) (p 0),
              tau_symm (p 2) (p 1)] at hc ⊢ <;> linear_combination hc)

section OrderedSquares
variable {n : Type u} [Fintype n] [DecidableEq n]
private def realTrace (A : Matrix n n ℂ) : ℝ := A.trace.re
private theorem realTrace_comm (A B : Matrix n n ℂ) :
    realTrace (A*B) = realTrace (B*A) :=
  congrArg Complex.re (Matrix.trace_mul_comm A B)
private theorem realTrace_add (A B : Matrix n n ℂ) :
    realTrace (A+B) = realTrace A+realTrace B := by
  simp [realTrace, Matrix.trace_add]
private theorem realTrace_sub (A B : Matrix n n ℂ) :
    realTrace (A-B) = realTrace A-realTrace B := by
  simp [realTrace, Matrix.trace_sub]
private theorem realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp [realTrace, Matrix.trace_sum, Complex.re_sum]

/-- An unconditional identity in ordered matrices. M and V need not be
Hermitian. The only Hermitian hypothesis is the prescribed all-Z shift W. -/
private theorem one_ordered_square (S W M V : Matrix n n ℂ) (hW : W.IsHermitian) :
    realTrace ((M-(V*W+V*W))ᴴ*S*(M-(V*W+V*W))) =
      realTrace (Mᴴ*S*M)-2*realTrace ((Vᴴ*S*M+Mᴴ*S*V)*W)+
        4*realTrace ((Vᴴ*S*V)*W*W) := by
  have hexpand : (M-(V*W+V*W))ᴴ*S*(M-(V*W+V*W)) =
      Mᴴ*S*M-(Mᴴ*S*V*W+Mᴴ*S*V*W)-
        (W*Vᴴ*S*M+W*Vᴴ*S*M)+
        (W*Vᴴ*S*V*W+W*Vᴴ*S*V*W+
          W*Vᴴ*S*V*W+W*Vᴴ*S*V*W) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, hW.eq]
    noncomm_ring
  rw [hexpand]
  simp only [realTrace_add, realTrace_sub, add_mul]
  have hcross : realTrace (W*Vᴴ*S*M) = realTrace (Vᴴ*S*M*W) := by
    simpa only [mul_assoc] using realTrace_comm W (Vᴴ*S*M)
  have hquad : realTrace (W*Vᴴ*S*V*W) = realTrace (Vᴴ*S*V*W*W) := by
    simpa only [mul_assoc] using realTrace_comm W (Vᴴ*S*V*W)
  rw [hcross, hquad]
  ring

private def rowEnergy {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) : ℝ :=
  ∑ a, realTrace ((M a-(V a*W+V a*W))ᴴ*S*(M a-(V a*W+V a*W)))
private theorem ordered_row_square {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hW : W.IsHermitian) :
    rowEnergy S W M V =
      (∑ a, realTrace ((M a)ᴴ*S*M a))-
        2*realTrace ((∑ a, ((V a)ᴴ*S*M a+(M a)ᴴ*S*V a))*W)+
        4*realTrace ((∑ a, (V a)ᴴ*S*V a)*W*W) := by
  unfold rowEnergy
  simp_rw [one_ordered_square S W _ _ hW]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_mul, realTrace_sum]
  simp only [add_mul, realTrace_add, Finset.sum_mul, realTrace_sum,
    Finset.sum_add_distrib]
private theorem rowEnergy_nonneg {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hS : S.PosSemidef) :
    0 ≤ rowEnergy S W M V := by
  exact Finset.sum_nonneg fun a _ =>
    (Complex.nonneg_iff.mp
      (hS.conjTranspose_mul_mul_same (M a-(V a*W+V a*W))).trace_nonneg).1

private def liftedV (level : n → Fin 3) (p : Fin 3 → ℝ) (a : Coeff) : Matrix n n ℂ :=
  diagonal (fun i => (v p (level i) a : ℂ))
private def liftedM (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (a : Coeff) : Matrix n n ℂ :=
  fun i j => (m p (level i) (level j) a : ℂ)*S i j
private def firstMatrix (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
private def qMatrix (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ k,
    (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level k))*
      HsfLocalSpectrumSupplier.spectralTau (p (level k)) (p (level j))+
      3*HsfLocalSpectrumSupplier.spectralKernel (p (level i)) (p (level j))
        (p (level k)) : ℝ) : ℂ)*S i k*S k j

private theorem tau_spectral (a b : ℝ) :
    tau a b = HsfLocalSpectrumSupplier.spectralTau a b := by
  unfold tau g q HsfLocalSpectrumSupplier.spectralTau
    HsfLocalSpectrumSupplier.spectralDen
  ring

private theorem sqrt_chain {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.sqrt (a*c)*Real.sqrt (c*b) = c*Real.sqrt (a*b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le, Real.sqrt_mul ha.le]
  calc
    _ = (Real.sqrt c*Real.sqrt c)*(Real.sqrt a*Real.sqrt b) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hc.le]

/-- The normalized beta is exactly the original ordered Q coefficient. -/
private theorem beta_spectral {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    beta a b c = (2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau a c*
      HsfLocalSpectrumSupplier.spectralTau c b+
      3*HsfLocalSpectrumSupplier.spectralKernel a b c := by
  rw [← tau_spectral a c, ← tau_spectral c b]
  have hk : HsfLocalSpectrumSupplier.spectralKernel a b c =
      Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q b c) := by
    unfold HsfLocalSpectrumSupplier.spectralKernel HsfLocalSpectrumSupplier.spectralDen
    change Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q c b) = _
    rw [q_symm c b]
  rw [hk]
  calc
    _ = (2/3 : ℝ)*(c*Real.sqrt (a*b))*g a c*g c b+
        3*(Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q b c)) := by
      unfold beta psi
      ring
    _ = _ := by
      rw [← sqrt_chain ha hc]
      unfold tau
      ring

private theorem liftedV_hermitian (level : n → Fin 3) (p : Fin 3 → ℝ) (a : Coeff) :
    (liftedV level p a)ᴴ = liftedV level p a := by
  simp [liftedV, Matrix.diagonal_conjTranspose]

private theorem liftedM_star (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (a : Coeff) (i j : n) :
    (liftedM level p S a)ᴴ i j = (m p (level j) (level i) a : ℂ)*S i j := by
  simp [liftedM, Matrix.conjTranspose_apply, hS.apply i j, mul_comm]

private theorem ordered_first_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p) (S : Matrix n n ℂ) :
    (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a) = firstMatrix level p S := by
  ext i j
  calc
    _ = ∑ a, ((v p (level i) a*v p (level j) a : ℝ) : ℂ)*S i j := by
      simp only [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [liftedV_hermitian]
      change (diagonal (fun t => (v p (level t) a : ℂ))*S*
        diagonal (fun t => (v p (level t) a : ℂ))) i j = _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      push_cast
      ring
    _ = (dot (v p (level i)) (v p (level j)) : ℂ)*S i j := by
      unfold dot
      push_cast
      rw [Finset.sum_mul]
    _ = _ := by
      change (dot (v p (level i)) (v p (level j)) : ℂ)*S i j =
        (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
      rw [v_gram p hp hinj, tau_spectral]

private theorem lifted_cross_entry (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (a : Coeff) (i j : n) :
    ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a) i j =
      ∑ k, ((v p (level i) a*m p (level k) (level j) a+
        m p (level k) (level i) a*v p (level j) a : ℝ) : ℂ)*S i k*S k j := by
  have hleft : ((liftedV level p a)ᴴ*S*liftedM level p S a) i j =
      ∑ k, (v p (level i) a : ℂ)*S i k*
        ((m p (level k) (level j) a : ℂ)*S k j) := by
    rw [liftedV_hermitian]
    change (diagonal (fun t => (v p (level t) a : ℂ))*S*liftedM level p S a) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, liftedM]
  have hright : ((liftedM level p S a)ᴴ*S*liftedV level p a) i j =
      ∑ k, ((m p (level k) (level i) a : ℂ)*S i k)*S k j*
        (v p (level j) a : ℂ) := by
    change ((liftedM level p S a)ᴴ*S*
      diagonal (fun t => (v p (level t) a : ℂ))) i j = _
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    simp only [liftedM_star level p S hS]
  change ((liftedV level p a)ᴴ*S*liftedM level p S a) i j+
    ((liftedM level p S a)ᴴ*S*liftedV level p a) i j = _
  rw [hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem ordered_mixed_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      (2 : ℝ) • qMatrix level p S := by
  ext i j
  calc
    _ = ∑ k, ((dot (v p (level i)) (m p (level k) (level j))+
        dot (m p (level k) (level i)) (v p (level j)) : ℝ) : ℂ)*S i k*S k j := by
      simp only [Matrix.sum_apply, lifted_cross_entry level p S hS]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 1
      unfold dot
      push_cast
      rw [Finset.sum_add_distrib]
    _ = ∑ k, ((2*beta (p (level i)) (p (level j)) (p (level k)) : ℝ) : ℂ)*
        S i k*S k j := by
      apply Finset.sum_congr rfl
      intro k _
      have hc : dot (v p (level i)) (m p (level k) (level j))+
          dot (m p (level k) (level i)) (v p (level j)) =
          2*beta (p (level i)) (p (level j)) (p (level k)) := by
        linarith only [mixed_moment p hp hinj (level i) (level j) (level k)]
      rw [hc]
    _ = _ := by
      simp only [qMatrix, Matrix.smul_apply, Complex.real_smul]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [beta_spectral (hp (level i)) (hp (level k))]
      push_cast
      ring

/-- Ordered scalar entry triangles. The two orientations are separate
summands throughout; no entrywise or real-triangle positivity is used. -/
private def triangle (S : Matrix n n ℂ) (i j k : n) : ℂ := S i j*S j k*S k i
private def sum3 (f : n → n → n → ℂ) : ℂ := ∑ i, ∑ j, ∑ k, f i j k

private theorem sum3_congr {f g : n → n → n → ℂ}
    (h : ∀ i j k, f i j k = g i j k) : sum3 f = sum3 g := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact h i j k

private theorem sum3_add (f g : n → n → n → ℂ) :
    sum3 (fun i j k => f i j k+g i j k) = sum3 f+sum3 g := by
  simp only [sum3, Finset.sum_add_distrib]

private theorem sum3_sub (f g : n → n → n → ℂ) :
    sum3 (fun i j k => f i j k-g i j k) = sum3 f-sum3 g := by
  simp only [sum3, Finset.sum_sub_distrib]

private theorem sum3_scale (r : ℂ) (f : n → n → n → ℂ) :
    sum3 (fun i j k => r*f i j k) = r*sum3 f := by
  simp only [sum3, Finset.mul_sum]

private theorem sum3_rotate (f : n → n → n → ℂ) :
    sum3 f = sum3 (fun i j k => f j k i) := by
  unfold sum3
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by rw [Finset.sum_comm]
    _ = _ := rfl

private theorem sum3_sum {ι : Type*} [Fintype ι] (f : ι → n → n → n → ℂ) :
    (∑ a, sum3 (f a)) = sum3 (fun i j k => ∑ a, f a i j k) := by
  unfold sum3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem triangle_rotate (S : Matrix n n ℂ) (i j k : n) :
    triangle S j k i = triangle S i j k := by unfold triangle; ring

private theorem weighted_triangle_rotate (S : Matrix n n ℂ) (f : n → n → n → ℝ) :
    sum3 (fun i j k => (f i j k : ℂ)*triangle S i j k) =
      sum3 (fun i j k => (f j k i : ℂ)*triangle S i j k) := by
  rw [sum3_rotate]
  apply sum3_congr
  intro i j k
  rw [triangle_rotate]

private theorem trace_cube_entries (A : Matrix n n ℂ) :
    (A^3).trace = sum3 (triangle A) := by
  rw [show A^3 = A*A*A by noncomm_ring]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, sum3]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rfl

private theorem lifted_cubic_trace_entries (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace) =
      sum3 (fun i j k =>
        (dot (m p (level j) (level i)) (m p (level k) (level i)) : ℂ)*
          triangle S i j k) := by
  have ha (a : Coeff) : ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace =
      sum3 (fun i j k => ((m p (level j) (level i) a*
        m p (level k) (level i) a : ℝ) : ℂ)*triangle S i j k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul, sum3]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [liftedM_star level p S hS]
    dsimp only [liftedM, triangle]
    push_cast
    ring
  simp_rw [ha]
  rw [sum3_sum]
  apply sum3_congr
  intro i j k
  rw [← Finset.sum_mul]
  congr 1
  unfold dot
  push_cast
  rfl

private theorem firstMatrix_cube_entries (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) :
    ((firstMatrix level p S)^3).trace = sum3 (fun i j k =>
      ((tau (p (level i)) (p (level j))*tau (p (level j)) (p (level k))*
        tau (p (level k)) (p (level i)) : ℝ) : ℂ)*triangle S i j k) := by
  rw [trace_cube_entries]
  apply sum3_congr
  intro i j k
  dsimp only [triangle, firstMatrix]
  simp only [tau_spectral]
  push_cast
  ring

private theorem ordered_cubic_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      (4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3))/3 := by
  let A : n → n → n → ℝ := fun i j k =>
    dot (m p (level j) (level i)) (m p (level k) (level i))
  let L : ℂ := sum3 (fun i j k => (A i j k : ℂ)*triangle S i j k)
  have hrot1 : L = sum3 (fun i j k => (A j k i : ℂ)*triangle S i j k) :=
    weighted_triangle_rotate S A
  have hrot2 : L = sum3 (fun i j k => (A k i j : ℂ)*triangle S i j k) := by
    rw [hrot1]
    exact weighted_triangle_rotate S (fun i j k => A j k i)
  have hthree : sum3 (fun i j k =>
      ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k) = 3*L := by
    simp only [add_mul, sum3_add]
    rw [← hrot1, ← hrot2]
    change L+L+L = 3*L
    ring
  have hcoeff : sum3 (fun i j k =>
      ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k) =
      4*(S^3).trace-((firstMatrix level p S)^3).trace := by
    rw [trace_cube_entries, firstMatrix_cube_entries]
    calc
      _ = sum3 (fun i j k =>
          (4-((tau (p (level i)) (p (level j))*tau (p (level j)) (p (level k))*
            tau (p (level k)) (p (level i)) : ℝ) : ℂ))*triangle S i j k) := by
        apply sum3_congr
        intro i j k
        have hc := congrArg (fun r : ℝ => (r : ℂ))
          (cyclic_moment p hp hinj (level i) (level j) (level k))
        change ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k = _
        push_cast at hc ⊢
        exact congrArg (fun z : ℂ => z*triangle S i j k) hc
      _ = _ := by simp only [sub_mul, sum3_sub, sum3_scale]
  have hcomplex : (3 : ℂ)*(∑ a,
      ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace) =
      4*(S^3).trace-((firstMatrix level p S)^3).trace := by
    rw [lifted_cubic_trace_entries level p S hS]
    change 3*L = _
    exact hthree.symm.trans hcoeff
  have hreal : 3*(∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3) := by
    have hr := congrArg Complex.re hcomplex
    simpa [realTrace, Complex.mul_re, Complex.re_sum] using hr
  linarith only [hreal]

/-- Proposed actual-jet bridge consumes the owner's coordinate proofs.
It has no assumed jet, recurrence, or spectral formula in its telescope. -/
private theorem actual_shifted_identity (p : n → ℝ) (hp : ∀ i, 0 < p i)
    (S Z : Matrix n n ℂ) (hS : S.IsHermitian) :
    let P : Matrix n n ℂ := diagonal (fun i => (p i : ℂ))
    let F := fun t : ℝ => P⁻¹*CFC.rpow (P^3+t •
      (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let X : Matrix n n ℂ := fun i j =>
      (HsfLocalSpectrumSupplier.spectralTau (p i) (p j) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p i) (p k)*
        HsfLocalSpectrumSupplier.spectralTau (p k) (p j)+
        3*HsfLocalSpectrumSupplier.spectralKernel (p i) (p j) (p k) : ℝ) : ℂ)*S i k*S k j
    let W := Z+(1/3 : ℝ) • X
    6*(B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        4*(Q*W).trace.re+4*(X*W*W).trace.re := by
  exact HsfLocalSpectrumSupplier.actual_shifted_supplier_identity p hp S Z hS

end OrderedSquares

/- Auxiliary propositions keep the exact coefficient and ordered-moment laws. -/



/-- O2. Complete the coefficient Gram laws from the rational formulas and
CFC.sqrt realization, including all 27 triples, not only distinct triples. -/
private def CanonicalGramObligation : Prop :=
  ∀ (p : Fin 3 → ℝ), (∀ i, 0 < p i) → Function.Injective p →
    (∀ i j k, (dot (v p i) (m p k j)+dot (m p k i) (v p j))/2 =
      beta (p i) (p j) (p k)) ∧
    (∀ i j k, dot (m p j i) (m p k i)+dot (m p k j) (m p i j)+
      dot (m p i k) (m p j k) =
        4-tau (p i) (p j)*tau (p j) (p k)*tau (p k) (p i))

/-- O3. Ordered finite-index transfer. No scalar-matrix or real-triangle
restriction occurs; arbitrary fiber sizes, zero fibers, and phases remain. -/
private def OrderedMomentObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ),
    (∀ i, 0 < p i) → Function.Injective p →
    ∀ (S : Matrix n n ℂ), S.IsHermitian →
    (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a) = firstMatrix level p S ∧
    (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      (2 : ℝ) • qMatrix level p S ∧
    (∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      (4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3))/3


private theorem orderedMoment_proof : OrderedMomentObligation.{u} := by
  intro n instFinite instDecEq level p hp hinj S hS
  exact ⟨ordered_first_moment level p hp hinj S,
    ordered_mixed_moment level p hp hinj S hS,
    ordered_cubic_moment level p hp hinj S hS⟩

/-- O4. Faithful coincident-label reduction. Use the existing actual two-level
supplier via the fiber equivalence and common scale; do not evaluate dualG at
a singular Gram or assume that a level fiber is inhabited. -/
private def CoincidentLevelObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ¬ Function.Injective p →
    ∀ (S : Matrix n n ℂ), S.PosSemidef →
    ∀ (Z : Matrix n n ℂ), Z.IsHermitian →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹*CFC.rpow (P^3+t •
      (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 ≤ (B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re



/-- Elementary diagonal CFC calculation, including the empty matrix algebra. -/
private theorem coincident_diagonal_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) (hs : 0 ≤ s) :
    CFC.rpow (diagonal (fun i => (d i : ℂ))) s =
      diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI : IsEmpty ι := hι
    exact Subsingleton.elim _ _
  · letI : Nonempty ι := hι
    letI : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℂ (ι → ℂ) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    let φ : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
      { toAlgHom := diagonalAlgHom (n := ι) (α := ℂ) ℂ
        map_star' := by
          intro x
          ext i j
          simp [diagonal] <;> split_ifs <;> simp_all }
    have hself : IsSelfAdjoint (fun i => (d i : ℂ)) := by
      change star (fun i => (d i : ℂ)) = _
      ext i
      simp
    have hD : 0 ≤ diagonal (fun i => (d i : ℂ)) := by
      apply Matrix.PosSemidef.nonneg
      apply Matrix.PosSemidef.diagonal
      intro i
      change (0 : ℂ) ≤ (d i : ℂ)
      exact_mod_cast hd i
    have hmap := φ.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (fun x : ℝ => x ^ s) (fun i => (d i : ℂ))
      (Real.continuous_rpow_const hs).continuousOn
      (show Continuous φ from continuous_id.matrix_diagonal) hself hD.isSelfAdjoint
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hD]
    change cfc (fun x : ℝ => x ^ s) (φ (fun i => (d i : ℂ))) = _
    rw [← hmap, cfc_map_pi (S := ℂ) (p := IsSelfAdjoint)
      (q := fun _ => IsSelfAdjoint) (fun x : ℝ => x ^ s)
      (fun i => (d i : ℂ)) (Real.continuous_rpow_const hs).continuousOn
      hself (by intro i; change star (d i : ℂ) = _; simp)]
    change diagonal (fun i => cfc (fun x : ℝ => x ^ s) (d i : ℂ)) = _
    congr 1
    funext i
    simpa using (cfc_algebraMap (A := ℂ) (d i) (fun x : ℝ => x ^ s))

/-- The two retained values are actual positive labels; they may coincide. -/
private theorem coincident_two_values (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hn : ¬ Function.Injective p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p i = a ∨ p i = b := by
  classical
  by_cases h01 : p 0 = p 1
  · refine ⟨p 0, p 2, hp 0, hp 2, ?_⟩
    intro i
    fin_cases i <;> simp_all
  · by_cases h02 : p 0 = p 2
    · refine ⟨p 0, p 1, hp 0, hp 1, ?_⟩
      intro i
      fin_cases i <;> simp_all
    · have h12 : p 1 = p 2 := by
        by_contra h12
        apply hn
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      refine ⟨p 0, p 1, hp 0, hp 1, ?_⟩
      intro i
      fin_cases i <;> simp_all

/-- Coincident labels in the unchanged actual factorial CFC supplier. -/
private theorem coincidentLevel_proof : CoincidentLevelObligation := by
  classical
  intro n _ _ level p hp hn S hS Z hZ
  obtain ⟨a, b, ha, hb, hab⟩ := coincident_two_values p hp hn
  let L := {i : n // p (level i) = a}
  let R := {i : n // ¬ p (level i) = a}
  -- sumCompl has forward map Sum.elim Subtype.val Subtype.val and inverse
  -- i ↦ if h : p (level i) = a then inl ⟨i,h⟩ else inr ⟨i,h⟩.
  -- Thus neither fiber nor the original carrier needs an inhabitant.
  let q : (L ⊕ R) ≃ n := Equiv.sumCompl (fun i : n => p (level i) = a)
  have hleft (i : L) : p (level (q (Sum.inl i))) = a := i.property
  have hright (i : R) : p (level (q (Sum.inr i))) = b :=
    (hab (level i.val)).resolve_left i.property
  let r : ℝ := b / a
  have hr : 0 < r := div_pos hb ha
  have har : a * r = b := by
    dsimp [r]
    field_simp [ha.ne'] <;> ring
  let e := HsfBalancedCfcBridge.spectralFrame q (1 : unitary (Matrix n n ℂ))
  have he_apply (M : Matrix (L ⊕ R) (L ⊕ R) ℂ) (i j : L ⊕ R) :
      e M (q i) (q j) = M i j := by
    change ((1 : Matrix n n ℂ) * Matrix.reindex q q M *
      star (1 : Matrix n n ℂ)) (q i) (q j) = M i j
    simp [Matrix.reindex_apply]
  have he_back (M : Matrix n n ℂ) : e (M.submatrix q q) = M := by
    ext i j
    obtain ⟨i, rfl⟩ := q.surjective i
    obtain ⟨j, rfl⟩ := q.surjective j
    exact he_apply (M.submatrix q q) i j
  have he_smul (x : ℝ) (M : Matrix (L ⊕ R) (L ⊕ R) ℂ) :
      e (x • M) = x • e M :=
    (e.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul x M
  let S0 : Matrix (L ⊕ R) (L ⊕ R) ℂ := S.submatrix q q
  let Z0 : Matrix (L ⊕ R) (L ⊕ R) ℂ := Z.submatrix q q
  have hS0 : S0.PosSemidef := hS.submatrix q
  have hZ0 : Z0.IsHermitian := hZ.submatrix q
  have hZ_back : (e Z0).IsHermitian := by
    change star (e Z0) = e Z0
    rw [← map_star, show star Z0 = Z0 from hZ0]
  have hZ_actual : Z.IsHermitian := by
    rw [← he_back Z]
    exact hZ_back
  let A : Matrix L L ℂ := S0.toBlocks₁₁
  let C : Matrix L R ℂ := S0.toBlocks₁₂
  let H : Matrix R R ℂ := S0.toBlocks₂₂
  have hdir : HsfBalancedSpectralCertificate.direction A C H = S0 := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact hS0.isHermitian.apply (Sum.inr i) (Sum.inl j)
      | inr j => rfl
  have hdirPSD : (HsfBalancedSpectralCertificate.direction A C H).PosSemidef := by
    rw [hdir]
    exact hS0
  let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
  let Q : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
    HsfBalancedSpectralCertificate.baseRoot r
  have hP_pull : P.submatrix q q = a • Q := by
    change (diagonal (fun i => (p (level i) : ℂ))).submatrix q q = a • Q
    rw [Matrix.submatrix_diagonal_equiv]
    ext i j
    cases i <;> cases j <;>
      simp [Q, Function.comp_def, hleft, hright,
        HsfBalancedSpectralCertificate.baseRoot, HsfBalancedSpectralCertificate.gramDiag,
        diagonal, Matrix.one_apply, RCLike.real_smul_eq_coe_mul, mul_ite,
        ← Complex.ofReal_mul, har]
  have hP_scale : P = a • e Q := by
    calc
      P = e (P.submatrix q q) := (he_back P).symm
      _ = e (a • Q) := congrArg e hP_pull
      _ = a • e Q := he_smul a Q
  let Y : Matrix n n ℂ := (a ^ 3) • e (Q ^ 3)
  have hY_actual : Y = P ^ 3 := by
    dsimp only [Y]
    rw [hP_scale, smul_pow, map_pow]
  have hP_nonneg : 0 ≤ P := by
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (p (level i) : ℂ)
    exact_mod_cast (hp (level i)).le
  have hroot_actual : CFC.rpow Y (1/3 : ℝ) = P := by
    rw [hY_actual, ← CFC.rpow_natCast P 3 hP_nonneg]
    change CFC.rpow (CFC.rpow P (3 : ℝ)) (1/3 : ℝ) = P
    calc
      CFC.rpow (CFC.rpow P (3 : ℝ)) (1/3 : ℝ) =
          CFC.rpow P ((3 : ℝ)*(1/3 : ℝ)) :=
        CFC.rpow_rpow_of_exponent_nonneg P (3 : ℝ) (1/3 : ℝ)
          (by norm_num) (by norm_num) hP_nonneg
      _ = P := by norm_num [CFC.rpow_one P hP_nonneg]
  have hr_half : r ^ (3/2 : ℝ) = r * Real.sqrt r := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hb_half : b ^ (3/2 : ℝ) = a ^ (3/2 : ℝ) * (r * Real.sqrt r) := by
    calc
      b ^ (3/2 : ℝ) = (a * r) ^ (3/2 : ℝ) :=
        congrArg (fun x : ℝ => x ^ (3/2 : ℝ)) har.symm
      _ = a ^ (3/2 : ℝ) * (r * Real.sqrt r) := by
        rw [Real.mul_rpow ha.le hr.le, hr_half]
  let D : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
    HsfBalancedSpectralCertificate.gramDiag 1 (r * Real.sqrt r)
  have hD_pull : (CFC.rpow P (3/2 : ℝ)).submatrix q q =
      a ^ (3/2 : ℝ) • D := by
    change (CFC.rpow (diagonal (fun i => (p (level i) : ℂ))) (3/2 : ℝ)).submatrix q q = _
    rw [coincident_diagonal_rpow (fun i => p (level i))
      (fun i => (hp (level i)).le) (3/2 : ℝ) (by norm_num),
      Matrix.submatrix_diagonal_equiv]
    ext i j
    cases i <;> cases j <;>
      simp [D, Function.comp_def, hleft, hright,
        HsfBalancedSpectralCertificate.gramDiag, diagonal, Matrix.one_apply,
        RCLike.real_smul_eq_coe_mul, mul_ite, ← Complex.ofReal_mul, hb_half]
  have hD_scale : CFC.rpow P (3/2 : ℝ) = a ^ (3/2 : ℝ) • e D := by
    calc
      CFC.rpow P (3/2 : ℝ) =
          e ((CFC.rpow P (3/2 : ℝ)).submatrix q q) := (he_back _).symm
      _ = e (a ^ (3/2 : ℝ) • D) := congrArg e hD_pull
      _ = a ^ (3/2 : ℝ) • e D := he_smul _ D
  have hr_square : (r * Real.sqrt r) * (r * Real.sqrt r) = r ^ 3 := by
    calc
      _ = r ^ 2 * (Real.sqrt r) ^ 2 := by ring
      _ = r ^ 3 := by rw [Real.sq_sqrt hr.le]; ring
  have hK_blocks : HsfBalancedSpectralCertificate.baseDirection r A C H = D * S0 * D := by
    rw [← hdir]
    simp only [D, HsfBalancedSpectralCertificate.baseDirection,
      HsfBalancedSpectralCertificate.gramDiag, HsfBalancedSpectralCertificate.direction,
      fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      smul_zero, one_smul, zero_add, add_zero, hr_square]
  have ha_half_square : a ^ (3/2 : ℝ) * a ^ (3/2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_add ha]
    norm_num
  let K : Matrix n n ℂ :=
    (a ^ 3) • e (HsfBalancedSpectralCertificate.baseDirection r A C H)
  have hK_actual : K = CFC.rpow P (3/2 : ℝ) * S * CFC.rpow P (3/2 : ℝ) := by
    dsimp only [K]
    rw [hK_blocks, map_mul, map_mul, he_back S, hD_scale]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha_half_square]
  let F : ℝ → Matrix n n ℂ := fun t => P⁻¹ *
    CFC.rpow (P ^ 3 + t • (CFC.rpow P (3/2 : ℝ) * S *
      CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
  let Ft : ℝ → Matrix n n ℂ := fun t => (CFC.rpow Y (1/3 : ℝ))⁻¹ *
    CFC.rpow (Y + t • K) (2/3 : ℝ) * (CFC.rpow Y (1/3 : ℝ))⁻¹
  -- Global equality, including negative t; no differentiability premise.
  have hcurve_actual : Ft = F := by
    funext t
    dsimp only [Ft, F]
    rw [hroot_actual, hY_actual, hK_actual]
  let B := RpowPencilTaylor.jetCoeff F
  have hjet_actual (j : ℕ) : RpowPencilTaylor.jetCoeff Ft j = B j := by
    rw [hcurve_actual]
  have htransport := HsfBalancedCfcBridge.transported_twoLevel_supplier
    r hr (a ^ 3) (pow_pos ha 3) A C H hdirPSD q
    (1 : unitary (Matrix n n ℂ)) Z hZ_actual
  have hsupplier := le_trans htransport.1 htransport.2
  change 0 ≤ HsfBalancedSpectralCertificate.tr (RpowPencilTaylor.jetCoeff Ft 3) +
    2 * HsfBalancedSpectralCertificate.tr (Z * RpowPencilTaylor.jetCoeff Ft 2) +
    HsfBalancedSpectralCertificate.tr (RpowPencilTaylor.jetCoeff Ft 1 * Z * Z) -
    (5/48 : ℝ) * HsfBalancedSpectralCertificate.tr
      ((RpowPencilTaylor.jetCoeff Ft 1) ^ 3) at hsupplier
  rw [hjet_actual 1, hjet_actual 2, hjet_actual 3] at hsupplier
  have htrace_actual :
      (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
        (5/48 : ℝ) • (B 1) ^ 3).trace.re =
      HsfBalancedSpectralCertificate.tr (B 3) +
        2 * HsfBalancedSpectralCertificate.tr (Z * B 2) +
        HsfBalancedSpectralCertificate.tr (B 1 * Z * Z) -
        (5/48 : ℝ) * HsfBalancedSpectralCertificate.tr ((B 1) ^ 3) := by
    simp [HsfBalancedSpectralCertificate.tr, pow_two, Matrix.mul_assoc]
  change 0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
    (5/48 : ℝ) • (B 1) ^ 3).trace.re
  rw [htrace_actual]
  exact hsupplier

/-- Exact additional PD statement. This retains the Sylvester operator and
its Hermitian solution, rather than an ordinary matrix inverse surrogate.
No such statement is asserted for singular PSD directions. -/
private def PDSylvesterObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ∀ (S : Matrix n n ℂ), S.PosDef →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X := firstMatrix level p S
    let D := qMatrix level p S-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P)

/- Singular PSD directions receive the supplier statement. The additional
Sylvester energy and rigidity below require a positive-definite direction. -/



/-- Actual at-most-three-positive-level supplier, with the unchanged original
factorial CFC jets, arbitrary finite complex matrices and all Hermitian Z. -/
theorem actual_threeLevel_supplier : ThreeLevelSupplierTarget.{u} := by
  classical
  intro n _ _ level p hp S hS Z hZ
  by_cases hinj : Function.Injective p
  · let X : Matrix n n ℂ := firstMatrix level p S
    let Q : Matrix n n ℂ := qMatrix level p S
    let W : Matrix n n ℂ := Z+(1/3 : ℝ) • X
    obtain ⟨hfirst, hmixed, hcubic⟩ :=
      orderedMoment_proof n level p hp hinj S hS.isHermitian
    -- Hermiticity uses the ordered congruence sum, with no commutation
    -- assumption on S, Z, Q, X or the lifted coefficient matrices.
    have hX : X.IsHermitian := by
      change Xᴴ = X
      calc
        Xᴴ = (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a)ᴴ :=
          congrArg (fun A : Matrix n n ℂ => Aᴴ) hfirst.symm
        _ = ∑ a, (liftedV level p a)ᴴ*S*liftedV level p a := by
          simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hS.isHermitian.eq, mul_assoc]
        _ = X := hfirst
    have hW : W.IsHermitian := by
      exact hZ.add (hX.smul (show IsSelfAdjoint (1/3 : ℝ) from rfl))
    have henergy := ordered_row_square S W
      (liftedM level p S) (liftedV level p) hW
    rw [hcubic, hmixed, hfirst] at henergy
    -- The mixed moment is 2 • Q; the square contributes -2 times its
    -- real trace. Thus the ordered cross term is -4 Re tr(Q*W).
    simp only [realTrace, Matrix.smul_mul, Matrix.trace_smul,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at henergy
    change rowEnergy S W (liftedM level p S) (liftedV level p) =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        2*(2*(Q*W).trace.re)+4*(X*W*W).trace.re at henergy
    have hpositive := rowEnergy_nonneg S W
      (liftedM level p S) (liftedV level p) hS
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P^3 + t • (CFC.rpow P (3/2 : ℝ) * S *
        CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    change 0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re
    have hshift := actual_shifted_identity (fun i => p (level i))
      (fun i => hp (level i)) S Z hS.isHermitian
    -- firstMatrix and qMatrix are definitionally the owner's X and Q
    -- after pulling p back along level. The curve and factorial jets
    -- above are definitionally the original target, including singular S.
    change 6*(B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        4*(Q*W).trace.re+4*(X*W*W).trace.re at hshift
    linarith only [hpositive, henergy, hshift]
  · exact coincidentLevel_proof n level p hp hinj S hS Z hZ


section PDContinuation
variable {n : Type u} [Fintype n] [DecidableEq n]

private theorem pd_realTrace_smul (r : ℝ) (A : Matrix n n ℂ) :
    realTrace (r • A) = r * realTrace A := by
  simp only [realTrace, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

/-- A weighted square has zero real trace precisely when its row matrix
vanishes. This uses strict positivity of S, not entrywise positivity. -/
private theorem pd_weighted_trace_zero (S N : Matrix n n ℂ) (hS : S.PosDef) :
    realTrace (Nᴴ*S*N) = 0 ↔ N = 0 := by
  constructor
  · intro h
    have hT := hS.posSemidef.conjTranspose_mul_mul_same N
    have ht : (Nᴴ*S*N).trace = 0 := by
      apply Complex.ext
      · exact h
      · exact (Complex.nonneg_iff.mp hT.trace_nonneg).2.symm
    have hmat : Nᴴ*S*N = 0 := hT.trace_eq_zero_iff.mp ht
    have hcol (j : n) : (fun i => N i j) = 0 := by
      by_contra hj
      have hp := hS.re_dotProduct_pos hj
      have he : star (fun i => N i j) ⬝ᵥ (S *ᵥ (fun i => N i j)) = 0 := by
        change (Nᴴ*(S*N)) j j = 0
        rw [← mul_assoc, hmat]
        rfl
      rw [he] at hp
      exact (lt_irrefl 0) hp
    ext i j
    exact congrFun (hcol j) i
  · rintro rfl
    simp [realTrace]

private theorem pd_rowEnergy_zero {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hS : S.PosDef)
    (h : rowEnergy S W M V = 0) :
    ∀ a, M a-(V a*W+V a*W) = 0 := by
  have hnonneg (a : ι) :
      0 ≤ realTrace ((M a-(V a*W+V a*W))ᴴ*S*(M a-(V a*W+V a*W))) :=
    (Complex.nonneg_iff.mp
      (hS.posSemidef.conjTranspose_mul_mul_same (M a-(V a*W+V a*W))).trace_nonneg).1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ (Finset.univ : Finset ι)) => hnonneg a)).mp h
  intro a
  exact (pd_weighted_trace_zero S _ hS).mp (hz a (Finset.mem_univ a))

/-- Common kernel of the diagonal V maps is zero, since their squared
coefficients sum to tau(a,a)=1. No fiber inhabitance is used. -/
private theorem pd_first_posDef (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.PosDef) : (firstMatrix level p S).PosDef := by
  have hfirst := ordered_first_moment level p hp hinj S
  have hps : (firstMatrix level p S).PosSemidef := by
    rw [← hfirst]
    exact Matrix.posSemidef_sum _ fun a _ =>
      hS.posSemidef.conjTranspose_mul_mul_same (liftedV level p a)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hps.isHermitian
  intro z hz
  have hi : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  obtain ⟨i, hi⟩ := hi
  have hv : dot (v p (level i)) (v p (level i)) = 1 := by
    rw [v_gram p hp hinj, tau_self (hp (level i))]
  have ha : ∃ a, v p (level i) a ≠ 0 := by
    by_contra! h
    simp only [dot, h, zero_mul, Finset.sum_const_zero] at hv
    norm_num at hv
  obtain ⟨a, ha⟩ := ha
  have hvz : liftedV level p a *ᵥ z ≠ 0 := by
    intro h
    have he := congrFun h i
    have hc : (v p (level i) a : ℂ) ≠ 0 := by exact_mod_cast ha
    exact (mul_ne_zero hc hi) (by simpa only [liftedV, Matrix.mulVec_diagonal,
      Pi.zero_apply] using he)
  have hform : star z ⬝ᵥ (firstMatrix level p S *ᵥ z) =
      ∑ b, star (liftedV level p b *ᵥ z) ⬝ᵥ
        (S *ᵥ (liftedV level p b *ᵥ z)) := by
    rw [← hfirst, Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have hpos : 0 < (star z ⬝ᵥ (firstMatrix level p S *ᵥ z)).re := by
    rw [hform, Complex.re_sum]
    exact Finset.sum_pos'
      (fun b _ => hS.posSemidef.re_dotProduct_nonneg _)
      ⟨a, Finset.mem_univ a, hS.re_dotProduct_pos hvz⟩
  exact Complex.pos_iff.mpr
    ⟨hpos, (Complex.nonneg_iff.mp (hps.dotProduct_mulVec_nonneg z)).2⟩

private theorem pd_q_hermitian (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) : (qMatrix level p S).IsHermitian := by
  let A := ∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
    (liftedM level p S a)ᴴ*S*liftedV level p a)
  have hA : A.IsHermitian := by
    change Aᴴ = A
    dsimp only [A]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS.eq,
      mul_assoc, add_comm]
  have he : qMatrix level p S = (1/2 : ℝ) • A := by
    dsimp only [A]
    rw [ordered_mixed_moment level p hp hinj S hS, smul_smul]
    norm_num
  rw [he]
  exact hA.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)

/-- Solve the actual Sylvester equation in a unitary eigenbasis. The
entrywise denominator is lambda_i+lambda_j, never an ordinary inverse of X.
The final clause proves injectivity on ALL matrices, hence uniqueness. -/
private theorem pd_sylvester_spectral (X D : Matrix n n ℂ)
    (hX : X.PosDef) (hD : D.IsHermitian) :
    ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      ∀ Z : Matrix n n ℂ, X*Z+Z*X = 0 → Z = 0 := by
  let U := hX.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let l : n → ℝ := hX.isHermitian.eigenvalues
  let L : Matrix n n ℂ := diagonal (fun i => (l i : ℂ))
  have hspec : X = φ L := hX.isHermitian.spectral_theorem
  have hl (i : n) : 0 < l i := hX.eigenvalues_pos i
  have hden (i j : n) : (l i : ℂ)+(l j : ℂ) ≠ 0 := by
    exact_mod_cast (add_pos (hl i) (hl j)).ne'
  let E : Matrix n n ℂ := φ.symm D
  let T : Matrix n n ℂ := fun i j => E i j / ((l i : ℂ)+(l j : ℂ))
  have hE : E.IsHermitian := (hD.isSelfAdjoint.map φ.symm).isHermitian
  have hT : T.IsHermitian := by
    ext i j
    change star (E j i / ((l j : ℂ)+(l i : ℂ))) =
      E i j / ((l i : ℂ)+(l j : ℂ))
    rw [star_div₀, hE.apply i j]
    congr 1
    simp [add_comm]
  have hsolve : L*T+T*L = E := by
    ext i j
    simp only [Matrix.add_apply, L, Matrix.diagonal_mul, Matrix.mul_diagonal, T]
    field_simp [hden i j] <;> ring
  refine ⟨φ T, ?_, ?_, ?_⟩
  · exact (hT.isSelfAdjoint.map φ).isHermitian
  · calc
      X*φ T+φ T*X = φ (L*T+T*L) := by
        rw [map_add, map_mul, map_mul, ← hspec]
      _ = φ E := congrArg φ hsolve
      _ = D := φ.apply_symm_apply D
  · intro Z hZ
    have hd : L*φ.symm Z+φ.symm Z*L = 0 := by
      have h := congrArg φ.symm hZ
      simpa only [hspec, map_add, map_mul, φ.symm_apply_apply, map_zero] using h
    have hz : φ.symm Z = 0 := by
      ext i j
      have he := congrArg (fun A : Matrix n n ℂ => A i j) hd
      simp only [Matrix.add_apply, L, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.zero_apply] at he
      have he' : ((l i : ℂ)+(l j : ℂ)) * (φ.symm Z) i j = 0 := by
        linear_combination he
      exact (mul_eq_zero.mp he').resolve_left (hden i j)
    have h := congrArg φ hz
    simpa only [φ.apply_symm_apply, map_zero] using h

/-- Pure cyclic-trace calculation at an actual Sylvester solution. In
particular it assumes no commutation between X, D and Y. -/
private theorem pd_energy_identity (S X D Y : Matrix n n ℂ)
    (h : X*Y+Y*X = D) :
    4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) =
      3*((4*realTrace (S^3)-realTrace (X^3))/3-
        4*realTrace ((X^2+D)*((1/2 : ℝ) • X+Y))+
        4*realTrace (X*((1/2 : ℝ) • X+Y)*((1/2 : ℝ) • X+Y))) := by
  have hxyx : realTrace (X*Y*X) = realTrace (X*X*Y) := by
    simpa only [mul_assoc] using realTrace_comm (X*Y) X
  have hyxy : realTrace (Y*X*Y) = realTrace (X*Y*Y) := by
    simpa only [mul_assoc] using realTrace_comm Y (X*Y)
  have hdy : realTrace (D*Y) = 2*realTrace (X*Y*Y) := by
    rw [← h, add_mul, realTrace_add, hyxy]
    ring
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    realTrace_add, realTrace_sub, pd_realTrace_smul, smul_smul,
    pow_succ, pow_zero, mul_one, one_mul, ← mul_assoc]
  rw [hxyx]
  linarith only [hdy, realTrace_comm D X]

private theorem pd_residual_nonzero (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    ∃ a : Fin 2, m p i j (.inr (j,a)) ≠ 0 := by
  have hi := column_indices j
  have hr := residualE_pos p hp hinj (left j) j hi.1
  have hdet := (canonical_residual_blocks p hp hinj).2 j
  have hrad : 0 < residualE p (right j) j-
      (residualY p j)^2/residualE p (left j) j := by
    apply (div_pos hdet hr).trans_eq
    field_simp [hr.ne'] <;> ring
  rcases off_column_cases i j hij with hleft | hright
  · subst i
    refine ⟨0, ?_⟩
    simpa only [ite_true, ite_false, m, if_neg hi.1, ite_true, residualFirst,
      Matrix.cons_val_zero] using (Real.sqrt_pos.mpr hr).ne'
  · subst i
    refine ⟨1, ?_⟩
    simpa only [ite_true, ite_false, m, if_neg hi.2.1, ite_true, if_neg hi.2.2.1.symm,
      residualSecond, Matrix.cons_val_one, Matrix.cons_val_zero]
      using (Real.sqrt_pos.mpr hrad).ne'

private theorem pd_commute_iff (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) :
    diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ)) ↔
    ∀ i j, p (level i) ≠ p (level j) → S i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun A : Matrix n n ℂ => A i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : ((p (level i) : ℂ)-(p (level j) : ℂ))*S i j = 0 := by
      linear_combination he
    have hc : (p (level i) : ℂ)-(p (level j) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hij
    exact (mul_eq_zero.mp hz).resolve_left hc
  · intro h
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases he : p (level i) = p (level j)
    · rw [he, mul_comm]
    · rw [h i j he, mul_zero, zero_mul]

/-- The W-independent residual coordinates force off-level entries to zero.
There is no argument from merely pointwise positivity or an unattained infimum. -/
private theorem pd_zero_row_commutes (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S W : Matrix n n ℂ) (hS : S.PosDef)
    (h : rowEnergy S W (liftedM level p S) (liftedV level p) = 0) :
    diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ)) := by
  have hrow := pd_rowEnergy_zero S W (liftedM level p S) (liftedV level p) hS h
  have hV (a : Fin 3 × Fin 2) : liftedV level p (.inr a) = 0 := by
    ext i j
    simp [liftedV, v]
  have hM (a : Fin 3 × Fin 2) : liftedM level p S (.inr a) = 0 := by
    simpa only [hV, zero_mul, zero_add, sub_zero] using hrow (.inr a)
  apply (pd_commute_iff level p S).mpr
  intro i j hij
  have hlev : level i ≠ level j := fun he => hij (congrArg p he)
  obtain ⟨a, ha⟩ := pd_residual_nonzero p hp hinj (level i) (level j) hlev
  have he := congrArg (fun A : Matrix n n ℂ => A i j) (hM (level j,a))
  change (m p (level i) (level j) (.inr (level j,a)) : ℂ)*S i j = 0 at he
  have hc : (m p (level i) (level j) (.inr (level j,a)) : ℂ) ≠ 0 := by
    exact_mod_cast ha
  exact (mul_eq_zero.mp he).resolve_left hc

/-- Under the desired commutation conclusion, the original X and Q reduce
to S and S^2. Q is identified by the ordered mixed moment, not by imposing
commutativity on arbitrary intermediate matrices. -/
private theorem pd_commuting_moments (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (hc : diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ))) :
    firstMatrix level p S = S ∧ qMatrix level p S = S^2 := by
  have hoff (i j : n) (hij : level i ≠ level j) : S i j = 0 :=
    (pd_commute_iff level p S).mp hc i j (fun h => hij (hinj h))
  have hX : firstMatrix level p S = S := by
    ext i j
    by_cases he : level i = level j
    · change (HsfLocalSpectrumSupplier.spectralTau (p (level i))
        (p (level j)) : ℂ)*S i j = S i j
      rw [← tau_spectral, he, tau_self (hp (level j))]
      simp
    · simp only [firstMatrix, hoff i j he, mul_zero]
  have hM (a : Coeff) : liftedM level p S a = liftedV level p a*S := by
    ext i j
    change (m p (level i) (level j) a : ℂ)*S i j =
      (diagonal (fun k => (v p (level k) a : ℂ))*S) i j
    rw [Matrix.diagonal_mul]
    by_cases he : level i = level j
    · rw [he, m_diagonal]
    · rw [hoff i j he, mul_zero, mul_zero]
  have hfirst := ordered_first_moment level p hp hinj S
  have hmixed := ordered_mixed_moment level p hp hinj S hS
  have hcross :
      (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
        (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      firstMatrix level p S*S+S*firstMatrix level p S := by
    have ha (a : Coeff) :
        (liftedV level p a)ᴴ*S*liftedM level p S a+
          (liftedM level p S a)ᴴ*S*liftedV level p a =
        ((liftedV level p a)ᴴ*S*liftedV level p a)*S+
          S*((liftedV level p a)ᴴ*S*liftedV level p a) := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, hS.eq]
      noncomm_ring
    simp_rw [ha]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hfirst]
  have htwo : (2 : ℝ) • qMatrix level p S = (2 : ℝ) • S^2 := by
    rw [← hmixed, hcross, hX, pow_two, two_smul]
  have hQ := congrArg (fun A : Matrix n n ℂ => (1/2 : ℝ) • A) htwo
  norm_num [smul_smul] at hQ
  exact ⟨hX, hQ⟩

/-- Exact original PD target for injective labels. All witnesses and both
rigidity implications are supplied; the next lemma removes injectivity. -/
private theorem pd_sylvester_injective (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X := firstMatrix level p S
    let D := qMatrix level p S-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P) := by
  let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
  let X := firstMatrix level p S
  let Q := qMatrix level p S
  let D := Q-X^2
  have hX : X.PosDef := pd_first_posDef level p hp hinj S hS
  have hQ : Q.IsHermitian := pd_q_hermitian level p hp hinj S hS.isHermitian
  have hD : D.IsHermitian := hQ.sub (hX.isHermitian.pow 2)
  obtain ⟨Y, hY, hsolve, huniq⟩ := pd_sylvester_spectral X D hX hD
  let W := (1/2 : ℝ) • X+Y
  have hW : W.IsHermitian :=
    (hX.isHermitian.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)).add hY
  obtain ⟨hfirst, hmixed, hcubic⟩ :=
    orderedMoment_proof n level p hp hinj S hS.isHermitian
  have hrow := ordered_row_square S W (liftedM level p S) (liftedV level p) hW
  rw [hcubic, hmixed, hfirst] at hrow
  simp only [Matrix.smul_mul, pd_realTrace_smul] at hrow
  change rowEnergy S W (liftedM level p S) (liftedV level p) =
    (4*realTrace (S^3)-realTrace (X^3))/3-
      2*(2*realTrace (Q*W))+4*realTrace (X*W*W) at hrow
  have hQD : Q = X^2+D := by
    dsimp only [D]
    abel
  have hid := pd_energy_identity S X D Y hsolve
  have henergy :
      4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) =
        3*rowEnergy S W (liftedM level p S) (liftedV level p) := by
    rw [hrow, hQD]
    dsimp only [W]
    linarith only [hid]
  have hnonneg := rowEnergy_nonneg S W (liftedM level p S) (liftedV level p)
    hS.posSemidef
  change X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
    0 ≤ 4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) ∧
    ((4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) = 0) ↔ P*S = S*P)
  refine ⟨hX, Y, hY, hsolve, ?_, ?_⟩
  · rw [henergy]
    exact mul_nonneg (by norm_num) hnonneg
  · constructor
    · intro hzero
      have hr : rowEnergy S W (liftedM level p S) (liftedV level p) = 0 := by
        linarith only [henergy, hzero]
      exact pd_zero_row_commutes level p hp hinj S W hS hr
    · intro hcomm
      obtain ⟨hXS, hQS⟩ := pd_commuting_moments level p hp hinj S hS.isHermitian hcomm
      have hDz : D = 0 := by
        dsimp only [D, Q, X]
        rw [hXS, hQS, sub_self]
      have hYz : Y = 0 := huniq Y (hsolve.trans hDz)
      change X = S at hXS
      rw [hXS, hDz, hYz]
      simp [realTrace]

/-- Three positive distinct slots retaining any two prescribed distinct
values. The unused third value exceeds both. -/
private theorem pd_two_slot_completion (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    (∀ i : Fin 3, 0 < (![a,b,a+b+1] : Fin 3 → ℝ) i) ∧
      Function.Injective (![a,b,a+b+1] : Fin 3 → ℝ) := by
  constructor
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · change 0 < a+b+1
      linarith
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      norm_num at h
    all_goals first | rfl | exact False.elim (hab h) |
      exact False.elim (hab h.symm) | linarith

/-- Faithful positive injective relabeling, including repeated labels and
unused fibers. This changes no pulled-back spectral value. -/
private theorem pd_faithful_relabel (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    ∃ (q : Fin 3 → ℝ) (r : Fin 3 → Fin 3),
      (∀ i, 0 < q i) ∧ Function.Injective q ∧ ∀ i, q (r i) = p i := by
  classical
  by_cases h01 : p 0 = p 1
  · by_cases h02 : p 0 = p 2
    · let q : Fin 3 → ℝ := ![p 0, p 0+1, p 0+(p 0+1)+1]
      have hq := pd_two_slot_completion (p 0) (p 0+1) (hp 0)
        (by linarith [hp 0]) (by linarith)
      refine ⟨q, fun _ => 0, hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · exact h01
      · exact h02
    · let q : Fin 3 → ℝ := ![p 0, p 2, p 0+p 2+1]
      have hq := pd_two_slot_completion (p 0) (p 2) (hp 0) (hp 2) h02
      refine ⟨q, ![0,0,1], hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · exact h01
      · rfl
  · by_cases h02 : p 0 = p 2
    · let q : Fin 3 → ℝ := ![p 0, p 1, p 0+p 1+1]
      have hq := pd_two_slot_completion (p 0) (p 1) (hp 0) (hp 1) h01
      refine ⟨q, ![0,1,0], hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · rfl
      · exact h02
    · by_cases h12 : p 1 = p 2
      · let q : Fin 3 → ℝ := ![p 0, p 1, p 0+p 1+1]
        have hq := pd_two_slot_completion (p 0) (p 1) (hp 0) (hp 1) h01
        refine ⟨q, ![0,1,1], hq.1, hq.2, ?_⟩
        intro i
        fin_cases i
        · rfl
        · rfl
        · exact h12
      · refine ⟨p, id, hp, ?_, fun _ => rfl⟩
        intro i j he
        fin_cases i <;> fin_cases j <;> simp_all

/-- Closed source proof of the exact ORIGINAL private PD obligation.
There is no supplier, Sylvester-solvability, or commutativity premise. -/
private theorem pdSylvester_proof : PDSylvesterObligation.{u} := by
  classical
  intro n _ _ level p hp S hS
  obtain ⟨q, r, hq, hqi, hr⟩ := pd_faithful_relabel p hp
  have ht := pd_sylvester_injective (r ∘ level) q hq hqi S hS
  have hX : firstMatrix (r ∘ level) q S = firstMatrix level p S := by
    ext i j
    simp only [firstMatrix, Function.comp_apply, hr]
  have hQ : qMatrix (r ∘ level) q S = qMatrix level p S := by
    ext i j
    simp only [qMatrix, Function.comp_apply, hr]
  rw [hX, hQ] at ht
  simpa only [Function.comp_apply, hr] using ht

end PDContinuation

/-- Original Hermitian Sylvester energy and exact rigidity for at most three
positive spectral levels, arbitrary finite complex PD directions, including
empty carriers and repeated labels. -/
theorem actual_threeLevel_PD_sylvester
    (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X : Matrix n n ℂ := fun i j =>
      (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level k))*
        HsfLocalSpectrumSupplier.spectralTau (p (level k)) (p (level j))+
        3*HsfLocalSpectrumSupplier.spectralKernel (p (level i)) (p (level j))
          (p (level k)) : ℝ) : ℂ)*S i k*S k j
    let D := Q-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P) := by
  exact pdSylvester_proof n level p hp S hS

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
