/- GID: D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol
   generality: I
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.claim; result=D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.result; claim=D5/S3/Quantum/ProcessReconstruction/ThreeQueryPhaseProtocol.claim
   digest: A three-query phase-dephasing protocol beats every pure parallel probe with finite memory. -/

import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace D5.S3.Quantum.ProcessReconstruction.ThreeQueryPhaseCertificate

abbrev Mat := Matrix (Fin 8) (Fin 8) ℂ
def c (a b : ℝ) : ℂ := ⟨a, b⟩

def coherenceContrast : Mat :=
  !![0, c 0 (5 / 8), c 0 (5 / 8), c 0 (15 / 16), c 0 (5 / 8), c 0 (15 / 16), c 0 (15 / 16), c 0 (2035 / 2048);
    c 0 (-5 / 8), 0, 0, c 0 (5 / 8), 0, c 0 (5 / 8), c 0 (845 / 2048), c 0 (15 / 16);
    c 0 (-5 / 8), 0, 0, c 0 (5 / 8), 0, c 0 (845 / 2048), c 0 (5 / 8), c 0 (15 / 16);
    c 0 (-15 / 16), c 0 (-5 / 8), c 0 (-5 / 8), 0, c 0 (-845 / 2048), 0, 0, c 0 (5 / 8);
    c 0 (-5 / 8), 0, 0, c 0 (845 / 2048), 0, c 0 (5 / 8), c 0 (5 / 8), c 0 (15 / 16);
    c 0 (-15 / 16), c 0 (-5 / 8), c 0 (-845 / 2048), 0, c 0 (-5 / 8), 0, 0, c 0 (5 / 8);
    c 0 (-15 / 16), c 0 (-845 / 2048), c 0 (-5 / 8), 0, c 0 (-5 / 8), 0, 0, c 0 (5 / 8);
    c 0 (-2035 / 2048), c 0 (-15 / 16), c 0 (-15 / 16), c 0 (-5 / 8), c 0 (-15 / 16), c 0 (-5 / 8), c 0 (-5 / 8), 0]

private def parallelDual : Mat :=
  !![(2159137 / 2000000), (476283 / 625000), (476283 / 625000), (2669701 / 10000000), (476283 / 625000), (2669701 / 10000000), (2669701 / 10000000), (-4077929 / 10000000);
    (476283 / 625000), (2159137 / 2000000), (4335781 / 5000000), (7312089 / 10000000), (4335781 / 5000000), (7312089 / 10000000), (7312089 / 10000000), (2669701 / 10000000);
    (476283 / 625000), (4335781 / 5000000), (2159137 / 2000000), (7312089 / 10000000), (4335781 / 5000000), (7312089 / 10000000), (7312089 / 10000000), (2669701 / 10000000);
    (2669701 / 10000000), (7312089 / 10000000), (7312089 / 10000000), (2159137 / 2000000), (7312089 / 10000000), (4335781 / 5000000), (4335781 / 5000000), (476283 / 625000);
    (476283 / 625000), (4335781 / 5000000), (4335781 / 5000000), (7312089 / 10000000), (2159137 / 2000000), (7312089 / 10000000), (7312089 / 10000000), (2669701 / 10000000);
    (2669701 / 10000000), (7312089 / 10000000), (7312089 / 10000000), (4335781 / 5000000), (7312089 / 10000000), (2159137 / 2000000), (4335781 / 5000000), (476283 / 625000);
    (2669701 / 10000000), (7312089 / 10000000), (7312089 / 10000000), (4335781 / 5000000), (7312089 / 10000000), (4335781 / 5000000), (2159137 / 2000000), (476283 / 625000);
    (-4077929 / 10000000), (2669701 / 10000000), (2669701 / 10000000), (476283 / 625000), (2669701 / 10000000), (476283 / 625000), (476283 / 625000), (2159137 / 2000000)]

def adaptiveGram : Mat :=
  !![(2989 / 10000), 0, (6 / 625), 0, (6 / 625), 0, 0, 0;
    0, (711 / 10000), 0, (-6 / 625), 0, (-6 / 625), 0, 0;
    (6 / 625), 0, (649 / 10000), 0, 0, 0, (-6 / 625), 0;
    0, (-6 / 625), 0, (651 / 10000), 0, 0, 0, (6 / 625);
    (6 / 625), 0, 0, 0, (651 / 10000), 0, (-6 / 625), 0;
    0, (-6 / 625), 0, 0, 0, (649 / 10000), 0, (6 / 625);
    0, 0, (-6 / 625), 0, (-6 / 625), 0, (711 / 10000), 0;
    0, 0, 0, (6 / 625), 0, (6 / 625), 0, (2989 / 10000)]

def adaptiveTest : Mat :=
  !![0, c 0 (16469 / 400000), c 0 (404987 / 10000000), c 0 (4409 / 1250000), c 0 (202829 / 5000000), c 0 (33907 / 10000000), c 0 (-8303 / 5000000), c 0 (2578323 / 10000000);
    c 0 (-16469 / 400000), 0, c 0 (12639 / 5000000), c 0 (404239 / 10000000), c 0 (25201 / 10000000), c 0 (403569 / 10000000), c 0 (-297809 / 10000000), c 0 (-8303 / 5000000);
    c 0 (-404987 / 10000000), c 0 (-12639 / 5000000), 0, c 0 (416541 / 10000000), c 0 (3 / 10000000), c 0 (-116573 / 5000000), c 0 (403569 / 10000000), c 0 (33907 / 10000000);
    c 0 (-4409 / 1250000), c 0 (-404239 / 10000000), c 0 (-416541 / 10000000), 0, c 0 (233757 / 10000000), c 0 (3 / 10000000), c 0 (25201 / 10000000), c 0 (202829 / 5000000);
    c 0 (-202829 / 5000000), c 0 (-25201 / 10000000), c 0 (-3 / 10000000), c 0 (-233757 / 10000000), 0, c 0 (416541 / 10000000), c 0 (404239 / 10000000), c 0 (4409 / 1250000);
    c 0 (-33907 / 10000000), c 0 (-403569 / 10000000), c 0 (116573 / 5000000), c 0 (-3 / 10000000), c 0 (-416541 / 10000000), 0, c 0 (12639 / 5000000), c 0 (404987 / 10000000);
    c 0 (8303 / 5000000), c 0 (297809 / 10000000), c 0 (-403569 / 10000000), c 0 (-25201 / 10000000), c 0 (-404239 / 10000000), c 0 (-12639 / 5000000), 0, c 0 (16469 / 400000);
    c 0 (-2578323 / 10000000), c 0 (8303 / 5000000), c 0 (-33907 / 10000000), c 0 (-202829 / 5000000), c 0 (-4409 / 1250000), c 0 (-404987 / 10000000), c 0 (-16469 / 400000), 0]

private def parallelFactor : Mat :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    c (7620528 / 10795685) (-1250000 / 2159137), 1, 0, 0, 0, 0, 0, 0;
    c (7620528 / 10795685) (-1250000 / 2159137), (-1173165062938 / 6470622540147), 1, 0, 0, 0, 0, 0;
    c (2669701 / 10795685) (-1875000 / 2159137), c (10555273 / 281331414789) (-1412912500000 / 2156874180049), c (242771279 / 5297457477209) (-4238737500000 / 5297457477209), 1, 0, 0, 0, 0;
    c (7620528 / 10795685) (-1250000 / 2159137), (-1173165062938 / 6470622540147), (-1173165062938 / 5297457477209), c (171892019154439 / 192885250147006694) (-11991061472208203125 / 3086164002352107104), 1, 0, 0, 0;
    c (2669701 / 10795685) (-1875000 / 2159137), c (10555273 / 281331414789) (-1412912500000 / 2156874180049), c (242771279 / 5297457477209) (25280821950802734375 / 60013073433928601104), c (-556872574336812125 / 192885250147006694) (-2750143394921875 / 3086164002352107104), c (2920720737439629369 / 77078710494692247673567) (-64340888803603187500000 / 77078710494692247673567), 1, 0, 0;
    c (2669701 / 10795685) (-1875000 / 2159137), c (10555273 / 281331414789) (54475069140625 / 103529960642352), c (242771279 / 5297457477209) (-17364719266602734375 / 30006536716964300552), c (-556872574336812125 / 192885250147006694) (-2750143394921875 / 3086164002352107104), c (2920720737439629369 / 77078710494692247673567) (-64340888803603187500000 / 77078710494692247673567), (27460376599329507876886 / 104539087094021755550453), 1, 0;
    c (-4077929 / 10795685) (-31796875 / 34546192), c (-245116479742 / 2156874180049) (-935546875 / 19411867620441), c (-735349439226 / 5297457477209) (-935546875 / 15892372431627), c (-521346751227119 / 1157311500882040164) (6402040711574609375 / 9258492007056321312), c (-22701795638156438801887 / 77078710494692247673567) (-57390191424746875000 / 231236131484076743020701), c (59836935644011861840 / 104539087094021755550453) (-34907918094248743750000 / 104539087094021755550453), c (84510551852240 / 186429124433968179) (-49302113993750000 / 186429124433968179), 1]

private def parallelDiag : Mat := diagonal ![(2159137 / 2000000), (19411867620441 / 107956850000000), (3750817089620537569 / 21568741800490000000), (289327875220510041 / 26487287386045000000), (231236131484076743020701 / 493786240376337136640000000), (3773051089151079478314241878366249 / 139711711378873327961702533752320000000), (6728646964005210426166875807 / 267620062960695694209159680000000), (2380564685069204239219 / 159086186183652846080000000)]

private theorem factor_diag_apply (L : Mat) (d : Fin 8 → ℂ) (i j : Fin 8) :
    (L * diagonal d * Lᴴ) i j = ∑ k, L i k * d k * star (L j k) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

private theorem parallel_plus_posSemidef : (parallelDual + coherenceContrast).PosSemidef := by
  have hD : parallelDiag.PosSemidef := by
    unfold parallelDiag
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
  have hfac : parallelFactor * parallelDiag * parallelFactorᴴ = parallelDual + coherenceContrast := by
    apply Matrix.ext
    intro i j
    simp only [parallelDiag, factor_diag_apply, Fin.sum_univ_succ, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [parallelFactor, parallelDual, coherenceContrast, c, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.star_def]
  rw [← hfac]
  exact hD.mul_mul_conjTranspose_same parallelFactor

private def adaptiveFactor : Mat :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    c 0 (-16469 / 119560), 1, 0, 0, 0, 0, 0, 0;
    c (96 / 2989) (-404987 / 2989000), c (-6669730903 / 78226460975) (-920652336 / 15645292195), 1, 0, 0, 0, 0, 0;
    c 0 (-4409 / 373625), c (-12058654568 / 78226460975) (-9666162968 / 15645292195), c (-36342112182321 / 571074652846870) (-8681948908008847 / 11421493056937400), 1, 0, 0, 0, 0;
    c (96 / 2989) (-202829 / 1494500), c (-6680781602 / 78226460975) (-918811112 / 15645292195), c (-31814843487462 / 285537326423435) (298777563241 / 5710746528468700), c (-981736807394302178938 / 1081777313073595384723) (-3731585094536915959750 / 1081777313073595384723), 1, 0, 0, 0;
    c 0 (-33907 / 2989000), c (-12036174383 / 78226460975) (-9650141928 / 15645292195), c (-72214073773197 / 1142149305693740) (16095092807418017 / 45685972227749600), c (-31753815041790247394759 / 12981327756883144616676) (2937205872042570282125 / 3245331939220786154169), c (-120206750972606181353 / 1534567591992955525710) (-191783573204231685380619 / 255761265332159254285000), 1, 0, 0;
    c 0 (8303 / 1494500), c (273484214 / 78226460975) (7121208808 / 15645292195), c (-7434478007889 / 57107465284687) (-1481786011906487 / 2284298611387480), c (-2576256131169355702585 / 1081777313073595384723) (1260599194813446321750 / 1081777313073595384723), c (-32964889205373020293 / 255761265332159254285) (-24035422740780026562194 / 31970158166519906785625), c (1791803377097814071182896 / 46148485965749108977851637) (3816637073644696642818000 / 46148485965749108977851637), 1, 0;
    c 0 (-2578323 / 2989000), c (-42462401487 / 78226460975) (397082672 / 15645292195), c (-740506123939059 / 1142149305693740) (5571138111404279 / 45685972227749600), c (14598356787080725462367 / 12981327756883144616676) (2586160053206951271875 / 1081777313073595384723), c (-279521579652635045797 / 306913518398591105142) (23426272940328304784021 / 767283795996477762855000), c (8656984524313491724573639 / 46148485965749108977851637) (-34668178572198848414822000 / 46148485965749108977851637), c (725718709326462654179 / 231701801413617581082886) (-124675695296658596345910187 / 231701801413617581082886000), 1]

private def adaptiveDiag : Mat := diagonal ![(2989 / 10000), (3129058439 / 47824000000), (57107465284687 / 977830762187500), (3245331939220786154169 / 713843316058587500000000), (153456759199295552571 / 8654218504588763077784000), (46148485965749108977851637 / 30691351839859110514200000000000), (347552702120426371624329 / 230742429828745544889258185000), (13657999493643646348718896289 / 2317018014136175810828860000000000)]

private theorem adaptive_plus_posDef : (adaptiveGram + adaptiveTest).PosDef := by
  have hD : adaptiveDiag.PosDef := by
    unfold adaptiveDiag
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.pos_iff, Complex.div_re, Complex.div_im]
  have hfac : adaptiveFactor * adaptiveDiag * adaptiveFactorᴴ = adaptiveGram + adaptiveTest := by
    apply Matrix.ext
    intro i j
    simp only [adaptiveDiag, factor_diag_apply, Fin.sum_univ_succ, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [adaptiveFactor, adaptiveGram, adaptiveTest, c, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im, Complex.star_def]
  rw [← hfac]
  have htri : adaptiveFactor.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [adaptiveFactor] at *
  have hdet : adaptiveFactor.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    have hd (i : Fin 8) : adaptiveFactor i i = 1 := by
      fin_cases i <;> rfl
    simp [hd]
  have hunit : IsUnit adaptiveFactor :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  exact hD.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hunit)

private theorem parallel_minus_posSemidef : (parallelDual - coherenceContrast).PosSemidef := by
  have ht := Matrix.posSemidef_transpose_iff.mpr parallel_plus_posSemidef
  convert ht using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [parallelDual, coherenceContrast, c, Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im]

private theorem adaptive_minus_posSemidef : (adaptiveGram - adaptiveTest).PosSemidef := by
  have ht := Matrix.posSemidef_transpose_iff.mpr adaptive_plus_posDef.posSemidef
  convert ht using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [adaptiveGram, adaptiveTest, c, Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im]

theorem adaptive_trace_exact :
    (Matrix.trace (coherenceContrast * adaptiveTest)).re = 88529493 / 81920000 := by
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ, coherenceContrast,
    adaptiveTest, c, Complex.re_sum, Complex.add_re, Complex.mul_re]

private theorem parallel_diagonal_le (i : Fin 8) :
    (parallelDual i i).re ≤ 2159137 / 2000000 := by
  fin_cases i <;> norm_num [parallelDual, Complex.div_re]

/-- Positive trace pairing with the two dual slack matrices bounds every
diagonal Gram and compressed test. -/
theorem parallel_trace_pairing_le (p : Fin 8 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (X : Mat)
    (hplus : (diagonal (fun i => (p i : ℂ)) + X).PosSemidef)
    (hminus : (diagonal (fun i => (p i : ℂ)) - X).PosSemidef) :
    (Matrix.trace (coherenceContrast * X)).re ≤ 2159137 / 2000000 := by
  let P : Mat := diagonal (fun i => (p i : ℂ))
  have h1 := RHLinalg.trace_mul_nonneg_of_posSemidef parallel_minus_posSemidef hplus
  have h2 := RHLinalg.trace_mul_nonneg_of_posSemidef parallel_plus_posSemidef hminus
  change 0 ≤ ((parallelDual - coherenceContrast) * (P + X)).trace.re at h1
  change 0 ≤ ((parallelDual + coherenceContrast) * (P - X)).trace.re at h2
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re] at h1 h2
  have htest : (coherenceContrast * X).trace.re ≤ (parallelDual * P).trace.re := by
    linarith only [h1, h2]
  have hdual : (parallelDual * P).trace.re ≤ 2159137 / 2000000 := by
    simp only [Matrix.trace, Matrix.diag_apply, P, Matrix.mul_diagonal, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ ∑ i, (2159137 / 2000000 : ℝ) * p i := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (parallel_diagonal_le i) (hp i)
      _ = _ := by rw [← Finset.mul_sum, hp1, mul_one]
  exact htest.trans hdual

theorem adaptive_gram_plus_test_pos :
    (adaptiveGram + adaptiveTest).PosSemidef := adaptive_plus_posDef.posSemidef

theorem adaptive_gram_minus_test_pos :
    (adaptiveGram - adaptiveTest).PosSemidef := adaptive_minus_posSemidef

theorem adaptive_gram_posDef : adaptiveGram.PosDef := by
  have h := (adaptive_plus_posDef.add_posSemidef adaptive_minus_posSemidef).smul
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have he : (adaptiveGram + adaptiveTest) + (adaptiveGram - adaptiveTest) =
      (2 : ℝ) • adaptiveGram := by
    rw [two_smul]
    abel
  simpa only [he, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] using h

end D5.S3.Quantum.ProcessReconstruction.ThreeQueryPhaseCertificate


set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder CStarAlgebra Matrix MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.ProcessReconstruction.ThreeQueryPhaseProtocol

open ThreeQueryPhaseCertificate
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm trace_norm_jordan_mass)
open D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality (hermitian_traceNorm_le_tests)

abbrev Prefix := Bool × Bool

/-- Computational order 000, 001, 010, 011, 100, 101, 110, 111.
The last coordinate is the qubit queried after the control. -/
def pathIndex : (Prefix × Bool) ≃ Fin 8 where
  toFun p := ⟨4 * p.1.1.toNat + 2 * p.1.2.toNat + p.2.toNat, by
    rcases p with ⟨⟨a, b⟩, j⟩
    cases a <;> cases b <;> cases j <;> decide⟩
  invFun i := ((decide (4 ≤ i.val), decide (i.val % 4 ≥ 2)), decide (i.val % 2 = 1))
  left_inv := by
    rintro ⟨⟨a, b⟩, j⟩
    cases a <;> cases b <;> cases j <;> decide
  right_inv := by
    intro i
    fin_cases i <;> decide

def coherence (plus : Bool) : ℂ := ⟨3 / 4, if plus then 5 / 16 else -(5 / 16)⟩

def bitCorrelation (plus : Bool) : Bool → Bool → ℂ
  | false, false => 1
  | false, true => coherence plus
  | true, false => star (coherence plus)
  | true, true => 1

/-- One channel use on the qubit selected by `bit`, with every other
computational coordinate retained as memory. -/
def phaseQuery {n : Type*} (plus : Bool) (bit : n → Bool)
    (X : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => bitCorrelation plus (bit i) (bit j) * X i j

private def krausEntry (plus : Bool) : Bool → Bool → ℂ
  | false, false => 1
  | false, true => star (coherence plus)
  | true, false => 0
  | true, true => ((Real.sqrt 87 / 16 : ℝ) : ℂ)

private theorem kraus_correlation (plus i j : Bool) :
    (∑ r, krausEntry plus r i * star (krausEntry plus r j)) =
      bitCorrelation plus i j := by
  have hs : Real.sqrt 87 * Real.sqrt 87 = 87 := Real.mul_self_sqrt (by norm_num)
  cases plus <;> cases i <;> cases j <;>
    apply Complex.ext <;>
    norm_num [Fintype.sum_bool, krausEntry, bitCorrelation, coherence, Complex.star_def,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_div,
      Complex.div_re, Complex.div_im] <;> nlinarith [hs]

/-- The entrywise action is CPTP on the joint qubit and memory, via
two explicit diagonal Kraus matrices. -/
theorem phaseQuery_channel {n : Type*} [Fintype n] [DecidableEq n]
    (plus : Bool) (bit : n → Bool) :
    ∃ C : QuantumChannel n n, ∀ X : Matrix n n ℂ,
      CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        phaseQuery plus bit X := by
  let K (r : Bool) : Matrix n n ℂ := diagonal (fun i => krausEntry plus r (bit i))
  have hK : (∑ r, (K r)ᴴ * K r) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [K, Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
        mul_comm] using (kraus_correlation plus (bit i) (bit i)).trans
          (by cases bit i <;> rfl)
    · simp [K, Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
        Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]
  obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
  refine ⟨C, fun X => (hC X).trans ?_⟩
  ext i j
  simp only [Matrix.sum_apply, K, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, phaseQuery, Matrix.of_apply]
  rw [← kraus_correlation, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.star_apply]; ring

private theorem phaseQuery_trace {n : Type*} [Fintype n]
    (b : Bool) (bit : n → Bool) (X : Matrix n n ℂ) :
    (phaseQuery b bit X).trace = X.trace := by
  have h (j : Bool) : bitCorrelation b j j = 1 := by cases j <;> rfl
  simp [Matrix.trace, phaseQuery, h]

private theorem phaseQuery_pos {n : Type*} [Fintype n] [DecidableEq n]
    (b : Bool) (bit : n → Bool) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (phaseQuery b bit X).PosSemidef := by
  obtain ⟨C, hC⟩ := phaseQuery_channel b bit
  rw [← hC X]
  exact Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg C.toCompletelyPositiveMap
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg)))

private def prefixCorrelation (plus : Bool) (p q : Prefix) : ℂ :=
  bitCorrelation plus p.1 q.1 * bitCorrelation plus p.2 q.2

def pathCorrelation (plus : Bool) : Mat :=
  Matrix.of fun i j =>
    prefixCorrelation plus (pathIndex.symm i).1 (pathIndex.symm j).1 *
      bitCorrelation plus (pathIndex.symm i).2 (pathIndex.symm j).2

theorem pathCorrelation_sub : pathCorrelation true - pathCorrelation false = coherenceContrast := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [pathCorrelation, prefixCorrelation, bitCorrelation, coherence, pathIndex,
      coherenceContrast, ThreeQueryPhaseCertificate.c, Matrix.sub_apply, Complex.star_def,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im] <;> rfl

private theorem pathCorrelation_hermitian (plus : Bool) : (pathCorrelation plus).IsHermitian := by
  have hc (i j : Bool) : star (bitCorrelation plus j i) = bitCorrelation plus i j := by
    cases i <;> cases j <;> simp [bitCorrelation]
  change (pathCorrelation plus)ᴴ = pathCorrelation plus
  ext i j
  simp [pathCorrelation, prefixCorrelation, Matrix.conjTranspose_apply, star_mul, hc,
    mul_comm, mul_left_comm, mul_assoc]

def pureDensity {n : Type*} (ψ : n → ℂ) : Matrix n n ℂ := vecMulVec ψ (star ψ)

def parallelOutput {m : Type*} (plus : Bool) (ψ : Fin 8 × m → ℂ) :
    Matrix (Fin 8 × m) (Fin 8 × m) ℂ :=
  phaseQuery plus (fun i => (pathIndex.symm i.1).2)
    (phaseQuery plus (fun i => (pathIndex.symm i.1).1.2)
      (phaseQuery plus (fun i => (pathIndex.symm i.1).1.1) (pureDensity ψ)))

def parallelPaths {m : Type*} (ψ : Fin 8 × m → ℂ) : Matrix (Fin 8 × m) (Fin 8) ℂ :=
  Matrix.of fun x i => if i = x.1 then ψ x else 0

theorem parallel_output_expansion {m : Type*} (plus : Bool) (ψ : Fin 8 × m → ℂ) :
    parallelOutput plus ψ = parallelPaths ψ * pathCorrelation plus * (parallelPaths ψ)ᴴ := by
  ext x y
  simp [parallelOutput, phaseQuery, pathCorrelation, prefixCorrelation, parallelPaths,
    pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, apply_ite, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq',
    mul_assoc, mul_left_comm, mul_comm]

theorem parallel_output_difference {m : Type*} (ψ : Fin 8 × m → ℂ) :
    parallelOutput true ψ - parallelOutput false ψ =
      parallelPaths ψ * coherenceContrast * (parallelPaths ψ)ᴴ := by
  rw [parallel_output_expansion, parallel_output_expansion, ← pathCorrelation_sub,
    Matrix.mul_sub, Matrix.sub_mul]

private def parallelWeight {m : Type*} [Fintype m] (ψ : Fin 8 × m → ℂ) (i : Fin 8) : ℝ :=
  ∑ k, Complex.normSq (ψ (i, k))

private theorem parallel_gram {m : Type*} [Fintype m] (ψ : Fin 8 × m → ℂ) :
    (parallelPaths ψ)ᴴ * parallelPaths ψ = diagonal (fun i => (parallelWeight ψ i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hterm (a : Fin 8) (k : m) :
        star (parallelPaths ψ (a,k) i) * parallelPaths ψ (a,k) i =
          if i = a then (Complex.normSq (ψ (a,k)) : ℂ) else 0 := by
      by_cases h : i = a <;>
        simp [parallelPaths, h, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      hterm, Matrix.diagonal_apply_eq, parallelWeight, Complex.ofReal_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.conjTranspose_apply]
    by_cases h : i = x.1
    · have hn : j ≠ x.1 := fun hj => hij (h.trans hj.symm)
      simp [parallelPaths, hn]
    · simp [parallelPaths, h]

private theorem compress_trace {n : Type*} [Fintype n] (V : Matrix n (Fin 8) ℂ)
    (H : Mat) (M : Matrix n n ℂ) :
    (M * (V * H * Vᴴ)).trace = (H * (Vᴴ * M * V)).trace := by
  calc
    _ = ((M * V) * H * Vᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (H * Vᴴ * (M * V)).trace := (Matrix.trace_mul_cycle H Vᴴ (M * V)).symm
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Every binary test on the three query outputs and arbitrary finite memory
obeys the same rational upper bound. -/
theorem parallel_test_le {m : Type*} [Fintype m] [DecidableEq m] (ψ : Fin 8 × m → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1)
    (M : Matrix (Fin 8 × m) (Fin 8 × m) ℂ)
    (hplus : (1 + M).PosSemidef) (hminus : (1 - M).PosSemidef) :
    (M * (parallelOutput true ψ - parallelOutput false ψ)).trace.re ≤ 2159137 / 2000000 := by
  classical
  let V := parallelPaths ψ
  have hgram : Vᴴ * V = diagonal (fun i => (parallelWeight ψ i : ℂ)) := parallel_gram ψ
  have hVplus := hplus.conjTranspose_mul_mul_same V
  have hVminus := hminus.conjTranspose_mul_mul_same V
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgram] at hVplus
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgram] at hVminus
  rw [parallel_output_difference, compress_trace]
  exact parallel_trace_pairing_le (parallelWeight ψ)
    (fun i => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
    (by simpa only [parallelWeight, Fintype.sum_prod_type] using hψ) _ hVplus hVminus

private theorem contraction_slacks {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (hn : ‖M‖ ≤ 1) :
    (1 + M).PosSemidef ∧ (1 - M).PosSemidef := by
  have hu : algebraMap ℝ (Matrix n n ℂ) ‖M‖ ≤ 1 := by
    rw [← map_one (algebraMap ℝ (Matrix n n ℂ))]
    exact algebraMap_mono (Matrix n n ℂ) hn
  have hl : -(1 : Matrix n n ℂ) ≤ M :=
    (neg_le_neg hu).trans (IsSelfAdjoint.neg_algebraMap_norm_le_self M hM)
  exact ⟨by simpa only [sub_neg_eq_add, add_comm] using Matrix.le_iff.mp hl,
    Matrix.le_iff.mp ((IsSelfAdjoint.le_algebraMap_norm_self M hM).trans hu)⟩

theorem parallel_trace_distance_le {m : Type*} [Fintype m] [DecidableEq m]
    (ψ : Fin 8 × m → ℂ) (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    traceNorm (parallelOutput true ψ - parallelOutput false ψ) / 2 ≤ 2159137 / 4000000 := by
  have hout (b : Bool) : (parallelOutput b ψ).IsHermitian := by
    rw [parallel_output_expansion]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ (pathCorrelation_hermitian b)
  have h := hermitian_traceNorm_le_tests _ ((hout true).sub (hout false)) (2159137 / 2000000)
    (fun M hM hn => parallel_test_le ψ hψ M
      (contraction_slacks M hM hn).1 (contraction_slacks M hM hn).2)
  linarith

def prefixProbability (p : Prefix) : ℝ := if p.1 = p.2 then 37 / 100 else 13 / 100

def adaptiveInput (p : Prefix) : ℂ := Real.sqrt (prefixProbability p)

private theorem prefixProbability_pos (p : Prefix) : 0 < prefixProbability p := by
  unfold prefixProbability
  split <;> norm_num

private theorem input_inner (p : Prefix) :
    star (adaptiveInput p) * adaptiveInput p = (prefixProbability p : ℂ) := by
  rw [adaptiveInput, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (prefixProbability_pos p).le]

theorem adaptive_input_normalized : (pureDensity adaptiveInput).trace = 1 := by
  rw [pureDensity, Matrix.trace_vecMulVec, dotProduct_comm]
  simp only [dotProduct, Pi.star_apply, input_inner, ← Complex.ofReal_sum]
  norm_num [prefixProbability, Fintype.sum_prod_type, Fintype.sum_bool]

private def gramBlock (j : Bool) : Matrix Prefix Prefix ℂ :=
  adaptiveGram.submatrix (fun p => pathIndex (p, j)) (fun p => pathIndex (p, j))

private theorem gramBlock_sum :
    (∑ j, gramBlock j) = diagonal (fun p => (prefixProbability p : ℂ)) := by
  ext ⟨a,b⟩ ⟨d,e⟩
  cases a <;> cases b <;> cases d <;> cases e <;>
    norm_num [Fintype.sum_bool, gramBlock, pathIndex, Matrix.submatrix_apply,
      adaptiveGram, prefixProbability, Matrix.diagonal_apply, Matrix.add_apply,
      Complex.ofReal_div]

private theorem gram_cross_block (p q : Prefix) (j k : Bool) (h : j ≠ k) :
    adaptiveGram (pathIndex (p,j)) (pathIndex (q,k)) = 0 := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨d,e⟩
  cases j <;> cases k <;> simp at h <;>
    cases a <;> cases b <;> cases d <;> cases e <;> rfl

private def blockRoot (j : Bool) : Matrix Prefix Prefix ℂ := CFC.sqrt (gramBlock j)

private theorem blockRoot_hermitian (j : Bool) : (blockRoot j).IsHermitian :=
  (CFC.sqrt_nonneg (gramBlock j)).posSemidef.isHermitian

private theorem blockRoot_sq (j : Bool) : blockRoot j * blockRoot j = gramBlock j :=
  CFC.sqrt_mul_sqrt_self _ (adaptive_gram_posDef.posSemidef.submatrix
    (fun p => pathIndex (p,j))).nonneg

private def inverseInput : Matrix Prefix Prefix ℂ := diagonal (fun p => (adaptiveInput p)⁻¹)

private theorem input_ne_zero (p : Prefix) : adaptiveInput p ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (prefixProbability_pos p)).ne'

/-- The row with third-query bit `j` is the corresponding Gram-block
square root followed by inverse diagonal input amplitudes. -/
def adaptiveControl : Matrix (Fin 8) Prefix ℂ :=
  Matrix.of fun r p => (blockRoot (pathIndex.symm r).2 * inverseInput) (pathIndex.symm r).1 p

theorem adaptive_control_isometry : adaptiveControlᴴ * adaptiveControl = 1 := by
  let row (j : Bool) := blockRoot j * inverseInput
  have hstack : adaptiveControlᴴ * adaptiveControl = ∑ j, (row j)ᴴ * row j := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]
    rw [← pathIndex.sum_comp, Fintype.sum_prod_type_right]
    simp [adaptiveControl, row]
  have hrow (j : Bool) : (row j)ᴴ * row j = inverseInputᴴ * gramBlock j * inverseInput := by
    simp only [row, Matrix.conjTranspose_mul, (blockRoot_hermitian j).eq]
    rw [Matrix.mul_assoc _ _ (blockRoot j * inverseInput), ← Matrix.mul_assoc
      (blockRoot j), blockRoot_sq]
    simp only [Matrix.mul_assoc]
  rw [hstack]
  simp_rw [hrow]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, gramBlock_sum]
  ext p q
  by_cases hpq : p = q
  · subst q
    simp only [inverseInput, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    rw [← input_inner, star_inv₀, ← mul_assoc,
      inv_mul_cancel₀ (show star (adaptiveInput p) ≠ 0 from by simpa using input_ne_zero p),
      one_mul, mul_inv_cancel₀ (input_ne_zero p)]
  · simp [inverseInput, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_apply_ne _ hpq, Matrix.one_apply, hpq]

/-- Queries one and two act on the two retained input qubits. The control
then supplies a fresh query qubit with four-dimensional output memory. -/
def adaptiveOutput (plus : Bool) (ψ : Prefix → ℂ) (W : Matrix (Fin 8) Prefix ℂ) : Mat :=
  phaseQuery plus (fun i => (pathIndex.symm i).2)
    (W * phaseQuery plus Prod.snd (phaseQuery plus Prod.fst (pureDensity ψ)) * Wᴴ)

theorem adaptive_output_state (b : Bool) :
    (adaptiveOutput b adaptiveInput adaptiveControl).PosSemidef ∧
      (adaptiveOutput b adaptiveInput adaptiveControl).trace = 1 := by
  constructor
  · have hprefix : (phaseQuery b Prod.snd
        (phaseQuery b Prod.fst (pureDensity adaptiveInput))).PosSemidef :=
      phaseQuery_pos _ _ (phaseQuery_pos _ _ (Matrix.posSemidef_vecMulVec_self_star adaptiveInput))
    exact phaseQuery_pos _ _ (hprefix.mul_mul_conjTranspose_same adaptiveControl)
  · unfold adaptiveOutput
    rw [phaseQuery_trace, Matrix.trace_mul_cycle, adaptive_control_isometry,
      Matrix.one_mul, phaseQuery_trace, phaseQuery_trace, adaptive_input_normalized]

def adaptivePaths (ψ : Prefix → ℂ) (W : Matrix (Fin 8) Prefix ℂ) : Mat :=
  Matrix.of fun r i =>
    if (pathIndex.symm i).2 = (pathIndex.symm r).2 then
      W r (pathIndex.symm i).1 * ψ (pathIndex.symm i).1
    else 0

private theorem sum_path_sector (j : Bool) (f : Fin 8 → ℂ) :
    (∑ i, if (pathIndex.symm i).2 = j then f i else 0) = ∑ p : Prefix, f (pathIndex (p,j)) := by
  rw [← pathIndex.sum_comp, Fintype.sum_prod_type]
  cases j <;> simp [Fintype.sum_bool]

theorem adaptive_output_expansion (plus : Bool) (ψ : Prefix → ℂ)
    (W : Matrix (Fin 8) Prefix ℂ) :
    adaptiveOutput plus ψ W = adaptivePaths ψ W * pathCorrelation plus * (adaptivePaths ψ W)ᴴ := by
  ext r s
  simp only [adaptiveOutput, phaseQuery, Matrix.of_apply, pureDensity, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, adaptivePaths, apply_ite,
    star_zero, ite_mul, mul_ite, zero_mul, mul_zero]
  simp_rw [sum_path_sector]
  simp only [pathCorrelation, pathIndex.symm_apply_apply, Matrix.of_apply, star_mul,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by
    unfold prefixCorrelation
    ring

theorem adaptive_output_difference (ψ : Prefix → ℂ) (W : Matrix (Fin 8) Prefix ℂ) :
    adaptiveOutput true ψ W - adaptiveOutput false ψ W =
      adaptivePaths ψ W * coherenceContrast * (adaptivePaths ψ W)ᴴ := by
  rw [adaptive_output_expansion, adaptive_output_expansion, ← pathCorrelation_sub,
    Matrix.mul_sub, Matrix.sub_mul]

private abbrev V : Mat := adaptivePaths adaptiveInput adaptiveControl

private theorem realized_path (r i : Fin 8) :
    V r i = if (pathIndex.symm i).2 = (pathIndex.symm r).2 then
      blockRoot (pathIndex.symm r).2 (pathIndex.symm r).1 (pathIndex.symm i).1 else 0 := by
  simp [adaptivePaths, adaptiveControl, inverseInput, Matrix.mul_diagonal,
    mul_assoc, inv_mul_cancel₀ (input_ne_zero _)]

private theorem realized_path_hermitian : V.IsHermitian := by
  change Vᴴ = V
  ext r i
  simp only [Matrix.conjTranspose_apply, realized_path, apply_ite, star_zero]
  by_cases h : (pathIndex.symm i).2 = (pathIndex.symm r).2
  · rw [if_pos h.symm, if_pos h]
    conv_lhs => rw [h]
    exact congrArg (fun A : Matrix Prefix Prefix ℂ => A (pathIndex.symm r).1
      (pathIndex.symm i).1) (blockRoot_hermitian (pathIndex.symm r).2).eq
  · simp [h, Ne.symm h]

theorem adaptive_gram_realized : Vᴴ * V = adaptiveGram := by
  rw [realized_path_hermitian.eq]
  ext r i
  let r' := pathIndex.symm r
  let i' := pathIndex.symm i
  change (V * V) r i = adaptiveGram r i
  by_cases h : i'.2 = r'.2
  · calc
      (V * V) r i = ∑ p : Prefix, blockRoot r'.2 r'.1 p * blockRoot r'.2 p i'.1 := by
        rw [Matrix.mul_apply]
        simp only [realized_path, ite_mul, zero_mul]
        rw [sum_path_sector]
        simp only [pathIndex.symm_apply_apply, show (pathIndex.symm i).2 = r'.2 from h,
          show r'.2 = (pathIndex.symm r).2 from rfl, ite_true] <;> rfl
      _ = gramBlock r'.2 r'.1 i'.1 := congrArg (fun A : Matrix Prefix Prefix ℂ =>
        A r'.1 i'.1) (blockRoot_sq r'.2)
      _ = adaptiveGram r i := by
        change adaptiveGram (pathIndex r') (pathIndex (i'.1, r'.2)) = _
        rw [← h]
        simp [r', i']
  · have hz : (V * V) r i = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [realized_path, realized_path]
      by_cases hk : (pathIndex.symm k).2 = r'.2
      · have hn : (pathIndex.symm i).2 ≠ (pathIndex.symm r).2 := h
        simp [show (pathIndex.symm k).2 = (pathIndex.symm r).2 from hk, hn]
      · simp [show (pathIndex.symm k).2 ≠ (pathIndex.symm r).2 from hk]
    rw [hz]
    have hb := gram_cross_block r'.1 i'.1 r'.2 i'.2 (Ne.symm h)
    change adaptiveGram (pathIndex r') (pathIndex i') = 0 at hb
    simpa [r', i'] using hb.symm

/-- The square path matrix is Hermitian and invertible. Congruence by its
inverse pulls the certificate's test back to the physical output. -/
def adaptiveObservable : Mat := V⁻¹ * adaptiveTest * V⁻¹

private theorem adaptive_inverse_laws :
    V⁻¹ᴴ = V⁻¹ ∧ V⁻¹ * V = 1 ∧ V * V⁻¹ = 1 := by
  have hv : V * V = adaptiveGram := by
    simpa only [realized_path_hermitian.eq] using adaptive_gram_realized
  have hd : V.det ≠ 0 := by
    intro hz
    have hg := congrArg Matrix.det hv
    rw [Matrix.det_mul, hz, zero_mul] at hg
    exact ((Matrix.isUnit_iff_isUnit_det _).mp adaptive_gram_posDef.isUnit).ne_zero hg.symm
  exact ⟨by rw [Matrix.conjTranspose_nonsing_inv, realized_path_hermitian.eq],
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)⟩

theorem adaptive_observable_valid :
    adaptiveObservable.IsHermitian ∧ (1 + adaptiveObservable).PosSemidef ∧
      (1 - adaptiveObservable).PosSemidef := by
  obtain ⟨hstar, hleft, hright⟩ := adaptive_inverse_laws
  have hunit : V⁻¹ * adaptiveGram * V⁻¹ = 1 := by
    rw [← adaptive_gram_realized, realized_path_hermitian.eq,
      ← Matrix.mul_assoc V⁻¹ V V, hleft, Matrix.one_mul, hright]
  have hp := adaptive_gram_plus_test_pos.mul_mul_conjTranspose_same V⁻¹
  have hm := adaptive_gram_minus_test_pos.mul_mul_conjTranspose_same V⁻¹
  rw [hstar, Matrix.mul_add, Matrix.add_mul, hunit] at hp
  rw [hstar, Matrix.mul_sub, Matrix.sub_mul, hunit] at hm
  have hherm : adaptiveObservable.IsHermitian := by
    rw [← show (1 : Mat) - (1 - adaptiveObservable) = adaptiveObservable by abel]
    exact Matrix.isHermitian_one.sub hm.isHermitian
  exact ⟨hherm, hp, hm⟩

theorem adaptive_test_exact :
    (adaptiveObservable *
      (adaptiveOutput true adaptiveInput adaptiveControl -
        adaptiveOutput false adaptiveInput adaptiveControl)).trace.re = 88529493 / 81920000 := by
  rw [adaptive_output_difference, compress_trace]
  suffices Vᴴ * adaptiveObservable * V = adaptiveTest by rw [this, adaptive_trace_exact]
  obtain ⟨_, hleft, hright⟩ := adaptive_inverse_laws
  rw [realized_path_hermitian.eq, adaptiveObservable]
  calc
    _ = (V * V⁻¹) * adaptiveTest * (V⁻¹ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hright, hleft, Matrix.one_mul, Matrix.mul_one]

/-- The same two effects are measured under either hypothesis. -/
def adaptiveEffect (plusOutcome : Bool) : Mat :=
  (1 / 2 : ℝ) • (if plusOutcome then 1 + adaptiveObservable else 1 - adaptiveObservable)

theorem adaptive_effects_valid :
    (∀ b, (adaptiveEffect b).PosSemidef) ∧ adaptiveEffect true + adaptiveEffect false = 1 := by
  refine ⟨?_, ?_⟩
  · intro b
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    cases b
    · exact adaptive_observable_valid.2.2.smul hhalf
    · exact adaptive_observable_valid.2.1.smul hhalf
  · change (1 / 2 : ℝ) • (1 + adaptiveObservable) +
      (1 / 2 : ℝ) • (1 - adaptiveObservable) = 1
    rw [← smul_add, show (1 + adaptiveObservable) + (1 - adaptiveObservable) =
      (2 : ℝ) • (1 : Mat) by rw [two_smul]; abel, smul_smul]
    norm_num

theorem adaptive_outcome_gap :
    (adaptiveEffect true * adaptiveOutput true adaptiveInput adaptiveControl).trace.re -
      (adaptiveEffect true * adaptiveOutput false adaptiveInput adaptiveControl).trace.re =
      88529493 / 163840000 := by
  rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub]
  let Δ := adaptiveOutput true adaptiveInput adaptiveControl -
    adaptiveOutput false adaptiveInput adaptiveControl
  change (((1 / 2 : ℝ) • (1 + adaptiveObservable)) * Δ).trace.re = _
  have hzero : Δ.trace = 0 := by
    simp only [Δ, Matrix.trace_sub, (adaptive_output_state true).2,
      (adaptive_output_state false).2, sub_self]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add,
    hzero, zero_add, Complex.smul_re, smul_eq_mul,
    show (adaptiveObservable * Δ).trace.re = 88529493 / 81920000 from adaptive_test_exact]
  norm_num

private theorem trace_test_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (X M : Matrix n n ℂ) (hX : X.IsHermitian)
    (hp : (1 + M).PosSemidef) (hm : (1 - M).PosSemidef) :
    (M * X).trace.re ≤ traceNorm X := by
  let P : Matrix n n ℂ := posPart X
  let N : Matrix n n ℂ := negPart X
  have hh := RHLinalg.trace_mul_nonneg_of_posSemidef hm (CFC.posPart_nonneg X).posSemidef
  have hl := RHLinalg.trace_mul_nonneg_of_posSemidef hp (CFC.negPart_nonneg X).posSemidef
  change 0 ≤ ((1 - M) * P).trace.re at hh
  change 0 ≤ ((1 + M) * N).trace.re at hl
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hh
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at hl
  have hpair : (M * X).trace.re = (M * P).trace.re - (M * N).trace.re := by
    rw [← show P - N = X from CFC.posPart_sub_negPart X hX,
      Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [trace_norm_jordan_mass X hX, hpair]
  change (M * P).trace.re - (M * N).trace.re ≤ P.trace.re + N.trace.re
  linarith

theorem adaptive_trace_distance_ge :
    88529493 / 163840000 ≤ traceNorm
      (adaptiveOutput true adaptiveInput adaptiveControl -
        adaptiveOutput false adaptiveInput adaptiveControl) / 2 := by
  have hout (b : Bool) : (adaptiveOutput b adaptiveInput adaptiveControl).IsHermitian := by
    rw [adaptive_output_expansion]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ (pathCorrelation_hermitian b)
  have h := trace_test_le_traceNorm _ adaptiveObservable ((hout true).sub (hout false))
    adaptive_observable_valid.2.1 adaptive_observable_valid.2.2
  rw [adaptive_test_exact] at h
  linarith

/-- With one fixed preparation, isometry and binary observable, the
adaptive protocol exceeds the trace distance of every normalized pure
parallel input, including inputs entangled with arbitrary finite memory. -/
theorem three_query_adaptive_advantage :
    (pureDensity adaptiveInput).trace = 1 ∧
    adaptiveControlᴴ * adaptiveControl = 1 ∧
    adaptiveObservable.IsHermitian ∧ (1 + adaptiveObservable).PosSemidef ∧
    (1 - adaptiveObservable).PosSemidef ∧
    0 < (2281037 / 4096000000 : ℝ) ∧
    ∀ (m : Type*) [Fintype m] [DecidableEq m]
      (ψ : Fin 8 × m → ℂ), (∑ x, Complex.normSq (ψ x) = 1) →
      2281037 / 4096000000 ≤
        traceNorm (adaptiveOutput true adaptiveInput adaptiveControl -
          adaptiveOutput false adaptiveInput adaptiveControl) / 2 -
          traceNorm (parallelOutput true ψ - parallelOutput false ψ) / 2 := by
  refine ⟨adaptive_input_normalized, adaptive_control_isometry, adaptive_observable_valid.1,
    adaptive_observable_valid.2.1, adaptive_observable_valid.2.2, by norm_num, ?_⟩
  intro m _ _ ψ hψ
  have hp := parallel_trace_distance_le ψ hψ
  have ha := adaptive_trace_distance_ge
  linarith

#print axioms three_query_adaptive_advantage

/-- Parallel dominance in this channel pair would provide a normalized
parallel probe that performs at least as well as every admissible control. -/
def claim : Prop :=
  ∀ (ψ : Prefix → ℂ) (W : Matrix (Fin 8) Prefix ℂ),
    (pureDensity ψ).trace = 1 → Wᴴ * W = 1 →
    ∃ (m : Type) (fm : Fintype m) (dm : DecidableEq m),
      letI := fm
      letI := dm
      ∃ χ : Fin 8 × m → ℂ,
        (∑ x, Complex.normSq (χ x) = 1) ∧
        traceNorm (adaptiveOutput true ψ W - adaptiveOutput false ψ W) ≤
          traceNorm (parallelOutput true χ - parallelOutput false χ)

theorem result : ¬ claim := by
  intro h
  obtain ⟨m, fm, dm, χ, hχ, hle⟩ :=
    h adaptiveInput adaptiveControl adaptive_input_normalized adaptive_control_isometry
  letI := fm
  letI := dm
  have hp := parallel_trace_distance_le χ hχ
  have ha := adaptive_trace_distance_ge
  linarith

#print axioms result

end D5.S3.Quantum.ProcessReconstruction.ThreeQueryPhaseProtocol
