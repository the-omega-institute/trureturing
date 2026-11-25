/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NineFour
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/NineFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rational Gram certificate for the refined BMV trace bound at bidegree (9,4). -/

import D5.S3.Quantum.Analysis.RefinedBMV67
import D5.S3.Quantum.Analysis.RefinedBMV84

/-! # The refined BMV lower bound at bidegree (9,4)

-/

open Matrix NormedSpace
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV

namespace WeightedGram67

open private gramTerms gapTerms scaleTerms coefficientsVanish coefficients_sound
  weightedSum weightedSum_append weightedSum_scale traceWord traceWord_cyclicRep
  eval_gapTerms eval_gramTerms weightedGram_nonneg_of_ldl orderedTraceSum_re
  real_rat_mul from D5.S3.Quantum.Analysis.RefinedBMV67

open private Algebra84.ldlChecks Algebra84.ldlChecks_sound
  from D5.S3.Quantum.Analysis.RefinedBMV84

local notation "𝔞" => true
local notation "𝔟" => false

private def words94 : Fin 15 → List Bool :=
  ![[𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟]]

private def comparator94 : List Bool := [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟]

-- The integer matrix 400 • C K Cᵀ in the order of words94.
private def G94 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![15904, 15904, 3884, 9636, -3588, -11528, -1792, -6652, -9273, -11163, -3606, 1960, -3606, 1960, 1960;
    15904, 15904, 3884, 9636, -3588, -11528, -1792, -6652, -9273, -11163, -3606, 1960, -3606, 1960, 1960;
    3884, 3884, 101824, 34408, -37522, 14660, 41306, -48980, -52728, -6044, -8224, -12748, -8224, -12748, -12748;
    9636, 9636, 34408, 82720, -34646, 7513, 11865, -59144, -11940, -16868, -10152, -4292, -10152, -4292, -4292;
    -3588, -3588, -37522, -34646, 69044, -16452, -54980, 20612, 21892, 16452, 3588, 5200, 3588, 5200, 5200;
    -11528, -11528, 14660, 7513, -16452, 42358, 32973, -9676, -12518, -13686, -7788, -2180, -7788, -2180, -2180;
    -1792, -1792, 41306, 11865, -54980, 32973, 92880, -20556, -37720, -22488, -7548, -8200, -7548, -8200, -8200;
    -6652, -6652, -48980, -59144, 20612, -9676, -20556, 66400, 20364, 7472, 8404, 6668, 8404, 6668, 6668;
    -9273, -9273, -52728, -11940, 21892, -12518, -37720, 20364, 63972, 11912, -144, 5200, -144, 5200, 5200;
    -11163, -11163, -6044, -16868, 16452, -13686, -22488, 7472, 11912, 51440, -5236, 1536, -5236, 1536, 1536;
    -3606, -3606, -8224, -10152, 3588, -7788, -7548, 8404, -144, -5236, 25184, -5352, 25184, -5352, -5352;
    1960, 1960, -12748, -4292, 5200, -2180, -8200, 6668, 5200, 1536, -5352, 5200, -5352, 5200, 5200;
    -3606, -3606, -8224, -10152, 3588, -7788, -7548, 8404, -144, -5236, 25184, -5352, 25184, -5352, -5352;
    1960, 1960, -12748, -4292, 5200, -2180, -8200, 6668, 5200, 1536, -5352, 5200, -5352, 5200, 5200;
    1960, 1960, -12748, -4292, 5200, -2180, -8200, 6668, 5200, 1536, -5352, 5200, -5352, 5200, 5200]

-- Fraction elimination on K has ten positive pivots. At pivot 9 (zero-based)
-- the pivot and all remaining entries in its column are exactly zero.
-- The columns of C L for positive pivots are rescaled to primitive integers.
private def d94 : Fin 15 → ℚ :=
  ![1 / 25456,
    1 / 2879300642064,
    1 / 202316037213293568048,
    1 / 291767507435343792409445871610320,
    1 / 410024904470668476830149207459888182537,
    1 / 65030582512084935175888568077984840802059509870,
    1 / 1527314972634112099330901738962603885439460122646858462,
    1 / 1833064511167352671645312994863975902640179193230087565250394753,
    4 / 3024313649917287993896743832379993360857043451921377789363410803904399871,
    20222393380686293763099121006002223993283 / 119317158684576476126036142788522737999,
    0, 0, 0, 0, 0]

private def F94 : Matrix (Fin 15) (Fin 15) ℚ :=
  !![1942, 52970962, 26829420904, -1077941810219798096, 358180293080084846078, 233327795743423443014587, -58467264060096483972362581785, -2329657950434854077467090463693366, -53298806824090203198565376555665337875, -3, 0, 0, 0, 0, 0;
    1942, 52970962, 26829420904, -1077941810219798096, 358180293080084846078, 233327795743423443014587, -58467264060096483972362581785, -2329657950434854077467090463693366, -53298806824090203198565376555665337875, -3, 0, 0, 0, 0, 0;
    50912, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    17204, 452435676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -18761, -139796083, 3130195817036, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    7330, 16286402, -663081438679, 3328950880957300665, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    20653, -13319693, -2611555442069, 1625131539017199135, 3695082196761866807934, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -24490, -271060926, -684964151700, -292374273264958764, -1015760371443856964728, 28158759799854441949016488, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -26364, 37405404, 276497490228, -370908200250798108, -1167599434916028206841, -8790203699641276812513669, 216957704599192906853480173971, 0, 0, 0, 0, 0, 0, 0, 0;
    -3022, -94350330, 623319868680, -897423036372735168, -824253782340276530939, -11890040609403231604611124, 28587214149966397061673458198, 8448948676672954440068101134934043, 0, 0, 0, 0, 0, 0, 0;
    -4112, -46921616, -111213549848, -587492014857636952, -287641363919338761806, -3803707122951326350717231, -40275524832083624258958193309, -2005974805039958721227739112997197, 119317158684576476126036142788522737999, 0, 0, 0, 0, 0, 0;
    -6374, 100286, 32785371464, -20836419977045888, -276182155461065757990, -112585612131375905495469, -16019780321599695817504027327, 74105611425557052440519339482361, -44012234573657515284980510821904933416, 2, 0, 0, 0, 0, 0;
    -4112, -46921616, -111213549848, -587492014857636952, -287641363919338761806, -3803707122951326350717231, -40275524832083624258958193309, -2005974805039958721227739112997197, 119317158684576476126036142788522737999, 0, 0, 0, 0, 0, 0;
    -6374, 100286, 32785371464, -20836419977045888, -276182155461065757990, -112585612131375905495469, -16019780321599695817504027327, 74105611425557052440519339482361, -44012234573657515284980510821904933416, 2, 0, 0, 0, 0, 0;
    -6374, 100286, 32785371464, -20836419977045888, -276182155461065757990, -112585612131375905495469, -16019780321599695817504027327, 74105611425557052440519339482361, -44012234573657515284980510821904933416, 2, 0, 0, 0, 0, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
private theorem ldl94 : Algebra84.ldlChecks G94 d94 F94 = true := by
  decide +kernel

private def features94 (i : Fin 15) : List (ℚ × List Bool) :=
  [(1, words94 i)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
private theorem coefficients94 :
    coefficientsVanish
      (scaleTerms 5200 (gapTerms 9 55 comparator94) ++
        scaleTerms (-1) (gramTerms G94 [𝔞] [] features94)) = true := by
  simp only [gapTerms, balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem comparator94_eval (A B : Mat) :
    traceWord A B comparator94 = trace ((A ^ 3 * B) * (A ^ 2 * B) ^ 3) := by
  simp only [traceWord, comparator94, evalWord, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]

private theorem trace_gap94 (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((5200 : ℚ) : ℂ) * (((1 / 13 : ℚ) : ℂ) * orderedTraceSum A B 9 -
      ((55 : ℚ) : ℂ) * trace ((A ^ 3 * B) * (A ^ 2 * B) ^ 3)) =
      weightedGram G94 (fun i => weightedSum (evalWord A B) (features94 i)) A 1 := by
  have h := coefficients_sound (traceWord A B) (traceWord_cyclicRep A B) _ coefficients94
  apply eq_of_sub_eq_zero
  simp only [weightedSum_append, weightedSum_scale, eval_gapTerms,
    eval_gramTerms A B hA hB, comparator94_eval, Rat.cast_neg, Rat.cast_one, neg_one_mul,
    evalWord, mul_one, sub_eq_add_neg] at h ⊢
  norm_num at h ⊢
  exact h

/-- The integer-balanced lower bound at bidegree (9,4) for Hermitian B. -/
theorem balanced_bound94 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    715 * (trace ((A ^ 3 * B) * (A ^ 2 * B) ^ 3)).re ≤
      ((balancedWords 9 4).map fun w => (trace (evalWord A B w)).re).sum := by
  obtain ⟨hd, hG⟩ := Algebra84.ldlChecks_sound ldl94
  have hgram := weightedGram_nonneg_of_ldl G94
    (fun i => weightedSum (evalWord A B) (features94 i)) A 1
    hA Matrix.PosSemidef.one d94 F94 hd hG
  have h := congrArg Complex.re (trace_gap94 A B hA.isHermitian hB)
  simp only [Complex.sub_re, real_rat_mul, orderedTraceSum_re] at h
  norm_num at h
  linarith only [h, hgram]

end

end WeightedGram67

open private fourth_trace_le_gram_square fourthWordTraceSum fourthRoot_rpow fourthRoot_four
  exponentialLowerOfRoot from D5.S3.Quantum.Analysis.RefinedBMV67
open private re_trace_sq_le_gram44 from D5.S3.Quantum.Analysis.RefinedBMV44
open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem balanced94_of_root (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    (trace ((X ^ 9 * B) ^ 4)).re ≤
      (trace ((X ^ 12 * B) * (X ^ 8 * B) ^ 3)).re := by
  let M := X ^ 4 * B * X ^ 5
  let Q := X ^ 4 * B * X ^ 8 * B * X ^ 6
  have ht : trace ((X ^ 9 * B) ^ 4) = trace (M ^ 4) := by
    calc
      _ = trace ((X ^ 5 * (X ^ 4 * B)) ^ 4) := congrArg trace (by noncomm_ring)
      _ = _ := trace_cycle_power _ _ _
  have hg : trace ((Mᴴ * M) ^ 2) = trace (Q ^ 2) := by
    simp only [M, Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X * (X ^ 4 * B * X ^ 8 * B * X ^ 5)) ^ 2) :=
        congrArg trace (by noncomm_ring)
      _ = trace (((X ^ 4 * B * X ^ 8 * B * X ^ 5) * X) ^ 2) :=
        trace_cycle_power _ _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have hq : trace (Qᴴ * Q) = trace ((X ^ 12 * B) * (X ^ 8 * B) ^ 3) := by
    simp only [Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X ^ 6 * B * X ^ 8 * B * X ^ 8 * B * X ^ 8 * B) * X ^ 6) :=
        congrArg trace (by noncomm_ring)
      _ = trace (X ^ 6 * (X ^ 6 * B * X ^ 8 * B * X ^ 8 * B * X ^ 8 * B)) :=
        trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have h := fourth_trace_le_gram_square M
  rw [trace_cycle_power M Mᴴ 2, hg] at h
  rw [ht, ← hq]
  exact h.trans (re_trace_sq_le_gram44 Q)

private theorem bound94_root (X B : Mat) (hX : X.PosSemidef) (hB : B.IsHermitian) :
    715 * (trace ((X ^ 9 * B) ^ 4)).re ≤ fourthWordTraceSum 9 (X ^ 4) B := by
  have h := balanced94_of_root X B hX.isHermitian hB
  have hg := WeightedGram67.balanced_bound94 (X ^ 4) B (hX.pow 4) hB
  rw [← pow_mul X 4 3, ← pow_mul X 4 2] at hg
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans hg

/-- The refined product lower bound with nine copies of A and four copies of B. -/
theorem product_bound94 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    715 * (trace (((A ^ (9 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 9 4).map fun w => (trace (evalWord A B w)).re).sum := by
  have hX : 0 ≤ A ^ (1 / 4 : ℝ) := CFC.rpow_nonneg
  simpa only [fourthRoot_four A hA, fourthRoot_rpow A hA, Nat.cast_ofNat, fourthWordTraceSum]
    using bound94_root (A ^ (1 / 4 : ℝ)) B hX.posSemidef hB

/-- The refined exponential lower bound at bidegree (9,4). -/
theorem exponential_bound94 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    715 * (trace (exp ((9 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 9 4).map fun w => (trace (evalWord (exp H) (exp K) w)).re).sum := by
  simpa only [Nat.cast_ofNat, fourthWordTraceSum] using
    exponentialLowerOfRoot 9 715 H K hH hK
      (fun X B hX hB => bound94_root X B hX hB.isHermitian)

end


end RefinedBMV
