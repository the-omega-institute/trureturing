/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMomentBox64
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: All actual compact moment and normalization boxes for the matrix input. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMomentBox64Data

/-! Kernel-checked 64-digit matrix inputs from actual compact Gaussian moments.
Every endpoint is an untrusted generated rational, checked against the proved
250-digit analytic boxes and the complete H0 beta-series tail. All odd moments
are retained. No matrix residual, physical cap, or RH conclusion is assumed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace FiniteGaussianCap475
open RHFiniteGaussian.AnalyticEndpoints

set_option maxHeartbeats 4000000 in
-- The 161-term positive prefix is evaluated once for all 61 consumers.
private theorem H0PrefixQ_value : H0PrefixQ =
  11683759704567666325174268431510291569846234683069026425591999302636618488824762707271821540469937102558169368334001589883149641902665521423644222283157958196780511249714460804889942079262675091524540845817738965243696203520521614108654913703644767279321448022534647544756813018920577012564945542553921534022 / 2662208065666341813689816123219947891947670368401452689992333416114706269979021005714891487337503933330885505374166349639572811905639471299213976351723012046475532347055076475605283967994270089006029975626202803635179837335969574974282974398225206132714819093768458054604765190297257504425942897796630859375 := by
  norm_num [H0PrefixQ, H0TermQ, Finset.sum_range_succ, Finset.prod_range_succ]

set_option maxHeartbeats 4000000 in
-- The full geometric tail is evaluated once, without dropping the first omitted term.
private theorem H0TailQ_value : H0TailQ =
  7382751983170210834158959755184182274773801384092020847389697035032269317274063546590476080184803678764367530276535424063554682447346891635094337000976580614272709436576653290730684416 / 827946708422232304057532814321403794395725484572851786587615692411673649963475532777331252561963723265905392171365734737907144502653875574055546645385856746453890559934128783913243314046217997680875322419749071930540929411486537817002005037848039107274308738161990454982081974182447083876468241214752197265625 := by
  norm_num [H0TailQ, H0TermQ, Finset.prod_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_0 :
    WLower64 ⟨0, by decide⟩ ≤ WLowerQ 0 ∧
    WUpperQ 0 ≤ WUpper64 ⟨0, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_1 :
    WLower64 ⟨1, by decide⟩ ≤ WLowerQ 1 ∧
    WUpperQ 1 ≤ WUpper64 ⟨1, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_2 :
    WLower64 ⟨2, by decide⟩ ≤ WLowerQ 2 ∧
    WUpperQ 2 ≤ WUpper64 ⟨2, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_3 :
    WLower64 ⟨3, by decide⟩ ≤ WLowerQ 3 ∧
    WUpperQ 3 ≤ WUpper64 ⟨3, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_4 :
    WLower64 ⟨4, by decide⟩ ≤ WLowerQ 4 ∧
    WUpperQ 4 ≤ WUpper64 ⟨4, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_5 :
    WLower64 ⟨5, by decide⟩ ≤ WLowerQ 5 ∧
    WUpperQ 5 ≤ WUpper64 ⟨5, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_6 :
    WLower64 ⟨6, by decide⟩ ≤ WLowerQ 6 ∧
    WUpperQ 6 ≤ WUpper64 ⟨6, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_7 :
    WLower64 ⟨7, by decide⟩ ≤ WLowerQ 7 ∧
    WUpperQ 7 ≤ WUpper64 ⟨7, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_8 :
    WLower64 ⟨8, by decide⟩ ≤ WLowerQ 8 ∧
    WUpperQ 8 ≤ WUpper64 ⟨8, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_9 :
    WLower64 ⟨9, by decide⟩ ≤ WLowerQ 9 ∧
    WUpperQ 9 ≤ WUpper64 ⟨9, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_10 :
    WLower64 ⟨10, by decide⟩ ≤ WLowerQ 10 ∧
    WUpperQ 10 ≤ WUpper64 ⟨10, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_11 :
    WLower64 ⟨11, by decide⟩ ≤ WLowerQ 11 ∧
    WUpperQ 11 ≤ WUpper64 ⟨11, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_12 :
    WLower64 ⟨12, by decide⟩ ≤ WLowerQ 12 ∧
    WUpperQ 12 ≤ WUpper64 ⟨12, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_13 :
    WLower64 ⟨13, by decide⟩ ≤ WLowerQ 13 ∧
    WUpperQ 13 ≤ WUpper64 ⟨13, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_14 :
    WLower64 ⟨14, by decide⟩ ≤ WLowerQ 14 ∧
    WUpperQ 14 ≤ WUpper64 ⟨14, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_15 :
    WLower64 ⟨15, by decide⟩ ≤ WLowerQ 15 ∧
    WUpperQ 15 ≤ WUpper64 ⟨15, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_16 :
    WLower64 ⟨16, by decide⟩ ≤ WLowerQ 16 ∧
    WUpperQ 16 ≤ WUpper64 ⟨16, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_17 :
    WLower64 ⟨17, by decide⟩ ≤ WLowerQ 17 ∧
    WUpperQ 17 ≤ WUpper64 ⟨17, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_18 :
    WLower64 ⟨18, by decide⟩ ≤ WLowerQ 18 ∧
    WUpperQ 18 ≤ WUpper64 ⟨18, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_19 :
    WLower64 ⟨19, by decide⟩ ≤ WLowerQ 19 ∧
    WUpperQ 19 ≤ WUpper64 ⟨19, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_20 :
    WLower64 ⟨20, by decide⟩ ≤ WLowerQ 20 ∧
    WUpperQ 20 ≤ WUpper64 ⟨20, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_21 :
    WLower64 ⟨21, by decide⟩ ≤ WLowerQ 21 ∧
    WUpperQ 21 ≤ WUpper64 ⟨21, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_22 :
    WLower64 ⟨22, by decide⟩ ≤ WLowerQ 22 ∧
    WUpperQ 22 ≤ WUpper64 ⟨22, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_23 :
    WLower64 ⟨23, by decide⟩ ≤ WLowerQ 23 ∧
    WUpperQ 23 ≤ WUpper64 ⟨23, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_24 :
    WLower64 ⟨24, by decide⟩ ≤ WLowerQ 24 ∧
    WUpperQ 24 ≤ WUpper64 ⟨24, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_25 :
    WLower64 ⟨25, by decide⟩ ≤ WLowerQ 25 ∧
    WUpperQ 25 ≤ WUpper64 ⟨25, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_26 :
    WLower64 ⟨26, by decide⟩ ≤ WLowerQ 26 ∧
    WUpperQ 26 ≤ WUpper64 ⟨26, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_27 :
    WLower64 ⟨27, by decide⟩ ≤ WLowerQ 27 ∧
    WUpperQ 27 ≤ WUpper64 ⟨27, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_28 :
    WLower64 ⟨28, by decide⟩ ≤ WLowerQ 28 ∧
    WUpperQ 28 ≤ WUpper64 ⟨28, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_29 :
    WLower64 ⟨29, by decide⟩ ≤ WLowerQ 29 ∧
    WUpperQ 29 ≤ WUpper64 ⟨29, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_30 :
    WLower64 ⟨30, by decide⟩ ≤ WLowerQ 30 ∧
    WUpperQ 30 ≤ WUpper64 ⟨30, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_31 :
    WLower64 ⟨31, by decide⟩ ≤ WLowerQ 31 ∧
    WUpperQ 31 ≤ WUpper64 ⟨31, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_32 :
    WLower64 ⟨32, by decide⟩ ≤ WLowerQ 32 ∧
    WUpperQ 32 ≤ WUpper64 ⟨32, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_33 :
    WLower64 ⟨33, by decide⟩ ≤ WLowerQ 33 ∧
    WUpperQ 33 ≤ WUpper64 ⟨33, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_34 :
    WLower64 ⟨34, by decide⟩ ≤ WLowerQ 34 ∧
    WUpperQ 34 ≤ WUpper64 ⟨34, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_35 :
    WLower64 ⟨35, by decide⟩ ≤ WLowerQ 35 ∧
    WUpperQ 35 ≤ WUpper64 ⟨35, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_36 :
    WLower64 ⟨36, by decide⟩ ≤ WLowerQ 36 ∧
    WUpperQ 36 ≤ WUpper64 ⟨36, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_37 :
    WLower64 ⟨37, by decide⟩ ≤ WLowerQ 37 ∧
    WUpperQ 37 ≤ WUpper64 ⟨37, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_38 :
    WLower64 ⟨38, by decide⟩ ≤ WLowerQ 38 ∧
    WUpperQ 38 ≤ WUpper64 ⟨38, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_39 :
    WLower64 ⟨39, by decide⟩ ≤ WLowerQ 39 ∧
    WUpperQ 39 ≤ WUpper64 ⟨39, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_40 :
    WLower64 ⟨40, by decide⟩ ≤ WLowerQ 40 ∧
    WUpperQ 40 ≤ WUpper64 ⟨40, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_41 :
    WLower64 ⟨41, by decide⟩ ≤ WLowerQ 41 ∧
    WUpperQ 41 ≤ WUpper64 ⟨41, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_42 :
    WLower64 ⟨42, by decide⟩ ≤ WLowerQ 42 ∧
    WUpperQ 42 ≤ WUpper64 ⟨42, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_43 :
    WLower64 ⟨43, by decide⟩ ≤ WLowerQ 43 ∧
    WUpperQ 43 ≤ WUpper64 ⟨43, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_44 :
    WLower64 ⟨44, by decide⟩ ≤ WLowerQ 44 ∧
    WUpperQ 44 ≤ WUpper64 ⟨44, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_45 :
    WLower64 ⟨45, by decide⟩ ≤ WLowerQ 45 ∧
    WUpperQ 45 ≤ WUpper64 ⟨45, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_46 :
    WLower64 ⟨46, by decide⟩ ≤ WLowerQ 46 ∧
    WUpperQ 46 ≤ WUpper64 ⟨46, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_47 :
    WLower64 ⟨47, by decide⟩ ≤ WLowerQ 47 ∧
    WUpperQ 47 ≤ WUpper64 ⟨47, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_48 :
    WLower64 ⟨48, by decide⟩ ≤ WLowerQ 48 ∧
    WUpperQ 48 ≤ WUpper64 ⟨48, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_49 :
    WLower64 ⟨49, by decide⟩ ≤ WLowerQ 49 ∧
    WUpperQ 49 ≤ WUpper64 ⟨49, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_50 :
    WLower64 ⟨50, by decide⟩ ≤ WLowerQ 50 ∧
    WUpperQ 50 ≤ WUpper64 ⟨50, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_51 :
    WLower64 ⟨51, by decide⟩ ≤ WLowerQ 51 ∧
    WUpperQ 51 ≤ WUpper64 ⟨51, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_52 :
    WLower64 ⟨52, by decide⟩ ≤ WLowerQ 52 ∧
    WUpperQ 52 ≤ WUpper64 ⟨52, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_53 :
    WLower64 ⟨53, by decide⟩ ≤ WLowerQ 53 ∧
    WUpperQ 53 ≤ WUpper64 ⟨53, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_54 :
    WLower64 ⟨54, by decide⟩ ≤ WLowerQ 54 ∧
    WUpperQ 54 ≤ WUpper64 ⟨54, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_55 :
    WLower64 ⟨55, by decide⟩ ≤ WLowerQ 55 ∧
    WUpperQ 55 ≤ WUpper64 ⟨55, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_56 :
    WLower64 ⟨56, by decide⟩ ≤ WLowerQ 56 ∧
    WUpperQ 56 ≤ WUpper64 ⟨56, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_57 :
    WLower64 ⟨57, by decide⟩ ≤ WLowerQ 57 ∧
    WUpperQ 57 ≤ WUpper64 ⟨57, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_58 :
    WLower64 ⟨58, by decide⟩ ≤ WLowerQ 58 ∧
    WUpperQ 58 ≤ WUpper64 ⟨58, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_59 :
    WLower64 ⟨59, by decide⟩ ≤ WLowerQ 59 ∧
    WUpperQ 59 ≤ WUpper64 ⟨59, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
-- Closed rational comparison; the endpoint proposal is not a proof premise.
private theorem W_comparisons64_60 :
    WLower64 ⟨60, by decide⟩ ≤ WLowerQ 60 ∧
    WUpperQ 60 ≤ WUpper64 ⟨60, by decide⟩ := by
  norm_num [WLower64, WUpper64, WLowerQ, WUpperQ, HLowerQ, HUpperQ,
    H0PrefixQ_value, H0TailQ_value, CLowerQ, CUpperQ, JLowerQ, JUpperQ, JSumQ,
    ALowerQ, AUpperQ, BLowerQ, BUpperQ, piLower250, piUpper250,
    sqrtPiLower250, sqrtPiUpper250, sqrt6Lower250, sqrt6Upper250,
    expNeg12Lower250, expNeg12Upper250, expNegTwoPiLower250, expNegTwoPiUpper250,
    Finset.sum_range_succ]

private theorem W_comparisons64 (m : Fin 61) :
    WLower64 m ≤ WLowerQ m ∧ WUpperQ m ≤ WUpper64 m := by
  fin_cases m
  · exact W_comparisons64_0
  · exact W_comparisons64_1
  · exact W_comparisons64_2
  · exact W_comparisons64_3
  · exact W_comparisons64_4
  · exact W_comparisons64_5
  · exact W_comparisons64_6
  · exact W_comparisons64_7
  · exact W_comparisons64_8
  · exact W_comparisons64_9
  · exact W_comparisons64_10
  · exact W_comparisons64_11
  · exact W_comparisons64_12
  · exact W_comparisons64_13
  · exact W_comparisons64_14
  · exact W_comparisons64_15
  · exact W_comparisons64_16
  · exact W_comparisons64_17
  · exact W_comparisons64_18
  · exact W_comparisons64_19
  · exact W_comparisons64_20
  · exact W_comparisons64_21
  · exact W_comparisons64_22
  · exact W_comparisons64_23
  · exact W_comparisons64_24
  · exact W_comparisons64_25
  · exact W_comparisons64_26
  · exact W_comparisons64_27
  · exact W_comparisons64_28
  · exact W_comparisons64_29
  · exact W_comparisons64_30
  · exact W_comparisons64_31
  · exact W_comparisons64_32
  · exact W_comparisons64_33
  · exact W_comparisons64_34
  · exact W_comparisons64_35
  · exact W_comparisons64_36
  · exact W_comparisons64_37
  · exact W_comparisons64_38
  · exact W_comparisons64_39
  · exact W_comparisons64_40
  · exact W_comparisons64_41
  · exact W_comparisons64_42
  · exact W_comparisons64_43
  · exact W_comparisons64_44
  · exact W_comparisons64_45
  · exact W_comparisons64_46
  · exact W_comparisons64_47
  · exact W_comparisons64_48
  · exact W_comparisons64_49
  · exact W_comparisons64_50
  · exact W_comparisons64_51
  · exact W_comparisons64_52
  · exact W_comparisons64_53
  · exact W_comparisons64_54
  · exact W_comparisons64_55
  · exact W_comparisons64_56
  · exact W_comparisons64_57
  · exact W_comparisons64_58
  · exact W_comparisons64_59
  · exact W_comparisons64_60

/-- All 61 actual signed moments in the matrix input box. -/
theorem W_bounds64 (m : Fin 61) :
    (WLower64 m : ℝ) ≤ W m ∧ W m ≤ (WUpper64 m : ℝ) := by
  have hc := W_comparisons64 m
  have hl : (WLower64 m : ℝ) ≤ (WLowerQ m : ℝ) := Rat.cast_le.mpr hc.1
  have hu : (WUpperQ m : ℝ) ≤ (WUpper64 m : ℝ) := Rat.cast_le.mpr hc.2
  exact ⟨hl.trans (W_bounds m).1, (W_bounds m).2.trans hu⟩

def normalizationSquaredLowerQ : ℚ := 256 * sqrt2Lower250 / (105 * sqrtPiUpper250)
def normalizationSquaredUpperQ : ℚ := 256 * sqrt2Upper250 / (105 * sqrtPiLower250)

/-- The explicit normalization formula, independently of its Gaussian/Gamma identity. -/
theorem normalizationSquared_bounds64 :
    (normalizationLower64 : ℝ) ≤ 256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi) ∧
    256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi) ≤ (normalizationUpper64 : ℝ) := by
  have hs := sqrt_two_250_bounds
  have hp := sqrt_pi_250_bounds
  have hdl : (0 : ℝ) < 105 * (sqrtPiLower250 : ℝ) := by norm_num [sqrtPiLower250]
  have hdu : (0 : ℝ) < 105 * (sqrtPiUpper250 : ℝ) := by norm_num [sqrtPiUpper250]
  have hd : (0 : ℝ) < 105 * Real.sqrt Real.pi := by positivity
  have hnu : (0 : ℝ) ≤ 256 * (sqrt2Upper250 : ℝ) := by norm_num [sqrt2Upper250]
  have hdenl := mul_le_mul_of_nonneg_left hp.1 (by norm_num : (0 : ℝ) ≤ 105)
  have hdenu := mul_le_mul_of_nonneg_left hp.2 (by norm_num : (0 : ℝ) ≤ 105)
  have hl : (normalizationSquaredLowerQ : ℝ) ≤
      256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi) := by
    simp only [normalizationSquaredLowerQ, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs.1 (by norm_num)) hdu.le).trans
      (div_le_div_of_nonneg_left (by positivity) hd hdenu)
  have hu : 256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi) ≤
      (normalizationSquaredUpperQ : ℝ) := by
    simp only [normalizationSquaredUpperQ, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs.2 (by norm_num)) hd.le).trans
      (div_le_div_of_nonneg_left hnu hdl hdenl)
  have hql : normalizationLower64 ≤ normalizationSquaredLowerQ := by
    norm_num [normalizationLower64, normalizationSquaredLowerQ, sqrt2Lower250, sqrtPiUpper250]
  have hqu : normalizationSquaredUpperQ ≤ normalizationUpper64 := by
    norm_num [normalizationUpper64, normalizationSquaredUpperQ, sqrt2Upper250, sqrtPiLower250]
  have hcl : (normalizationLower64 : ℝ) ≤ (normalizationSquaredLowerQ : ℝ) :=
    Rat.cast_le.mpr hql
  have hcu : (normalizationSquaredUpperQ : ℝ) ≤ (normalizationUpper64 : ℝ) :=
    Rat.cast_le.mpr hqu
  exact ⟨hcl.trans hl, hu.trans hcu⟩

end FiniteGaussianCap475
