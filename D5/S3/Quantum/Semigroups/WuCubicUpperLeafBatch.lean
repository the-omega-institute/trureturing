import D5.S3.Quantum.Semigroups.WuCubicUpperFocal

/-! Exact rational certificates for a batch of the upper focal partition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicUpperLeafBatch

open _root_.Matrix
open scoped BigOperators
open WuCubicUpperPartition (Box InBox tree root leaf_count)
open WuCubicUpperFocal (cellCheck)
open WuCubicUpperScalarCells (longTestCheck longTestCheck_sound)
open WuCubicUpperMatrixCells (check_sound)
open private checkSign from D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells
open private first_leaf_accepted from D5.S3.Quantum.Semigroups.WuCubicUpperFocal

/-- The zero-based leaf of the fixed midpoint partition. -/
def leaf (i : Fin 103) : Box :=
  (tree.leaves root).get ⟨i.val, by simpa only [leaf_count] using i.isLt⟩

private theorem leaf0_accepted : cellCheck (leaf 0) = true := first_leaf_accepted

-- Normalize each box before any interval evaluation.

private def box1 : Box :=
  ![(33719 / 32000, 3387 / 3200), (0, 1 / 256), (-1 / 128, -1 / 256), (0, 1 / 4)]

private theorem leaf1_eq : leaf 1 = box1 := by
  funext j
  fin_cases j <;> decide +kernel

private def box2 : Box :=
  ![(1049 / 1000, 33719 / 32000), (0, 1 / 256), (-1 / 128, -1 / 256), (1 / 4, 1 / 2)]

private theorem leaf2_eq : leaf 2 = box2 := by
  funext j
  fin_cases j <;> decide +kernel

private def box3 : Box :=
  ![(33719 / 32000, 3387 / 3200), (0, 1 / 256), (-1 / 128, -1 / 256), (1 / 4, 1 / 2)]

private theorem leaf3_eq : leaf 3 = box3 := by
  funext j
  fin_cases j <;> decide +kernel

open private totalError allCorners cornerCheck
  from D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells
open private Jet.ok jetSignedMatrixEntry from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational

private theorem checkSign_of_cachedErrors (b : Box) (sign : ℚ) (errors : Vector ℚ 6)
    (herrors : Vector.ofFn (totalError b sign) = errors)
    (hjet : ((List.finRange 4).all fun i => (List.finRange 6).all fun k =>
      Jet.ok (jetSignedMatrixEntry b i sign k)) = true)
    (hcorners : allCorners (fun ε => cornerCheck b sign ε errors) = true) :
    checkSign b sign = true := by
  unfold checkSign
  rw [herrors]
  exact Bool.and_eq_true_iff.mpr ⟨hjet, hcorners⟩

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box1_scalar : longTestCheck box1 (1 / 8) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box1_minus : checkSign box1 (-1) = true := by
  refine checkSign_of_cachedErrors box1 (-1) #v[
      4781148717125538372449409074763191273533355684981 / 2787593149816327892691964784081045188247552000000,
      519102739577498367973936043078282629753176144869 / 696898287454081973172991196020261297061888000000,
      195365734276528780380767513199610242336882702669 / 87112285931760246646623899502532662132736000000,
      4545775147285139369825408410942958283722192185841 / 557518629963265578538392956816209037649510400000,
      222817289972823691892114231734727501679490675299 / 174224571863520493293247799005065324265472000000,
      411156515733955727979410956370135585846801989457 / 69689828745408197317299119602026129706188800000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box1_plus : checkSign box1 1 = true := by
  refine checkSign_of_cachedErrors box1 (1) #v[
      2426533015705192326790854848023524854318939316783 / 1393796574908163946345982392040522594123776000000,
      1103063015139038350646274308317863122981934170931 / 1393796574908163946345982392040522594123776000000,
      255317715831410006900277803326322288605094656573 / 111503725992653115707678591363241807529902080000,
      11193732833626710172359791915299431304291125295311 / 1393796574908163946345982392040522594123776000000,
      3818494290351603617673557413451208727736361762963 / 2787593149816327892691964784081045188247552000000,
      133364949503986612425958808295247040184579560887 / 22300745198530623141535718272648361505980416000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem leaf1_accepted : cellCheck (leaf 1) = true := by
  rw [leaf1_eq]
  exact Bool.and_eq_true_iff.mpr
    ⟨box1_scalar, Bool.and_eq_true_iff.mpr ⟨box1_minus, box1_plus⟩⟩

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box2_scalar : longTestCheck box2 (1 / 8) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box2_minus : checkSign box2 (-1) = true := by
  refine checkSign_of_cachedErrors box2 (-1) #v[
      7293034410134514403736622284366218063958064801589 / 2787593149816327892691964784081045188247552000000,
      3060153808214305127642620575003033412779377030353 / 2787593149816327892691964784081045188247552000000,
      2425003054775574622813098459350200442492585942071 / 696898287454081973172991196020261297061888000000,
      1682905361668209819626388815220112994562492828183 / 139379657490816394634598239204052259412377600000,
      659094423911516322970917826751121368239070649053 / 348449143727040986586495598010130648530944000000,
      12638778043251762752679892892750021428984033231263 / 1393796574908163946345982392040522594123776000000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box2_plus : checkSign box2 1 = true := by
  refine checkSign_of_cachedErrors box2 (1) #v[
      7347776680874413522197863363513630353989912440351 / 2787593149816327892691964784081045188247552000000,
      3226215872905384871394099883784302611641214502647 / 2787593149816327892691964784081045188247552000000,
      9822234911002355322656650566429053554713166541081 / 2787593149816327892691964784081045188247552000000,
      8290410656162333282903882080810879681580112004957 / 696898287454081973172991196020261297061888000000,
      5587142409904485328933528671297963462978907576333 / 2787593149816327892691964784081045188247552000000,
      6358025253957265242453932200450239314814379892791 / 696898287454081973172991196020261297061888000000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem leaf2_accepted : cellCheck (leaf 2) = true := by
  rw [leaf2_eq]
  exact Bool.and_eq_true_iff.mpr
    ⟨box2_scalar, Bool.and_eq_true_iff.mpr ⟨box2_minus, box2_plus⟩⟩

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box3_scalar : longTestCheck box3 (1 / 8) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box3_minus : checkSign box3 (-1) = true := by
  refine checkSign_of_cachedErrors box3 (-1) #v[
      1340919396984705175684270115617700953024155885969 / 696898287454081973172991196020261297061888000000,
      446294665645818401368082131696599131391440316837 / 557518629963265578538392956816209037649510400000,
      3542029728055944377226908199736876183262041039411 / 1393796574908163946345982392040522594123776000000,
      12377220492938480433737582254496419402620929965597 / 1393796574908163946345982392040522594123776000000,
      153485379623139442067047564330764360449319641761 / 111503725992653115707678591363241807529902080000,
      9222100990326647057881586812497921595243365795521 / 1393796574908163946345982392040522594123776000000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
set_option trace.profiler true in
set_option trace.profiler.threshold 1000 in
-- The kernel normalizes the rational corner and derivative certificates.
set_option maxHeartbeats 2000000 in
private theorem box3_plus : checkSign box3 1 = true := by
  refine checkSign_of_cachedErrors box3 (1) #v[
      5408250319319714046771555220270321691789057673403 / 2787593149816327892691964784081045188247552000000,
      118239383337612774365264462157395904541843173337 / 139379657490816394634598239204052259412377600000,
      7180010705347181728329011574905658898616530836777 / 2787593149816327892691964784081045188247552000000,
      12187902945947247672249421115775608808606294995597 / 1393796574908163946345982392040522594123776000000,
      2037922612212528330355014133853609832702063256321 / 1393796574908163946345982392040522594123776000000,
      371438824127809717998690102767365694359374215099 / 55751862996326557853839295681620903764951040000] ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem leaf3_accepted : cellCheck (leaf 3) = true := by
  rw [leaf3_eq]
  exact Bool.and_eq_true_iff.mpr
    ⟨box3_scalar, Bool.and_eq_true_iff.mpr ⟨box3_minus, box3_plus⟩⟩

/-- The first 4 leaves pass the scalar and signed matrix checkers. -/
theorem accepted (i : Fin 4) :
    cellCheck (leaf (i.castLE (by decide))) = true := by
  fin_cases i
  · exact leaf0_accepted
  · exact leaf1_accepted
  · exact leaf2_accepted
  · exact leaf3_accepted

#print axioms accepted

open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicHellingerMatrix
  (displacement focalOffsets levels longTest signedMatrix normalized_deficit_ge_of_matrix_tests)
open WuCubicOccupationTaylor (gibbsLevels)
open private pad from D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells
open private physical_admissible
  Admissible.lowGibbs Admissible.midGibbs Admissible.lowLevel
  Admissible.midLevel Admissible.highMiddleLevel Admissible.lowOrder
  Admissible.highOrder Admissible.mixtureNonneg Admissible.mixtureLower
  Admissible.mixtureUpper Admissible.lowerPos Admissible.upperPos
  Admissible.junctionNonneg
  from D5.S3.Quantum.Semigroups.WuCubicUpperRegion
open private boxSub sub_sound from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

private theorem leaf_subset_root (i : Fin 4) :
    boxSub (leaf (i.castLE (by decide))) root := by
  fin_cases i <;> decide +kernel

/-- The checked cells give the physical normalized-deficit bound for any unitary
frame and any physical displacement in a cell, including its faces. -/
theorem normalized_deficit_ge (i : Fin 4) (U : unitary Mat) {r d : ℝ}
    (hd : 0 ≤ d) (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (h₀ : 0 ≤ h 0) (h₁₂ : h 1 ≤ h 2) {blend : ℝ}
    (hcell : InBox (leaf (i.castLE (by decide))) ![r, d * h 0, d * h 1, blend])
    (hy : displacement d h = focalOffsets (d * h 0) (d * h 1) blend) :
    (d ^ 2 / 64) * (∑ j, h j ^ 2) ≤
      normalizedDeficit r U (levels r (displacement d h) 0)
        (levels r (displacement d h) 1) (levels r (displacement d h) 2) := by
  let b := leaf (i.castLE (by decide))
  let x : Fin 4 → ℝ := ![r, d * h 0, d * h 1, blend]
  have hx₀ : x 0 = r := rfl
  have hx₁ : x 1 = d * h 0 := rfl
  have hx₂ : x 2 = d * h 1 := rfl
  have hx₃ : x 3 = blend := rfl
  have hx : InBox b x := hcell
  have hroot : InBox root x := sub_sound (leaf_subset_root i) hx
  have rBounds := hroot 0
  have lowBounds := hroot 1
  have midBounds := hroot 2
  have blendBounds := hroot 3
  change ((1049 / 1000 : ℚ) : ℝ) ≤ r ∧ r ≤ ((6 / 5 : ℚ) : ℝ) at rBounds
  change ((0 : ℚ) : ℝ) ≤ d * h 0 ∧ d * h 0 ≤ ((1 / 256 : ℚ) : ℝ) at lowBounds
  change ((-1 / 128 : ℚ) : ℝ) ≤ d * h 1 ∧ d * h 1 ≤ ((1 / 128 : ℚ) : ℝ) at midBounds
  change ((0 : ℚ) : ℝ) ≤ blend ∧ blend ≤ ((1 : ℚ) : ℝ) at blendBounds
  push_cast at rBounds lowBounds midBounds blendBounds
  have hHigh : d * h 2 ≤ 1 / 128 := by
    have hy₂ := congrFun hy (2 : Fin 3)
    change d * h 2 = d * h 1 + (1 / 128 - d * h 1) * blend at hy₂
    rw [hy₂]
    nlinarith only [mul_nonneg (sub_nonneg.mpr midBounds.2) (sub_nonneg.mpr blendBounds.2)]
  let m := levels r (displacement d h) 0
  let n := levels r (displacement d h) 1
  let q := levels r (displacement d h) 2
  have hm : m - (r ^ 2)⁻¹ = d * h 0 := by
    change (r ^ 2)⁻¹ + d * h 0 - (r ^ 2)⁻¹ = d * h 0
    ring
  have hn : n - r⁻¹ = d * h 1 := by
    change r⁻¹ + d * h 1 - r⁻¹ = d * h 1
    ring
  have hq : q - r⁻¹ = d * h 2 := by
    change r⁻¹ + d * h 2 - r⁻¹ = d * h 2
    ring
  have hnq : n ≤ q := by
    linarith only [hn, hq, mul_le_mul_of_nonneg_left h₁₂ hd]
  have ha := physical_admissible (m := m) (n := n) (q := q) rBounds.1 rBounds.2
    (hm.symm ▸ lowBounds.1) (hm.symm ▸ lowBounds.2)
    (hn.symm ▸ (by simpa only [neg_div] using midBounds.1)) hnq (hq.symm ▸ hHigh)
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 1049 / 1000).trans_le rBounds.1
  have hxLevels : ∀ j, 1 / 2 ≤ gibbsLevels r j + d * h j := by
    intro j
    fin_cases j
    · exact (Admissible.lowLevel ha)
    · exact (Admissible.midLevel ha)
    · exact (Admissible.highMiddleLevel ha)
    · change (1 : ℝ) / 2 ≤ 1 + d * h 3
      rw [hh]
      norm_num
  have hg : ∀ j, 1 / 2 ≤ gibbsLevels r j := by
    intro j
    fin_cases j
    · exact (Admissible.lowGibbs ha)
    · exact (Admissible.midGibbs ha)
    · exact (Admissible.midGibbs ha)
    · norm_num [gibbsLevels]
  obtain ⟨hcScalar, hcMatrix⟩ := Bool.and_eq_true_iff.mp
    (show (longTestCheck b (1 / 8) && WuCubicUpperMatrixCells.check b) = true from accepted i)
  obtain ⟨hf, hlminus, hlplus⟩ := longTestCheck_sound hcScalar hx
  obtain ⟨hmminus, hmplus⟩ := check_sound hcMatrix (x := x) hx
  have hpad (j : Fin 4) : pad x j.castSucc = x j := Fin.lastCases_castSucc j
  have hp₁ := hpad 1
  have hp₂ := hpad 2
  have hp₃ := hpad 3
  change pad x 1 = x 1 at hp₁
  change pad x 2 = x 2 at hp₂
  change pad x 3 = x 3 at hp₃
  refine normalized_deficit_ge_of_matrix_tests U hr hd h hh h₀ h₁₂ hxLevels hg
    (Admissible.lowOrder ha) hnq (Admissible.highOrder ha) (Admissible.mixtureNonneg ha)
    (Admissible.mixtureLower ha) (Admissible.mixtureUpper ha)
    (Admissible.lowerPos ha) (Admissible.upperPos ha) (Admissible.junctionNonneg ha) ?_ ?_ ?_ ?_
  · rw [hy]
    exact hf.trans_le hlminus
  · rw [hy]
    exact hf.trans_le hlplus
  · rw [hy]
    simpa only [WuCubicUpperMatrixCells.focalMatrix, WuCubicUpperCornerJet.replayFocalY,
      hp₁, hp₂, hp₃, hx₀, hx₁, hx₂, hx₃, Rat.cast_neg, Rat.cast_one]
      using hmminus.posSemidef
  · rw [hy]
    simpa only [WuCubicUpperMatrixCells.focalMatrix, WuCubicUpperCornerJet.replayFocalY,
      hp₁, hp₂, hp₃, hx₀, hx₁, hx₂, hx₃, Rat.cast_one]
      using hmplus.posSemidef

run_cmd do
  for name in #[``accepted, ``normalized_deficit_ge] do
    for axiomName in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom for {name}: {axiomName}"

#print axioms normalized_deficit_ge

end D5.S3.Quantum.Semigroups.WuCubicUpperLeafBatch
