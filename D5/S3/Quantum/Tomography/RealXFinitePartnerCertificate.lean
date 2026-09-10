/- GID: D5/S3/Quantum/Tomography/RealXFinitePartnerCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/RealXFinitePartnerCertificate
   mirror-E: none(waiver:finite-certificate-with-explicit-analytic-premises)
   anchors: []
   digest: A literal sixty-label certificate eliminates the finite no-partner hypothesis in the real-X strong-unextendibility consumer. -/

import D5.S3.Quantum.Tomography.RootTubeStrongUnextendibility

/- The two relations below are the conservative arc relations at the fixed
   Q(i,sqrt(21)) seed, with radius 1/16 except the refined label 5 (1/32).
   The orthogonality relation retains the larger, unrefined outer bound.
   Entries are bit masks; no absent table entry suppresses an actual vector.
   Mathematical coverage and the one-sided interval implications remain
   explicit premises. The finite coloring is instead proved by reduction of
   the literal data in this module. No external PASS or computed hash is a
   proof premise, and the labels are not declared to be an intrinsic Arena.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.RealXFinitePartnerCertificate

open Matrix
open D5.S3.Quantum.Tomography.RootTubeStrongUnextendibility

private def orthogonalityRows : List Nat :=
  [
    151191722, 302039125, 603992618,
    151191829, 302041130, 603993109,
    9122510539394, 1855425873217, 1855425874568,
    6609954669892, 6609954671264, 9122510538064,
    9194086436, 4899033124, 34628345874,
    17481945106, 137455902729, 68870557705,
    864673539501326336, 576372794599931904, 864110589547905024,
    576443163344109568, 862421739687641088, 575317263437266944,
    1100216467465, 8796445376530, 4398751166500,
    550108266505, 275582599186, 2199375589412,
    963752730235240448, 1058328321336279040, 6777458402816,
    6687264085504, 9251359590464, 365072238656,
    1829656199552, 1189706006912, 11596680136768,
    5841289740672, 11751047299456, 5785857820160,
    11557824103936, 5789649471552, 1149930836217036800,
    1151390987658723328, 1151390987658199040, 1005815648141180928,
    1079333393620795392, 1140923636961247232, 1146887388022964224,
    1149930836212842496, 1057202421429436416, 963189780281819136,
    1058328321336279040, 963752730235240448, 1058046846359568384,
    963611992746885120, 864673539501326336, 576443163344109568
  ]

private def unbiasednessRows : List Nat :=
  [
    681571829041125888, 485997262302290176, 708595659983243392,
    481497850024603712, 816681492946694784, 479803760195272704,
    852694365669781512, 1146896193770926100, 969791266045816834,
    1133386107315019793, 1005815992791592960, 1079335730964066309,
    1056903113782070745, 960937499448578010, 1057105527100411717,
    963629314417102729, 1057958069922434902, 963048785363865510,
    5953529577390, 11772857941845, 6022249037562,
    11644008922581, 5957824543659, 11635418986461,
    862426408317103826, 576058570497595341, 863952736614911947,
    566002334070753236, 861842567642877676, 575212530659823059,
    11636123459306, 5953881812949, 769826641746100311,
    385050899404619951, 768980292666523935, 387084721002385982,
    770043245466494013, 386744696931371583, 396017921309529143,
    767564731055272495, 386166142707167327, 787971863932041278,
    531337020607820061, 841592808441361087, 17588612618922,
    17588243572053, 13087252067669, 15355498035882,
    16759851771221, 8655080643210, 16471585695071,
    17030317333162, 5953881812823, 11910867148715,
    8152905067989, 11636123459310, 14749974833109,
    16034169969402, 5953529577386, 11635418988501
  ]

private def partnerColorCodes : List Nat :=
  [
    351292698724383459836617435016638580078125, 49150961008356610780584874253846436328125, 351559152251795316827520752945709375234375,
    49150961009549215787166359523806152359375, 358220490399436053135432387390138433828125, 49149573301385392669625582794952392578125,
    358498046153963514409417534866645019531375, 92516734919172449860201840600651855470700, 385976066013654418071367171806496826171885,
    92463444213992336888875191410859375001878, 351570254480293457179021323719342285156250, 91131176583348933498418395719210449218828,
    403323670664380557721480754474639912547501, 385976066016079188571311560768127494297005, 403323670662594668104320791763305684000025,
    385976066014683965584264722961425894687625, 403323670663713710851036015647888203547525, 385976066016475671799927974838256887737505,
    709557440876960755984181728255, 3547059046220958233038594173177, 710648717918395996889701253385,
    3552501485799431801001231282552, 709554530315101148440041097255, 141911488142848015912363688153,
    192264352677739453168585908908845328281255, 53481293372397092955186965564727803531276, 192264352676831341038458061714172464922005,
    80943770109342980050481860836035176187525, 178386564869042711022309971353149564534500, 49324618368022298921830954650878917219376,
    2368326019571781158448048912755, 473892200000882151126719157552, 368627513773854298054509187736633300814427,
    73725858818553024335259263714141845791010, 187928839085561776303180230162811279689403, 73725562572328271940615897377015138678255,
    368629222487470906347245420017246103516926, 73726284575832323767548089225781349615755, 73727338383378097265963261326068369141302,
    368627439854662959118187452356021974615755, 37586877982676020600050690275032959001903, 368628182889097009322606648007246679697140,
    73727410006085862419568245610968262501303, 368628151625216633200660372774906252115755, 746528432153463363806551015885,
    2641702536493599414857218016927, 2368833636942625046571074656328, 464599603049755096594879150260,
    1200608909207642079957305892575, 746528432161211967786043203255, 2641324186847150328310586345027,
    473679998338520527045074462760, 473673921503722670108652751901, 2322894940193057060700248128385,
    464433455102443697452403157552, 2368326019759595394135548915755, 237414846390783789157735173177,
    2501141350053548813025687584640, 709557440690696241029103600135, 3552516619791269302527109782552
  ]

/-- Literal outer orthogonality relation for the sixty certified tube labels.
Its enclosure of actual small overlaps is a separate analytic premise. -/
def realXOrthogonalityCandidate (i j : Fin 60) : Bool :=
  (orthogonalityRows.getD i.val 0).testBit j.val

/-- Literal unbiasedness relation after residual-preserving refinement of
label five. Its enclosure of actual near-unbiased overlaps remains explicit. -/
def realXUnbiasednessCandidate (i j : Fin 60) : Bool :=
  (unbiasednessRows.getD i.val 0).testBit j.val

private def partnerColor (l i : Fin 60) : Fin 5 :=
  ⟨((partnerColorCodes.getD l.val 0) / 5 ^ i.val) % 5,
    Nat.mod_lt _ (by decide)⟩

/- Each possible extra-vector label has a five-colorable orthogonality
neighborhood. This verifies the supplied finite certificate, not its discovery.
The proof is pure decidable reduction; no native external evaluation is used. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem partner_colors_separate :
    ∀ l i j : Fin 60,
      realXUnbiasednessCandidate i l = true →
      realXUnbiasednessCandidate j l = true →
      realXOrthogonalityCandidate i j = true →
      partnerColor l i ≠ partnerColor l j := by
  decide +kernel

private theorem concrete_no_partner
    (c : Fin 6 → Fin 60) (_hinj : Function.Injective c)
    (hclique : ∀ i j, i ≠ j →
      realXOrthogonalityCandidate (c i) (c j) = true)
    (l : Fin 60) :
    ∃ i, ¬ realXUnbiasednessCandidate (c i) l = true := by
  classical
  by_contra hnone
  have hcommon (i : Fin 6) : realXUnbiasednessCandidate (c i) l = true := by
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hInjective : Function.Injective (fun i : Fin 6 ↦ partnerColor l (c i)) := by
    intro i j hij
    by_contra hne
    exact partner_colors_separate l (c i) (c j)
      (hcommon i) (hcommon j) (hclique i j hne) hij
  have hcard := Fintype.card_le_of_injective _ hInjective
  norm_num at hcard

/-- Concrete finite-certificate consumer at tolerance 1/256. For an actual
six-frame in the exhaustive tube cover, every further covered matrix has a
cross-unbiasedness error at least 1/256. The former quantified no-partner or
first-clique enumeration hypothesis has been discharged from literal data.

The complete residual-sublevel cover, the same-tube lower bound, and actual
interval-to-matrix transfer are still explicit mathematical hypotheses. Thus
this is not an unconditional claim about all order-six Hadamard matrices.
The intended matrices are normalized rank-one outer products; the theorem
needs only the stated trace inequalities, and permits empty or overlapping
multiple-root tubes. -/
theorem realX_six_frame_has_cross_error_to_any_covered_point
    (tube : Fin 60 → Set (Matrix (Fin 6) (Fin 6) ℂ))
    (hSame : ∀ k, ∀ P ∈ tube k, ∀ Q ∈ tube k,
      (3 / 4 : ℝ) ≤ (trace (P * Q)).re)
    (hOrth : ∀ k l, k ≠ l → ∀ P ∈ tube k, ∀ Q ∈ tube l,
      (trace (P * Q)).re < (1 / 256 : ℝ) ^ 2 →
        realXOrthogonalityCandidate k l = true)
    (hUnbiased : ∀ k l, ∀ P ∈ tube k, ∀ Q ∈ tube l,
      |(trace (P * Q)).re - (1 / 6 : ℝ)| < (1 / 256 : ℝ) →
        realXUnbiasednessCandidate k l = true)
    (C : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
    (Q : Matrix (Fin 6) (Fin 6) ℂ)
    (hCoverC : ∀ i, ∃ k, C i ∈ tube k)
    (hCoverQ : ∃ k, Q ∈ tube k)
    (hSmallC : ∀ i j, i ≠ j →
      (trace (C i * C j)).re < (1 / 256 : ℝ) ^ 2) :
    ∃ i, (1 / 256 : ℝ) ≤
      |(trace (C i * Q)).re - (1 / 6 : ℝ)| := by
  exact six_frame_has_cross_error_to_any_covered_point tube
    (fun i j ↦ realXOrthogonalityCandidate i j = true)
    (fun i j ↦ realXUnbiasednessCandidate i j = true)
    ((1 / 256 : ℝ) ^ 2) (3 / 4) (1 / 256) (by norm_num)
    hSame hOrth hUnbiased concrete_no_partner C Q hCoverC hCoverQ hSmallC

#print axioms realX_six_frame_has_cross_error_to_any_covered_point

end D5.S3.Quantum.Tomography.RealXFinitePartnerCertificate
