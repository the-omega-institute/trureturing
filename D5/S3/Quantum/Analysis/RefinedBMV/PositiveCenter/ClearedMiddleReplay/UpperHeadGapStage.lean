/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay/UpperHeadGapStage
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Check the exponential factor shared by the first cleared middle upper score. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay
import Lean.Elab.Tactic.CbvSimproc
import Lean.Elab.Tactic.Conv.Cbv
import Lean.Meta.Eval

/-! Staged kernel equalities for the upper-gap exponential on leaf zero. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

open private CompactMiddleBox.Fv CompactMiddleBox.V from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox
open private Model.center Model.expHalvings expCenteredModel from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

private def firstUpperGapArgument : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), (-145851844628532076024478635846)⟩,
    ⟨(0, 0, 1), (-145851844628532076024478635846)⟩,
    ⟨(0, 1, 0), (-10803840342854227853665084137)⟩,
    ⟨(0, 1, 1), (-10803840342854227853665084137)⟩,
    ⟨(1, 0, 0), (-5401920171427113926832542068)⟩,
    ⟨(1, 0, 1), (-5401920171427113926832542068)⟩]⟩, 4⟩

private theorem first_upper_gap_argument_eq :
    (leafAt 0).model.H.mul
        ((CompactMiddleBox.V (leafAt 0).model).mul (Model.ofRat (-1 / 2))) =
      firstUpperGapArgument := by
  have hBox : (leafAt 0).box = (⟨1 / 2, 5 / 8, 1, 5 / 4⟩ : Rectangle) := by rfl'
  simp only [CompactMiddleBox.V, Leaf.model, hBox, CompactMiddleBox.ofIntervals]
  all_goals rfl'

/-- Exact fixed-point exponential used in the first upper-gap model. -/
def firstUpperGapDecay : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), 1129876627987107834736984679412⟩,
    ⟨(0, 0, 1), (-130000009754198486667181475898)⟩,
    ⟨(0, 0, 2), 7478693742961702713097797974⟩,
    ⟨(0, 0, 3), (-286824902073815302917103047)⟩,
    ⟨(0, 0, 4), 8250290151981193017146785⟩,
    ⟨(0, 0, 5), (-189850426792749043860480)⟩,
    ⟨(0, 0, 6), 3640597672872318312666⟩,
    ⟨(0, 1, 0), (-9629630352162850864235664882)⟩,
    ⟨(0, 1, 1), (-8521675723575931943776731848)⟩,
    ⟨(0, 1, 2), 1044215761459404408699576800⟩,
    ⟨(0, 1, 3), (-61294336712112676791312741)⟩,
    ⟨(0, 1, 4), 2374215442515631618465536⟩,
    ⟨(0, 1, 5), (-68696929476037874772326)⟩,
    ⟨(0, 2, 0), 41035356614330330387367890⟩,
    ⟨(0, 2, 1), 77349315663659585829598282⟩,
    ⟨(0, 2, 2), 31864175974928384382431059⟩,
    ⟨(0, 2, 3), (-4188585616820845448472716)⟩,
    ⟨(0, 2, 4), 251080062228396499316110⟩,
    ⟨(0, 3, 0), (-116577717654347529509568)⟩,
    ⟨(0, 3, 1), (-336320091698834989252745)⟩,
    ⟨(0, 3, 2), (-310265601245988551738720)⟩,
    ⟨(0, 3, 3), (-78623836244623690153291)⟩,
    ⟨(0, 4, 0), 248390023411251838444⟩,
    ⟨(0, 4, 1), 964981127883201389408⟩,
    ⟨(0, 4, 2), 1377668379854027431089⟩,
    ⟨(0, 5, 0), (-423392085360088361)⟩,
    ⟨(0, 5, 1), (-2068246280615545275)⟩,
    ⟨(0, 6, 0), 601409212159216⟩,
    ⟨(1, 0, 0), (-4814815176081425432117832440)⟩,
    ⟨(1, 0, 1), (-4260837861787965971888365924)⟩,
    ⟨(1, 0, 2), 522107880729702204349788400⟩,
    ⟨(1, 0, 3), (-30647168356056338395656370)⟩,
    ⟨(1, 0, 4), 1187107721257815809232768⟩,
    ⟨(1, 0, 5), (-34348464738018937386164)⟩,
    ⟨(1, 1, 0), 41035356614330330387367890⟩,
    ⟨(1, 1, 1), 77349315663659585829598282⟩,
    ⟨(1, 1, 2), 31864175974928384382431059⟩,
    ⟨(1, 1, 3), (-4188585616820845448472716)⟩,
    ⟨(1, 1, 4), 251080062228396499316110⟩,
    ⟨(1, 2, 0), (-174866576481521294264352)⟩,
    ⟨(1, 2, 1), (-504480137548252483879117)⟩,
    ⟨(1, 2, 2), (-465398401868982827608079)⟩,
    ⟨(1, 2, 3), (-117935754366935535229936)⟩,
    ⟨(1, 3, 0), 496780046822503676887⟩,
    ⟨(1, 3, 1), 1929962255766402778817⟩,
    ⟨(1, 3, 2), 2755336759708054862180⟩,
    ⟨(1, 4, 0), (-1058480213400220902)⟩,
    ⟨(1, 4, 1), (-5170615701538863187)⟩,
    ⟨(1, 5, 0), 1804227636477650⟩,
    ⟨(2, 0, 0), 10258839153582582596841973⟩,
    ⟨(2, 0, 1), 19337328915914896457399570⟩,
    ⟨(2, 0, 2), 7966043993732096095607765⟩,
    ⟨(2, 0, 3), (-1047146404205211362118179)⟩,
    ⟨(2, 0, 4), 62770015557099124829028⟩,
    ⟨(2, 1, 0), (-87433288240760647132176)⟩,
    ⟨(2, 1, 1), (-252240068774126241939559)⟩,
    ⟨(2, 1, 2), (-232699200934491413804040)⟩,
    ⟨(2, 1, 3), (-58967877183467767614968)⟩,
    ⟨(2, 2, 0), 372585035116877757666⟩,
    ⟨(2, 2, 1), 1447471691824802084113⟩,
    ⟨(2, 2, 2), 2066502569781041146635⟩,
    ⟨(2, 3, 0), (-1058480213400220902)⟩,
    ⟨(2, 3, 1), (-5170615701538863187)⟩,
    ⟨(2, 4, 0), 2255284545597061⟩,
    ⟨(3, 0, 0), (-14572214706793441188696)⟩,
    ⟨(3, 0, 1), (-42040011462354373656593)⟩,
    ⟨(3, 0, 2), (-38783200155748568967340)⟩,
    ⟨(3, 0, 3), (-9827979530577961269161)⟩,
    ⟨(3, 1, 0), 124195011705625919222⟩,
    ⟨(3, 1, 1), 482490563941600694705⟩,
    ⟨(3, 1, 2), 688834189927013715545⟩,
    ⟨(3, 2, 0), (-529240106700110452)⟩,
    ⟨(3, 2, 1), (-2585307850769431593)⟩,
    ⟨(3, 3, 0), 1503523030398041⟩,
    ⟨(4, 0, 0), 15524376463203239903⟩,
    ⟨(4, 0, 1), 60311320492700086838⟩,
    ⟨(4, 0, 2), 86104273740876714443⟩,
    ⟨(4, 1, 0), (-132310026675027613)⟩,
    ⟨(4, 1, 1), (-646326962692357898)⟩,
    ⟨(4, 2, 0), 563821136399266⟩,
    ⟨(5, 0, 0), (-13231002667502762)⟩,
    ⟨(5, 0, 1), (-64632696269235790)⟩,
    ⟨(5, 1, 0), 112764227279853⟩,
    ⟨(6, 0, 0), 9397018939988⟩]⟩, 71059880224794142256140⟩

section

open Lean Meta Sym.Simp
open DimThree.Certificate (Sparse)

-- Replay individual model operations as in CompactShortTangentPilot.
private meta def quoteModel (p : Model) : MetaM Expr := do
  let terms ← p.polynomial.terms.mapM fun a => do
    let (i, j, k) := a.exponents
    let jk ← mkAppM ``Prod.mk #[toExpr j, toExpr k]
    let ijk ← mkAppM ``Prod.mk #[toExpr i, jk]
    return mkApp2 (mkConst ``DimThree.Certificate.Term.mk) ijk (toExpr a.coefficient)
  let terms ← mkListLit (mkConst ``DimThree.Certificate.Term) terms
  return mkApp2 (mkConst ``Model.mk) (mkApp (mkConst ``Sparse.mk) terms) (toExpr p.radius)

private meta def stageModel (modelInputs : Nat) : Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    return .rfl
  unless (e.getAppArgs.extract 0 modelInputs).all (fun a => a.isAppOfArity ``Model.mk 2) do
    throwError "expected reduced model inputs for {e.getAppFn}"
  let (output, equality) ← liftM (m := MetaM) <| do
    let value ← unsafe evalExpr Model (mkConst ``Model) e
    let output ← quoteModel value
    let theoremType ← mkEq e output
    let proof ← mkEqRefl output
    let equality ← try
      withOptions (fun opts ↦ Lean.maxHeartbeats.set (Elab.async.set opts false) 350000) <|
        mkAuxLemma [] theoremType proof
    catch err =>
      throwError "kernel replay of {e.getAppFn} failed: {err.toMessageData}"
    pure (output, equality)
  return .step (← Sym.shareCommon output) (mkConst equality) (done := true)

local cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageModel 2
local cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageModel 2
local cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageModel 2
local cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := stageModel 0
local cbv_simproc cbv_eval stageWiden (Model.widen _ _) := stageModel 1
attribute [local cbv_opaque] Model.mul Model.add Model.sub Model.ofRat Model.widen

set_option profiler true in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
set_option maxHeartbeats 0 in
-- Check each model operation after reducing its inputs.
private theorem first_upper_gap_decay_eq :
    firstUpperGapArgument.centeredExp = firstUpperGapDecay := by
  have hCenter : Model.center firstUpperGapArgument =
      (-72925922314266038012239317923 / 633825300114114700748351602688 : ℚ) := by rfl'
  have hHalvings : Model.expHalvings firstUpperGapArgument = 0 := by rfl'
  simp only [Model.centeredExp, hCenter, hHalvings, expCenteredModel, pow_zero, div_one, Model.pow]
  conv_lhs => cbv
  all_goals rfl

private def firstUpperGapHalf : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), (-1069580193942568557512843329536)⟩,
    ⟨(0, 1, 0), (-79228162514264337593543950336)⟩,
    ⟨(1, 0, 0), (-39614081257132168796771975168)⟩]⟩, 0⟩

/-- Exact fixed-point value of the regularized quotient in the first upper gap. -/
def firstUpperGapQuotient : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), (-1010342463101558156237935857067)⟩,
    ⟨(0, 0, 1), 57009058237435920678605033813⟩,
    ⟨(0, 0, 2), (-2165304122383434115887848668)⟩,
    ⟨(0, 0, 3), 61921507175455227829092988⟩,
    ⟨(0, 0, 4), (-1419379394259812370016564)⟩,
    ⟨(0, 0, 5), 27142931112986048373044⟩,
    ⟨(0, 0, 6), (-445214845255714080164)⟩,
    ⟨(0, 1, 0), (-70617289249194239671061542463)⟩,
    ⟨(0, 1, 1), 8125000609637405416698842244⟩,
    ⟨(0, 1, 2), (-467418358935106419568612374)⟩,
    ⟨(0, 1, 3), 17926556379613456432318941⟩,
    ⟨(0, 1, 4), (-515643134498824563571675)⟩,
    ⟨(0, 1, 5), 11865651674546815241280⟩,
    ⟨(0, 2, 0), 300925948505089089507364528⟩,
    ⟨(0, 2, 1), 266302366361747873243022870⟩,
    ⟨(0, 2, 2), (-32631742545606387771861775)⟩,
    ⟨(0, 2, 3), 1915448022253521149728523⟩,
    ⟨(0, 2, 4), (-74194232578613488077048)⟩,
    ⟨(0, 3, 0), (-854903262798548549736831)⟩,
    ⟨(0, 3, 1), (-1611444076326241371449964)⟩,
    ⟨(0, 3, 2), (-663836999477674674633980)⟩,
    ⟨(0, 3, 3), 87262200350434280176515⟩,
    ⟨(0, 4, 0), 1821526838349180148587⟩,
    ⟨(0, 4, 1), 5255001432794296707075⟩,
    ⟨(0, 4, 2), 4847900019468571120917⟩,
    ⟨(0, 5, 0), (-3104875292640647980)⟩,
    ⟨(0, 5, 1), (-12062264098540017368)⟩,
    ⟨(0, 6, 0), 4410334222500921⟩,
    ⟨(1, 0, 0), (-35308644624597119835530771232)⟩,
    ⟨(1, 0, 1), 4062500304818702708349421122⟩,
    ⟨(1, 0, 2), (-233709179467553209784306186)⟩,
    ⟨(1, 0, 3), 8963278189806728216159470⟩,
    ⟨(1, 0, 4), (-257821567249412281785837)⟩,
    ⟨(1, 0, 5), 5932825837273407620640⟩,
    ⟨(1, 1, 0), 300925948505089089507364528⟩,
    ⟨(1, 1, 1), 266302366361747873243022870⟩,
    ⟨(1, 1, 2), (-32631742545606387771861775)⟩,
    ⟨(1, 1, 3), 1915448022253521149728523⟩,
    ⟨(1, 1, 4), (-74194232578613488077048)⟩,
    ⟨(1, 2, 0), (-1282354894197822824605247)⟩,
    ⟨(1, 2, 1), (-2417166114489362057174946)⟩,
    ⟨(1, 2, 2), (-995755499216512011950970)⟩,
    ⟨(1, 2, 3), 130893300525651420264772⟩,
    ⟨(1, 3, 0), 3643053676698360297174⟩,
    ⟨(1, 3, 1), 10510002865588593414148⟩,
    ⟨(1, 3, 2), 9695800038937142241835⟩,
    ⟨(1, 4, 0), (-7762188231601619952)⟩,
    ⟨(1, 4, 1), (-30155660246350043419)⟩,
    ⟨(1, 5, 0), 13231002667502761⟩,
    ⟨(2, 0, 0), 75231487126272272376841132⟩,
    ⟨(2, 0, 1), 66575591590436968310755718⟩,
    ⟨(2, 0, 2), (-8157935636401596942965444)⟩,
    ⟨(2, 0, 3), 478862005563380287432131⟩,
    ⟨(2, 0, 4), (-18548558144653372019262)⟩,
    ⟨(2, 1, 0), (-641177447098911412302623)⟩,
    ⟨(2, 1, 1), (-1208583057244681028587473)⟩,
    ⟨(2, 1, 2), (-497877749608256005975485)⟩,
    ⟨(2, 1, 3), 65446650262825710132386⟩,
    ⟨(2, 2, 0), 2732290257523770222880⟩,
    ⟨(2, 2, 1), 7882502149191445060611⟩,
    ⟨(2, 2, 2), 7271850029202856681376⟩,
    ⟨(2, 3, 0), (-7762188231601619952)⟩,
    ⟨(2, 3, 1), (-30155660246350043419)⟩,
    ⟨(2, 4, 0), 16538753334378452⟩,
    ⟨(3, 0, 0), (-106862907849818568717104)⟩,
    ⟨(3, 0, 1), (-201430509540780171431245)⟩,
    ⟨(3, 0, 2), (-82979624934709334329247)⟩,
    ⟨(3, 0, 3), 10907775043804285022064⟩,
    ⟨(3, 1, 0), 910763419174590074293⟩,
    ⟨(3, 1, 1), 2627500716397148353537⟩,
    ⟨(3, 1, 2), 2423950009734285560459⟩,
    ⟨(3, 2, 0), (-3881094115800809976)⟩,
    ⟨(3, 2, 1), (-15077830123175021710)⟩,
    ⟨(3, 3, 0), 11025835556252301⟩,
    ⟨(4, 0, 0), 113845427396823759287⟩,
    ⟨(4, 0, 1), 328437589549643544192⟩,
    ⟨(4, 0, 2), 302993751216785695057⟩,
    ⟨(4, 1, 0), (-970273528950202494)⟩,
    ⟨(4, 1, 1), (-3769457530793755427)⟩,
    ⟨(4, 2, 0), 4134688333594613⟩,
    ⟨(5, 0, 0), (-97027352895020249)⟩,
    ⟨(5, 0, 1), (-376945753079375543)⟩,
    ⟨(5, 1, 0), 826937666718923⟩,
    ⟨(6, 0, 0), 68911472226577⟩]⟩, 33145699943768962686570⟩

set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
set_option maxHeartbeats 0 in
-- Check the Horner evaluation one model operation at a time.
theorem first_upper_gap_quotient_eq :
    positiveRateGapModel (leafAt 0).model.H
        ((CompactMiddleBox.V (leafAt 0).model).mul (Model.ofRat (-1 / 2))) =
      firstUpperGapQuotient := by
  have hHalf :
      (CompactMiddleBox.V (leafAt 0).model).mul (Model.ofRat (-1 / 2)) =
        firstUpperGapHalf := by
    have hBox : (leafAt 0).box = (⟨1 / 2, 5 / 8, 1, 5 / 4⟩ : Rectangle) := by rfl'
    simp only [CompactMiddleBox.V, Leaf.model, hBox, CompactMiddleBox.ofIntervals]
    all_goals rfl'
  have hRadius : firstUpperGapArgument.argumentRadius =
      (162057605142813417804976262053 / 633825300114114700748351602688 : ℚ) := by rfl'
  dsimp only [positiveRateGapModel]
  rw [first_upper_gap_argument_eq, hHalf, hRadius]
  conv_lhs => cbv
  all_goals rfl

/-- Resume upper-gap arithmetic using the checked exponential and the original quotient model. -/
theorem first_upper_gap_eq :
    let b := (leafAt 0).model
    let half := (CompactMiddleBox.V b).mul (Model.ofRat (-1 / 2))
    CompactMiddleBox.Fv b =
      ((Model.ofRat 1).add firstUpperGapDecay).mul
        (Model.zero.sub (positiveRateGapModel b.H half)) := by
  dsimp only [CompactMiddleBox.Fv, middleGapModel]
  refine congrArg (fun decay : Model ↦ ((Model.ofRat 1).add decay).mul
    (Model.zero.sub (positiveRateGapModel (leafAt 0).model.H
      ((CompactMiddleBox.V (leafAt 0).model).mul (Model.ofRat (-1 / 2)))))) ?_
  exact
    ((congrArg Model.centeredExp first_upper_gap_argument_eq).trans first_upper_gap_decay_eq)


/-- Fixed-point model of the first leaf's upper gap. -/
def firstUpperGapFv : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), 1910876360309392189308429633784⟩,
    ⟨(0, 0, 1), (-211434680336359526936103202941)⟩,
    ⟨(0, 0, 2), 15902327953098666634741781210⟩,
    ⟨(0, 0, 3), (-904107741882634736625990339)⟩,
    ⟨(0, 0, 4), 41283993936257901578135893⟩,
    ⟨(0, 0, 5), (-1574491900089422237865319)⟩,
    ⟨(0, 0, 6), 51542248134097035894715⟩,
    ⟨(0, 1, 0), 125884568886891308323876031913⟩,
    ⟨(0, 1, 1), (-28967755908631238563164655072)⟩,
    ⟨(0, 1, 2), 3332937824714673755136842417⟩,
    ⟨(0, 1, 3), (-255651480873000543717882800)⟩,
    ⟨(0, 1, 4), 14707222976358696051952066⟩,
    ⟨(0, 1, 5), (-676866511980144534209157)⟩,
    ⟨(0, 2, 0), (-1072879848467823650487579818)⟩,
    ⟨(0, 2, 1), (-825995565155625594551517415)⟩,
    ⟨(0, 2, 2), 218478563215197995522964313⟩,
    ⟨(0, 2, 3), (-26226872248650623960957042)⟩,
    ⟨(0, 2, 4), 2053502197982743019880091⟩,
    ⟨(0, 3, 0), 6095908229930816195952158⟩,
    ⟨(0, 3, 1), 10789064850133234346813052⟩,
    ⟨(0, 3, 2), 3451801147388793176298596⟩,
    ⟨(0, 3, 3), (-1092339153219019156602314)⟩,
    ⟨(0, 4, 0), (-25976881661637000835023)⟩,
    ⟨(0, 4, 1), (-71953010284363851744740)⟩,
    ⟨(0, 4, 2), (-60685508512167730922350)⟩,
    ⟨(0, 5, 0), 88557551119217048300⟩,
    ⟨(0, 5, 1), 333851904361366542886⟩,
    ⟨(0, 6, 0), (-251583952043230252)⟩,
    ⟨(1, 0, 0), 62942284443445654161938015958⟩,
    ⟨(1, 0, 1), (-14483877954315619281582327536)⟩,
    ⟨(1, 0, 2), 1666468912357336877568421206⟩,
    ⟨(1, 0, 3), (-127825740436500271858941399)⟩,
    ⟨(1, 0, 4), 7353611488179348025976032⟩,
    ⟨(1, 0, 5), (-338433255990072267104579)⟩,
    ⟨(1, 1, 0), (-1072879848467823650487579818)⟩,
    ⟨(1, 1, 1), (-825995565155625594551517415)⟩,
    ⟨(1, 1, 2), 218478563215197995522964313⟩,
    ⟨(1, 1, 3), (-26226872248650623960957042)⟩,
    ⟨(1, 1, 4), 2053502197982743019880091⟩,
    ⟨(1, 2, 0), 9143862344896224293928238⟩,
    ⟨(1, 2, 1), 16183597275199851520219578⟩,
    ⟨(1, 2, 2), 5177701721083189764447895⟩,
    ⟨(1, 2, 3), (-1638508729828528734903470)⟩,
    ⟨(1, 3, 0), (-51953763323274001670047)⟩,
    ⟨(1, 3, 1), (-143906020568727703489475)⟩,
    ⟨(1, 3, 2), (-121371017024335461844701)⟩,
    ⟨(1, 4, 0), 221393877798042620755⟩,
    ⟨(1, 4, 1), 834629760903416357214⟩,
    ⟨(1, 5, 0), (-754751856129690751)⟩,
    ⟨(2, 0, 0), (-268219962116955912621894954)⟩,
    ⟨(2, 0, 1), (-206498891288906398637879355)⟩,
    ⟨(2, 0, 2), 54619640803799498880741079⟩,
    ⟨(2, 0, 3), (-6556718062162655990239261)⟩,
    ⟨(2, 0, 4), 513375549495685754970023⟩,
    ⟨(2, 1, 0), 4571931172448112146964118⟩,
    ⟨(2, 1, 1), 8091798637599925760109789⟩,
    ⟨(2, 1, 2), 2588850860541594882223947⟩,
    ⟨(2, 1, 3), (-819254364914264367451735)⟩,
    ⟨(2, 2, 0), (-38965322492455501252534)⟩,
    ⟨(2, 2, 1), (-107929515426545777617106)⟩,
    ⟨(2, 2, 2), (-91028262768251596383525)⟩,
    ⟨(2, 3, 0), 221393877798042620755⟩,
    ⟨(2, 3, 1), 834629760903416357214⟩,
    ⟨(2, 4, 0), (-943439820162113442)⟩,
    ⟨(3, 0, 0), 761988528741352024494020⟩,
    ⟨(3, 0, 1), 1348633106266654293351631⟩,
    ⟨(3, 0, 2), 431475143423599147037324⟩,
    ⟨(3, 0, 3), (-136542394152377394575288)⟩,
    ⟨(3, 1, 0), (-12988440830818500417511)⟩,
    ⟨(3, 1, 1), (-35976505142181925872368)⟩,
    ⟨(3, 1, 2), (-30342754256083865461176)⟩,
    ⟨(3, 2, 0), 110696938899021310377⟩,
    ⟨(3, 2, 1), 417314880451708178608⟩,
    ⟨(3, 3, 0), (-628959880108075627)⟩,
    ⟨(4, 0, 0), (-1623555103852312552189)⟩,
    ⟨(4, 0, 1), (-4497063142772740734046)⟩,
    ⟨(4, 0, 2), (-3792844282010483182646)⟩,
    ⟨(4, 1, 0), 27674234724755327594⟩,
    ⟨(4, 1, 1), 104328720112927044651⟩,
    ⟨(4, 2, 0), (-235859955040528360)⟩,
    ⟨(5, 0, 0), 2767423472475532758⟩,
    ⟨(5, 0, 1), 10432872011292704466⟩,
    ⟨(5, 1, 0), (-47171991008105673)⟩,
    ⟨(6, 0, 0), (-3930999250675473)⟩]⟩, 919496540790027313526247⟩

set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- The two input models are checked independently before this product.
theorem first_upper_gap_fv_eq : CompactMiddleBox.Fv (leafAt 0).model = firstUpperGapFv := by
  simp only [first_upper_gap_eq, first_upper_gap_quotient_eq]
  conv_lhs => cbv
  all_goals rfl


open private CompactMiddleBox.clearedScores CompactMiddleBox.neg CompactMiddleBox.headChecks
  CompactMiddleBox.weights CompactMiddleBox.upperRadicand from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

private def firstUpperHead : Model :=
  let leaf := leafAt 0
  (CompactMiddleBox.neg
    (CompactMiddleBox.clearedScores leaf.model leaf.box.dLo false false).2).truncate leaf.degree

private def literalUpperHead : Model :=
  ⟨⟨[
    ⟨(0, 0, 0), 6231844086616625887510337182⟩,
    ⟨(0, 0, 1), 2337631093169065890083191932⟩,
    ⟨(0, 0, 2), 201382025140634830660590174⟩,
    ⟨(0, 1, 0), 4252928988803093314781558232⟩,
    ⟨(0, 1, 1), 1276062203174574027055479277⟩,
    ⟨(0, 2, 0), 1040188302662403566203808477⟩,
    ⟨(1, 0, 0), 1130138193616327799130608879⟩,
    ⟨(1, 0, 1), 336002510131095972453442576⟩,
    ⟨(1, 1, 0), 653928865150639160231832882⟩,
    ⟨(2, 0, 0), 36258241862870258559509720⟩]⟩, 837602719323187650309189221⟩


set_option profiler true in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- Replay the corner after substituting its checked upper-gap model.
private theorem firstUpperHead_eq : firstUpperHead = literalUpperHead := by
  simp only [firstUpperHead, CompactMiddleBox.clearedScores, CompactMiddleBox.weights,
    CompactMiddleBox.upperRadicand, first_upper_gap_fv_eq]
  conv_lhs => cbv
  all_goals rfl

private theorem literalUpperHead_checked :
    CompactMiddleBox.headChecks 2 literalUpperHead = true := by
  decide +kernel

/-- The first upper corner satisfies the original degree-two endpoint check. -/
theorem firstUpperCorner_checked :
    (leafAt 0).model.clearedUpperCheck (leafAt 0).box.dLo false false (leafAt 0).degree = true := by
  change CompactMiddleBox.headChecks 2 firstUpperHead = true
  exact (congrArg (CompactMiddleBox.headChecks 2) firstUpperHead_eq).trans literalUpperHead_checked

#print axioms firstUpperCorner_checked

end

#print axioms first_upper_gap_fv_eq

#print axioms first_upper_gap_eq
#print axioms first_upper_gap_quotient_eq

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid
