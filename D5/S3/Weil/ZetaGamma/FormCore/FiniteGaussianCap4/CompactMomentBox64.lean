/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMomentBox64
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: All actual compact moment and normalization boxes for the matrix input. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMomentEnclosures

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

def normalizationLower64 : ℚ := 19453185482431764867166893589181287300918058967280623307138478551 / (10 : ℚ) ^ 64
def normalizationUpper64 : ℚ := 19453185482431764867166893589181287300918058967280623307138478552 / (10 : ℚ) ^ 64

def WLower64 : Fin 61 → ℚ := ![
  3471252578010904836453183492679326587955076928134180463207572634 / (10 : ℚ) ^ 64,
  10177750771851376944637605400184734886678650069360320275717668532 / (10 : ℚ) ^ 64,
  31796183554932679676092684370001040551335328520198071028360533782 / (10 : ℚ) ^ 64,
  103543633149531519256975546180174492608067383940525283867870074430 / (10 : ℚ) ^ 64,
  346104999195396358521185565364319466759887497168161574883589997166 / (10 : ℚ) ^ 64,
  1172282988849606397995925037543316881312362222208404017719694536869 / (10 : ℚ) ^ 64,
  3967862789798410745526728578581334725708844227478543331108337805790 / (10 : ℚ) ^ 64,
  13159704868956569159149077042192988295482331960922502362784942350542 / (10 : ℚ) ^ 64,
  41267810964245059298409536664372000676125307338694646717471150788123 / (10 : ℚ) ^ 64,
  112201533080734993044605802693933233361835346198717372268459771104020 / (10 : ℚ) ^ 64,
  181644347077028695626019716603963665295999026032643243825269620581843 / (10 : ℚ) ^ 64,
  -704221907740260505399535330515722783641463923315216959074637674756321 / (10 : ℚ) ^ 64,
  -10763287768564535180929817327146179020615126080253777531296860348745408 / (10 : ℚ) ^ 64,
  -88126419982205065008073320027847818536076262870649540109178931718876633 / (10 : ℚ) ^ 64,
  -611155892876290764308754034552483837179838572587976564163705136611669988 / (10 : ℚ) ^ 64,
  -3938053603037992231105678898978731667757230729872130454902755496743893071 / (10 : ℚ) ^ 64,
  -24402663476978212628001532532114765438254197673929978973101068267150417719 / (10 : ℚ) ^ 64,
  -147797903010702851311880847538529874990305341894858541972515832028612793547 / (10 : ℚ) ^ 64,
  -882604884410111057113116661678032890980156344949484490380074851412773265076 / (10 : ℚ) ^ 64,
  -5223315223631973076158251672937210726958637945941855790840567344521208127124 / (10 : ℚ) ^ 64,
  -30731003878100018919643027543252877951797993276955028635249033531292955624790 / (10 : ℚ) ^ 64,
  -180110359185199778953196317602975458538418466431500124686158388946268024364187 / (10 : ℚ) ^ 64,
  -1052970677772447063483977830197757377609394341918975882735800759431478001595566 / (10 : ℚ) ^ 64,
  -6146189696440190546886928430516195435871917994499200174209982884373677840418276 / (10 : ℚ) ^ 64,
  -35841116057687972417703565089689939990066042020087042586508848142047990916876100 / (10 : ℚ) ^ 64,
  -208898112663913230154534617098801501202019675275309620742381421719336686164743525 / (10 : ℚ) ^ 64,
  -1217307135900373776789541888120956659780991912771573472206427284169516184515225509 / (10 : ℚ) ^ 64,
  -7093726903499977884986211156302786350148403868540946385871786654267163807159940486 / (10 : ℚ) ^ 64,
  -41345250565362293144595856852302770546215042363112487965708101140559130178557802261 / (10 : ℚ) ^ 64,
  -241047144356547685237534642317727859195903942468752910630568587769847204538781361355 / (10 : ℚ) ^ 64,
  -1405845158105701516894707570963540663705123944657898183878721776769618971091826039895 / (10 : ℚ) ^ 64,
  -8202675874001269480242351218628652291617455456389246317952703802150877979634712431247 / (10 : ℚ) ^ 64,
  -47881955279387585307902512348113594022616265466734823083569854073109631775961546609658 / (10 : ℚ) ^ 64,
  -279638176777604435845700598661356988610339644912344410527572420461648014034559150574654 / (10 : ℚ) ^ 64,
  -1633936117216996922409774380551083486379403370785522445102395669836079115485172651956429 / (10 : ℚ) ^ 64,
  -9551912554515575928292382063963337834154513394429342829776270852589234935403957105233624 / (10 : ℚ) ^ 64,
  -55867927545675316611357430143633760595161786486810976899597935732806914865734333539556046 / (10 : ℚ) ^ 64,
  -326926653984826870236430497756950807505097929929459551040092233648201829019520758224209190 / (10 : ℚ) ^ 64,
  -1914039833139432536492149839288226706637945741150002276460182733871279648858012281173216037 / (10 : ℚ) ^ 64,
  -11211427286988883372059436698033723067394137886155186615899210422433540505545486202164839304 / (10 : ℚ) ^ 64,
  -65701592692053038873356713259806149735553724558446293422767310872412853391500820705430121376 / (10 : ℚ) ^ 64,
  -385204429058787508766512769497160672725428864317795215874448373193927548535229818174924023339 / (10 : ℚ) ^ 64,
  -2259446458971727362255724900355256669732178645022693100954776446990156625902338340918697195122 / (10 : ℚ) ^ 64,
  -13258765617545671053484094187930177243035290090401406215292728233235843568169342459829834539848 / (10 : ℚ) ^ 64,
  -77837548093854014285431618660229739235070998961992805023648712897019915453959032040666615333637 / (10 : ℚ) ^ 64,
  -457146028572621329549483581488483038270494040963436324958073619883721114370182430490428602774857 / (10 : ℚ) ^ 64,
  -2685933584351693999056087371228628080801673060474955766295793448817718528521376404580138477809177 / (10 : ℚ) ^ 64,
  -15787193487867725095647559982275513961379161253473105274866260021281866942774072159437502028684703 / (10 : ℚ) ^ 64,
  -92827971660754081177878762816694912799363917900250359567207247209499403622525971711310185186511188 / (10 : ℚ) ^ 64,
  -546024455997108868448534454988468088123488089752334677114231028145811100209993676022722322703454103 / (10 : ℚ) ^ 64,
  -3212919164149403528658336956542136694751137389304761188276412713989162465190246600959127316553037502 / (10 : ℚ) ^ 64,
  -18911992075252533677563735402634639007060072174621453289684603860942736766934714439277152150211165977 / (10 : ℚ) ^ 64,
  -111357629460857094864064255146460975323831841120641106173029384042067767496065151146083215729945353228 / (10 : ℚ) ^ 64,
  -655908855263833120620614649161717160491596206096214158792844670292129654751338765983169963488603665753 / (10 : ℚ) ^ 64,
  -3864591298546391580074711536579158265361402922080120189391772049938706643152404284634860947764655987621 / (10 : ℚ) ^ 64,
  -22776977936493846276956601069718890577161380244940383097337610043135432156907283634396496578929662712619 / (10 : ℚ) ^ 64,
  -134281789498644357104925350696407074455375367131362966080316649040114534789770283284965988810271471975917 / (10 : ℚ) ^ 64,
  -791886264948092287923563618974618504479011842837355855279587989514889810452933907497470218917476238633279 / (10 : ℚ) ^ 64,
  -4671211085700955347799103168212928126271928604484978725409827385816540036329297944394165475834015721413956 / (10 : ℚ) ^ 64,
  -27562183890177018474675659115715229314171667186491803648315909495902515079384026872077473321659284664408719 / (10 : ℚ) ^ 64,
  -162671622929552044858142728673615255701358749221331879343091365927081316516873253506867821443884661629211664 / (10 : ℚ) ^ 64]

def WUpper64 : Fin 61 → ℚ := ![
  3471252578010904836453183492679326587955076928134180463207572635 / (10 : ℚ) ^ 64,
  10177750771851376944637605400184734886678650069360320275717668533 / (10 : ℚ) ^ 64,
  31796183554932679676092684370001040551335328520198071028360533783 / (10 : ℚ) ^ 64,
  103543633149531519256975546180174492608067383940525283867870074431 / (10 : ℚ) ^ 64,
  346104999195396358521185565364319466759887497168161574883589997167 / (10 : ℚ) ^ 64,
  1172282988849606397995925037543316881312362222208404017719694536870 / (10 : ℚ) ^ 64,
  3967862789798410745526728578581334725708844227478543331108337805791 / (10 : ℚ) ^ 64,
  13159704868956569159149077042192988295482331960922502362784942350543 / (10 : ℚ) ^ 64,
  41267810964245059298409536664372000676125307338694646717471150788124 / (10 : ℚ) ^ 64,
  112201533080734993044605802693933233361835346198717372268459771104021 / (10 : ℚ) ^ 64,
  181644347077028695626019716603963665295999026032643243825269620581844 / (10 : ℚ) ^ 64,
  -704221907740260505399535330515722783641463923315216959074637674756320 / (10 : ℚ) ^ 64,
  -10763287768564535180929817327146179020615126080253777531296860348745407 / (10 : ℚ) ^ 64,
  -88126419982205065008073320027847818536076262870649540109178931718876632 / (10 : ℚ) ^ 64,
  -611155892876290764308754034552483837179838572587976564163705136611669987 / (10 : ℚ) ^ 64,
  -3938053603037992231105678898978731667757230729872130454902755496743893070 / (10 : ℚ) ^ 64,
  -24402663476978212628001532532114765438254197673929978973101068267150417718 / (10 : ℚ) ^ 64,
  -147797903010702851311880847538529874990305341894858541972515832028612793546 / (10 : ℚ) ^ 64,
  -882604884410111057113116661678032890980156344949484490380074851412773265075 / (10 : ℚ) ^ 64,
  -5223315223631973076158251672937210726958637945941855790840567344521208127123 / (10 : ℚ) ^ 64,
  -30731003878100018919643027543252877951797993276955028635249033531292955624789 / (10 : ℚ) ^ 64,
  -180110359185199778953196317602975458538418466431500124686158388946268024364186 / (10 : ℚ) ^ 64,
  -1052970677772447063483977830197757377609394341918975882735800759431478001595565 / (10 : ℚ) ^ 64,
  -6146189696440190546886928430516195435871917994499200174209982884373677840418275 / (10 : ℚ) ^ 64,
  -35841116057687972417703565089689939990066042020087042586508848142047990916876099 / (10 : ℚ) ^ 64,
  -208898112663913230154534617098801501202019675275309620742381421719336686164743524 / (10 : ℚ) ^ 64,
  -1217307135900373776789541888120956659780991912771573472206427284169516184515225508 / (10 : ℚ) ^ 64,
  -7093726903499977884986211156302786350148403868540946385871786654267163807159940485 / (10 : ℚ) ^ 64,
  -41345250565362293144595856852302770546215042363112487965708101140559130178557802260 / (10 : ℚ) ^ 64,
  -241047144356547685237534642317727859195903942468752910630568587769847204538781361354 / (10 : ℚ) ^ 64,
  -1405845158105701516894707570963540663705123944657898183878721776769618971091826039894 / (10 : ℚ) ^ 64,
  -8202675874001269480242351218628652291617455456389246317952703802150877979634712431246 / (10 : ℚ) ^ 64,
  -47881955279387585307902512348113594022616265466734823083569854073109631775961546609657 / (10 : ℚ) ^ 64,
  -279638176777604435845700598661356988610339644912344410527572420461648014034559150574653 / (10 : ℚ) ^ 64,
  -1633936117216996922409774380551083486379403370785522445102395669836079115485172651956428 / (10 : ℚ) ^ 64,
  -9551912554515575928292382063963337834154513394429342829776270852589234935403957105233623 / (10 : ℚ) ^ 64,
  -55867927545675316611357430143633760595161786486810976899597935732806914865734333539556045 / (10 : ℚ) ^ 64,
  -326926653984826870236430497756950807505097929929459551040092233648201829019520758224209189 / (10 : ℚ) ^ 64,
  -1914039833139432536492149839288226706637945741150002276460182733871279648858012281173216036 / (10 : ℚ) ^ 64,
  -11211427286988883372059436698033723067394137886155186615899210422433540505545486202164839303 / (10 : ℚ) ^ 64,
  -65701592692053038873356713259806149735553724558446293422767310872412853391500820705430121375 / (10 : ℚ) ^ 64,
  -385204429058787508766512769497160672725428864317795215874448373193927548535229818174924023338 / (10 : ℚ) ^ 64,
  -2259446458971727362255724900355256669732178645022693100954776446990156625902338340918697195121 / (10 : ℚ) ^ 64,
  -13258765617545671053484094187930177243035290090401406215292728233235843568169342459829834539847 / (10 : ℚ) ^ 64,
  -77837548093854014285431618660229739235070998961992805023648712897019915453959032040666615333636 / (10 : ℚ) ^ 64,
  -457146028572621329549483581488483038270494040963436324958073619883721114370182430490428602774856 / (10 : ℚ) ^ 64,
  -2685933584351693999056087371228628080801673060474955766295793448817718528521376404580138477809176 / (10 : ℚ) ^ 64,
  -15787193487867725095647559982275513961379161253473105274866260021281866942774072159437502028684702 / (10 : ℚ) ^ 64,
  -92827971660754081177878762816694912799363917900250359567207247209499403622525971711310185186511187 / (10 : ℚ) ^ 64,
  -546024455997108868448534454988468088123488089752334677114231028145811100209993676022722322703454102 / (10 : ℚ) ^ 64,
  -3212919164149403528658336956542136694751137389304761188276412713989162465190246600959127316553037501 / (10 : ℚ) ^ 64,
  -18911992075252533677563735402634639007060072174621453289684603860942736766934714439277152150211165976 / (10 : ℚ) ^ 64,
  -111357629460857094864064255146460975323831841120641106173029384042067767496065151146083215729945353227 / (10 : ℚ) ^ 64,
  -655908855263833120620614649161717160491596206096214158792844670292129654751338765983169963488603665752 / (10 : ℚ) ^ 64,
  -3864591298546391580074711536579158265361402922080120189391772049938706643152404284634860947764655987619 / (10 : ℚ) ^ 64,
  -22776977936493846276956601069718890577161380244940383097337610043135432156907283634396496578929662712579 / (10 : ℚ) ^ 64,
  -134281789498644357104925350696407074455375367131362966080316649040114534789770283284965988810271471974712 / (10 : ℚ) ^ 64,
  -791886264948092287923563618974618504479011842837355855279587989514889810452933907497470218917476238595656 / (10 : ℚ) ^ 64,
  -4671211085700955347799103168212928126271928604484978725409827385816540036329297944394165475834015720219459 / (10 : ℚ) ^ 64,
  -27562183890177018474675659115715229314171667186491803648315909495902515079384026872077473321659284625886220 / (10 : ℚ) ^ 64,
  -162671622929552044858142728673615255701358749221331879343091365927081316516873253506867821443884660367599852 / (10 : ℚ) ^ 64]

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
