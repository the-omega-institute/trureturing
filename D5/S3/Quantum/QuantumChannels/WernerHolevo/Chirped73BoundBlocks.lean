/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73BoundBlocks
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.row_bounds; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73BoundBlocks.H
   digest: Checked integer preconditioned row bounds for the first block of order-73 equations. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73Correlations

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

def H : ℤ := D * scale ^ 2
def E : ℤ := 135687631082149874210586736815260797248452185015511623913485835825390094931451324088704
def delta : ℤ := 17571217473034473117416689921377547700291789627182888307146154313883093791716928719711744
def M : ℤ := 839665530938580108460717191577538723261199564582188269131524992

private def defectChunks_0 : Array (ℤ) := #[3361413346428276263008042008790589023173087784031052701551269611217454542433567568, 3269718297758705892289406524722260596578708666947608486250734054138369957992003768, 4253107084565470341275803697687397361329643822294442533180193767678784145385672888, 3497815865945834743542021420564921062698740103571943214802361228438805189445804424, 1826533727148011283717423390309925365753497445107285138123273447498546485724282664]
private def defectChunks_1 : Array (ℤ) := #[2069372396696241431120714587697123798471036935542093066122769051174928640454138624, 1621915660386930431511954868705450324655393801863970867241422084638369776688407552, 2449549853219972819393413991929238455849834818253184991989506486612528959910302080, 2146953697904318710091615818935981072511248144946548764388730058222595616573130624, 1495288807675505010986747130860208151597223746143540224626156660131425570675835136]
private def defectChunks_2 : Array (ℤ) := #[4851236336818835126268128448098458129577844289947149258768109631605387155512311424, 5576942969658556974774265473632093465886753562749441283136514224558875133923097216, 8738113601699934401320817215173618874847445751454179327911642995492042136393226624, 6121328681445176555375835846370548853030143802595546301217538164929086121770481408, 2158690733207155605713702970983323151769160663635478519249779025068072924782920960]
private def defectChunks_3 : Array (ℤ) := #[4293700473288598706443143324659114878500326665378467638756105836430651317747376608, 4333330885692073986449678669495083638045233814206935658689915518423155019430180992, 6541481825868088190454943422681840691710636635653386653955964497761097006387587392, 4771638975093177187488677824683395901858783759292062517991802427577002818623026304, 2314127026302340052988875701294436979761484373027834059810750904433957619118675808]
private def defectChunks_4 : Array (ℤ) := #[3282598448402226898517263395439538027488534308461106668695323519306207746646938240, 2929846750594060331472701637552228247198949362341179958796013120513079986123174656, 4776424022874300525257431385658142929023847519804589340798391449842572400604101696, 3589680624434059109333104341418135878666085385588253854157024372702344874598052544, 1587543934479330250874817491223369950626425632134353914906035172958195030947201728]
private def defectChunks_5 : Array (ℤ) := #[6325326029740161792021330087944241383878975203525323635435987915117477693325003648, 3763156815280253032748702701543094182000837534419925126511157830895921433423176704, 7416725961831721937924775334369014932068322643345143495369790354375277718913322496, 5537735380422085229838981214810146121774795102499563734405182086742422334714800640, 2333275997189481176250085471890942030227523840996711125681705058045976747821697408]
private def defectChunks_6 : Array (ℤ) := #[5444721225136198467337744669365030585130975885920448728299927061006483845975572992, 5666152443320436712460943982449458414464933865018772001640446966710386290150064896, 7959235135905122972364237688577191722515003828568443905896711374917497918462677760, 6638837537462522364083348833601920817546619017893790037333152888901901769714199552, 3049939752687159985662220366073486727971871649314787089980547446536534845566593536]
private def defectChunks_7 : Array (ℤ) := #[7812869047827740969626497375233465098319142743331441305316295098281605134974754816, 5834287242904262082153947124226227024674800746502760101594641402124518534395142144, 10119164877537412962036210781974752210561427932945479758301744915499574257192325376, 7939526685604777403633798679097204575019626507611823848255263489001458006218035200, 3913029876287376130876552770353954871595156224614957344232426715386758462591012352]
private def defectChunks_8 : Array (ℤ) := #[5150633038032496976634057857805999850173745034575308100389512137550703256344182080, 6617220085808971491525356567655415888780853399290724558623998496708223707716915456, 10347484641193513306422616413263898939180957995741778297552581916698352421372764416, 7492402525654514122910859539165456332831453344987537052962097966391417614898592512, 3005353533995450097395628927592975627018821418444868094595909994574225121973801024]
private def defectChunks_9 : Array (ℤ) := #[4970254462930955956653886335759691440222132062540551588495915604278146282491987952, 5425324523782344304558081561029320332752658737897967348549944044000135388424676160, 7400696364563581666264539200543641527607111177053001496584018592277429110440448880, 6358342886223648407585078528929552464584920332260258163320217451621170475545002720, 2537789931897890765197349900851160722515248653973250329639908411032822181564809664]
private def defectChunks_10 : Array (ℤ) := #[2771432420088203147755594775056984057166499425520156497466552831416539161280331520, 3166511160764312603535162193989491338128045262639137805903830126530422728708834560, 4678334432289574631590179696067215959941428206863952222424079398579585549339100928, 3793228560227401740956068244140728007546741020382055670155074566319159519907704064, 1692365427074989155248740617682656439316300970570120331115228946830798321201703296]
private def defectChunks_11 : Array (ℤ) := #[4245784854131962024710122727507875953642863514741485932987076340876058356875123392, 5853850502827957015855538074978671289066235994453159664369822734538060740602423376, 7254080189591445082919674526450040960984401434081715499844222838942059415413707040, 6298040883363802489553627757450222954054311438166966027953726194604933900676680000, 2340741561816273692564989652105005578118085141164165058733249573882139997832826688]
private def defectChunks_12 : Array (ℤ) := #[5016332707318650535608248180334063512487164781001301090621970904246361560461332352, 6261760263425500341466531671796563425718389628647864826864979537614595770972324352, 9504955992969604547468640801821100806666950654428532213370947296111751752895323904, 7304482246399490358419773976293671069200201567982366279613063575771101059776957184, 3185602463402035342029304495238418635817137337207014425557429714008131224962457984]
private def defectChunks_13 : Array (ℤ) := #[3354236721674931548939145497495655678940643141450524761422672717003735887292197312, 3065419906216227879576674507303337683250878002295244194951432998255572773302966976, 4471338939520920086112004631493610946672961744084801710341616761968566234006445760, 3926636740099389651399029259771883818910076650977223461829449395683235591513900992, 1335468870173934561976359517003624855360728678942079356815580215876356448821853824]
private def defectChunks_14 : Array (ℤ) := #[3058077689134801311748572575297870177014717789993650050114457992959842120876721600, 3594519461147102332545925402289058103886961714644225749209325165446616985721076032, 6499706761263098227739508297659488581517146569737611121100366510394485256929521344, 4996636682057967244536869284485954844278155486045007357891244497215063973423288096, 1813307801465106429108626658745166898301085106209214607102161388378176498547613568]
private def defectChunks_15 : Array (ℤ) := #[6956809820714116745272677713907691160125108125137859051020808806485229338882741600, 5285177237582630051057595964227641708684012068268890809582574773145893092789063488, 10876780754802602477905948094069968395399233029184251009296986738028547013952102784, 8948858050012787798979344342079199510628710382821226797086346188060249796685160384, 2352659744542603270188594980248117076663122440185999119053919901301418942885709248]
private def defectChunks_16 : Array (ℤ) := #[3607791017463273429211303469042649173378705886432339052477372164825901473405785600, 2968172060655798705144810689468523419192733080973959602681432818041061243689575168, 5749296524924243462217587168626048233895989268070828734016456592740887683516062208, 4415914788139648347580294208103067386861365871822772754696057497463807307384688640, 1504212418213784587130045929591470688124843771059608695117756575024119820421830400]
private def defectChunks_17 : Array (ℤ) := #[3993057754112210034148863906253246565241016360086227622002663483241988077869471360, 4360987990841728097490238921836502158947547547101982536731176768904707569536054272, 6907294885365196648583154348889511565807211298978840401580761458491344475020244480, 5076321644672535700802767935591605003750718496921650497860814265265617730276724608, 2289522238050514901982658628307990854064582238950084552842266986585958059661720320]
private def defectChunks_18 : Array (ℤ) := #[4705163808323065720264346393252986214530839168601575462487402296412073900943057296, 4424773753230588266410185527742972114144271756217898996943934030022478698304763472, 6931413660144217060087601846244360813675803786487980247891454087500932412919759504, 4958627966481964577481446328100001071923940903160633113575657608096161367038837104, 2156171252028726880905630887762416875479169379050425322373252296307435475050148112]
private def defectChunks_19 : Array (ℤ) := #[3632930162764361884083834937713749223477982492767933936475216330051365739843143680, 3995017061540999566636117052051383576743170059013629720719083591113632762171784672, 6989062310851906969163201269535290235305748007869583378194026728989210343521656384, 4544055946986363693873007306767792763076160120486504204663901514472894781146286272, 2158444456621602837724377461624371157278072923654503941397101067049225573307134016]
private def defectChunks_20 : Array (ℤ) := #[4289103811164046665216754679092533624100261079012161438028756964113255538896751360, 4657258640908369594527317104798912928978910829591677418730454189507179683319299520, 7174388265562526281522202177661816570087213517947206087310893600362421376758291840, 5775833952036751068254263650942550147403553583132951916103611341832941217125816032, 2852847290360441674181194810873304462982653381326031721739869179886514859017198208]
private def defectChunks_21 : Array (ℤ) := #[2905213661424976357717816320680359632862570000628003659303658696947898325444569072, 3197508123690928035562729533337664579967934980454322043328250234930341082793284128, 5296093660146110812453492929836115032100053739827421526112943868533468639481597856, 3477781243964000075558785107583448312665091256726222453644415851615750905443858144, 1650302076769255584677190659680677630422571211464605094685687776243318399743751984]
private def defectChunks_22 : Array (ℤ) := #[5991273984405069303003936286734166748938124700260045752468360360971963754505704704, 5748738391489290704632886658526685363094609940759776779841519927219881273662467072, 9939982889724357259391415097462909809006282996447000213988908047895933619275800576, 7247455859487772425925176170606296217421396066073765493747737522953361566888477440, 2868804052243963513879739381365966424336152891516963181125809079683896844466063104]
private def defectChunks_23 : Array (ℤ) := #[3850322655619727842150774014583473117307061388208059821053971274251145634641244672, 1609844394813170850251789512624546945353759821247550765626771223046110710120166400, 3534263126512656735649499968462518598364163558810027716210531523048175655470035968, 2808684741786348543184858865632371652904094121701776168569402196341696085219994112, 1384142433804172522640371438357434877739789455353823365375853536873696277809195520]
private def defectChunks_24 : Array (ℤ) := #[5223044334325475450605428865992717887077293801100362021236290900767176715833040128, 5695323872366445948755968981436585236946471157373672571392935864778520243606560000, 8987850824393211469957985513908055601055479782758692849216921621458428825986159616, 6665516684691690746876595401972887893308395747644949758667960995720896778176489728, 2908884252187591066006963699447719218253573458426059701437166690085401925358863104]
private def defectChunks_25 : Array (ℤ) := #[4087078224780545206366409854535037119489852657423814216880815111438170966066440704, 4258888875709081121850243981623410254448593067212264826081809804308144877750137792, 6323006845964394032106852177479504307206935775464611589217304028153273745421068736, 5730086003474843624563729078077409555799997558496930051534132370848170422996290880, 2343912279578296368179243769839773147608411375119446223810952309061412428543730368]
private def defectChunks_26 : Array (ℤ) := #[2482242233861328076199721698247429354188852609822790126847964579117892321843997936, 1471018089507592482836746266046639981395183794075686529840194073544477151777281024, 2607245442072260349152679097256625973810038898896825361190137965041878293193120208, 3066400692594332570822424870728385653093171752886826637086021073814570286324435536, 1586199011212217278019722600798686877786529455125686334096096541555983119792340848]
private def defectChunks_27 : Array (ℤ) := #[2946306922172248617142565009385351937044366012164805893819573724822086658311203968, 2344887051832300449920367834645691567237909637436208338597474464812489699085293696, 4713026727069729524888805866531608560032370961286506522510130136787259696740233088, 2828319711427978094108476383339548375187066226660940987274143102948648517207675328, 1433627313917711720378152878968666527051450120752982627099354348216903680837425408]
private def defectChunks_28 : Array (ℤ) := #[4831918623950157746086902926816597679160506595200061768577446446935192008021608704, 5075167409416600455207456474337336951201132800882196785950510395663334709452155904, 7226776702683766595272308572977187287255563008396019593027438968677817936846061888, 6556987470919728205985785335002825032669632051461371583208915122855021251814016832, 2619409758827363288958272091204285833652031270779425486816938761157859573209879040]
private def defectChunks_29 : Array (ℤ) := #[4722856037510043422003012255102325742663747578703235242185947243677219295285491712, 3589547505205558433014305504978156230888313548044911255206705792297653244163196928, 5565115677295158199511207682670193544021969552233056352552199743753656733638509056, 5420465890199868658916484853929168160266585217640443256226320295370258321482345984, 2124157645207098683058774812758837330989103268897478503979931224477792254500038144]
private def defectChunks_30 : Array (ℤ) := #[2362859629672784916770541152495087609093973757226347629586920535243476569350256576, 1854373177222406710141362903602079206987927900796932678077539391789693576896534464, 3858018054074130335571630711937886681592883888404831315689604185449726597314103232, 2822285330067156978980623559094216781910763152113869856318083389310675187654726336, 1862871901337718639735074678133952568229995111196929840443438875501325778614719424]
private def defectChunks_31 : Array (ℤ) := #[4042139105832439440779587781434727792599668893747400564033802099215207239019650198, 3735503415865069117918909887068569843078532813174376201417619899663724670280695790, 6518466544548716644244781657701153166256349750905564969157497843237961290051700110, 5576415145540095324685330481755962920082370785356233637050404406710833798136698282, 2301250183248551891371511853745731578159162744447095057128232212120257907585985126]
private def defectChunks_32 : Array (ℤ) := #[1340314247789415145520714163896819569219026305696522253399177850240692678124165248, 1160063720142840397447307403701751036705930808376654329986329377161884503501050240, 2228201695842660016377427433537570066437332642524021719374508187933645187940662912, 1872481707786988530571344226662009529408879014591784088651146828815222885901865856, 1491047041621498408924077602703344257986835199750690093006754255862107783918542464]
private def defectChunks_33 : Array (ℤ) := #[5805897418148090463820744532495855264300865209937935887397810648386544657348927360, 6370626510593970145110711657356116843475427734594967912365638632348791561973081344, 8333610227384041483924612854720219704569929221927485293695684881033285078334277120, 6111469885216753466597431961421602093770696899651393729243624928280081296364397056, 3751899856971761301805265889300403680908230464887790958665819432650113084928898176]
private def defectChunks_34 : Array (ℤ) := #[2804445393223464802781472177441542052727622325066770432290932798287765375916178688, 3046783770265212941971427583386419214079716796059227926408565913061474519547657088, 4629006220784290394157163770994387666356491057236894334155773540489788980364108032, 3247625194917753293747170293575545672656041544582735598665007010783960592934168192, 2457876102566934545780378723426651852865503781406234995433725796362813583236041344]
private def defectChunks_35 : Array (ℤ) := #[3809263381384615106882765905366051714134129536843092555565839627797910702474231808, 3245066432520979679230518193834920105391018172373001428199189091793222470352621952, 5277649499653455701403555135793253846392528714229938949299622405342898446041746304, 4404756064599456688728671961729958424875642188420920009233464260933788978819792000, 2150029557597685109095078471747070749574992266077054903347191311270005593981956864]
private def defectChunks_36 : Array (ℤ) := #[20119568956765856110935295514299957480114830482801748724648207216637228817856913664, 16350548757317816065264643819880126778203944420053845575049158329567632441928695808, 11596613884188198329323909197188763611230151134328106137021183616300379506516013056, 18130542633220320900366103141001790968500297647183472944000568911606659336771846656, 11948051889756478983608213014556100994202499132852584064367882123204521968752024320]
private def defectChunks : Array (Array (ℤ)) := #[defectChunks_0,
  defectChunks_1,
  defectChunks_2,
  defectChunks_3,
  defectChunks_4,
  defectChunks_5,
  defectChunks_6,
  defectChunks_7,
  defectChunks_8,
  defectChunks_9,
  defectChunks_10,
  defectChunks_11,
  defectChunks_12,
  defectChunks_13,
  defectChunks_14,
  defectChunks_15,
  defectChunks_16,
  defectChunks_17,
  defectChunks_18,
  defectChunks_19,
  defectChunks_20,
  defectChunks_21,
  defectChunks_22,
  defectChunks_23,
  defectChunks_24,
  defectChunks_25,
  defectChunks_26,
  defectChunks_27,
  defectChunks_28,
  defectChunks_29,
  defectChunks_30,
  defectChunks_31,
  defectChunks_32,
  defectChunks_33,
  defectChunks_34,
  defectChunks_35,
  defectChunks_36]

def defectPart (i b : ℕ) : ℤ := (defectChunks.getD i #[]).getD b 0

def checkedDefect (i : ℕ) : ℤ :=
  sumChunks m (defectPart i) + rowWeight m a i * (m : ℤ) * (420 * (n : ℤ) * scale)

private theorem defect_0_0 : defectPart 0 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 0) := by
  decide +kernel

private theorem defect_0_1 : defectPart 0 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 0) := by
  decide +kernel

private theorem defect_0_2 : defectPart 0 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 0) := by
  decide +kernel

private theorem defect_0_3 : defectPart 0 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 0) := by
  decide +kernel

private theorem defect_0_4 : defectPart 0 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 0) := by
  decide +kernel

theorem defect_0 : ∀ b : ℕ, b < m / width + 1 → defectPart 0 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 0) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_0_0) defect_0_1) defect_0_2) defect_0_3) defect_0_4

theorem row_0 : stepRow n m a fAt 0 ≤ E ∧ rowWeight m a 0 ≤ M ∧ checkedDefect 0 ≤ delta := by
  decide +kernel

private theorem defect_1_0 : defectPart 1 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 1) := by
  decide +kernel

private theorem defect_1_1 : defectPart 1 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 1) := by
  decide +kernel

private theorem defect_1_2 : defectPart 1 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 1) := by
  decide +kernel

private theorem defect_1_3 : defectPart 1 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 1) := by
  decide +kernel

private theorem defect_1_4 : defectPart 1 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 1) := by
  decide +kernel

theorem defect_1 : ∀ b : ℕ, b < m / width + 1 → defectPart 1 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 1) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_1_0) defect_1_1) defect_1_2) defect_1_3) defect_1_4

theorem row_1 : stepRow n m a fAt 1 ≤ E ∧ rowWeight m a 1 ≤ M ∧ checkedDefect 1 ≤ delta := by
  decide +kernel

private theorem defect_2_0 : defectPart 2 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 2) := by
  decide +kernel

private theorem defect_2_1 : defectPart 2 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 2) := by
  decide +kernel

private theorem defect_2_2 : defectPart 2 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 2) := by
  decide +kernel

private theorem defect_2_3 : defectPart 2 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 2) := by
  decide +kernel

private theorem defect_2_4 : defectPart 2 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 2) := by
  decide +kernel

theorem defect_2 : ∀ b : ℕ, b < m / width + 1 → defectPart 2 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 2) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_2_0) defect_2_1) defect_2_2) defect_2_3) defect_2_4

theorem row_2 : stepRow n m a fAt 2 ≤ E ∧ rowWeight m a 2 ≤ M ∧ checkedDefect 2 ≤ delta := by
  decide +kernel

private theorem defect_3_0 : defectPart 3 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 3) := by
  decide +kernel

private theorem defect_3_1 : defectPart 3 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 3) := by
  decide +kernel

private theorem defect_3_2 : defectPart 3 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 3) := by
  decide +kernel

private theorem defect_3_3 : defectPart 3 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 3) := by
  decide +kernel

private theorem defect_3_4 : defectPart 3 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 3) := by
  decide +kernel

theorem defect_3 : ∀ b : ℕ, b < m / width + 1 → defectPart 3 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 3) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_3_0) defect_3_1) defect_3_2) defect_3_3) defect_3_4

theorem row_3 : stepRow n m a fAt 3 ≤ E ∧ rowWeight m a 3 ≤ M ∧ checkedDefect 3 ≤ delta := by
  decide +kernel

private theorem defect_4_0 : defectPart 4 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 4) := by
  decide +kernel

private theorem defect_4_1 : defectPart 4 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 4) := by
  decide +kernel

private theorem defect_4_2 : defectPart 4 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 4) := by
  decide +kernel

private theorem defect_4_3 : defectPart 4 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 4) := by
  decide +kernel

private theorem defect_4_4 : defectPart 4 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 4) := by
  decide +kernel

theorem defect_4 : ∀ b : ℕ, b < m / width + 1 → defectPart 4 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 4) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_4_0) defect_4_1) defect_4_2) defect_4_3) defect_4_4

theorem row_4 : stepRow n m a fAt 4 ≤ E ∧ rowWeight m a 4 ≤ M ∧ checkedDefect 4 ≤ delta := by
  decide +kernel

private theorem defect_5_0 : defectPart 5 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 5) := by
  decide +kernel

private theorem defect_5_1 : defectPart 5 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 5) := by
  decide +kernel

private theorem defect_5_2 : defectPart 5 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 5) := by
  decide +kernel

private theorem defect_5_3 : defectPart 5 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 5) := by
  decide +kernel

private theorem defect_5_4 : defectPart 5 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 5) := by
  decide +kernel

theorem defect_5 : ∀ b : ℕ, b < m / width + 1 → defectPart 5 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 5) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_5_0) defect_5_1) defect_5_2) defect_5_3) defect_5_4

theorem row_5 : stepRow n m a fAt 5 ≤ E ∧ rowWeight m a 5 ≤ M ∧ checkedDefect 5 ≤ delta := by
  decide +kernel

private theorem defect_6_0 : defectPart 6 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 6) := by
  decide +kernel

private theorem defect_6_1 : defectPart 6 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 6) := by
  decide +kernel

private theorem defect_6_2 : defectPart 6 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 6) := by
  decide +kernel

private theorem defect_6_3 : defectPart 6 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 6) := by
  decide +kernel

private theorem defect_6_4 : defectPart 6 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 6) := by
  decide +kernel

theorem defect_6 : ∀ b : ℕ, b < m / width + 1 → defectPart 6 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 6) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_6_0) defect_6_1) defect_6_2) defect_6_3) defect_6_4

theorem row_6 : stepRow n m a fAt 6 ≤ E ∧ rowWeight m a 6 ≤ M ∧ checkedDefect 6 ≤ delta := by
  decide +kernel

private theorem defect_7_0 : defectPart 7 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 7) := by
  decide +kernel

private theorem defect_7_1 : defectPart 7 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 7) := by
  decide +kernel

private theorem defect_7_2 : defectPart 7 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 7) := by
  decide +kernel

private theorem defect_7_3 : defectPart 7 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 7) := by
  decide +kernel

private theorem defect_7_4 : defectPart 7 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 7) := by
  decide +kernel

theorem defect_7 : ∀ b : ℕ, b < m / width + 1 → defectPart 7 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 7) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_7_0) defect_7_1) defect_7_2) defect_7_3) defect_7_4

theorem row_7 : stepRow n m a fAt 7 ≤ E ∧ rowWeight m a 7 ≤ M ∧ checkedDefect 7 ≤ delta := by
  decide +kernel

private theorem defect_8_0 : defectPart 8 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 8) := by
  decide +kernel

private theorem defect_8_1 : defectPart 8 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 8) := by
  decide +kernel

private theorem defect_8_2 : defectPart 8 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 8) := by
  decide +kernel

private theorem defect_8_3 : defectPart 8 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 8) := by
  decide +kernel

private theorem defect_8_4 : defectPart 8 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 8) := by
  decide +kernel

theorem defect_8 : ∀ b : ℕ, b < m / width + 1 → defectPart 8 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 8) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_8_0) defect_8_1) defect_8_2) defect_8_3) defect_8_4

theorem row_8 : stepRow n m a fAt 8 ≤ E ∧ rowWeight m a 8 ≤ M ∧ checkedDefect 8 ≤ delta := by
  decide +kernel

private theorem defect_9_0 : defectPart 9 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 9) := by
  decide +kernel

private theorem defect_9_1 : defectPart 9 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 9) := by
  decide +kernel

private theorem defect_9_2 : defectPart 9 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 9) := by
  decide +kernel

private theorem defect_9_3 : defectPart 9 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 9) := by
  decide +kernel

private theorem defect_9_4 : defectPart 9 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 9) := by
  decide +kernel

theorem defect_9 : ∀ b : ℕ, b < m / width + 1 → defectPart 9 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 9) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_9_0) defect_9_1) defect_9_2) defect_9_3) defect_9_4

theorem row_9 : stepRow n m a fAt 9 ≤ E ∧ rowWeight m a 9 ≤ M ∧ checkedDefect 9 ≤ delta := by
  decide +kernel

private theorem defect_10_0 : defectPart 10 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 10) := by
  decide +kernel

private theorem defect_10_1 : defectPart 10 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 10) := by
  decide +kernel

private theorem defect_10_2 : defectPart 10 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 10) := by
  decide +kernel

private theorem defect_10_3 : defectPart 10 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 10) := by
  decide +kernel

private theorem defect_10_4 : defectPart 10 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 10) := by
  decide +kernel

theorem defect_10 : ∀ b : ℕ, b < m / width + 1 → defectPart 10 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 10) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_10_0) defect_10_1) defect_10_2) defect_10_3) defect_10_4

theorem row_10 : stepRow n m a fAt 10 ≤ E ∧ rowWeight m a 10 ≤ M ∧ checkedDefect 10 ≤ delta := by
  decide +kernel

private theorem defect_11_0 : defectPart 11 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 11) := by
  decide +kernel

private theorem defect_11_1 : defectPart 11 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 11) := by
  decide +kernel

private theorem defect_11_2 : defectPart 11 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 11) := by
  decide +kernel

private theorem defect_11_3 : defectPart 11 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 11) := by
  decide +kernel

private theorem defect_11_4 : defectPart 11 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 11) := by
  decide +kernel

theorem defect_11 : ∀ b : ℕ, b < m / width + 1 → defectPart 11 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 11) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_11_0) defect_11_1) defect_11_2) defect_11_3) defect_11_4

theorem row_11 : stepRow n m a fAt 11 ≤ E ∧ rowWeight m a 11 ≤ M ∧ checkedDefect 11 ≤ delta := by
  decide +kernel

private theorem defect_12_0 : defectPart 12 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 12) := by
  decide +kernel

private theorem defect_12_1 : defectPart 12 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 12) := by
  decide +kernel

private theorem defect_12_2 : defectPart 12 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 12) := by
  decide +kernel

private theorem defect_12_3 : defectPart 12 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 12) := by
  decide +kernel

private theorem defect_12_4 : defectPart 12 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 12) := by
  decide +kernel

theorem defect_12 : ∀ b : ℕ, b < m / width + 1 → defectPart 12 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 12) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_12_0) defect_12_1) defect_12_2) defect_12_3) defect_12_4

theorem row_12 : stepRow n m a fAt 12 ≤ E ∧ rowWeight m a 12 ≤ M ∧ checkedDefect 12 ≤ delta := by
  decide +kernel

private theorem defect_13_0 : defectPart 13 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 13) := by
  decide +kernel

private theorem defect_13_1 : defectPart 13 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 13) := by
  decide +kernel

private theorem defect_13_2 : defectPart 13 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 13) := by
  decide +kernel

private theorem defect_13_3 : defectPart 13 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 13) := by
  decide +kernel

private theorem defect_13_4 : defectPart 13 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 13) := by
  decide +kernel

theorem defect_13 : ∀ b : ℕ, b < m / width + 1 → defectPart 13 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 13) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_13_0) defect_13_1) defect_13_2) defect_13_3) defect_13_4

theorem row_13 : stepRow n m a fAt 13 ≤ E ∧ rowWeight m a 13 ≤ M ∧ checkedDefect 13 ≤ delta := by
  decide +kernel

private theorem defect_14_0 : defectPart 14 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 14) := by
  decide +kernel

private theorem defect_14_1 : defectPart 14 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 14) := by
  decide +kernel

private theorem defect_14_2 : defectPart 14 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 14) := by
  decide +kernel

private theorem defect_14_3 : defectPart 14 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 14) := by
  decide +kernel

private theorem defect_14_4 : defectPart 14 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 14) := by
  decide +kernel

theorem defect_14 : ∀ b : ℕ, b < m / width + 1 → defectPart 14 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 14) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_14_0) defect_14_1) defect_14_2) defect_14_3) defect_14_4

theorem row_14 : stepRow n m a fAt 14 ≤ E ∧ rowWeight m a 14 ≤ M ∧ checkedDefect 14 ≤ delta := by
  decide +kernel

private theorem defect_15_0 : defectPart 15 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 15) := by
  decide +kernel

private theorem defect_15_1 : defectPart 15 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 15) := by
  decide +kernel

private theorem defect_15_2 : defectPart 15 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 15) := by
  decide +kernel

private theorem defect_15_3 : defectPart 15 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 15) := by
  decide +kernel

private theorem defect_15_4 : defectPart 15 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 15) := by
  decide +kernel

theorem defect_15 : ∀ b : ℕ, b < m / width + 1 → defectPart 15 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 15) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_15_0) defect_15_1) defect_15_2) defect_15_3) defect_15_4

theorem row_15 : stepRow n m a fAt 15 ≤ E ∧ rowWeight m a 15 ≤ M ∧ checkedDefect 15 ≤ delta := by
  decide +kernel

private theorem defect_16_0 : defectPart 16 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 16) := by
  decide +kernel

private theorem defect_16_1 : defectPart 16 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 16) := by
  decide +kernel

private theorem defect_16_2 : defectPart 16 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 16) := by
  decide +kernel

private theorem defect_16_3 : defectPart 16 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 16) := by
  decide +kernel

private theorem defect_16_4 : defectPart 16 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 16) := by
  decide +kernel

theorem defect_16 : ∀ b : ℕ, b < m / width + 1 → defectPart 16 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 16) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_16_0) defect_16_1) defect_16_2) defect_16_3) defect_16_4

theorem row_16 : stepRow n m a fAt 16 ≤ E ∧ rowWeight m a 16 ≤ M ∧ checkedDefect 16 ≤ delta := by
  decide +kernel

private theorem defect_17_0 : defectPart 17 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 17) := by
  decide +kernel

private theorem defect_17_1 : defectPart 17 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 17) := by
  decide +kernel

private theorem defect_17_2 : defectPart 17 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 17) := by
  decide +kernel

private theorem defect_17_3 : defectPart 17 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 17) := by
  decide +kernel

private theorem defect_17_4 : defectPart 17 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 17) := by
  decide +kernel

theorem defect_17 : ∀ b : ℕ, b < m / width + 1 → defectPart 17 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 17) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_17_0) defect_17_1) defect_17_2) defect_17_3) defect_17_4

theorem row_17 : stepRow n m a fAt 17 ≤ E ∧ rowWeight m a 17 ≤ M ∧ checkedDefect 17 ≤ delta := by
  decide +kernel

private theorem defect_18_0 : defectPart 18 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 18) := by
  decide +kernel

private theorem defect_18_1 : defectPart 18 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 18) := by
  decide +kernel

private theorem defect_18_2 : defectPart 18 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 18) := by
  decide +kernel

private theorem defect_18_3 : defectPart 18 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 18) := by
  decide +kernel

private theorem defect_18_4 : defectPart 18 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 18) := by
  decide +kernel

theorem defect_18 : ∀ b : ℕ, b < m / width + 1 → defectPart 18 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 18) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_18_0) defect_18_1) defect_18_2) defect_18_3) defect_18_4

theorem row_18 : stepRow n m a fAt 18 ≤ E ∧ rowWeight m a 18 ≤ M ∧ checkedDefect 18 ≤ delta := by
  decide +kernel

end Chirped73
