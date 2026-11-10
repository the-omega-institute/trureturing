/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0191
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0162
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part05
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0170 : List (List (List (List ℕ))) :=
  [[[[13323037,88623674,67553437],[3154837,68287274,57385237]],[[23491237,108960074,77721637],[13323037,88623674,67553437]]],[[[24493224,172941648,132954024],[3866304,131687808,112327104]],[[45120144,214195488,153580944],[24493224,172941648,132954024]]],[[[11080408,84138416,65310808],[621688,63220976,54852088]],[[21539128,105055856,75769528],[11080408,84138416,65310808]]]]

private theorem identity_0170 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0170 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0170, p_coupled] <;> ring

private theorem negative_0170 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0170 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0170] at hp
  linarith only [hp]

private def coefficients_0171 : List (List (List (List ℕ))) :=
  [[[[76471712429341,30633079469341],[61430910989341,15592278029341]],[[145173176938682,53495911018682],[115091574058682,23414308138682]],[[62255406749341,16416773789341],[47214605309341,1375972349341]]],[[[304787080717364,122072157709364],[244618878013364,61903955005364]],[[577582970594728,212153124578728],[457246565186728,91816719170728]],[[247101603829364,64386680821364],[186933401125364,4218478117364]]],[[[455481181683646,182365979226046],[365223648267646,92108445810046]],[[861615257880092,315384852964892],[681100191048092,134869786132892]],[[367727250850846,94612048393246],[277469717434846,4354514977246]]],[[[302487962357124,121047794625924],[242314287418404,60874119687204]],[[571174306781688,208293971319288],[450826956904248,87946621441848]],[[243171320837364,61731153106164],[182997645898644,1557478167444]]],[[[75322145553939,30120890232339],[60278602767219,15077347445619]],[[141968835742518,51566325099318],[111881750169078,21479239525878]],[[60290263658979,15089008337379],[45246720872259,45465550659]]]]

private theorem identity_0171 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(5051727851 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0171 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0171, p_headbox] <;> ring

private theorem negative_0171 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0171 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0171] at hp
  linarith only [hp]

private def coefficients_0172 : List (List (List (List ℕ))) :=
  [[[[60755419,369421238,293171419],[20082619,288075638,252498619]],[[101428219,450766838,333844219],[60755419,369421238,293171419]]],[[[112318398,720457596,577150398],[30391758,556604316,495223758]],[[194245038,884310876,659077038],[112318398,720457596,577150398]]],[[[51383421,350677242,283799421],[10129581,268169562,242545581]],[[92637261,433184922,325053261],[51383421,350677242,283799421]]]]

private theorem identity_0172 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(1125509 / 110182400 : ℝ)) =
      tensor4 coefficients_0172 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0172, p_coupled] <;> ring

private theorem negative_0172 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0172 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0172] at hp
  linarith only [hp]

private def coefficients_0173 : List (List (List (List ℕ))) :=
  [[[[785178362354381,418469298674381],[664851950834381,298142887154381]],[[1405057817188762,671639689828762],[1164404994148762,430986866788762]],[[594095223794381,227386160114381],[473768812274381,107059748594381]]],[[[3125333276297524,1661055456905524],[2644007642441524,1179729823049524]],[[5586549685811048,2657994047027048],[4623898418099048,1695342779315048]],[[2358259375337524,893981555945524],[1876933741481524,412655922089524]]],[[[4664753706313486,2472170167830286],[3942739805977486,1750156267494286]],[[8328958961374172,3943791884407772],[6884931160702172,2499764083735772]],[[3510039225011086,1317455686527886],[2788025324675086,595441786191886]]],[[[3094221029946004,1635051156435604],[2612864474303284,1153694600792884]],[[5518500139860248,2600160392839448],[4555787028574808,1637447281554008]],[[2321681228183044,862511354672644],[1840324672540324,381154799029924]]],[[[769622234168099,405467143428899],[649280356525379,285125265786179]],[[1371033040293238,642722858814838],[1130349285007798,402039103529398]],[[575806151307539,211651060568339],[455464273664819,91309182925619]]]]

private theorem identity_0173 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(91309182925619 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0173 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0173, p_headbox] <;> ring

private theorem negative_0173 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0173 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0173] at hp
  linarith only [hp]

private def coefficients_0174 : List (List (List (List ℕ))) :=
  [[[[192596579,881013958,672922979],[29905379,555631558,510231779]],[[273942179,1043705158,754268579],[111250979,718322758,591577379]]],[[[366227238,1724096076,1326880038],[39682758,1071007116,1000335558]],[[529499478,2050640556,1490152278],[202954998,1397551596,1163607798]]],[[[173451101,842723002,653777501],[9597821,515016442,489924221]],[[255377741,1006576282,735704141],[91524461,678869722,571850861]]]]

private theorem identity_0174 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(9597821 / 3966566400 : ℝ)) =
      tensor4 coefficients_0174 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0174, p_coupled] <;> ring

private theorem negative_0174 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0174 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0174] at hp
  linarith only [hp]

private theorem node_0185 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0173 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0174 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0175 : List (List (List (List ℕ))) :=
  [[[[388832516877107,206754971507507],[328661578055747,146584032686147]],[[693559319732734,329404228993534],[573217442090014,209062351350814]],[[291924475446827,109846930077227],[231753536625467,49675991255867]]],[[[1547464020871624,820428594670024],[1306774788122104,579739361920504]],[[2757053289587288,1302982437184088],[2275674824088248,821603971685048]],[[1158469590310864,431434164109264],[917780357561344,190744931359744]]],[[[2309308972094264,1220665734513464],[1948269157141784,859625919560984]],[[4109632342141888,1932345866980288],[3387552712236928,1210266237075328]],[[1723778142405224,635134904824424],[1362738327452744,274095089871944]]],[[[1531555940664000,807065562628800],[1290860248492800,566369870457600]],[[2722342083717600,1273361327647200],[2240950699375200,791969943304800]],[[1139845413348000,415355035312800],[899149721176800,174659343141600]]],[[[380878470860472,200073449574072],[320704299713592,139899278427192]],[[676203708022704,314593665449904],[555855365728944,194245323156144]],[[282612384103032,101807362816632],[222438212956152,41633191669752]]]]

private theorem identity_0175 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(578238773191 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0175 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0175, p_headbox] <;> ring

private theorem negative_0175 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0175 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0175] at hp
  linarith only [hp]

private def coefficients_0176 : List (List (List (List ℕ))) :=
  [[[[772551761,970880081],[5246328322,5642984962],[4529556401,4727884721]],[[3335287762,3731944402],[14138101604,14931414884],[10914373522,11311030162]],[[2576680961,2775009281],[8919663202,9316319842],[6398762081,6597090401]]],[[[1952842886,2349499526],[11323242412,12116555692],[9481959206,9878615846]],[[7493607772,8286921052],[29952481784,31539108344],[22681993372,23475306652]],[[5568654806,5965311446],[18685019212,19478332492],[13227924086,13624580726]]],[[[1180983127,1379311447],[6078298094,6474954734],[4953094807,5151423127]],[[4159704014,4556360654],[15817148188,16610461468],[11769003854,12165660494]],[[2992665847,3190994167],[9766740014,10163396654],[6829854007,7028182327]]]]

private theorem identity_0176 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(772551761 / 5553192960 : ℝ)) =
      tensor4 coefficients_0176 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0176, p_variance] <;> ring

private theorem negative_0176 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0176 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0176] at hp
  linarith only [hp]

private theorem node_0186 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0175 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0176 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0184 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 64 : ℝ)
  · exact node_0185 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0186 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0177 : List (List (List (List ℕ))) :=
  [[[[100750339,317708678,213084739],[60077539,236363078,172411939]],[[141423139,399054278,253757539],[100750339,317708678,213084739]]],[[[191727198,615870396,416395998],[109800558,452017116,334469358]],[[273653838,779723676,498322638],[191727198,615870396,416395998]]],[[[90797301,297802602,203131701],[49543461,215294922,161877861]],[[132051141,380310282,244385541],[90797301,297802602,203131701]]]]

private theorem identity_0177 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(5504829 / 110182400 : ℝ)) =
      tensor4 coefficients_0177 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0177, p_coupled] <;> ring

private theorem negative_0177 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0177 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0177] at hp
  linarith only [hp]

private theorem node_0183 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0184 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0177 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0182 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0172 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0183 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0181 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0171 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0182 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0178 : List (List (List (List ℕ))) :=
  [[[[36136037444267,13535409783467],[32375151747587,9774524086787]],[[67934347205854,22733091884254],[60412575812494,15211320490894]],[[28620096496787,6019468835987],[24859210800107,2258583139307]]],[[[143944459706384,53859522285584],[128900792867624,38815855446824]],[[270087906917608,89918032076008],[240000573240088,59830698398488]],[[113475252886424,23390315465624],[98431586047664,8346648626864]]],[[[214992238421504,80340076527104],[192427110755264,57774948860864]],[[402610313512768,133305989723968],[357480058180288,88175734391488]],[[168682614824864,34030452930464],[146117487158624,11465325264224]]],[[[142695236398080,53243214228480],[127652436180480,38200414010880]],[[266694278991360,87790234652160],[236608678556160,57704634216960]],[[111419851975680,21967829806080],[96377051758080,6925029588480]]],[[[35511418534912,13227248499712],[31750964841472,9466794806272]],[[66237521782784,21669181712384],[58716614395904,14148274325504]],[[27592391836672,5308221801472],[23831938143232,1547768108032]]]]

private theorem identity_0178 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1511492293 / 49582080000 : ℝ)) =
      tensor4 coefficients_0178 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0178, p_headbox] <;> ring

private theorem negative_0178 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0178 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0178] at hp
  linarith only [hp]

private def coefficients_0179 : List (List (List (List ℕ))) :=
  [[[[28684336085507,17384022255107],[24923450388827,13623136558427]],[[53030944488334,30430316827534],[45509173094974,22908545434174]],[[21168395138027,9868081307627],[17407509441347,6107195610947]]],[[[114137530219304,69095061508904],[99093863380544,54051394670144]],[[210474047943448,120389110522648],[180386714265928,90301776845128]],[[83668323399344,38625854688944],[68624656560584,23582187850184]]],[[[170282216782784,102956135835584],[147717089116544,80391008169344]],[[313190270235328,178538108340928],[268060014902848,133407853008448]],[[123972593186144,56646512238944],[101407465519904,34081384572704]]],[[[112889173532160,68163162447360],[97846373314560,53120362229760]],[[207082153259520,117630131089920],[176996552824320,87544530654720]],[[81613789109760,36887778024960],[66570988892160,21844977807360]]],[[[28060149179392,16918064161792],[24299695485952,13157610468352]],[[51334983071744,29050813036544],[43814075684864,21529905649664]],[[20141122481152,8999037463552],[16380668787712,5238583770112]]]]

private theorem identity_0179 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(5115804463 / 49582080000 : ℝ)) =
      tensor4 coefficients_0179 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0179, p_headbox] <;> ring

private theorem negative_0179 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0179 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0179] at hp
  linarith only [hp]

private def coefficients_0180 : List (List (List (List ℕ))) :=
  [[[[37953749,134011498,94120949],[17326829,92757658,73494029]],[[58580669,175265338,114747869],[37953749,134011498,94120949]]],[[[70550680,257309360,182885080],[29006320,174220640,141340720]],[[112095040,340398080,224429440],[70550680,257309360,182885080]]],[[[32507152,123118304,88674352],[11589712,81283424,67756912]],[[53424592,164953184,109591792],[32507152,123118304,88674352]]]]

private theorem identity_0180 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(724357 / 30988800 : ℝ)) =
      tensor4 coefficients_0180 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0180, p_coupled] <;> ring

private theorem negative_0180 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0180 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0180] at hp
  linarith only [hp]

private theorem node_0189 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0179 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0180 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0188 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0178 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0189 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0181 : List (List (List (List ℕ))) :=
  [[[[28269749,180494698,144477749],[7642829,139240858,123850829]],[[48896669,221748538,165104669],[28269749,180494698,144477749]]],[[[51763720,351437840,284179720],[10219360,268349120,242635360]],[[93308080,434526560,325724080],[51763720,351437840,284179720]]],[[[23404192,170763584,139612192],[2486752,128928704,118694752]],[[44321632,212598464,160529632],[23404192,170763584,139612192]]]]

private theorem identity_0181 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0181 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0181, p_coupled] <;> ring

private theorem negative_0181 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0181 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0181] at hp
  linarith only [hp]

private def coefficients_0182 : List (List (List (List ℕ))) :=
  [[[[21217761,120381921],[955249362,1153577682],[947976561,1047140721]],[[927359442,1125687762],[3712884804,4109541444],[2813415282,3011743602]],[[920086641,1019250801],[2785525362,2983853682],[1879383681,1978547841]]],[[[243220446,441548766],[2319622092,2716278732],[2104291566,2302619886]],[[2263842252,2660498892],[8259123384,9052436664],[6051060972,6447717612]],[[2048511726,2246840046],[5995281132,6391937772],[3974659326,4172987646]]],[[[222694687,321858847],[1365756734,1564085054],[1157007007,1256171167]],[[1337866814,1536195134],[4549006588,4945663228],[3239029694,3437358014]],[[1129117087,1228281247],[3211139774,3409468094],[2095967647,2195131807]]]]

private theorem identity_0182 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(2357529 / 154255360 : ℝ)) =
      tensor4 coefficients_0182 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0182, p_variance] <;> ring

private theorem negative_0182 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0182 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0182] at hp
  linarith only [hp]

private theorem node_0190 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0181 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0182 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0187 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0188 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0190 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0180 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0181 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0187 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0183 : List (List (List (List ℕ))) :=
  [[[[22910197,72935594,48088597],[12741997,52599194,37920397]],[[33078397,93271994,58256797],[22910197,72935594,48088597]]],[[[43377024,140984448,93733824],[22750104,99730608,73106904]],[[64003944,182238288,114360744],[43377024,140984448,93733824]]],[[[20377048,67869296,45555448],[9918328,46951856,35096728]],[[30835768,88786736,56014168],[20377048,67869296,45555448]]]]

private theorem identity_0183 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(1239791 / 15494400 : ℝ)) =
      tensor4 coefficients_0183 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0183, p_coupled] <;> ring

private theorem negative_0183 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0183 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0183] at hp
  linarith only [hp]

private theorem node_0179 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0180 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0183 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0178 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0170 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0179 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0184 : List (List (List (List ℕ))) :=
  [[[[23491237,108960074,77721637],[3154837,68287274,57385237]],[[33659437,129296474,87889837],[13323037,88623674,67553437]]],[[[45120144,214195488,153580944],[3866304,131687808,112327104]],[[65747064,255449328,174207864],[24493224,172941648,132954024]]],[[[21539128,105055856,75769528],[621688,63220976,54852088]],[[31997848,125973296,86228248],[11080408,84138416,65310808]]]]

private theorem identity_0184 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0184 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0184, p_coupled] <;> ring

private theorem negative_0184 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0184 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0184] at hp
  linarith only [hp]

private theorem node_0177 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0178 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0184 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0161 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 16 : ℝ)
  · exact SixRowMiddleCertificate.Subtrees.Part05Node0162.exclude x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0177 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0185 : List (List (List (List ℕ))) :=
  [[[[11932667,35486134,21616667],[6993827,25608454,16677827]],[[16871507,45363814,26555507],[11932667,35486134,21616667]]],[[[22878688,68998976,42246688],[12710488,48662576,32078488]],[[33046888,89335376,52414888],[22878688,68998976,42246688]]],[[[10856242,33333284,20540242],[5626882,22874564,15310882]],[[16085602,43792004,25769602],[10856242,33333284,20540242]]]]

private theorem identity_0185 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(2813441 / 15494400 : ℝ)) =
      tensor4 coefficients_0185 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0185, p_coupled] <;> ring

private theorem negative_0185 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0185 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0185] at hp
  linarith only [hp]

private theorem node_0160 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0161 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0185 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0159 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0160 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact SixRowMiddleCertificate.Subtrees.Part05Node0191.exclude x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0206 : List (List (List (List ℕ))) :=
  [[[[7478027,45944854,30719627],[2539187,36067174,25780787]],[[12416867,55822534,35658467],[7478027,45944854,30719627]]],[[[14259928,90497456,60743128],[4091728,70161056,50574928]],[[24428128,110833856,70911328],[14259928,90497456,60743128]]],[[[6692122,44373044,29933722],[1462762,33914324,24704362]],[[11921482,54831764,35163082],[6692122,44373044,29933722]]]]

private theorem identity_0206 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(731381 / 15494400 : ℝ)) =
      tensor4 coefficients_0206 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0206, p_coupled] <;> ring

private theorem negative_0206 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0206 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0206] at hp
  linarith only [hp]

private def coefficients_0207 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0207 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0207 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0207, p_mass] <;> ring

private theorem negative_0207 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0207 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0207] at hp
  linarith only [hp]

private theorem node_0210 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0206 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.mass) (negative_0207 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_0159 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0210 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0208 : List (List (List (List ℕ))) :=
  [[[[10143107,28033414,14016707],[5494787,18736774,9368387]],[[14791427,37330054,18665027],[10143107,28033414,14016707]]],[[[19479126,54452652,27226326],[9601446,34697292,17348646]],[[29356806,74208012,37104006],[19479126,54452652,27226326]]],[[[9156461,26060122,13030061],[3927101,15601402,7800701]],[[14385821,36518842,18259421],[9156461,26060122,13030061]]]]

private theorem identity_0208 (x0 x1 x2 x3 : ℝ) :
    (15494400 : ℝ)*(-p_coupled x0 x1 x2 x3-(3927101 / 15494400 : ℝ)) =
      tensor4 coefficients_0208 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0208, p_coupled] <;> ring

private theorem negative_0208 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0208 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0208] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0208 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0209 : List (List (List (List ℕ))) :=
  [[[[9134272,15332032],[78696704,91092224],[76534912,82732672]],[[78696704,91092224],[294518848,319309888],[229767104,242162624]],[[76534912,82732672],[229767104,242162624],[160204672,166402432]]],[[[32100480,44496000],[188834040,213625080],[170678520,183074040]],[[188834040,213625080],[659472480,709054560],[498528360,523319400]],[[170678520,183074040],[498528360,523319400],[341794800,354190320]]],[[[23312209,29509969],[110829338,123224858],[94489609,100687369]],[[110829338,123224858],[366337636,391128676],[269453258,281848778]],[[94489609,100687369],[269453258,281848778],[181936129,188133889]]]]

private theorem identity_0209 (x0 x1 x2 x3 : ℝ) :
    (10846080 : ℝ)*(-p_variance x0 x1 x2 x3-(20389 / 24210 : ℝ)) =
      tensor4 coefficients_0209 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1)) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0209, p_variance] <;> ring

private theorem negative_0209 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0209 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0209] at hp
  linarith only [hp]

theorem exclude_02 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.variance) (negative_0209 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part05
